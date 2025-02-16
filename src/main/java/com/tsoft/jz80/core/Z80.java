/**
 *          The "halt" instruction enables the HALT state after PC is incremented during the opcode
 *          fetch. The CPU neither decrements nor avoids incrementing PC "so that the instruction is
 *          re-executed" as Sean Young writes in section 5.4 of "The Undocumented Z80 Documented".
 *          During the HALT state, the CPU repeatedly executes an internal NOP operation. Each NOP
 *          consists of 1 M1 cycle with 4 T-states that fetches and disregards the next opcode after
 *          "halt" without incrementing PC. This opcode is read again and again until an exit
 *          condition occurs (i.e., INT, NMI or RESET). This was first documented by Tony Brewer and
 *          later re-confirmed by the HALT2INT test written by Mark Woodmass.
 *
 *          If the opcode following halt is read from an address that is not contended, but the halt
 *          opcode is, or viceversa, then the contention emulation will not be accurate if the
 *          emulator doesn't implement this correctly. The test places a "halt" opcode in the
 *          boundaries of the VRAM so that this can be tested.
 *          ----------------------------------
 *          Contended RAM | Uncontended RAM
 *          --------------+-------------------
 *             ... | halt | nop  | nop  | ...
 *          --------------+-------------------
 *            7FFE | 7FFF | 8000 | 8001 | ...
 *
 *          Correct implementation:
 *
 *          fetch(7FFFh)
 *          -> CPU increments PC
 *          -> CPU enables the HALT state
 *          (void)fetch(8000h)
 *          (void)fetch(8000h)
 *          (void)fetch(8000h)
 *          (void)fetch(8000h)
 *          (void)fetch(8000h)
 *          ...
 *          INT
 *          -> CPU disables the HALT state
 *          -> CPU responds to the interrupt
 *          -> CPU returns from the ISR
 *          fetch(8000h)
 *          fetch(8001h)
 *
 *
 *          Incorrect implementation:
 *
 *          fetch(7FFFh)
 *          -> CPU enables the HALT state
 *          fetch(7FFFh)
 *          fetch(7FFFh)
 *          fetch(7FFFh)
 *          fetch(7FFFh)
 *          fetch(7FFFh)
 *          ...
 *          INT
 *          -> CPU disables the HALT state
 *          -> CPU responds to the interrupt
 *          -> CPU returns from the ISR
 *          fetch(8000h)
 *          fetch(8001h)
 *
 *          https://spectrumcomputing.co.uk/forums/viewtopic.php?f=23&t=6058&start=20
 */
package com.tsoft.jz80.core;

import java.util.BitSet;

import static com.tsoft.jz80.utils.HexUtils.*;

public class Z80 {

    private MemIoOps MemIoImpl;
    private NotifyOps NotifyImpl;
    // An instruction is being executed DDXX, EDXX or FDXX
    // It should only contain one of four values [0x00, 0xDD, 0xED, 0xFD]
    private int prefixOpcode = 0x00;
    // Notification subsystem
    private boolean execDone = false;
    // Flag positions
    private static final int CARRY_MASK = 0x01;
    private static final int ADDSUB_MASK = 0x02;
    private static final int PARITY_MASK = 0x04;
    private static final int OVERFLOW_MASK = 0x04; // alias de PARITY_MASK
    private static final int BIT3_MASK = 0x08;
    private static final int HALFCARRY_MASK = 0x10;
    private static final int BIT5_MASK = 0x20;
    private static final int ZERO_MASK = 0x40;
    private static final int SIGN_MASK = 0x80;
    // Convenience masks
    private static final int FLAG_53_MASK = BIT5_MASK | BIT3_MASK;
    private static final int FLAG_SZ_MASK = SIGN_MASK | ZERO_MASK;
    private static final int FLAG_SZHN_MASK = FLAG_SZ_MASK | HALFCARRY_MASK | ADDSUB_MASK;
    private static final int FLAG_SZP_MASK = FLAG_SZ_MASK | PARITY_MASK;
    private static final int FLAG_SZHP_MASK = FLAG_SZP_MASK | HALFCARRY_MASK;
    // Accumulator and the rest of the 8-bit registers
    private int regA, regB, regC, regD, regE, regH, regL;
    // Flags sIGN, zERO, 5, hALFCARRY, 3, pARITY and ADDSUB (n)
    private int sz5h3pnFlags;
    // The Carry flag is the only one that is handled separately
    private boolean carryFlag;
    /* Flags to indicate the modification of the F register in the current and
     * previous instruction. They are necessary to emulate the behavior
     * of bits 3 and 5 of the F register with the CCF/SCF instructions.
     *
     * http://www.worldofspectrum.org/forums/showthread.php?t=41834
     * http://www.worldofspectrum.org/forums/showthread.php?t=41704
     *
     * Thanks to Patrik Rak for his tests and investigations.
     */
    private boolean flagQ, lastFlagQ;
    // Alternate accumulator and flags — 8 bits
    private int regAx;
    private int regFx;
    // Alternate registers
    private int regBx, regCx, regDx, regEx, regHx, regLx;
    // Specific-purpose registers
    // *PC -- Program Counter -- 16 bits*
    private int regPC;
    // *IX -- Registro de índice -- 16 bits*
    private int regIX;
    // *IY -- Registro de índice -- 16 bits*
    private int regIY;
    // *SP -- Stack Pointer -- 16 bits*
    private int regSP;
    // *I -- Vector de interrupción -- 8 bits*
    private int regI;
    // *R -- Memory refresh -- 7 bits*
    private int regR;
    // *R7 -- Memory refresh -- 1 bit* (bit superior de R)
    private boolean regRbit7;
    // Flip-flops de interrupción
    private boolean ffIFF1 = false;

    private boolean ffIFF2 = false;

    // EI only enables interrupts AFTER executing the next instruction
    // (except if the next instruction is another EI...)
    private boolean pendingEI = false;

    // NMI line state
    private boolean activeNMI = false;

    // If the INT line is active:
    //  - On the 48 and +2A/+3, the INT line is activated for 32 clock cycles.
    //  - On the 128 and +2, it is activated for 36 clock cycles.
    private boolean activeINT = false;

    // Interruption mode
    private IntMode modeINT = IntMode.IM0;

    // halted == true cuando la CPU está ejecutando un HALT
    private boolean halted = false;

    // pinReset == true, se ha producido un reset a través de la patilla
    private boolean pinReset = false;

    /*
     * Internal register used by the CPU in the following way
     *
     * ADD HL,xx      = Valor del registro H antes de la suma
     * LD r,(IX/IY+d) = Byte superior de la suma de IX/IY+d
     * JR d           = Byte superior de la dirección de destino del salto
     *
     * 04/12/2008     No se vayan todavía, aún hay más. Con lo que se ha
     *                implementado hasta ahora parece que funciona. El resto de
     *                la historia está contada en:
     *                http://zx.pk.ru/attachment.php?attachmentid=2989
     *
     * 25/09/2009     Se ha completado la emulación de MEMPTR. A señalar que
     *                no se puede comprobar si MEMPTR se ha emulado bien hasta
     *                que no se emula el comportamiento del registro en las
     *                instrucciones CPI y CPD. Sin ello, todos los tests de
     *                z80tests.tap fallarán aunque se haya emulado bien al
     *                registro en TODAS las otras instrucciones.
     *                Shit yourself, little parrot.
     */
    private int memptr;

    /* Algunos flags se precalculan para un tratamiento más rápido
     * Concretamente, SIGN, ZERO, los bits 3, 5, PARITY y ADDSUB:
     * sz53n_addTable tiene el ADDSUB flag a 0 y paridad sin calcular
     * sz53pn_addTable tiene el ADDSUB flag a 0 y paridad calculada
     * sz53n_subTable tiene el ADDSUB flag a 1 y paridad sin calcular
     * sz53pn_subTable tiene el ADDSUB flag a 1 y paridad calculada
     * El resto de bits están a 0 en las cuatro tablas lo que es
     * importante para muchas operaciones que ponen ciertos flags a 0 por real
     * decreto. Si lo ponen a 1 por el mismo método basta con hacer un OR con
     * la máscara correspondiente.
     */
    private static final int sz53n_addTable[] = new int[256];
    private static final int sz53pn_addTable[] = new int[256];
    private static final int sz53n_subTable[] = new int[256];
    private static final int sz53pn_subTable[] = new int[256];

    // Used by debugger
    private int regPCd;

    static {
        boolean evenBits;

        for (int idx = 0; idx < 256; idx++) {
            if (idx > 0x7f) {
                sz53n_addTable[idx] |= SIGN_MASK;
            }

            evenBits = true;
            for (int mask = 0x01; mask < 0x100; mask <<= 1) {
                if ((idx & mask) != 0) {
                    evenBits = !evenBits;
                }
            }

            sz53n_addTable[idx] |= (idx & FLAG_53_MASK);
            sz53n_subTable[idx] = sz53n_addTable[idx] | ADDSUB_MASK;

            if (evenBits) {
                sz53pn_addTable[idx] = sz53n_addTable[idx] | PARITY_MASK;
                sz53pn_subTable[idx] = sz53n_subTable[idx] | PARITY_MASK;
            } else {
                sz53pn_addTable[idx] = sz53n_addTable[idx];
                sz53pn_subTable[idx] = sz53n_subTable[idx];
            }
        }

        sz53n_addTable[0] |= ZERO_MASK;
        sz53pn_addTable[0] |= ZERO_MASK;
        sz53n_subTable[0] |= ZERO_MASK;
        sz53pn_subTable[0] |= ZERO_MASK;
    }

    // Constructor de la clase
    public Z80(MemIoOps memory, NotifyOps notify) {
        MemIoImpl = memory;
        NotifyImpl = notify;
        execDone = false;
        reset();
    }

    public void setMemIoHandler(MemIoOps memIo) {
        MemIoImpl = memIo;
    }

    public void setNotifyHandler(NotifyOps notify) {
        NotifyImpl = notify;
    }

    // Acceso a registros de 8 bits
    public final int getRegA() {
        return regA;
    }

    public final void setRegA(int value) {
        regA = value & 0xff;
    }

    public final int getRegB() {
        return regB;
    }

    public final void setRegB(int value) {
        regB = value & 0xff;
    }

    public final int getRegC() {
        return regC;
    }

    public final void setRegC(int value) {
        regC = value & 0xff;
    }

    public final int getRegD() {
        return regD;
    }

    public final void setRegD(int value) {
        regD = value & 0xff;
    }

    public final int getRegE() {
        return regE;
    }

    public final void setRegE(int value) {
        regE = value & 0xff;
    }

    public final int getRegH() {
        return regH;
    }

    public final void setRegH(int value) {
        regH = value & 0xff;
    }

    public final int getRegL() {
        return regL;
    }

    public final void setRegL(int value) {
        regL = value & 0xff;
    }

    // Acceso a registros alternativos de 8 bits
    public final int getRegAx() {
        return regAx;
    }

    public final void setRegAx(int value) {
        regAx = value & 0xff;
    }

    public final int getRegFx() {
        return regFx;
    }

    public final void setRegFx(int value) {
        regFx = value & 0xff;
    }

    public final int getRegBx() {
        return regBx;
    }

    public final void setRegBx(int value) {
        regBx = value & 0xff;
    }

    public final int getRegCx() {
        return regCx;
    }

    public final void setRegCx(int value) {
        regCx = value & 0xff;
    }

    public final int getRegDx() {
        return regDx;
    }

    public final void setRegDx(int value) {
        regDx = value & 0xff;
    }

    public final int getRegEx() {
        return regEx;
    }

    public final void setRegEx(int value) {
        regEx = value & 0xff;
    }

    public final int getRegHx() {
        return regHx;
    }

    public final void setRegHx(int value) {
        regHx = value & 0xff;
    }

    public final int getRegLx() {
        return regLx;
    }

    public final void setRegLx(int value) {
        regLx = value & 0xff;
    }

    // Acceso a registros de 16 bits
    public final int getRegAF() {
        return (regA << 8) | (carryFlag ? sz5h3pnFlags | CARRY_MASK : sz5h3pnFlags);
    }

    public final void setRegAF(int word) {
        regA = (word >>> 8) & 0xff;

        sz5h3pnFlags = word & 0xfe;
        carryFlag = (word & CARRY_MASK) != 0;
    }

    public final int getRegAFx() {
        return (regAx << 8) | regFx;
    }

    public final void setRegAFx(int word) {
        regAx = (word >>> 8) & 0xff;
        regFx = word & 0xff;
    }

    public final int getRegBC() {
        return (regB << 8) | regC;
    }

    public final void setRegBC(int word) {
        regB = (word >>> 8) & 0xff;
        regC = word & 0xff;
    }

    private void incRegBC() {
        if (++regC < 0x100) {
            return;
        }

        regC = 0;

        if (++regB < 0x100) {
            return;
        }

        regB = 0;
    }

    private void decRegBC() {
        if (--regC >= 0) {
            return;
        }

        regC = 0xff;

        if (--regB >= 0) {
            return;
        }

        regB = 0xff;
    }

    public final int getRegBCx() {
        return (regBx << 8) | regCx;
    }

    public final void setRegBCx(int word) {
        regBx = (word >>> 8) & 0xff;
        regCx = word & 0xff;
    }

    public final int getRegDE() {
        return (regD << 8) | regE;
    }

    public final void setRegDE(int word) {
        regD = (word >>> 8) & 0xff;
        regE = word & 0xff;
    }

    private void incRegDE() {
        if (++regE < 0x100) {
            return;
        }

        regE = 0;

        if (++regD < 0x100) {
            return;
        }

        regD = 0;
    }

    private void decRegDE() {
        if (--regE >= 0) {
            return;
        }

        regE = 0xff;

        if (--regD >= 0) {
            return;
        }

        regD = 0xff;
    }

    public final int getRegDEx() {
        return (regDx << 8) | regEx;
    }

    public final void setRegDEx(int word) {
        regDx = (word >>> 8) & 0xff;
        regEx = word & 0xff;
    }

    public final int getRegHL() {
        return (regH << 8) | regL;
    }

    public final void setRegHL(int word) {
        regH = (word >>> 8) & 0xff;
        regL = word & 0xff;
    }

    /* Las funciones incRegXX y decRegXX están escritas pensando en que
     * puedan aprovechar el camino más corto aunque tengan un poco más de
     * código (al menos en bytecodes lo tienen)
     */
    private void incRegHL() {
        if (++regL < 0x100) {
            return;
        }

        regL = 0;

        if (++regH < 0x100) {
            return;
        }

        regH = 0;
    }

    private void decRegHL() {
        if (--regL >= 0) {
            return;
        }

        regL = 0xff;

        if (--regH >= 0) {
            return;
        }

        regH = 0xff;
    }

    public final int getRegHLx() {
        return (regHx << 8) | regLx;
    }

    public final void setRegHLx(int word) {
        regHx = (word >>> 8) & 0xff;
        regLx = word & 0xff;
    }

    // Acceso a registros de propósito específico
    public final int getRegPC() {
        return regPC;
    }

    public final void setRegPC(int address) {
        regPC = address & 0xffff;
    }

    public final int getRegSP() {
        return regSP;
    }

    public final void setRegSP(int word) {
        regSP = word & 0xffff;
    }

    public final int getRegIX() {
        return regIX;
    }

    public final void setRegIX(int word) {
        regIX = word & 0xffff;
    }

    public final int getRegIY() {
        return regIY;
    }

    public final void setRegIY(int word) {
        regIY = word & 0xffff;
    }

    public final int getRegI() {
        return regI;
    }

    public final void setRegI(int value) {
        regI = value & 0xff;
    }

    public final int getRegR() {
        return regRbit7 ? (regR & 0x7f) | SIGN_MASK : regR & 0x7f;
    }

    public final void setRegR(int value) {
        regR = value & 0x7f;
        regRbit7 = (value > 0x7f);
    }

    public final int getPairIR() {
        if (regRbit7) {
            return (regI << 8) | ((regR & 0x7f) | SIGN_MASK);
        }
        return (regI << 8) | (regR & 0x7f);
    }

    // Acceso al registro oculto MEMPTR
    public final int getMemPtr() {
        return memptr & 0xffff;
    }

    public final void setMemPtr(int word) {
        memptr = word & 0xffff;
    }

    // Acceso a los flags uno a uno
    public final boolean isCarryFlag() {
        return carryFlag;
    }

    public final void setCarryFlag(boolean state) {
        carryFlag = state;
    }

    public final boolean isAddSubFlag() {
        return (sz5h3pnFlags & ADDSUB_MASK) != 0;
    }

    public final void setAddSubFlag(boolean state) {
        if (state) {
            sz5h3pnFlags |= ADDSUB_MASK;
        } else {
            sz5h3pnFlags &= ~ADDSUB_MASK;
        }
    }

    public final boolean isParOverFlag() {
        return (sz5h3pnFlags & PARITY_MASK) != 0;
    }

    public final void setParOverFlag(boolean state) {
        if (state) {
            sz5h3pnFlags |= PARITY_MASK;
        } else {
            sz5h3pnFlags &= ~PARITY_MASK;
        }
    }

    public final boolean isBit3Flag() {
        return (sz5h3pnFlags & BIT3_MASK) != 0;
    }

    public final void setBit3Fag(boolean state) {
        if (state) {
            sz5h3pnFlags |= BIT3_MASK;
        } else {
            sz5h3pnFlags &= ~BIT3_MASK;
        }
    }

    public final boolean isHalfCarryFlag() {
        return (sz5h3pnFlags & HALFCARRY_MASK) != 0;
    }

    public final void setHalfCarryFlag(boolean state) {
        if (state) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        } else {
            sz5h3pnFlags &= ~HALFCARRY_MASK;
        }
    }

    public final boolean isBit5Flag() {
        return (sz5h3pnFlags & BIT5_MASK) != 0;
    }

    public final void setBit5Flag(boolean state) {
        if (state) {
            sz5h3pnFlags |= BIT5_MASK;
        } else {
            sz5h3pnFlags &= ~BIT5_MASK;
        }
    }

    public final boolean isZeroFlag() {
        return (sz5h3pnFlags & ZERO_MASK) != 0;
    }

    public final void setZeroFlag(boolean state) {
        if (state) {
            sz5h3pnFlags |= ZERO_MASK;
        } else {
            sz5h3pnFlags &= ~ZERO_MASK;
        }
    }

    public final boolean isSignFlag() {
        return sz5h3pnFlags >= SIGN_MASK;
    }

    public final void setSignFlag(boolean state) {
        if (state) {
            sz5h3pnFlags |= SIGN_MASK;
        } else {
            sz5h3pnFlags &= ~SIGN_MASK;
        }
    }

    // Acceso a los flags F
    public final int getFlags() {
        return carryFlag ? sz5h3pnFlags | CARRY_MASK : sz5h3pnFlags;
    }

    public final void setFlags(int regF) {
        sz5h3pnFlags = regF & 0xfe;

        carryFlag = (regF & CARRY_MASK) != 0;
    }

    // Acceso a los flip-flops de interrupción
    public final boolean isIFF1() {
        return ffIFF1;
    }

    public final void setIFF1(boolean state) {
        ffIFF1 = state;
    }

    public final boolean isIFF2() {
        return ffIFF2;
    }

    public final void setIFF2(boolean state) {
        ffIFF2 = state;
    }

    public final boolean isNMI() {
        return activeNMI;
    }

    public final void setNMI(boolean nmi) {
        activeNMI = nmi;
    }

    // La línea de NMI se activa por impulso, no por nivel
    public final void triggerNMI() {
        activeNMI = true;
    }

    // La línea INT se activa por nivel
    public final boolean isINTLine() {
        return activeINT;
    }

    public final void setINTLine(boolean intLine) {
        activeINT = intLine;
    }

    //Acceso al modo de interrupción
    public final IntMode getIM() {
        return modeINT;
    }

    public final void setIM(IntMode mode) {
        modeINT = mode;
    }

    public final boolean isHalted() {
        return halted;
    }

    public void setHalted(boolean state) {
        halted = state;
    }

    public void setPinReset() {
        pinReset = true;
    }

    public final boolean isPendingEI() {
        return pendingEI;
    }

    public final void setPendingEI(boolean state) {
        pendingEI = state;
    }

    public final Z80State getZ80State() {
        Z80State state = new Z80State();
        state.setRegA(regA);
        state.setRegF(getFlags());
        state.setRegB(regB);
        state.setRegC(regC);
        state.setRegD(regD);
        state.setRegE(regE);
        state.setRegH(regH);
        state.setRegL(regL);
        state.setRegAx(regAx);
        state.setRegFx(regFx);
        state.setRegBx(regBx);
        state.setRegCx(regCx);
        state.setRegDx(regDx);
        state.setRegEx(regEx);
        state.setRegHx(regHx);
        state.setRegLx(regLx);
        state.setRegIX(regIX);
        state.setRegIY(regIY);
        state.setRegSP(regSP);
        state.setRegPC(regPC);
        state.setRegI(regI);
        state.setRegR(getRegR());
        state.setMemPtr(memptr);
        state.setHalted(halted);
        state.setIFF1(ffIFF1);
        state.setIFF2(ffIFF2);
        state.setIM(modeINT);
        state.setINTLine(activeINT);
        state.setPendingEI(pendingEI);
        state.setNMI(activeNMI);
        state.setFlagQ(lastFlagQ);
        return state;
    }

    public final void setZ80State(Z80State state) {
        regA = state.getRegA();
        setFlags(state.getRegF());
        regB = state.getRegB();
        regC = state.getRegC();
        regD = state.getRegD();
        regE = state.getRegE();
        regH = state.getRegH();
        regL = state.getRegL();
        regAx = state.getRegAx();
        regFx = state.getRegFx();
        regBx = state.getRegBx();
        regCx = state.getRegCx();
        regDx = state.getRegDx();
        regEx = state.getRegEx();
        regHx = state.getRegHx();
        regLx = state.getRegLx();
        regIX = state.getRegIX();
        regIY = state.getRegIY();
        regSP = state.getRegSP();
        regPC = state.getRegPC();
        regI = state.getRegI();
        setRegR(state.getRegR());
        memptr = state.getMemPtr();
        halted = state.isHalted();
        ffIFF1 = state.isIFF1();
        ffIFF2 = state.isIFF2();
        modeINT = state.getIM();
        activeINT = state.isINTLine();
        pendingEI = state.isPendingEI();
        activeNMI = state.isNMI();
        flagQ = false;
        lastFlagQ = state.isFlagQ();
    }

    // Reset
    /* Según el documento de Sean Young, que se encuentra en
     * [http://www.myquest.com/z80undocumented], la mejor manera de emular el
     * reset es poniendo PC, IFF1, IFF2, R e IM0 a 0 y todos los demás registros
     * a 0xFFFF.
     *
     * 29/05/2011: cuando la CPU recibe alimentación por primera vez, los
     *             registros PC e IR se inicializan a cero y el resto a 0xFF.
     *             Si se produce un reset a través de la patilla correspondiente,
     *             los registros PC e IR se inicializan a 0 y el resto se preservan.
     *             En cualquier caso, todo parece depender bastante del modelo
     *             concreto de Z80, así que se escoge el comportamiento del
     *             modelo Zilog Z8400APS. Z80A CPU.
     *             http://www.worldofspectrum.org/forums/showthread.php?t=34574
     */
    public final void reset() {
        if (pinReset) {
            pinReset = false;
        } else {
            regA = regAx = 0xff;
            setFlags(0xff);
            regFx = 0xff;
            regB = regBx = 0xff;
            regC = regCx = 0xff;
            regD = regDx = 0xff;
            regE = regEx = 0xff;
            regH = regHx = 0xff;
            regL = regLx = 0xff;

            regIX = regIY = 0xffff;

            regSP = 0xffff;

            memptr = 0xffff;
        }

        regPC = 0;
        regI = regR = 0;
        regRbit7 = false;
        ffIFF1 = false;
        ffIFF2 = false;
        pendingEI = false;
        activeNMI = false;
        activeINT = false;
        halted = false;
        setIM(IntMode.IM0);
        lastFlagQ = false;
        prefixOpcode = 0x00;
    }

    // Rota a la izquierda el valor del argumento
    // El bit 0 y el flag C toman el valor del bit 7 antes de la operación
    private int rlc(int oper8) {
        carryFlag = (oper8 > 0x7f);
        oper8 = (oper8 << 1) & 0xfe;
        if (carryFlag) {
            oper8 |= CARRY_MASK;
        }
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la izquierda el valor del argumento
    // El bit 7 va al carry flag
    // El bit 0 toma el valor del flag C antes de la operación
    private int rl(int oper8) {
        boolean carry = carryFlag;
        carryFlag = (oper8 > 0x7f);
        oper8 = (oper8 << 1) & 0xfe;
        if (carry) {
            oper8 |= CARRY_MASK;
        }
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la izquierda el valor del argumento
    // El bit 7 va al carry flag
    // El bit 0 toma el valor 0
    private int sla(int oper8) {
        carryFlag = (oper8 > 0x7f);
        oper8 = (oper8 << 1) & 0xfe;
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la izquierda el valor del argumento (como sla salvo por el bit 0)
    // El bit 7 va al carry flag
    // El bit 0 toma el valor 1
    // Instrucción indocumentada
    private int sll(int oper8) {
        carryFlag = (oper8 > 0x7f);
        oper8 = ((oper8 << 1) | CARRY_MASK) & 0xff;
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la derecha el valor del argumento
    // El bit 7 y el flag C toman el valor del bit 0 antes de la operación
    private int rrc(int oper8) {
        carryFlag = (oper8 & CARRY_MASK) != 0;
        oper8 >>>= 1;
        if (carryFlag) {
            oper8 |= SIGN_MASK;
        }
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la derecha el valor del argumento
    // El bit 0 va al carry flag
    // El bit 7 toma el valor del flag C antes de la operación
    private int rr(int oper8) {
        boolean carry = carryFlag;
        carryFlag = (oper8 & CARRY_MASK) != 0;
        oper8 >>>= 1;
        if (carry) {
            oper8 |= SIGN_MASK;
        }
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // A = A7 A6 A5 A4 (HL)3 (HL)2 (HL)1 (HL)0
    // (HL) = A3 A2 A1 A0 (HL)7 (HL)6 (HL)5 (HL)4
    // Los bits 3,2,1 y 0 de (HL) se copian a los bits 3,2,1 y 0 de A.
    // Los 4 bits bajos que había en A se copian a los bits 7,6,5 y 4 de (HL).
    // Los 4 bits altos que había en (HL) se copian a los 4 bits bajos de (HL)
    // Los 4 bits superiores de A no se tocan. ¡p'habernos matao!
    private void rrd() {
        int aux = (regA & 0x0f) << 4;
        memptr = getRegHL();
        int memHL = MemIoImpl.peek8(memptr);
        regA = (regA & 0xf0) | (memHL & 0x0f);
        MemIoImpl.addressOnBus(memptr, 4);
        MemIoImpl.poke8(memptr, (memHL >>> 4) | aux);
        sz5h3pnFlags = sz53pn_addTable[regA];
        memptr++;
        flagQ = true;
    }

    // A = A7 A6 A5 A4 (HL)7 (HL)6 (HL)5 (HL)4
    // (HL) = (HL)3 (HL)2 (HL)1 (HL)0 A3 A2 A1 A0
    // Los 4 bits bajos que había en (HL) se copian a los bits altos de (HL).
    // Los 4 bits altos que había en (HL) se copian a los 4 bits bajos de A
    // Los bits 3,2,1 y 0 de A se copian a los bits 3,2,1 y 0 de (HL).
    // Los 4 bits superiores de A no se tocan. ¡p'habernos matao!
    private void rld() {
        int aux = regA & 0x0f;
        memptr = getRegHL();
        int memHL = MemIoImpl.peek8(memptr);
        regA = (regA & 0xf0) | (memHL >>> 4);
        MemIoImpl.addressOnBus(memptr, 4);
        MemIoImpl.poke8(memptr, ((memHL << 4) | aux) & 0xff);
        sz5h3pnFlags = sz53pn_addTable[regA];
        memptr++;
        flagQ = true;
    }

    // Rota a la derecha 1 bit el valor del argumento
    // El bit 0 pasa al carry.
    // El bit 7 conserva el valor que tenga
    private int sra(int oper8) {
        int sign = oper8 & SIGN_MASK;
        carryFlag = (oper8 & CARRY_MASK) != 0;
        oper8 = (oper8 >> 1) | sign;
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    // Rota a la derecha 1 bit el valor del argumento
    // El bit 0 pasa al carry.
    // El bit 7 toma el valor 0
    private int srl(int oper8) {
        carryFlag = (oper8 & CARRY_MASK) != 0;
        oper8 >>>= 1;
        sz5h3pnFlags = sz53pn_addTable[oper8];
        flagQ = true;
        return oper8;
    }

    /*
     * Half-carry flag:
     *
     * FLAG = (A^B^RESULT)&0x10  for any operation
     *
     * Overflow flag:
     *
     * FLAG = ~(A^B)&(B^RESULT)&0x80 for addition [ADD/ADC]
     * FLAG = (A^B)&(A^RESULT)&0x80  for subtraction [SUB/SBC]
     *
     * For INC/DEC, you can use following simplifications:
     *
     * INC:
     * H_FLAG = (RESULT&0x0F)==0x00
     * V_FLAG = RESULT==0x80
     *
     * DEC:
     * H_FLAG = (RESULT&0x0F)==0x0F
     * V_FLAG = RESULT==0x7F
     */
    // Incrementa un valor de 8 bits modificando los flags oportunos
    private int inc8(int oper8) {
        oper8 = (oper8 + 1) & 0xff;

        sz5h3pnFlags = sz53n_addTable[oper8];

        if ((oper8 & 0x0f) == 0) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (oper8 == 0x80) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        flagQ = true;
        return oper8;
    }

    // Decrementa un valor de 8 bits modificando los flags oportunos
    private int dec8(int oper8) {
        oper8 = (oper8 - 1) & 0xff;

        sz5h3pnFlags = sz53n_subTable[oper8];

        if ((oper8 & 0x0f) == 0x0f) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (oper8 == 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        flagQ = true;
        return oper8;
    }

    // Suma de 8 bits afectando a los flags
    private void add(int oper8) {
        int res = regA + oper8;

        carryFlag = res > 0xff;
        res &= 0xff;
        sz5h3pnFlags = sz53n_addTable[res];

        /* El módulo 16 del resultado será menor que el módulo 16 del registro A
         * si ha habido HalfCarry. Sucede lo mismo para todos los métodos suma
         * SIN carry */
        if ((res & 0x0f) < (regA & 0x0f)) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regA ^ ~oper8) & (regA ^ res)) > 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        regA = res;
        flagQ = true;
    }

    // Suma con acarreo de 8 bits
    private void adc(int oper8) {
        int res = regA + oper8;

        if (carryFlag) {
            res++;
        }

        carryFlag = res > 0xff;
        res &= 0xff;
        sz5h3pnFlags = sz53n_addTable[res];

        if (((regA ^ oper8 ^ res) & 0x10) != 0) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regA ^ ~oper8) & (regA ^ res)) > 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        regA = res;
        flagQ = true;
    }

    // Suma dos operandos de 16 bits sin carry afectando a los flags
    private int add16(int reg16, int oper16) {
        oper16 += reg16;

        carryFlag = oper16 > 0xffff;
        sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | ((oper16 >>> 8) & FLAG_53_MASK);
        oper16 &= 0xffff;

        if ((oper16 & 0x0fff) < (reg16 & 0x0fff)) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        memptr = reg16 + 1;
        flagQ = true;
        return oper16;
    }

    // Suma con acarreo de 16 bits
    private void adc16(int reg16) {
        int regHL = getRegHL();
        memptr = regHL + 1;

        int res = regHL + reg16;
        if (carryFlag) {
            res++;
        }

        carryFlag = res > 0xffff;
        res &= 0xffff;
        setRegHL(res);

        sz5h3pnFlags = sz53n_addTable[regH];
        if (res != 0) {
            sz5h3pnFlags &= ~ZERO_MASK;
        }

        if (((res ^ regHL ^ reg16) & 0x1000) != 0) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regHL ^ ~reg16) & (regHL ^ res)) > 0x7fff) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        flagQ = true;
    }

    // Resta de 8 bits
    private void sub(int oper8) {
        int res = regA - oper8;

        carryFlag = res < 0;
        res &= 0xff;
        sz5h3pnFlags = sz53n_subTable[res];

        /* El módulo 16 del resultado será mayor que el módulo 16 del registro A
         * si ha habido HalfCarry. Sucede lo mismo para todos los métodos resta
         * SIN carry, incluido cp */
        if ((res & 0x0f) > (regA & 0x0f)) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regA ^ oper8) & (regA ^ res)) > 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        regA = res;
        flagQ = true;
    }

    // Resta con acarreo de 8 bits
    private void sbc(int oper8) {
        int res = regA - oper8;

        if (carryFlag) {
            res--;
        }

        carryFlag = res < 0;
        res &= 0xff;
        sz5h3pnFlags = sz53n_subTable[res];

        if (((regA ^ oper8 ^ res) & 0x10) != 0) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regA ^ oper8) & (regA ^ res)) > 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        regA = res;
        flagQ = true;
    }

    // Resta con acarreo de 16 bits
    private void sbc16(int reg16) {
        int regHL = getRegHL();
        memptr = regHL + 1;

        int res = regHL - reg16;
        if (carryFlag) {
            res--;
        }

        carryFlag = res < 0;
        res &= 0xffff;
        setRegHL(res);

        sz5h3pnFlags = sz53n_subTable[regH];
        if (res != 0) {
            sz5h3pnFlags &= ~ZERO_MASK;
        }

        if (((res ^ regHL ^ reg16) & 0x1000) != 0) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regHL ^ reg16) & (regHL ^ res)) > 0x7fff) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }
        flagQ = true;
    }

    // Operación AND lógica
    private void and(int oper8) {
        regA &= oper8;
        carryFlag = false;
        sz5h3pnFlags = sz53pn_addTable[regA] | HALFCARRY_MASK;
        flagQ = true;
    }

    // Operación XOR lógica
    private void xor(int oper8) {
        regA = (regA ^ oper8) & 0xff;
        carryFlag = false;
        sz5h3pnFlags = sz53pn_addTable[regA];
        flagQ = true;
    }

    // Operación OR lógica
    private void or(int oper8) {
        regA = (regA | oper8) & 0xff;
        carryFlag = false;
        sz5h3pnFlags = sz53pn_addTable[regA];
        flagQ = true;
    }

    // Operación de comparación con el registro A
    // es como SUB, pero solo afecta a los flags
    // Los flags SIGN y ZERO se calculan a partir del resultado
    // Los flags 3 y 5 se copian desde el operando (sigh!)
    private void cp(int oper8) {
        int res = regA - (oper8 & 0xff);

        carryFlag = res < 0;
        res &= 0xff;

        sz5h3pnFlags = (sz53n_addTable[oper8] & FLAG_53_MASK)
            | // No necesito preservar H, pero está a 0 en la tabla de todas formas
            (sz53n_subTable[res] & FLAG_SZHN_MASK);

        if ((res & 0x0f) > (regA & 0x0f)) {
            sz5h3pnFlags |= HALFCARRY_MASK;
        }

        if (((regA ^ oper8) & (regA ^ res)) > 0x7f) {
            sz5h3pnFlags |= OVERFLOW_MASK;
        }

        flagQ = true;
    }

    // DAA
    private void daa() {
        int suma = 0;
        boolean carry = carryFlag;

        if ((sz5h3pnFlags & HALFCARRY_MASK) != 0 || (regA & 0x0f) > 0x09) {
            suma = 6;
        }

        if (carry || (regA > 0x99)) {
            suma |= 0x60;
        }

        if (regA > 0x99) {
            carry = true;
        }

        if ((sz5h3pnFlags & ADDSUB_MASK) != 0) {
            sub(suma);
            sz5h3pnFlags = (sz5h3pnFlags & HALFCARRY_MASK) | sz53pn_subTable[regA];
        } else {
            add(suma);
            sz5h3pnFlags = (sz5h3pnFlags & HALFCARRY_MASK) | sz53pn_addTable[regA];
        }

        carryFlag = carry;
        // Los add/sub ya ponen el resto de los flags
        flagQ = true;
    }

    // POP
    private int pop() {
        int word = MemIoImpl.peek16(regSP);
        regSP = (regSP + 2) & 0xffff;
        return word;
    }

    // PUSH
    private void push(int word) {
        regSP = (regSP - 1) & 0xffff;
        MemIoImpl.poke8(regSP, word >>> 8);
        regSP = (regSP - 1) & 0xffff;
        MemIoImpl.poke8(regSP, word);
    }

    // LDI
    private void ldi() {
        int work8 = MemIoImpl.peek8(getRegHL());
        int regDE = getRegDE();
        MemIoImpl.poke8(regDE, work8);
        MemIoImpl.addressOnBus(regDE, 2);
        incRegHL();
        incRegDE();
        decRegBC();
        work8 += regA;

        sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZ_MASK) | (work8 & BIT3_MASK);

        if ((work8 & ADDSUB_MASK) != 0) {
            sz5h3pnFlags |= BIT5_MASK;
        }

        if (regC != 0 || regB != 0) {
            sz5h3pnFlags |= PARITY_MASK;
        }
        flagQ = true;
    }

    // LDD
    private void ldd() {
        int work8 = MemIoImpl.peek8(getRegHL());
        int regDE = getRegDE();
        MemIoImpl.poke8(regDE, work8);
        MemIoImpl.addressOnBus(regDE, 2);
        decRegHL();
        decRegDE();
        decRegBC();
        work8 += regA;

        sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZ_MASK) | (work8 & BIT3_MASK);

        if ((work8 & ADDSUB_MASK) != 0) {
            sz5h3pnFlags |= BIT5_MASK;
        }

        if (regC != 0 || regB != 0) {
            sz5h3pnFlags |= PARITY_MASK;
        }
        flagQ = true;
    }

    // CPI
    private void cpi() {
        int regHL = getRegHL();
        int memHL = MemIoImpl.peek8(regHL);
        boolean carry = carryFlag; // lo guardo porque cp lo toca
        cp(memHL);
        carryFlag = carry;
        MemIoImpl.addressOnBus(regHL, 5);
        incRegHL();
        decRegBC();
        memHL = regA - memHL - ((sz5h3pnFlags & HALFCARRY_MASK) != 0 ? 1 : 0);
        sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHN_MASK) | (memHL & BIT3_MASK);

        if ((memHL & ADDSUB_MASK) != 0) {
            sz5h3pnFlags |= BIT5_MASK;
        }

        if (regC != 0 || regB != 0) {
            sz5h3pnFlags |= PARITY_MASK;
        }

        memptr++;
        flagQ = true;
    }

    // CPD
    private void cpd() {
        int regHL = getRegHL();
        int memHL = MemIoImpl.peek8(regHL);
        boolean carry = carryFlag; // lo guardo porque cp lo toca
        cp(memHL);
        carryFlag = carry;
        MemIoImpl.addressOnBus(regHL, 5);
        decRegHL();
        decRegBC();
        memHL = regA - memHL - ((sz5h3pnFlags & HALFCARRY_MASK) != 0 ? 1 : 0);
        sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHN_MASK) | (memHL & BIT3_MASK);

        if ((memHL & ADDSUB_MASK) != 0) {
            sz5h3pnFlags |= BIT5_MASK;
        }

        if (regC != 0 || regB != 0) {
            sz5h3pnFlags |= PARITY_MASK;
        }

        memptr--;
        flagQ = true;
    }

    // INI
    private void ini() {
        memptr = getRegBC();
        MemIoImpl.addressOnBus(getPairIR(), 1);
        int work8 = MemIoImpl.inPort(memptr);
        MemIoImpl.poke8(getRegHL(), work8);

        memptr++;
        regB = (regB - 1) & 0xff;

        incRegHL();

        sz5h3pnFlags = sz53pn_addTable[regB];
        if (work8 > 0x7f) {
            sz5h3pnFlags |= ADDSUB_MASK;
        }

        carryFlag = false;
        int tmp = work8 + ((regC + 1) & 0xff);
        if (tmp > 0xff) {
            sz5h3pnFlags |= HALFCARRY_MASK;
            carryFlag = true;
        }

        if ((sz53pn_addTable[((tmp & 0x07) ^ regB)]
            & PARITY_MASK) == PARITY_MASK) {
            sz5h3pnFlags |= PARITY_MASK;
        } else {
            sz5h3pnFlags &= ~PARITY_MASK;
        }
        flagQ = true;
    }

    // IND
    private void ind() {
        memptr = getRegBC();
        MemIoImpl.addressOnBus(getPairIR(), 1);
        int work8 = MemIoImpl.inPort(memptr);
        MemIoImpl.poke8(getRegHL(), work8);

        memptr--;
        regB = (regB - 1) & 0xff;

        decRegHL();

        sz5h3pnFlags = sz53pn_addTable[regB];
        if (work8 > 0x7f) {
            sz5h3pnFlags |= ADDSUB_MASK;
        }

        carryFlag = false;
        int tmp = work8 + ((regC - 1) & 0xff);
        if (tmp > 0xff) {
            sz5h3pnFlags |= HALFCARRY_MASK;
            carryFlag = true;
        }

        if ((sz53pn_addTable[((tmp & 0x07) ^ regB)]
            & PARITY_MASK) == PARITY_MASK) {
            sz5h3pnFlags |= PARITY_MASK;
        } else {
            sz5h3pnFlags &= ~PARITY_MASK;
        }
        flagQ = true;
    }

    // OUTI
    private void outi() {

        MemIoImpl.addressOnBus(getPairIR(), 1);

        regB = (regB - 1) & 0xff;
        memptr = getRegBC();

        int work8 = MemIoImpl.peek8(getRegHL());
        MemIoImpl.outPort(memptr, work8);
        memptr++;

        incRegHL();

        carryFlag = false;
        if (work8 > 0x7f) {
            sz5h3pnFlags = sz53n_subTable[regB];
        } else {
            sz5h3pnFlags = sz53n_addTable[regB];
        }

        if ((regL + work8) > 0xff) {
            sz5h3pnFlags |= HALFCARRY_MASK;
            carryFlag = true;
        }

        if ((sz53pn_addTable[(((regL + work8) & 0x07) ^ regB)]
            & PARITY_MASK) == PARITY_MASK) {
            sz5h3pnFlags |= PARITY_MASK;
        }
        flagQ = true;
    }

    // OUTD
    private void outd() {

        MemIoImpl.addressOnBus(getPairIR(), 1);

        regB = (regB - 1) & 0xff;
        memptr = getRegBC();

        int work8 = MemIoImpl.peek8(getRegHL());
        MemIoImpl.outPort(memptr, work8);
        memptr--;

        decRegHL();

        carryFlag = false;
        if (work8 > 0x7f) {
            sz5h3pnFlags = sz53n_subTable[regB];
        } else {
            sz5h3pnFlags = sz53n_addTable[regB];
        }

        if ((regL + work8) > 0xff) {
            sz5h3pnFlags |= HALFCARRY_MASK;
            carryFlag = true;
        }

        if ((sz53pn_addTable[(((regL + work8) & 0x07) ^ regB)]
            & PARITY_MASK) == PARITY_MASK) {
            sz5h3pnFlags |= PARITY_MASK;
        }
        flagQ = true;
    }

    // Pone a 1 el Flag Z si el bit b del registro
    // r es igual a 0
    /*
     * En contra de lo que afirma el Z80-Undocumented, los bits 3 y 5 toman
     * SIEMPRE el valor de los bits correspondientes del valor a comparar para
     * las instrucciones BIT n,r. Para BIT n,(HL) toman el valor del registro
     * escondido (memptr), y para las BIT n, (IX/IY+n) toman el valor de los
     * bits superiores de la dirección indicada por IX/IY+n.
     *
     * 04/12/08 Confirmado el comentario anterior:
     *          http://scratchpad.wikia.com/wiki/Z80
     */
    private void bit(int mask, int reg) {
        boolean zeroFlag = (mask & reg) == 0;

        sz5h3pnFlags = (sz53n_addTable[reg] & ~FLAG_SZP_MASK) | HALFCARRY_MASK;

        if (zeroFlag) {
            sz5h3pnFlags |= (PARITY_MASK | ZERO_MASK);
        }

        if (mask == SIGN_MASK && !zeroFlag) {
            sz5h3pnFlags |= SIGN_MASK;
        }
        flagQ = true;
    }

    //Interrupción
    /* Desglose de la interrupción, según el modo:
     * IM0:
     *      M1: 7 T-Estados -> reconocer INT y decSP
     *      M2: 3 T-Estados -> escribir byte alto y decSP
     *      M3: 3 T-Estados -> escribir byte bajo y salto a N
     * IM1:
     *      M1: 7 T-Estados -> reconocer INT y decSP
     *      M2: 3 T-Estados -> escribir byte alto PC y decSP
     *      M3: 3 T-Estados -> escribir byte bajo PC y PC=0x0038
     * IM2:
     *      M1: 7 T-Estados -> reconocer INT y decSP
     *      M2: 3 T-Estados -> escribir byte alto y decSP
     *      M3: 3 T-Estados -> escribir byte bajo
     *      M4: 3 T-Estados -> leer byte bajo del vector de INT
     *      M5: 3 T-Estados -> leer byte alto y saltar a la rutina de INT
     */
    private void interruption() {

        //System.out.println(String.format("INT at %d T-States", tEstados));
//        int tmp = tEstados; // peek8 modifica los tEstados
        lastFlagQ = false;
        // Si estaba en un HALT esperando una INT, lo saca de la espera
        halted = false;

        MemIoImpl.interruptHandlingTime(7);

        regR++;
        ffIFF1 = ffIFF2 = false;
        push(regPC);  // el push a�adir� 6 t-estados (+contended si toca)
        if (modeINT == IntMode.IM2) {
            regPC = MemIoImpl.peek16((regI << 8) | 0xff); // +6 t-estados
        } else {
            regPC = 0x0038;
        }
        memptr = regPC;
        //System.out.println(String.format("Coste INT: %d", tEstados-tmp));
    }

    //Interrupción NMI, no utilizado por ahora
    /* Desglose de ciclos de máquina y T-Estados
     * M1: 5 T-Estados -> extraer opcode (pá ná, es tontería) y decSP
     * M2: 3 T-Estados -> escribe byte alto de PC y decSP
     * M3: 3 T-Estados -> escribe byte bajo de PC y PC=0x0066
     */
    private void nmi() {
        lastFlagQ = false;
        halted = false;
        // Esta lectura consigue dos cosas:
        //      1.- La lectura del opcode del M1 que se descarta
        //      2.- Si estaba en un HALT esperando una INT, lo saca de la espera
        MemIoImpl.fetchOpcode(regPC);
        MemIoImpl.interruptHandlingTime(1);

        regR++;
        ffIFF1 = false;
        push(regPC);  // 3+3 t-estados + contended si procede
        regPC = memptr = 0x0066;
    }

    public boolean isExecDone() {
        return execDone;
    }

    public void setExecDone(boolean state) {
        execDone = state;
    }

    /* Los tEstados transcurridos se calculan teniendo en cuenta el número de
     * ciclos de máquina reales que se ejecutan. Esa es la única forma de poder
     * simular la contended memory del Spectrum.
     */
    public final void execute() {
        int opCode = MemIoImpl.fetchOpcode(regPC);
        regR ++;

        if (prefixOpcode == 0) {
            opCode = NotifyImpl.beforeStep(regPC, opCode);
        }

        if (!halted) {
            regPCd = regPC;
            regPC = (regPC + 1) & 0xffff;

            // El prefijo 0xCB no cuenta para esta guerra.
            // En CBxx todas las xx producen un código válido
            // de instrucción, incluyendo CBCB.
            switch (prefixOpcode) {
                case 0x00:
                    flagQ = pendingEI = false;
                    decodeOpcode(opCode);
                    break;
                case 0xDD:
                    prefixOpcode = 0;
                    regIX = decodeDDFD(opCode, regIX);
                    break;
                case 0xED:
                    prefixOpcode = 0;
                    decodeED(opCode);
                    break;
                case 0xFD:
                    prefixOpcode = 0;
                    regIY = decodeDDFD(opCode, regIY);
                    break;
                default:
                    System.out.println(String.format("ERROR!: prefixOpcode = %02x, opCode = %02x", prefixOpcode, opCode));
            }

            if (prefixOpcode != 0x00) {
                return;
            }

            lastFlagQ = flagQ;

            if (execDone) {
                NotifyImpl.execDone();
            }
        }

        // Primero se comprueba NMI
        // Si se activa NMI no se comprueba INT porque la siguiente
        // instrucción debe ser la de 0x0066.
        if (activeNMI) {
            activeNMI = false;
            nmi();
            return;
        }

        // Now it checks if there is an INT
        if (ffIFF1 && !pendingEI && MemIoImpl.isActiveINT()) {
            interruption();
        }
    }

    private void step(int len, String op) {
        System.out.print(reg16(regPC - 1) + ":");
        for (int i = 0; i < 5; i ++) {
            String val =  (len <= 0) ? "  " : reg8(MemIoImpl.getRam()[(regPCd + i) & 0xffff] & 0xff);
            System.out.print(" " + val);
            len --;
        }
        System.out.println(" " + op);
    }

    private void decodeOpcode(int opCode) {
        switch (opCode) {
            case 0x00:       /* NOP */
                step(1, "NOP");
                break;
            case 0x01: {     /* LD BC,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD BC," + hex16(value));

                setRegBC(value);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x02: {     /* LD (BC),A */
                step(1, "LD (BC),A");

                MemIoImpl.poke8(getRegBC(), regA);
                memptr = (regA << 8) | ((regC + 1) & 0xff);
                break;
            }
            case 0x03: {     /* INC BC */
                step(1, "INC BC");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                incRegBC();
                break;
            }
            case 0x04: {     /* INC B */
                step(1, "INC B");

                regB = inc8(regB);
                break;
            }
            case 0x05: {     /* DEC B */
                step(1, "DEC BC");

                regB = dec8(regB);
                break;
            }
            case 0x06: {     /* LD B,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD B," + hex8(value));

                regB = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x07: {     /* RLCA */
                step(1, "RLCA");

                carryFlag = (regA > 0x7f);
                regA = (regA << 1) & 0xff;
                if (carryFlag) {
                    regA |= CARRY_MASK;
                }
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (regA & FLAG_53_MASK);
                flagQ = true;
                break;
            }
            case 0x08: {      /* EX AF,AF' */
                step(1, "EX AF,AF'");

                int work8 = regA;
                regA = regAx;
                regAx = work8;

                work8 = getFlags();
                setFlags(regFx);
                regFx = work8;
                break;
            }
            case 0x09: {     /* ADD HL,BC */
                step(1, "ADD HL,BC");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                setRegHL(add16(getRegHL(), getRegBC()));
                break;
            }
            case 0x0A: {     /* LD A,(BC) */
                step(1, "LD A,(BC)");

                memptr = getRegBC();
                regA = MemIoImpl.peek8(memptr++);
                break;
            }
            case 0x0B: {     /* DEC BC */
                step(1, "DEC BC");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                decRegBC();
                break;
            }
            case 0x0C: {     /* INC C */
                step(1, "INC C");

                regC = inc8(regC);
                break;
            }
            case 0x0D: {     /* DEC C */
                step(1, "DEC C");

                regC = dec8(regC);
                break;
            }
            case 0x0E: {     /* LD C,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD C," + hex8(value));

                regC = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x0F: {     /* RRCA */
                step(1, "RRCA");

                carryFlag = (regA & CARRY_MASK) != 0;
                regA >>>= 1;
                if (carryFlag) {
                    regA |= SIGN_MASK;
                }
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (regA & FLAG_53_MASK);
                flagQ = true;
                break;
            }
            case 0x10: {     /* DJNZ e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "DJNZ " + off8(value));

                MemIoImpl.addressOnBus(getPairIR(), 1);
                byte offset = (byte) value;
                regB--;
                if (regB != 0) {
                    regB &= 0xff;
                    MemIoImpl.addressOnBus(regPC, 5);
                    regPC = memptr = (regPC + offset + 1) & 0xffff;
                } else {
                    regPC = (regPC + 1) & 0xffff;
                }
                break;
            }
            case 0x11: {     /* LD DE,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD DE," + hex16(value));

                setRegDE(value);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x12: {     /* LD (DE),A */
                step(1, "LD (DE),A");

                MemIoImpl.poke8(getRegDE(), regA);
                memptr = (regA << 8) | ((regE + 1) & 0xff);
                break;
            }
            case 0x13: {     /* INC DE */
                step(1, "INC DE");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                incRegDE();
                break;
            }
            case 0x14: {     /* INC D */
                step(1, "INC D");

                regD = inc8(regD);
                break;
            }
            case 0x15: {     /* DEC D */
                step(1, "DEC D");

                regD = dec8(regD);
                break;
            }
            case 0x16: {     /* LD D,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD D," + hex16(value));

                regD = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x17: {     /* RLA */
                step(1, "RLA");

                boolean oldCarry = carryFlag;
                carryFlag = (regA > 0x7f);
                regA = (regA << 1) & 0xff;
                if (oldCarry) {
                    regA |= CARRY_MASK;
                }
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (regA & FLAG_53_MASK);
                flagQ = true;
                break;
            }
            case 0x18: {     /* JR e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "JR " + off8(value));

                byte offset = (byte) value;
                MemIoImpl.addressOnBus(regPC, 5);
                regPC = memptr = (regPC + offset + 1) & 0xffff;
                break;
            }
            case 0x19: {     /* ADD HL,DE */
                step(1, "ADD HL,DE");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                setRegHL(add16(getRegHL(), getRegDE()));
                break;
            }
            case 0x1A: {     /* LD A,(DE) */
                step(1, "LD A,(DE)");

                memptr = getRegDE();
                regA = MemIoImpl.peek8(memptr++);
                break;
            }
            case 0x1B: {     /* DEC DE */
                step(1, "DEC DE");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                decRegDE();
                break;
            }
            case 0x1C: {     /* INC E */
                step(1, "INC E");

                regE = inc8(regE);
                break;
            }
            case 0x1D: {     /* DEC E */
                step(1, "DEC E");

                regE = dec8(regE);
                break;
            }
            case 0x1E: {     /* LD E,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD E," + hex8(value));

                regE = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x1F: {     /* RRA */
                step(1, "RRA");

                boolean oldCarry = carryFlag;
                carryFlag = (regA & CARRY_MASK) != 0;
                regA >>>= 1;
                if (oldCarry) {
                    regA |= SIGN_MASK;
                }
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (regA & FLAG_53_MASK);
                flagQ = true;
                break;
            }
            case 0x20: {     /* JR NZ,e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "JR NZ," + off8(value));

                byte offset = (byte) value;
                if ((sz5h3pnFlags & ZERO_MASK) == 0) {
                    MemIoImpl.addressOnBus(regPC, 5);
                    regPC += offset;
                    memptr = regPC + 1;
                }
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x21: {     /* LD HL,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD HL," + hex16(value));

                setRegHL(value);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x22: {     /* LD (nn),HL */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD (" + hex16(value) + "),HL");

                memptr = value;
                MemIoImpl.poke16(memptr++, getRegHL());
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x23: {     /* INC HL */
                step(1, "INC HL");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                incRegHL();
                break;
            }
            case 0x24: {     /* INC H */
                step(1, "INC H");

                regH = inc8(regH);
                break;
            }
            case 0x25: {     /* DEC H */
                step(1, "DEC H");

                regH = dec8(regH);
                break;
            }
            case 0x26: {     /* LD H,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD H," + hex8(value));

                regH = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x27: {     /* DAA */
                step(1, "DAA");

                daa();
                break;
            }
            case 0x28: {     /* JR Z,e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "JR Z," + off8(value));

                byte offset = (byte) value;
                if ((sz5h3pnFlags & ZERO_MASK) != 0) {
                    MemIoImpl.addressOnBus(regPC, 5);
                    regPC += offset;
                    memptr = regPC + 1;
                }
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x29: {     /* ADD HL,HL */
                step(1, "ADD HL,HL");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                int work16 = getRegHL();
                setRegHL(add16(work16, work16));
                break;
            }
            case 0x2A: {     /* LD HL,(nn) */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD HL,(" + hex16(value) + ")");

                memptr = value;
                setRegHL(MemIoImpl.peek16(memptr++));
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x2B: {     /* DEC HL */
                step(1, "DEC HL");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                decRegHL();
                break;
            }
            case 0x2C: {     /* INC L */
                step(1, "INC L");

                regL = inc8(regL);
                break;
            }
            case 0x2D: {     /* DEC L */
                step(1, "DEC L");

                regL = dec8(regL);
                break;
            }
            case 0x2E: {     /* LD L,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD L," + hex8(value));

                regL = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x2F: {     /* CPL */
                step(1, "CPL");

                regA ^= 0xff;
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | HALFCARRY_MASK
                    | (regA & FLAG_53_MASK) | ADDSUB_MASK;
                flagQ = true;
                break;
            }
            case 0x30: {     /* JR NC,e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "JR NC," + off8(value));

                byte offset = (byte) value;
                if (!carryFlag) {
                    MemIoImpl.addressOnBus(regPC, 5);
                    regPC += offset;
                    memptr = regPC + 1;
                }
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x31: {     /* LD SP,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD SP," + hex16(value));

                regSP = value;
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x32: {     /* LD (nn),A */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD (" + hex16(value) + "),A");

                memptr = value;
                MemIoImpl.poke8(memptr, regA);
                memptr = (regA << 8) | ((memptr + 1) & 0xff);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x33: {     /* INC SP */
                step(1, "INC SP");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                regSP = (regSP + 1) & 0xffff;
                break;
            }
            case 0x34: {     /* INC (HL) */
                step(1, "INC (HL)");

                int work16 = getRegHL();
                int work8 = inc8(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x35: {     /* DEC (HL) */
                step(1, "DEC (HL)");

                int work16 = getRegHL();
                int work8 = dec8(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x36: {     /* LD (HL),n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD (HL)," + hex8(value));

                MemIoImpl.poke8(getRegHL(), value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x37: {     /* SCF */
                step(1, "SCF");

                int regQ = lastFlagQ ? sz5h3pnFlags : 0;
                carryFlag = true;
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (((regQ ^ sz5h3pnFlags) | regA) & FLAG_53_MASK);
                flagQ = true;
                break;
            }
            case 0x38: {     /* JR C,e */
                int value = MemIoImpl.peek8(regPC);
                step(2, "JR C," + off8(value));

                byte offset = (byte) value;
                if (carryFlag) {
                    MemIoImpl.addressOnBus(regPC, 5);
                    regPC += offset;
                    memptr = regPC + 1;
                }
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x39: {     /* ADD HL,SP */
                step(1, "ADD HL,SP");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                setRegHL(add16(getRegHL(), regSP));
                break;
            }
            case 0x3A: {     /* LD A,(nn) */
                int value = MemIoImpl.peek16(regPC);
                step(3, "LD A,(" + hex16(value) + ")");

                memptr = MemIoImpl.peek16(regPC);
                regA = MemIoImpl.peek8(memptr++);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x3B: {     /* DEC SP */
                step(1, "DEC SP");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                regSP = (regSP - 1) & 0xffff;
                break;
            }
            case 0x3C: {     /* INC A */
                step(1, "INC A");

                regA = inc8(regA);
                break;
            }
            case 0x3D: {     /* DEC A */
                step(1, "DEC A");

                regA = dec8(regA);
                break;
            }
            case 0x3E: {     /* LD A,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "LD A," + hex8(value));

                regA = value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x3F: {     /* CCF */
                step(1, "CCF");

                int regQ = lastFlagQ ? sz5h3pnFlags : 0;
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZP_MASK) | (((regQ ^ sz5h3pnFlags) | regA) & FLAG_53_MASK);
                if (carryFlag) {
                    sz5h3pnFlags |= HALFCARRY_MASK;
                }
                carryFlag = !carryFlag;
                flagQ = true;
                break;
            }
            case 0x40: {     /* LD B,B */
                step(1, "LD B,B");

                break;
            }
            case 0x41: {     /* LD B,C */
                step(1, "LD B,C");

                regB = regC;
                break;
            }
            case 0x42: {     /* LD B,D */
                step(1, "LD B,D");

                regB = regD;
                break;
            }
            case 0x43: {     /* LD B,E */
                step(1, "LD B,E");

                regB = regE;
                break;
            }
            case 0x44: {     /* LD B,H */
                step(1, "LD B,H");

                regB = regH;
                break;
            }
            case 0x45: {     /* LD B,L */
                step(1, "LD B,L");

                regB = regL;
                break;
            }
            case 0x46: {     /* LD B,(HL) */
                step(1, "LD B,(HL)");

                regB = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x47: {     /* LD B,A */
                step(1, "LD B,A");

                regB = regA;
                break;
            }
            case 0x48: {     /* LD C,B */
                step(1, "LD C,B");

                regC = regB;
                break;
            }
            case 0x49: {     /* LD C,C */
                step(1, "LD C,C");

                break;
            }
            case 0x4A: {     /* LD C,D */
                step(1, "LD C,D");

                regC = regD;
                break;
            }
            case 0x4B: {     /* LD C,E */
                step(1, "LD C,E");

                regC = regE;
                break;
            }
            case 0x4C: {     /* LD C,H */
                step(1, "LD C,H");

                regC = regH;
                break;
            }
            case 0x4D: {     /* LD C,L */
                step(1, "LD C,L");

                regC = regL;
                break;
            }
            case 0x4E: {     /* LD C,(HL) */
                step(1, "LD C,(HL)");

                regC = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x4F: {     /* LD C,A */
                step(1, "LD C,A");

                regC = regA;
                break;
            }
            case 0x50: {     /* LD D,B */
                step(1, "LD D,B");

                regD = regB;
                break;
            }
            case 0x51: {     /* LD D,C */
                step(1, "LD D,C");

                regD = regC;
                break;
            }
            case 0x52: {     /* LD D,D */
                step(1, "LD D,D");

                break;
            }
            case 0x53: {     /* LD D,E */
                step(1, "LD D,E");

                regD = regE;
                break;
            }
            case 0x54: {     /* LD D,H */
                step(1, "LD D,H");

                regD = regH;
                break;
            }
            case 0x55: {     /* LD D,L */
                step(1, "LD D,L");

                regD = regL;
                break;
            }
            case 0x56: {     /* LD D,(HL) */
                step(1, "LD D,(HL)");

                regD = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x57: {     /* LD D,A */
                step(1, "LD D,A");

                regD = regA;
                break;
            }
            case 0x58: {     /* LD E,B */
                step(1, "LD E,B");

                regE = regB;
                break;
            }
            case 0x59: {     /* LD E,C */
                step(1, "LD E,C");

                regE = regC;
                break;
            }
            case 0x5A: {     /* LD E,D */
                step(1, "LD E,D");

                regE = regD;
                break;
            }
            case 0x5B: {     /* LD E,E */
                step(1, "LD E,E");

                break;
            }
            case 0x5C: {     /* LD E,H */
                step(1, "LD E,H");

                regE = regH;
                break;
            }
            case 0x5D: {     /* LD E,L */
                step(1, "LD E,L");

                regE = regL;
                break;
            }
            case 0x5E: {     /* LD E,(HL) */
                step(1, "LD E,(HL)");

                regE = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x5F: {     /* LD E,A */
                step(1, "LD E,A");

                regE = regA;
                break;
            }
            case 0x60: {     /* LD H,B */
                step(1, "LD H,B");

                regH = regB;
                break;
            }
            case 0x61: {     /* LD H,C */
                step(1, "LD H,C");

                regH = regC;
                break;
            }
            case 0x62: {     /* LD H,D */
                step(1, "LD H,D");

                regH = regD;
                break;
            }
            case 0x63: {     /* LD H,E */
                step(1, "LD H,E");

                regH = regE;
                break;
            }
            case 0x64: {     /* LD H,H */
                step(1, "LD H,H");

                break;
            }
            case 0x65: {     /* LD H,L */
                step(1, "LD H,L");

                regH = regL;
                break;
            }
            case 0x66: {     /* LD H,(HL) */
                step(1, "LD H,(HL)");

                regH = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x67: {     /* LD H,A */
                step(1, "LD H,A");

                regH = regA;
                break;
            }
            case 0x68: {     /* LD L,B */
                step(1, "LD L,B");

                regL = regB;
                break;
            }
            case 0x69: {     /* LD L,C */
                step(1, "LD L,C");

                regL = regC;
                break;
            }
            case 0x6A: {     /* LD L,D */
                step(1, "LD L,D");

                regL = regD;
                break;
            }
            case 0x6B: {     /* LD L,E */
                step(1, "LD L,E");

                regL = regE;
                break;
            }
            case 0x6C: {     /* LD L,H */
                step(1, "LD L,H");

                regL = regH;
                break;
            }
            case 0x6D: {     /* LD L,L */
                step(1, "LD L,L");

                break;
            }
            case 0x6E: {     /* LD L,(HL) */
                step(1, "LD L,(HL)");

                regL = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x6F: {     /* LD L,A */
                step(1, "LD L,A");

                regL = regA;
                break;
            }
            case 0x70: {     /* LD (HL),B */
                step(1, "LD (HL),B");

                MemIoImpl.poke8(getRegHL(), regB);
                break;
            }
            case 0x71: {     /* LD (HL),C */
                step(1, "LD (HL),C");

                MemIoImpl.poke8(getRegHL(), regC);
                break;
            }
            case 0x72: {     /* LD (HL),D */
                step(1, "LD (HL),D");

                MemIoImpl.poke8(getRegHL(), regD);
                break;
            }
            case 0x73: {     /* LD (HL),E */
                step(1, "LD (HL),E");

                MemIoImpl.poke8(getRegHL(), regE);
                break;
            }
            case 0x74: {     /* LD (HL),H */
                step(1, "LD (HL),H");

                MemIoImpl.poke8(getRegHL(), regH);
                break;
            }
            case 0x75: {     /* LD (HL),L */
                step(1, "LD (HL),L");

                MemIoImpl.poke8(getRegHL(), regL);
                break;
            }
            case 0x76: {     /* HALT */
                step(1, "HALT");

                halted = true;
                break;
            }
            case 0x77: {     /* LD (HL),A */
                step(1, "LD (HL),A");

                MemIoImpl.poke8(getRegHL(), regA);
                break;
            }
            case 0x78: {     /* LD A,B */
                step(1, "LD A,B");

                regA = regB;
                break;
            }
            case 0x79: {     /* LD A,C */
                step(1, "LD A,C");

                regA = regC;
                break;
            }
            case 0x7A: {     /* LD A,D */
                step(1, "LD A,D");

                regA = regD;
                break;
            }
            case 0x7B: {     /* LD A,E */
                step(1, "LD A,E");

                regA = regE;
                break;
            }
            case 0x7C: {     /* LD A,H */
                step(1, "LD A,H");

                regA = regH;
                break;
            }
            case 0x7D: {     /* LD A,L */
                step(1, "LD A,L");

                regA = regL;
                break;
            }
            case 0x7E: {     /* LD A,(HL) */
                step(1, "LD A,(HL)");

                regA = MemIoImpl.peek8(getRegHL());
                break;
            }
            case 0x7F: {     /* LD A,A */
                step(1, "LD A,A");

                break;
            }
            case 0x80: {     /* ADD A,B */
                step(1, "ADD A,B");

                add(regB);
                break;
            }
            case 0x81: {     /* ADD A,C */
                step(1, "ADD A,C");

                add(regC);
                break;
            }
            case 0x82: {     /* ADD A,D */
                step(1, "ADD A,D");

                add(regD);
                break;
            }
            case 0x83: {     /* ADD A,E */
                step(1, "ADD A,E");

                add(regE);
                break;
            }
            case 0x84: {     /* ADD A,H */
                step(1, "ADD A,H");

                add(regH);
                break;
            }
            case 0x85: {     /* ADD A,L */
                step(1, "ADD A,L");

                add(regL);
                break;
            }
            case 0x86: {     /* ADD A,(HL) */
                step(1, "ADD A,(HL)");

                add(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0x87: {     /* ADD A,A */
                step(1, "ADD A,A");

                add(regA);
                break;
            }
            case 0x88: {     /* ADC A,B */
                step(1, "ADC A,B");

                adc(regB);
                break;
            }
            case 0x89: {     /* ADC A,C */
                step(1, "ADC A,C");

                adc(regC);
                break;
            }
            case 0x8A: {     /* ADC A,D */
                step(1, "ADC A,D");

                adc(regD);
                break;
            }
            case 0x8B: {     /* ADC A,E */
                step(1, "ADC A,E");

                adc(regE);
                break;
            }
            case 0x8C: {     /* ADC A,H */
                step(1, "ADC A,H");

                adc(regH);
                break;
            }
            case 0x8D: {     /* ADC A,L */
                step(1, "ADC A,L");

                adc(regL);
                break;
            }
            case 0x8E: {     /* ADC A,(HL) */
                step(1, "ADC A,(HL)");

                adc(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0x8F: {     /* ADC A,A */
                step(1, "ADC A,A");

                adc(regA);
                break;
            }
            case 0x90: {     /* SUB B */
                step(1, "SUB B");

                sub(regB);
                break;
            }
            case 0x91: {     /* SUB C */
                step(1, "SUB C");

                sub(regC);
                break;
            }
            case 0x92: {     /* SUB D */
                step(1, "SUB D");

                sub(regD);
                break;
            }
            case 0x93: {     /* SUB E */
                step(1, "SUB E");

                sub(regE);
                break;
            }
            case 0x94: {     /* SUB H */
                step(1, "SUB H");

                sub(regH);
                break;
            }
            case 0x95: {     /* SUB L */
                step(1, "SUB L");

                sub(regL);
                break;
            }
            case 0x96: {     /* SUB (HL) */
                step(1, "SUB (HL)");

                sub(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0x97: {     /* SUB A */
                step(1, "SUB A");

                sub(regA);
                break;
            }
            case 0x98: {     /* SBC A,B */
                step(1, "SBC A,B");

                sbc(regB);
                break;
            }
            case 0x99: {     /* SBC A,C */
                step(1, "SBC A,C");

                sbc(regC);
                break;
            }
            case 0x9A: {     /* SBC A,D */
                step(1, "SBC A,D");

                sbc(regD);
                break;
            }
            case 0x9B: {     /* SBC A,E */
                step(1, "SBC A,E");

                sbc(regE);
                break;
            }
            case 0x9C: {     /* SBC A,H */
                step(1, "SBC A,H");

                sbc(regH);
                break;
            }
            case 0x9D: {     /* SBC A,L */
                step(1, "SBC A,L");

                sbc(regL);
                break;
            }
            case 0x9E: {     /* SBC A,(HL) */
                step(1, "SBC A,(HL)");

                sbc(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0x9F: {     /* SBC A,A */
                step(1, "SBC A,A");

                sbc(regA);
                break;
            }
            case 0xA0: {     /* AND B */
                step(1, "AND B");

                and(regB);
                break;
            }
            case 0xA1: {     /* AND C */
                step(1, "AND C");

                and(regC);
                break;
            }
            case 0xA2: {     /* AND D */
                step(1, "AND D");

                and(regD);
                break;
            }
            case 0xA3: {     /* AND E */
                step(1, "AND E");

                and(regE);
                break;
            }
            case 0xA4: {     /* AND H */
                step(1, "AND H");

                and(regH);
                break;
            }
            case 0xA5: {     /* AND L */
                step(1, "AND L");

                and(regL);
                break;
            }
            case 0xA6: {     /* AND (HL) */
                step(1, "AND (HL)");

                and(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0xA7: {     /* AND A */
                step(1, "AND A");

                and(regA);
                break;
            }
            case 0xA8: {     /* XOR B */
                step(1, "XOR B");

                xor(regB);
                break;
            }
            case 0xA9: {     /* XOR C */
                step(1, "XOR C");

                xor(regC);
                break;
            }
            case 0xAA: {     /* XOR D */
                step(1, "XOR D");

                xor(regD);
                break;
            }
            case 0xAB: {     /* XOR E */
                step(1, "XOR E");

                xor(regE);
                break;
            }
            case 0xAC: {     /* XOR H */
                step(1, "XOR H");

                xor(regH);
                break;
            }
            case 0xAD: {     /* XOR L */
                step(1, "XOR L");

                xor(regL);
                break;
            }
            case 0xAE: {     /* XOR (HL) */
                step(1, "XOR (HL)");

                xor(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0xAF: {     /* XOR A */
                step(1, "XOR A");

                xor(regA);
                break;
            }
            case 0xB0: {     /* OR B */
                step(1, "OR B");

                or(regB);
                break;
            }
            case 0xB1: {     /* OR C */
                step(1, "OR C");

                or(regC);
                break;
            }
            case 0xB2: {     /* OR D */
                step(1, "OR D");

                or(regD);
                break;
            }
            case 0xB3: {     /* OR E */
                step(1, "OR E");

                or(regE);
                break;
            }
            case 0xB4: {     /* OR H */
                step(1, "OR H");

                or(regH);
                break;
            }
            case 0xB5: {     /* OR L */
                step(1, "OR L");

                or(regL);
                break;
            }
            case 0xB6: {     /* OR (HL) */
                step(1, "OR (HL)");

                or(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0xB7: {     /* OR A */
                step(1, "OR A");

                or(regA);
                break;
            }
            case 0xB8: {     /* CP B */
                step(1, "CP B");

                cp(regB);
                break;
            }
            case 0xB9: {     /* CP C */
                step(1, "CP C");

                cp(regC);
                break;
            }
            case 0xBA: {     /* CP D */
                step(1, "CP D");

                cp(regD);
                break;
            }
            case 0xBB: {     /* CP E */
                step(1, "CP E");

                cp(regE);
                break;
            }
            case 0xBC: {     /* CP H */
                step(1, "CP H");

                cp(regH);
                break;
            }
            case 0xBD: {     /* CP L */
                step(1, "CP L");

                cp(regL);
                break;
            }
            case 0xBE: {     /* CP (HL) */
                step(1, "CP (HL)");

                cp(MemIoImpl.peek8(getRegHL()));
                break;
            }
            case 0xBF: {     /* CP A */
                step(1, "CP A");

                cp(regA);
                break;
            }
            case 0xC0: {     /* RET NZ */
                step(1, "RET NZ");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if ((sz5h3pnFlags & ZERO_MASK) == 0) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xC1: {     /* POP BC */
                step(1, "POP BC");

                setRegBC(pop());
                break;
            }
            case 0xC2: {     /* JP NZ,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP NZ," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & ZERO_MASK) == 0) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xC3: {     /* JP nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP " + hex16(value));

                memptr = regPC = value;
                break;
            }
            case 0xC4: {     /* CALL NZ,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL NZ," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & ZERO_MASK) == 0) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xC5: {     /* PUSH BC */
                step(1, "PUSH BC");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(getRegBC());
                break;
            }
            case 0xC6: {     /* ADD A,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, " ADD A," + hex8(value));

                add(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xC7: {     /* RST 00H */
                step(1, "RST 00H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x00;
                break;
            }
            case 0xC8: {     /* RET Z */
                step(1, "RET Z");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if ((sz5h3pnFlags & ZERO_MASK) != 0) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xC9: {     /* RET */
                step(1, "RET");

                regPC = memptr = pop();
                break;
            }
            case 0xCA: {     /* JP Z,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP Z," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & ZERO_MASK) != 0) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xCB: {     /* Subconjunto de instrucciones */
                decodeCB();
                break;
            }
            case 0xCC: {     /* CALL Z,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL Z," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & ZERO_MASK) != 0) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xCD: {     /* CALL nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL " + hex16(value));

                memptr = value;
                MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                push(regPC + 2);
                regPC = memptr;
                break;
            }
            case 0xCE: {     /* ADC A,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "ADC A," + hex8(value));

                adc(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xCF: {     /* RST 08H */
                step(1, "RST 08H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x08;
                break;
            }
            case 0xD0: {     /* RET NC */
                step(1, "RET NC");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if (!carryFlag) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xD1: {     /* POP DE */
                step(1, "POP DE");

                setRegDE(pop());
                break;
            }
            case 0xD2: {     /* JP NC,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP NC," + hex16(value));

                memptr = value;
                if (!carryFlag) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xD3: {     /* OUT (n),A */
                int value = MemIoImpl.peek8(regPC);
                step(2, "OUT (" + hex8(value) + "),A");

                int work8 = value;
                memptr = regA << 8;
                MemIoImpl.outPort(memptr | work8, regA);
                memptr |= ((work8 + 1) & 0xff);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xD4: {     /* CALL NC,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL NC," + hex16(value));

                memptr = value;
                if (!carryFlag) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xD5: {     /* PUSH DE */
                step(1, "PUSH DE");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(getRegDE());
                break;
            }
            case 0xD6: {     /* SUB n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "SUB " + hex8(value));

                sub(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xD7: {     /* RST 10H */
                step(1, "RST 10H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x10;
                break;
            }
            case 0xD8: {     /* RET C */
                step(1, "RET C");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if (carryFlag) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xD9: {     /* EXX */
                step(1, "EXX");

                int work8 = regB;
                regB = regBx;
                regBx = work8;

                work8 = regC;
                regC = regCx;
                regCx = work8;

                work8 = regD;
                regD = regDx;
                regDx = work8;

                work8 = regE;
                regE = regEx;
                regEx = work8;

                work8 = regH;
                regH = regHx;
                regHx = work8;

                work8 = regL;
                regL = regLx;
                regLx = work8;
                break;
            }
            case 0xDA: {     /* JP C,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP C," + hex16(value));

                memptr = value;
                if (carryFlag) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xDB: {     /* IN A,(n) */
                int value = MemIoImpl.peek8(regPC);
                step(2, "IN A,(" + hex8(value) + ")");

                memptr = (regA << 8) | value;
                regA = MemIoImpl.inPort(memptr++);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xDC: {     /* CALL C,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL C," + hex16(value));

                memptr = value;
                if (carryFlag) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xDD: {     /* Subconjunto de instrucciones */
                opCode = MemIoImpl.fetchOpcode(regPC);
                regPC = (regPC + 1) & 0xffff;
                regR ++;
                regIX = decodeDDFD(opCode, regIX);
                break;
            }
            case 0xDE: {     /* SBC A,n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "SBC A," + hex8(value));

                sbc(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xDF: {     /* RST 18H */
                step(1, "RST 18H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x18;
                break;
            }
            case 0xE0: {     /* RET PO */
                step(1, "RET PO");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if ((sz5h3pnFlags & PARITY_MASK) == 0) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xE1: {     /* POP HL */
                step(1, "POP HL");

                setRegHL(pop());
                break;
            }
            case 0xE2: {     /* JP PO,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP PO," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & PARITY_MASK) == 0) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xE3: {     /* EX (SP),HL */
                step(1, "EX (SP),HL");

                // Instrucción de ejecución sutil.
                int work16 = regH;
                int work8 = regL;
                setRegHL(MemIoImpl.peek16(regSP));
                MemIoImpl.addressOnBus((regSP + 1) & 0xffff, 1);
                // No se usa poke16 porque el Z80 escribe los bytes AL REVES
                MemIoImpl.poke8((regSP + 1) & 0xffff, work16);
                MemIoImpl.poke8(regSP, work8);
                MemIoImpl.addressOnBus(regSP, 2);
                memptr = getRegHL();
                break;
            }
            case 0xE4: {     /* CALL PO,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL PO," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & PARITY_MASK) == 0) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xE5: {      /* PUSH HL */
                step(1, "PUSH HL");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(getRegHL());
                break;
            }
            case 0xE6: {     /* AND n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "AND " + hex8(value));

                and(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xE7: {     /* RST 20H */
                step(1, "RST 20H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x20;
                break;
            }
            case 0xE8: {     /* RET PE */
                step(1, "RET PE");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if ((sz5h3pnFlags & PARITY_MASK) != 0) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xE9: {     /* JP (HL) */
                step(1, "JP (HL)");

                regPC = getRegHL();
                break;
            }
            case 0xEA: {     /* JP PE,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP PE," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & PARITY_MASK) != 0) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xEB: {     /* EX DE,HL */
                step(1, "EX DE,HL");

                int work8 = regH;
                regH = regD;
                regD = work8;

                work8 = regL;
                regL = regE;
                regE = work8;
                break;
            }
            case 0xEC: {     /* CALL PE,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL PE," + hex16(value));

                memptr = value;
                if ((sz5h3pnFlags & PARITY_MASK) != 0) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xED: {     /* Subconjunto de instrucciones*/
                opCode = MemIoImpl.fetchOpcode(regPC);
                regPC = (regPC + 1) & 0xffff;
                regR++;
                decodeED(opCode);
                break;
            }
            case 0xEE: {     /* XOR n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "XOR " + hex8(value));

                xor(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xEF: {     /* RST 28H */
                step(1, "RST 28H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x28;
                break;
            }
            case 0xF0: {     /* RET P */
                step(1, "RET P");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if (sz5h3pnFlags < SIGN_MASK) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xF1: {     /* POP AF */
                step(1, "POP AF");

                setRegAF(pop());
                break;
            }
            case 0xF2: {     /* JP P,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP P," + hex16(value));

                memptr = value;
                if (sz5h3pnFlags < SIGN_MASK) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xF3: {     /* DI */
                step(1, "DI");

                ffIFF1 = ffIFF2 = false;
                break;
            }
            case 0xF4: {     /* CALL P,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL P," + hex16(value));

                memptr = value;
                if (sz5h3pnFlags < SIGN_MASK) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xF5: {     /* PUSH AF */
                step(1, "PUSH AF");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(getRegAF());
                break;
            }
            case 0xF6: {     /* OR n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "CALL P," + hex8(value));

                or(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xF7: {     /* RST 30H */
                step(1, "RST 30H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x30;
                break;
            }
            case 0xF8: {     /* RET M */
                step(1, "RET M");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                if (sz5h3pnFlags > 0x7f) {
                    regPC = memptr = pop();
                }
                break;
            }
            case 0xF9: {     /* LD SP,HL */
                step(1, "LD SP,HL");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                regSP = getRegHL();
                break;
            }
            case 0xFA: {     /* JP M,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "JP M," + hex16(value));

                memptr = value;
                if (sz5h3pnFlags > 0x7f) {
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xFB: {     /* EI */
                step(1, "EI");

                ffIFF1 = ffIFF2 = true;
                pendingEI = true;
                break;
            }
            case 0xFC: {     /* CALL M,nn */
                int value = MemIoImpl.peek16(regPC);
                step(3, "CALL M," + hex16(value));

                memptr = value;
                if (sz5h3pnFlags > 0x7f) {
                    MemIoImpl.addressOnBus((regPC + 1) & 0xffff, 1);
                    push(regPC + 2);
                    regPC = memptr;
                    break;
                }
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xFD: {     /* Subconjunto de instrucciones */
                opCode = MemIoImpl.fetchOpcode(regPC);
                regPC = (regPC + 1) & 0xffff;
                regR++;
                regIY = decodeDDFD(opCode, regIY);
                break;
            }
            case 0xFE: {      /* CP n */
                int value = MemIoImpl.peek8(regPC);
                step(2, "CP " + hex8(value));

                cp(value);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xFF: {     /* RST 38H */
                step(1, "RST 38H");

                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regPC);
                regPC = memptr = 0x38;
            }
        }
    }

    // Subconjunto de instrucciones 0xCB
    private void decodeCB() {
        int opCode = MemIoImpl.fetchOpcode(regPC);
        regPC = (regPC + 1) & 0xffff;
        regR++;

        switch (opCode) {
            case 0x00: {     /* RLC B */
                step(2, "RLC B");

                regB = rlc(regB);
                break;
            }
            case 0x01: {     /* RLC C */
                step(2, "RLC C");

                regC = rlc(regC);
                break;
            }
            case 0x02: {     /* RLC D */
                step(2, "RLC D");

                regD = rlc(regD);
                break;
            }
            case 0x03: {     /* RLC E */
                step(2, "RLC E");

                regE = rlc(regE);
                break;
            }
            case 0x04: {     /* RLC H */
                step(2, "RLC H");

                regH = rlc(regH);
                break;
            }
            case 0x05: {     /* RLC L */
                step(2, "RLC L");

                regL = rlc(regL);
                break;
            }
            case 0x06: {     /* RLC (HL) */
                step(2, "RLC (HL)");

                int work16 = getRegHL();
                int work8 = rlc(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x07: {     /* RLC A */
                step(2, "RLC A");

                regA = rlc(regA);
                break;
            }
            case 0x08: {     /* RRC B */
                step(2, "RRC B");

                regB = rrc(regB);
                break;
            }
            case 0x09: {     /* RRC C */
                step(2, "RRC C");

                regC = rrc(regC);
                break;
            }
            case 0x0A: {     /* RRC D */
                step(2, "RRC D");

                regD = rrc(regD);
                break;
            }
            case 0x0B: {     /* RRC E */
                step(2, "RRC E");

                regE = rrc(regE);
                break;
            }
            case 0x0C: {     /* RRC H */
                step(2, "RRC H");

                regH = rrc(regH);
                break;
            }
            case 0x0D: {     /* RRC L */
                step(2, "RRC L");

                regL = rrc(regL);
                break;
            }
            case 0x0E: {     /* RRC (HL) */
                step(2, "RRC (HL)");

                int work16 = getRegHL();
                int work8 = rrc(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x0F: {     /* RRC A */
                step(2, "RRC A");

                regA = rrc(regA);
                break;
            }
            case 0x10: {     /* RL B */
                step(2, "RL B");

                regB = rl(regB);
                break;
            }
            case 0x11: {     /* RL C */
                step(2, "RL C");

                regC = rl(regC);
                break;
            }
            case 0x12: {     /* RL D */
                step(2, "RL D");

                regD = rl(regD);
                break;
            }
            case 0x13: {     /* RL E */
                step(2, "RL E");

                regE = rl(regE);
                break;
            }
            case 0x14: {     /* RL H */
                step(2, "RL H");

                regH = rl(regH);
                break;
            }
            case 0x15: {     /* RL L */
                step(2, "RL L");

                regL = rl(regL);
                break;
            }
            case 0x16: {     /* RL (HL) */
                step(2, "RL (HL)");

                int work16 = getRegHL();
                int work8 = rl(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x17: {     /* RL A */
                step(2, "RL A");

                regA = rl(regA);
                break;
            }
            case 0x18: {     /* RR B */
                step(2, "RR B");

                regB = rr(regB);
                break;
            }
            case 0x19: {     /* RR C */
                step(2, "RR C");

                regC = rr(regC);
                break;
            }
            case 0x1A: {     /* RR D */
                step(2, "RR D");

                regD = rr(regD);
                break;
            }
            case 0x1B: {     /* RR E */
                step(2, "RR E");

                regE = rr(regE);
                break;
            }
            case 0x1C: {     /*RR H*/
                step(2, "RR H");

                regH = rr(regH);
                break;
            }
            case 0x1D: {     /* RR L */
                step(2, "RR L");

                regL = rr(regL);
                break;
            }
            case 0x1E: {     /* RR (HL) */
                step(2, "RR (HL)");

                int work16 = getRegHL();
                int work8 = rr(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x1F: {     /* RR A */
                step(2, "RR A");

                regA = rr(regA);
                break;
            }
            case 0x20: {     /* SLA B */
                step(2, "SLA B");

                regB = sla(regB);
                break;
            }
            case 0x21: {     /* SLA C */
                step(2, "SLA C");

                regC = sla(regC);
                break;
            }
            case 0x22: {     /* SLA D */
                step(2, "SLA D");

                regD = sla(regD);
                break;
            }
            case 0x23: {     /* SLA E */
                step(2, "SLA E");

                regE = sla(regE);
                break;
            }
            case 0x24: {     /* SLA H */
                step(2, "SLA H");

                regH = sla(regH);
                break;
            }
            case 0x25: {     /* SLA L */
                step(2, "SLA L");

                regL = sla(regL);
                break;
            }
            case 0x26: {     /* SLA (HL) */
                step(2, "SLA (HL)");

                int work16 = getRegHL();
                int work8 = sla(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x27: {     /* SLA A */
                step(2, "SLA A");

                regA = sla(regA);
                break;
            }
            case 0x28: {     /* SRA B */
                step(2, "SRA B");

                regB = sra(regB);
                break;
            }
            case 0x29: {     /* SRA C */
                step(2, "SRA C");

                regC = sra(regC);
                break;
            }
            case 0x2A: {     /* SRA D */
                step(2, "SRA D");

                regD = sra(regD);
                break;
            }
            case 0x2B: {     /* SRA E */
                step(2, "SRA E");

                regE = sra(regE);
                break;
            }
            case 0x2C: {     /* SRA H */
                step(2, "SRA H");

                regH = sra(regH);
                break;
            }
            case 0x2D: {     /* SRA L */
                step(2, "SRA L");

                regL = sra(regL);
                break;
            }
            case 0x2E: {     /* SRA (HL) */
                step(2, "SRA (HL)");

                int work16 = getRegHL();
                int work8 = sra(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x2F: {     /* SRA A */
                step(2, "SRA A");

                regA = sra(regA);
                break;
            }
            case 0x30: {     /* SLL B */
                step(2, "SLL B");

                regB = sll(regB);
                break;
            }
            case 0x31: {     /* SLL C */
                step(2, "SLL C");

                regC = sll(regC);
                break;
            }
            case 0x32: {     /* SLL D */
                step(2, "SLL D");

                regD = sll(regD);
                break;
            }
            case 0x33: {     /* SLL E */
                step(2, "SLL E");

                regE = sll(regE);
                break;
            }
            case 0x34: {     /* SLL H */
                step(2, "SLL H");

                regH = sll(regH);
                break;
            }
            case 0x35: {     /* SLL L */
                step(2, "SLL L");

                regL = sll(regL);
                break;
            }
            case 0x36: {     /* SLL (HL) */
                step(2, "SLL (HL)");

                int work16 = getRegHL();
                int work8 = sll(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x37: {     /* SLL A */
                step(2, "SLL A");

                regA = sll(regA);
                break;
            }
            case 0x38: {     /* SRL B */
                step(2, "SRL B");

                regB = srl(regB);
                break;
            }
            case 0x39: {     /* SRL C */
                step(2, "SRL C");

                regC = srl(regC);
                break;
            }
            case 0x3A: {     /* SRL D */
                step(2, "SRL D");

                regD = srl(regD);
                break;
            }
            case 0x3B: {     /* SRL E */
                step(2, "SRL E");

                regE = srl(regE);
                break;
            }
            case 0x3C: {     /* SRL H */
                step(2, "SRL H");

                regH = srl(regH);
                break;
            }
            case 0x3D: {     /* SRL L */
                step(2, "SRL L");

                regL = srl(regL);
                break;
            }
            case 0x3E: {     /* SRL (HL) */
                step(2, "SRL (HL)");

                int work16 = getRegHL();
                int work8 = srl(MemIoImpl.peek8(work16));
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x3F: {     /* SRL A */
                step(2, "SRL A");

                regA = srl(regA);
                break;
            }
            case 0x40: {     /* BIT 0,B */
                bit(0x01, regB);
                break;
            }
            case 0x41: {     /* BIT 0,C */
                bit(0x01, regC);
                break;
            }
            case 0x42: {     /* BIT 0,D */
                bit(0x01, regD);
                break;
            }
            case 0x43: {     /* BIT 0,E */
                bit(0x01, regE);
                break;
            }
            case 0x44: {     /* BIT 0,H */
                bit(0x01, regH);
                break;
            }
            case 0x45: {     /* BIT 0,L */
                bit(0x01, regL);
                break;
            }
            case 0x46: {     /* BIT 0,(HL) */
                int work16 = getRegHL();
                bit(0x01, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x47: {     /* BIT 0,A */
                bit(0x01, regA);
                break;
            }
            case 0x48: {     /* BIT 1,B */
                bit(0x02, regB);
                break;
            }
            case 0x49: {     /* BIT 1,C */
                bit(0x02, regC);
                break;
            }
            case 0x4A: {     /* BIT 1,D */
                bit(0x02, regD);
                break;
            }
            case 0x4B: {     /* BIT 1,E */
                bit(0x02, regE);
                break;
            }
            case 0x4C: {     /* BIT 1,H */
                bit(0x02, regH);
                break;
            }
            case 0x4D: {     /* BIT 1,L */
                bit(0x02, regL);
                break;
            }
            case 0x4E: {     /* BIT 1,(HL) */
                int work16 = getRegHL();
                bit(0x02, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x4F: {     /* BIT 1,A */
                bit(0x02, regA);
                break;
            }
            case 0x50: {     /* BIT 2,B */
                bit(0x04, regB);
                break;
            }
            case 0x51: {     /* BIT 2,C */
                bit(0x04, regC);
                break;
            }
            case 0x52: {     /* BIT 2,D */
                bit(0x04, regD);
                break;
            }
            case 0x53: {     /* BIT 2,E */
                bit(0x04, regE);
                break;
            }
            case 0x54: {     /* BIT 2,H */
                bit(0x04, regH);
                break;
            }
            case 0x55: {     /* BIT 2,L */
                bit(0x04, regL);
                break;
            }
            case 0x56: {     /* BIT 2,(HL) */
                int work16 = getRegHL();
                bit(0x04, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x57: {     /* BIT 2,A */
                bit(0x04, regA);
                break;
            }
            case 0x58: {     /* BIT 3,B */
                bit(0x08, regB);
                break;
            }
            case 0x59: {     /* BIT 3,C */
                bit(0x08, regC);
                break;
            }
            case 0x5A: {     /* BIT 3,D */
                bit(0x08, regD);
                break;
            }
            case 0x5B: {     /* BIT 3,E */
                bit(0x08, regE);
                break;
            }
            case 0x5C: {     /* BIT 3,H */
                bit(0x08, regH);
                break;
            }
            case 0x5D: {     /* BIT 3,L */
                bit(0x08, regL);
                break;
            }
            case 0x5E: {     /* BIT 3,(HL) */
                int work16 = getRegHL();
                bit(0x08, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x5F: {     /* BIT 3,A */
                bit(0x08, regA);
                break;
            }
            case 0x60: {     /* BIT 4,B */
                bit(0x10, regB);
                break;
            }
            case 0x61: {     /* BIT 4,C */
                bit(0x10, regC);
                break;
            }
            case 0x62: {     /* BIT 4,D */
                bit(0x10, regD);
                break;
            }
            case 0x63: {     /* BIT 4,E */
                bit(0x10, regE);
                break;
            }
            case 0x64: {     /* BIT 4,H */
                bit(0x10, regH);
                break;
            }
            case 0x65: {     /* BIT 4,L */
                bit(0x10, regL);
                break;
            }
            case 0x66: {     /* BIT 4,(HL) */
                int work16 = getRegHL();
                bit(0x10, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x67: {     /* BIT 4,A */
                bit(0x10, regA);
                break;
            }
            case 0x68: {     /* BIT 5,B */
                bit(0x20, regB);
                break;
            }
            case 0x69: {     /* BIT 5,C */
                bit(0x20, regC);
                break;
            }
            case 0x6A: {     /* BIT 5,D */
                bit(0x20, regD);
                break;
            }
            case 0x6B: {     /* BIT 5,E */
                bit(0x20, regE);
                break;
            }
            case 0x6C: {     /* BIT 5,H */
                bit(0x20, regH);
                break;
            }
            case 0x6D: {     /* BIT 5,L */
                bit(0x20, regL);
                break;
            }
            case 0x6E: {     /* BIT 5,(HL) */
                int work16 = getRegHL();
                bit(0x20, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x6F: {     /* BIT 5,A */
                bit(0x20, regA);
                break;
            }
            case 0x70: {     /* BIT 6,B */
                bit(0x40, regB);
                break;
            }
            case 0x71: {     /* BIT 6,C */
                bit(0x40, regC);
                break;
            }
            case 0x72: {     /* BIT 6,D */
                bit(0x40, regD);
                break;
            }
            case 0x73: {     /* BIT 6,E */
                bit(0x40, regE);
                break;
            }
            case 0x74: {     /* BIT 6,H */
                bit(0x40, regH);
                break;
            }
            case 0x75: {     /* BIT 6,L */
                bit(0x40, regL);
                break;
            }
            case 0x76: {     /* BIT 6,(HL) */
                int work16 = getRegHL();
                bit(0x40, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x77: {     /* BIT 6,A */
                bit(0x40, regA);
                break;
            }
            case 0x78: {     /* BIT 7,B */
                bit(0x80, regB);
                break;
            }
            case 0x79: {     /* BIT 7,C */
                bit(0x80, regC);
                break;
            }
            case 0x7A: {     /* BIT 7,D */
                bit(0x80, regD);
                break;
            }
            case 0x7B: {     /* BIT 7,E */
                bit(0x80, regE);
                break;
            }
            case 0x7C: {     /* BIT 7,H */
                bit(0x80, regH);
                break;
            }
            case 0x7D: {     /* BIT 7,L */
                bit(0x80, regL);
                break;
            }
            case 0x7E: {     /* BIT 7,(HL) */
                int work16 = getRegHL();
                bit(0x80, MemIoImpl.peek8(work16));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((memptr >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(work16, 1);
                break;
            }
            case 0x7F: {     /* BIT 7,A */
                bit(0x80, regA);
                break;
            }
            case 0x80: {     /* RES 0,B */
                regB &= 0xFE;
                break;
            }
            case 0x81: {     /* RES 0,C */
                regC &= 0xFE;
                break;
            }
            case 0x82: {     /* RES 0,D */
                regD &= 0xFE;
                break;
            }
            case 0x83: {     /* RES 0,E */
                regE &= 0xFE;
                break;
            }
            case 0x84: {     /* RES 0,H */
                regH &= 0xFE;
                break;
            }
            case 0x85: {     /* RES 0,L */
                regL &= 0xFE;
                break;
            }
            case 0x86: {     /* RES 0,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xFE;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x87: {     /* RES 0,A */
                regA &= 0xFE;
                break;
            }
            case 0x88: {     /* RES 1,B */
                regB &= 0xFD;
                break;
            }
            case 0x89: {     /* RES 1,C */
                regC &= 0xFD;
                break;
            }
            case 0x8A: {     /* RES 1,D */
                regD &= 0xFD;
                break;
            }
            case 0x8B: {     /* RES 1,E */
                regE &= 0xFD;
                break;
            }
            case 0x8C: {     /* RES 1,H */
                regH &= 0xFD;
                break;
            }
            case 0x8D: {     /* RES 1,L */
                regL &= 0xFD;
                break;
            }
            case 0x8E: {     /* RES 1,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xFD;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x8F: {     /* RES 1,A */
                regA &= 0xFD;
                break;
            }
            case 0x90: {     /* RES 2,B */
                regB &= 0xFB;
                break;
            }
            case 0x91: {     /* RES 2,C */
                regC &= 0xFB;
                break;
            }
            case 0x92: {     /* RES 2,D */
                regD &= 0xFB;
                break;
            }
            case 0x93: {     /* RES 2,E */
                regE &= 0xFB;
                break;
            }
            case 0x94: {     /* RES 2,H */
                regH &= 0xFB;
                break;
            }
            case 0x95: {     /* RES 2,L */
                regL &= 0xFB;
                break;
            }
            case 0x96: {     /* RES 2,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xFB;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x97: {     /* RES 2,A */
                regA &= 0xFB;
                break;
            }
            case 0x98: {     /* RES 3,B */
                regB &= 0xF7;
                break;
            }
            case 0x99: {     /* RES 3,C */
                regC &= 0xF7;
                break;
            }
            case 0x9A: {     /* RES 3,D */
                regD &= 0xF7;
                break;
            }
            case 0x9B: {     /* RES 3,E */
                regE &= 0xF7;
                break;
            }
            case 0x9C: {     /* RES 3,H */
                regH &= 0xF7;
                break;
            }
            case 0x9D: {     /* RES 3,L */
                regL &= 0xF7;
                break;
            }
            case 0x9E: {     /* RES 3,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xF7;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0x9F: {     /* RES 3,A */
                regA &= 0xF7;
                break;
            }
            case 0xA0: {     /* RES 4,B */
                regB &= 0xEF;
                break;
            }
            case 0xA1: {     /* RES 4,C */
                regC &= 0xEF;
                break;
            }
            case 0xA2: {     /* RES 4,D */
                regD &= 0xEF;
                break;
            }
            case 0xA3: {     /* RES 4,E */
                regE &= 0xEF;
                break;
            }
            case 0xA4: {     /* RES 4,H */
                regH &= 0xEF;
                break;
            }
            case 0xA5: {     /* RES 4,L */
                regL &= 0xEF;
                break;
            }
            case 0xA6: {     /* RES 4,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xEF;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xA7: {     /* RES 4,A */
                regA &= 0xEF;
                break;
            }
            case 0xA8: {     /* RES 5,B */
                regB &= 0xDF;
                break;
            }
            case 0xA9: {     /* RES 5,C */
                regC &= 0xDF;
                break;
            }
            case 0xAA: {     /* RES 5,D */
                regD &= 0xDF;
                break;
            }
            case 0xAB: {     /* RES 5,E */
                regE &= 0xDF;
                break;
            }
            case 0xAC: {     /* RES 5,H */
                regH &= 0xDF;
                break;
            }
            case 0xAD: {     /* RES 5,L */
                regL &= 0xDF;
                break;
            }
            case 0xAE: {     /* RES 5,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xDF;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xAF: {     /* RES 5,A */
                regA &= 0xDF;
                break;
            }
            case 0xB0: {     /* RES 6,B */
                regB &= 0xBF;
                break;
            }
            case 0xB1: {     /* RES 6,C */
                regC &= 0xBF;
                break;
            }
            case 0xB2: {     /* RES 6,D */
                regD &= 0xBF;
                break;
            }
            case 0xB3: {     /* RES 6,E */
                regE &= 0xBF;
                break;
            }
            case 0xB4: {     /* RES 6,H */
                regH &= 0xBF;
                break;
            }
            case 0xB5: {     /* RES 6,L */
                regL &= 0xBF;
                break;
            }
            case 0xB6: {     /* RES 6,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0xBF;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xB7: {     /* RES 6,A */
                regA &= 0xBF;
                break;
            }
            case 0xB8: {     /* RES 7,B */
                regB &= 0x7F;
                break;
            }
            case 0xB9: {     /* RES 7,C */
                regC &= 0x7F;
                break;
            }
            case 0xBA: {     /* RES 7,D */
                regD &= 0x7F;
                break;
            }
            case 0xBB: {     /* RES 7,E */
                regE &= 0x7F;
                break;
            }
            case 0xBC: {     /* RES 7,H */
                regH &= 0x7F;
                break;
            }
            case 0xBD: {     /* RES 7,L */
                regL &= 0x7F;
                break;
            }
            case 0xBE: {     /* RES 7,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) & 0x7F;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xBF: {     /* RES 7,A */
                regA &= 0x7F;
                break;
            }
            case 0xC0: {     /* SET 0,B */
                regB |= 0x01;
                break;
            }
            case 0xC1: {     /* SET 0,C */
                regC |= 0x01;
                break;
            }
            case 0xC2: {     /* SET 0,D */
                regD |= 0x01;
                break;
            }
            case 0xC3: {     /* SET 0,E */
                regE |= 0x01;
                break;
            }
            case 0xC4: {     /* SET 0,H */
                regH |= 0x01;
                break;
            }
            case 0xC5: {     /* SET 0,L */
                regL |= 0x01;
                break;
            }
            case 0xC6: {     /* SET 0,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x01;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xC7: {     /* SET 0,A */
                regA |= 0x01;
                break;
            }
            case 0xC8: {     /* SET 1,B */
                regB |= 0x02;
                break;
            }
            case 0xC9: {     /* SET 1,C */
                regC |= 0x02;
                break;
            }
            case 0xCA: {     /* SET 1,D */
                regD |= 0x02;
                break;
            }
            case 0xCB: {     /* SET 1,E */
                regE |= 0x02;
                break;
            }
            case 0xCC: {     /* SET 1,H */
                regH |= 0x02;
                break;
            }
            case 0xCD: {     /* SET 1,L */
                regL |= 0x02;
                break;
            }
            case 0xCE: {     /* SET 1,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x02;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xCF: {     /* SET 1,A */
                regA |= 0x02;
                break;
            }
            case 0xD0: {     /* SET 2,B */
                regB |= 0x04;
                break;
            }
            case 0xD1: {     /* SET 2,C */
                regC |= 0x04;
                break;
            }
            case 0xD2: {     /* SET 2,D */
                regD |= 0x04;
                break;
            }
            case 0xD3: {     /* SET 2,E */
                regE |= 0x04;
                break;
            }
            case 0xD4: {     /* SET 2,H */
                regH |= 0x04;
                break;
            }
            case 0xD5: {     /* SET 2,L */
                regL |= 0x04;
                break;
            }
            case 0xD6: {     /* SET 2,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x04;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xD7: {     /* SET 2,A */
                regA |= 0x04;
                break;
            }
            case 0xD8: {     /* SET 3,B */
                regB |= 0x08;
                break;
            }
            case 0xD9: {     /* SET 3,C */
                regC |= 0x08;
                break;
            }
            case 0xDA: {     /* SET 3,D */
                regD |= 0x08;
                break;
            }
            case 0xDB: {     /* SET 3,E */
                regE |= 0x08;
                break;
            }
            case 0xDC: {     /* SET 3,H */
                regH |= 0x08;
                break;
            }
            case 0xDD: {     /* SET 3,L */
                regL |= 0x08;
                break;
            }
            case 0xDE: {     /* SET 3,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x08;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xDF: {     /* SET 3,A */
                regA |= 0x08;
                break;
            }
            case 0xE0: {     /* SET 4,B */
                regB |= 0x10;
                break;
            }
            case 0xE1: {     /* SET 4,C */
                regC |= 0x10;
                break;
            }
            case 0xE2: {     /* SET 4,D */
                regD |= 0x10;
                break;
            }
            case 0xE3: {     /* SET 4,E */
                regE |= 0x10;
                break;
            }
            case 0xE4: {     /* SET 4,H */
                regH |= 0x10;
                break;
            }
            case 0xE5: {     /* SET 4,L */
                regL |= 0x10;
                break;
            }
            case 0xE6: {     /* SET 4,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x10;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xE7: {     /* SET 4,A */
                regA |= 0x10;
                break;
            }
            case 0xE8: {     /* SET 5,B */
                regB |= 0x20;
                break;
            }
            case 0xE9: {     /* SET 5,C */
                regC |= 0x20;
                break;
            }
            case 0xEA: {     /* SET 5,D */
                regD |= 0x20;
                break;
            }
            case 0xEB: {     /* SET 5,E */
                regE |= 0x20;
                break;
            }
            case 0xEC: {     /* SET 5,H */
                regH |= 0x20;
                break;
            }
            case 0xED: {     /* SET 5,L */
                regL |= 0x20;
                break;
            }
            case 0xEE: {     /* SET 5,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x20;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xEF: {     /* SET 5,A */
                regA |= 0x20;
                break;
            }
            case 0xF0: {     /* SET 6,B */
                regB |= 0x40;
                break;
            }
            case 0xF1: {     /* SET 6,C */
                regC |= 0x40;
                break;
            }
            case 0xF2: {     /* SET 6,D */
                regD |= 0x40;
                break;
            }
            case 0xF3: {     /* SET 6,E */
                regE |= 0x40;
                break;
            }
            case 0xF4: {     /* SET 6,H */
                regH |= 0x40;
                break;
            }
            case 0xF5: {     /* SET 6,L */
                regL |= 0x40;
                break;
            }
            case 0xF6: {     /* SET 6,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x40;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xF7: {     /* SET 6,A */
                regA |= 0x40;
                break;
            }
            case 0xF8: {     /* SET 7,B */
                regB |= 0x80;
                break;
            }
            case 0xF9: {     /* SET 7,C */
                regC |= 0x80;
                break;
            }
            case 0xFA: {     /* SET 7,D */
                regD |= 0x80;
                break;
            }
            case 0xFB: {     /* SET 7,E */
                regE |= 0x80;
                break;
            }
            case 0xFC: {     /* SET 7,H */
                regH |= 0x80;
                break;
            }
            case 0xFD: {     /* SET 7,L */
                regL |= 0x80;
                break;
            }
            case 0xFE: {     /* SET 7,(HL) */
                int work16 = getRegHL();
                int work8 = MemIoImpl.peek8(work16) | 0x80;
                MemIoImpl.addressOnBus(work16, 1);
                MemIoImpl.poke8(work16, work8);
                break;
            }
            case 0xFF: {     /* SET 7,A */
                regA |= 0x80;
                break;
            }
            default: {
//                System.out.println("Error instrucción CB " + Integer.toHexString(opCode));
                break;
            }
        }
    }

    //Subconjunto de instrucciones 0xDD / 0xFD
    /*
     * Hay que tener en cuenta el manejo de secuencias códigos DD/FD que no
     * hacen nada. Según el apartado 3.7 del documento
     * [http://www.myquest.nl/z80undocumented/z80-documented-v0.91.pdf]
     * secuencias de códigos como FD DD 00 21 00 10 NOP NOP NOP LD HL,1000h
     * activan IY con el primer FD, IX con el segundo DD y vuelven al
     * registro HL con el código NOP. Es decir, si detrás del código DD/FD no
     * viene una instrucción que maneje el registro HL, el código DD/FD
     * "se olvida" y hay que procesar la instrucción como si nunca se
     * hubiera visto el prefijo (salvo por los 4 t-estados que ha costado).
     * Naturalmente, en una serie repetida de DDFD no hay que comprobar las
     * interrupciones entre cada prefijo.
     */
    private int decodeDDFD(int opCode, int regIXY) {
        switch (opCode) {
            case 0x09: {     /* ADD IX,BC */
                step(3, "ADD IX,BC");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                regIXY = add16(regIXY, getRegBC());
                break;
            }
            case 0x19: {     /* ADD IX,DE */
                step(3, "ADD IX,DE");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                regIXY = add16(regIXY, getRegDE());
                break;
            }
            case 0x21: {     /* LD IX,nn */
                int value = MemIoImpl.peek16(regPC);
                step(5, "LD IX," + hex16(value));

                regIXY = value;
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x22: {     /* LD (nn),IX */
                int value = MemIoImpl.peek16(regPC);
                step(5, "LD (" + hex16(value) + "),IX");

                memptr = value;
                MemIoImpl.poke16(memptr++, regIXY);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x23: {     /* INC IX */
                step(3, "INC IX");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                regIXY = (regIXY + 1) & 0xffff;
                break;
            }
            case 0x24: {     /* INC IXh */
                step(3, "INC IXh");

                regIXY = (inc8(regIXY >>> 8) << 8) | (regIXY & 0xff);
                break;
            }
            case 0x25: {     /* DEC IXh */
                step(3, "DEC IXh");

                regIXY = (dec8(regIXY >>> 8) << 8) | (regIXY & 0xff);
                break;
            }
            case 0x26: {     /* LD IXh,n */
                int value = MemIoImpl.peek8(regPC);
                step(3, "LD IXh," + hex8(value));

                regIXY = (value << 8) | (regIXY & 0xff);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x29: {     /* ADD IX,IX */
                step(3, "ADD IX,IX");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                regIXY = add16(regIXY, regIXY);
                break;
            }
            case 0x2A: {     /* LD IX,(nn) */
                int value = MemIoImpl.peek16(regPC);
                step(5, "LD IX,(" + hex16(value) + ")");

                memptr = value;
                regIXY = MemIoImpl.peek16(memptr++);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x2B: {     /* DEC IX */
                step(3, "DEC IX");

                MemIoImpl.addressOnBus(getPairIR(), 2);
                regIXY = (regIXY - 1) & 0xffff;
                break;
            }
            case 0x2C: {     /* INC IXl */
                step(3, "INC IXl");

                regIXY = (regIXY & 0xff00) | inc8(regIXY & 0xff);
                break;
            }
            case 0x2D: {     /* DEC IXl */
                step(3, "DEC IXl");

                regIXY = (regIXY & 0xff00) | dec8(regIXY & 0xff);
                break;
            }
            case 0x2E: {     /* LD IXl,n */
                int value = MemIoImpl.peek8(regPC);
                step(3, "LD IXl," + hex8(value));

                regIXY = (regIXY & 0xff00) | value;
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x34: {     /* INC (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                int work8 = MemIoImpl.peek8(memptr);
                MemIoImpl.addressOnBus(memptr, 1);
                MemIoImpl.poke8(memptr, inc8(work8));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x35: {     /* DEC (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                int work8 = MemIoImpl.peek8(memptr);
                MemIoImpl.addressOnBus(memptr, 1);
                MemIoImpl.poke8(memptr, dec8(work8));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x36: {     /* LD (IX+d),n */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                regPC = (regPC + 1) & 0xffff;
                int work8 = MemIoImpl.peek8(regPC);
                MemIoImpl.addressOnBus(regPC, 2);
                regPC = (regPC + 1) & 0xffff;
                MemIoImpl.poke8(memptr, work8);
                break;
            }
            case 0x39: {     /* ADD IX,SP */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                regIXY = add16(regIXY, regSP);
                break;
            }
            case 0x44: {     /* LD B,IXh */
                regB = regIXY >>> 8;
                break;
            }
            case 0x45: {     /* LD B,IXl */
                regB = regIXY & 0xff;
                break;
            }
            case 0x46: {     /* LD B,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regB = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x4C: {     /* LD C,IXh */
                regC = regIXY >>> 8;
                break;
            }
            case 0x4D: {     /* LD C,IXl */
                regC = regIXY & 0xff;
                break;
            }
            case 0x4E: {     /* LD C,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regC = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x54: {     /* LD D,IXh */
                regD = regIXY >>> 8;
                break;
            }
            case 0x55: {     /* LD D,IXl */
                regD = regIXY & 0xff;
                break;
            }
            case 0x56: {     /* LD D,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regD = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x5C: {     /* LD E,IXh */
                regE = regIXY >>> 8;
                break;
            }
            case 0x5D: {     /* LD E,IXl */
                regE = regIXY & 0xff;
                break;
            }
            case 0x5E: {     /* LD E,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regE = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x60: {     /* LD IXh,B */
                regIXY = (regIXY & 0x00ff) | (regB << 8);
                break;
            }
            case 0x61: {     /* LD IXh,C */
                regIXY = (regIXY & 0x00ff) | (regC << 8);
                break;
            }
            case 0x62: {     /* LD IXh,D */
                regIXY = (regIXY & 0x00ff) | (regD << 8);
                break;
            }
            case 0x63: {     /* LD IXh,E */
                regIXY = (regIXY & 0x00ff) | (regE << 8);
                break;
            }
            case 0x64: {     /* LD IXh,IXh */
                break;
            }
            case 0x65: {     /* LD IXh,IXl */
                regIXY = (regIXY & 0x00ff) | ((regIXY & 0xff) << 8);
                break;
            }
            case 0x66: {     /* LD H,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regH = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x67: {     /* LD IXh,A */
                regIXY = (regIXY & 0x00ff) | (regA << 8);
                break;
            }
            case 0x68: {     /* LD IXl,B */
                regIXY = (regIXY & 0xff00) | regB;
                break;
            }
            case 0x69: {     /* LD IXl,C */
                regIXY = (regIXY & 0xff00) | regC;
                break;
            }
            case 0x6A: {     /* LD IXl,D */
                regIXY = (regIXY & 0xff00) | regD;
                break;
            }
            case 0x6B: {     /* LD IXl,E */
                regIXY = (regIXY & 0xff00) | regE;
                break;
            }
            case 0x6C: {     /* LD IXl,IXh */
                regIXY = (regIXY & 0xff00) | (regIXY >>> 8);
                break;
            }
            case 0x6D: {     /* LD IXl,IXl */
                break;
            }
            case 0x6E: {     /* LD L,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regL = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x6F: {     /* LD IXl,A */
                regIXY = (regIXY & 0xff00) | regA;
                break;
            }
            case 0x70: {     /* LD (IX+d),B */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regB);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x71: {     /* LD (IX+d),C */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regC);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x72: {     /* LD (IX+d),D */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regD);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x73: {     /* LD (IX+d),E */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regE);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x74: {     /* LD (IX+d),H */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regH);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x75: {     /* LD (IX+d),L */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regL);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x77: {     /* LD (IX+d),A */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                MemIoImpl.poke8(memptr, regA);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x7C: {     /* LD A,IXh */
                regA = regIXY >>> 8;
                break;
            }
            case 0x7D: {     /* LD A,IXl */
                regA = regIXY & 0xff;
                break;
            }
            case 0x7E: {     /* LD A,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                regA = MemIoImpl.peek8(memptr);
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x84: {     /* ADD A,IXh */
                add(regIXY >>> 8);
                break;
            }
            case 0x85: {     /* ADD A,IXl */
                add(regIXY & 0xff);
                break;
            }
            case 0x86: {     /* ADD A,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                add(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x8C: {     /* ADC A,IXh */
                adc(regIXY >>> 8);
                break;
            }
            case 0x8D: {     /* ADC A,IXl */
                adc(regIXY & 0xff);
                break;
            }
            case 0x8E: {     /* ADC A,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                adc(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x94: {     /* SUB IXh */
                sub(regIXY >>> 8);
                break;
            }
            case 0x95: {     /* SUB IXl */
                sub(regIXY & 0xff);
                break;
            }
            case 0x96: {     /* SUB (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                sub(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0x9C: {     /* SBC A,IXh */
                sbc(regIXY >>> 8);
                break;
            }
            case 0x9D: {     /* SBC A,IXl */
                sbc(regIXY & 0xff);
                break;
            }
            case 0x9E: {     /* SBC A,(IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                sbc(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xA4: {     /* AND IXh */
                and(regIXY >>> 8);
                break;
            }
            case 0xA5: {     /* AND IXl */
                and(regIXY & 0xff);
                break;
            }
            case 0xA6: {     /* AND (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                and(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xAC: {     /* XOR IXh */
                xor(regIXY >>> 8);
                break;
            }
            case 0xAD: {     /* XOR IXl */
                xor(regIXY & 0xff);
                break;
            }
            case 0xAE: {     /* XOR (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                xor(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xB4: {     /* OR IXh */
                or(regIXY >>> 8);
                break;
            }
            case 0xB5: {     /* OR IXl */
                or(regIXY & 0xff);
                break;
            }
            case 0xB6: {     /* OR (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                or(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xBC: {     /* CP IXh */
                cp(regIXY >>> 8);
                break;
            }
            case 0xBD: {     /* CP IXl */
                cp(regIXY & 0xff);
                break;
            }
            case 0xBE: {     /* CP (IX+d) */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                MemIoImpl.addressOnBus(regPC, 5);
                cp(MemIoImpl.peek8(memptr));
                regPC = (regPC + 1) & 0xffff;
                break;
            }
            case 0xCB: {     /* Subconjunto de instrucciones */
                memptr = (regIXY + (byte) MemIoImpl.peek8(regPC)) & 0xffff;
                regPC = (regPC + 1) & 0xffff;
                opCode = MemIoImpl.peek8(regPC);
                MemIoImpl.addressOnBus(regPC, 2);
                regPC = (regPC + 1) & 0xffff;
                decodeDDFDCB(opCode, memptr);
                break;
            }
            case 0xDD: {
                prefixOpcode = 0xDD;
                break;
            }
            case 0xE1: {     /* POP IX */
                regIXY = pop();
                break;
            }
            case 0xE3: {     /* EX (SP),IX */
                // Instrucción de ejecución sutil como pocas... atento al dato.
                int work16 = regIXY;
                regIXY = MemIoImpl.peek16(regSP);
                MemIoImpl.addressOnBus((regSP + 1) & 0xffff, 1);
                MemIoImpl.poke8((regSP + 1) & 0xffff, work16 >>> 8);
                MemIoImpl.poke8(regSP, work16);
                MemIoImpl.addressOnBus(regSP, 2);
                memptr = regIXY;
                break;
            }
            case 0xE5: {     /* PUSH IX */
                MemIoImpl.addressOnBus(getPairIR(), 1);
                push(regIXY);
                break;
            }
            case 0xE9: {     /* JP (IX) */
                regPC = regIXY;
                break;
            }
            case 0xED: {
                prefixOpcode = 0xED;
                break;
            }
            case 0xF9: {     /* LD SP,IX */
                MemIoImpl.addressOnBus(getPairIR(), 2);
                regSP = regIXY;
                break;
            }
            case 0xFD: {
                prefixOpcode = 0xFD;
                break;
            }
            default: {
                // Detrás de un DD/FD o varios en secuencia venía un código
                // que no correspondía con una instrucción que involucra a 
                // IX o IY. Se trata como si fuera un código normal.
                // Sin esto, además de emular mal, falla el test
                // ld <bcdexya>,<bcdexya> de ZEXALL.

//                System.out.println("Error instrucción DD/FD" + Integer.toHexString(opCode));

                //if (breakpointAt.get(regPC)) {
                //    opCode = NotifyImpl.breakpoint(regPC, opCode);
                //}

                decodeOpcode(opCode);
                break;
            }
        }
        return regIXY;
    }

    // Subconjunto de instrucciones 0xDD/0xFD 0xCB
    private void decodeDDFDCB(int opCode, int address) {

        switch (opCode) {
            case 0x00: /* RLC (IX+d),B */
            case 0x01: /* RLC (IX+d),C */
            case 0x02: /* RLC (IX+d),D */
            case 0x03: /* RLC (IX+d),E */
            case 0x04: /* RLC (IX+d),H */
            case 0x05: /* RLC (IX+d),L */
            case 0x06: /* RLC (IX+d)   */
            case 0x07: /* RLC (IX+d),A */
            {
                int work8 = rlc(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x08: /* RRC (IX+d),B */
            case 0x09: /* RRC (IX+d),C */
            case 0x0A: /* RRC (IX+d),D */
            case 0x0B: /* RRC (IX+d),E */
            case 0x0C: /* RRC (IX+d),H */
            case 0x0D: /* RRC (IX+d),L */
            case 0x0E: /* RRC (IX+d)   */
            case 0x0F: /* RRC (IX+d),A */
            {
                int work8 = rrc(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x10: /* RL (IX+d),B */
            case 0x11: /* RL (IX+d),C */
            case 0x12: /* RL (IX+d),D */
            case 0x13: /* RL (IX+d),E */
            case 0x14: /* RL (IX+d),H */
            case 0x15: /* RL (IX+d),L */
            case 0x16: /* RL (IX+d)   */
            case 0x17: /* RL (IX+d),A */
            {
                int work8 = rl(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x18: /* RR (IX+d),B */
            case 0x19: /* RR (IX+d),C */
            case 0x1A: /* RR (IX+d),D */
            case 0x1B: /* RR (IX+d),E */
            case 0x1C: /* RR (IX+d),H */
            case 0x1D: /* RR (IX+d),L */
            case 0x1E: /* RR (IX+d)   */
            case 0x1F: /* RR (IX+d),A */
            {
                int work8 = rr(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x20: /* SLA (IX+d),B */
            case 0x21: /* SLA (IX+d),C */
            case 0x22: /* SLA (IX+d),D */
            case 0x23: /* SLA (IX+d),E */
            case 0x24: /* SLA (IX+d),H */
            case 0x25: /* SLA (IX+d),L */
            case 0x26: /* SLA (IX+d)   */
            case 0x27: /* SLA (IX+d),A */
            {
                int work8 = sla(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x28: /* SRA (IX+d),B */
            case 0x29: /* SRA (IX+d),C */
            case 0x2A: /* SRA (IX+d),D */
            case 0x2B: /* SRA (IX+d),E */
            case 0x2C: /* SRA (IX+d),H */
            case 0x2D: /* SRA (IX+d),L */
            case 0x2E: /* SRA (IX+d)   */
            case 0x2F: /* SRA (IX+d),A */
            {
                int work8 = sra(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x30: /* SLL (IX+d),B */
            case 0x31: /* SLL (IX+d),C */
            case 0x32: /* SLL (IX+d),D */
            case 0x33: /* SLL (IX+d),E */
            case 0x34: /* SLL (IX+d),H */
            case 0x35: /* SLL (IX+d),L */
            case 0x36: /* SLL (IX+d)   */
            case 0x37: /* SLL (IX+d),A */
            {
                int work8 = sll(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x38: /* SRL (IX+d),B */
            case 0x39: /* SRL (IX+d),C */
            case 0x3A: /* SRL (IX+d),D */
            case 0x3B: /* SRL (IX+d),E */
            case 0x3C: /* SRL (IX+d),H */
            case 0x3D: /* SRL (IX+d),L */
            case 0x3E: /* SRL (IX+d)   */
            case 0x3F: /* SRL (IX+d),A */
            {
                int work8 = srl(MemIoImpl.peek8(address));
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x40:
            case 0x41:
            case 0x42:
            case 0x43:
            case 0x44:
            case 0x45:
            case 0x46:
            case 0x47: {     /* BIT 0,(IX+d) */
                bit(0x01, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x48:
            case 0x49:
            case 0x4A:
            case 0x4B:
            case 0x4C:
            case 0x4D:
            case 0x4E:
            case 0x4F: {     /* BIT 1,(IX+d) */
                bit(0x02, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x50:
            case 0x51:
            case 0x52:
            case 0x53:
            case 0x54:
            case 0x55:
            case 0x56:
            case 0x57: {     /* BIT 2,(IX+d) */
                bit(0x04, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x58:
            case 0x59:
            case 0x5A:
            case 0x5B:
            case 0x5C:
            case 0x5D:
            case 0x5E:
            case 0x5F: {     /* BIT 3,(IX+d) */
                bit(0x08, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x60:
            case 0x61:
            case 0x62:
            case 0x63:
            case 0x64:
            case 0x65:
            case 0x66:
            case 0x67: {     /* BIT 4,(IX+d) */
                bit(0x10, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x68:
            case 0x69:
            case 0x6A:
            case 0x6B:
            case 0x6C:
            case 0x6D:
            case 0x6E:
            case 0x6F: {     /* BIT 5,(IX+d) */
                bit(0x20, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x70:
            case 0x71:
            case 0x72:
            case 0x73:
            case 0x74:
            case 0x75:
            case 0x76:
            case 0x77: {     /* BIT 6,(IX+d) */
                bit(0x40, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x78:
            case 0x79:
            case 0x7A:
            case 0x7B:
            case 0x7C:
            case 0x7D:
            case 0x7E:
            case 0x7F: {     /* BIT 7,(IX+d) */
                bit(0x80, MemIoImpl.peek8(address));
                sz5h3pnFlags = (sz5h3pnFlags & FLAG_SZHP_MASK)
                    | ((address >>> 8) & FLAG_53_MASK);
                MemIoImpl.addressOnBus(address, 1);
                break;
            }
            case 0x80: /* RES 0,(IX+d),B */
            case 0x81: /* RES 0,(IX+d),C */
            case 0x82: /* RES 0,(IX+d),D */
            case 0x83: /* RES 0,(IX+d),E */
            case 0x84: /* RES 0,(IX+d),H */
            case 0x85: /* RES 0,(IX+d),L */
            case 0x86: /* RES 0,(IX+d)   */
            case 0x87: /* RES 0,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xFE;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x88: /* RES 1,(IX+d),B */
            case 0x89: /* RES 1,(IX+d),C */
            case 0x8A: /* RES 1,(IX+d),D */
            case 0x8B: /* RES 1,(IX+d),E */
            case 0x8C: /* RES 1,(IX+d),H */
            case 0x8D: /* RES 1,(IX+d),L */
            case 0x8E: /* RES 1,(IX+d)   */
            case 0x8F: /* RES 1,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xFD;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x90: /* RES 2,(IX+d),B */
            case 0x91: /* RES 2,(IX+d),C */
            case 0x92: /* RES 2,(IX+d),D */
            case 0x93: /* RES 2,(IX+d),E */
            case 0x94: /* RES 2,(IX+d),H */
            case 0x95: /* RES 2,(IX+d),L */
            case 0x96: /* RES 2,(IX+d)   */
            case 0x97: /* RES 2,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xFB;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0x98: /* RES 3,(IX+d),B */
            case 0x99: /* RES 3,(IX+d),C */
            case 0x9A: /* RES 3,(IX+d),D */
            case 0x9B: /* RES 3,(IX+d),E */
            case 0x9C: /* RES 3,(IX+d),H */
            case 0x9D: /* RES 3,(IX+d),L */
            case 0x9E: /* RES 3,(IX+d)   */
            case 0x9F: /* RES 3,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xF7;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xA0: /* RES 4,(IX+d),B */
            case 0xA1: /* RES 4,(IX+d),C */
            case 0xA2: /* RES 4,(IX+d),D */
            case 0xA3: /* RES 4,(IX+d),E */
            case 0xA4: /* RES 4,(IX+d),H */
            case 0xA5: /* RES 4,(IX+d),L */
            case 0xA6: /* RES 4,(IX+d)   */
            case 0xA7: /* RES 4,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xEF;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xA8: /* RES 5,(IX+d),B */
            case 0xA9: /* RES 5,(IX+d),C */
            case 0xAA: /* RES 5,(IX+d),D */
            case 0xAB: /* RES 5,(IX+d),E */
            case 0xAC: /* RES 5,(IX+d),H */
            case 0xAD: /* RES 5,(IX+d),L */
            case 0xAE: /* RES 5,(IX+d)   */
            case 0xAF: /* RES 5,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xDF;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xB0: /* RES 6,(IX+d),B */
            case 0xB1: /* RES 6,(IX+d),C */
            case 0xB2: /* RES 6,(IX+d),D */
            case 0xB3: /* RES 6,(IX+d),E */
            case 0xB4: /* RES 6,(IX+d),H */
            case 0xB5: /* RES 6,(IX+d),L */
            case 0xB6: /* RES 6,(IX+d)   */
            case 0xB7: /* RES 6,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0xBF;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xB8: /* RES 7,(IX+d),B */
            case 0xB9: /* RES 7,(IX+d),C */
            case 0xBA: /* RES 7,(IX+d),D */
            case 0xBB: /* RES 7,(IX+d),E */
            case 0xBC: /* RES 7,(IX+d),H */
            case 0xBD: /* RES 7,(IX+d),L */
            case 0xBE: /* RES 7,(IX+d)   */
            case 0xBF: /* RES 7,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) & 0x7F;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xC0: /* SET 0,(IX+d),B */
            case 0xC1: /* SET 0,(IX+d),C */
            case 0xC2: /* SET 0,(IX+d),D */
            case 0xC3: /* SET 0,(IX+d),E */
            case 0xC4: /* SET 0,(IX+d),H */
            case 0xC5: /* SET 0,(IX+d),L */
            case 0xC6: /* SET 0,(IX+d)   */
            case 0xC7: /* SET 0,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x01;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xC8: /* SET 1,(IX+d),B */
            case 0xC9: /* SET 1,(IX+d),C */
            case 0xCA: /* SET 1,(IX+d),D */
            case 0xCB: /* SET 1,(IX+d),E */
            case 0xCC: /* SET 1,(IX+d),H */
            case 0xCD: /* SET 1,(IX+d),L */
            case 0xCE: /* SET 1,(IX+d)   */
            case 0xCF: /* SET 1,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x02;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xD0: /* SET 2,(IX+d),B */
            case 0xD1: /* SET 2,(IX+d),C */
            case 0xD2: /* SET 2,(IX+d),D */
            case 0xD3: /* SET 2,(IX+d),E */
            case 0xD4: /* SET 2,(IX+d),H */
            case 0xD5: /* SET 2,(IX+d),L */
            case 0xD6: /* SET 2,(IX+d)   */
            case 0xD7: /* SET 2,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x04;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xD8: /* SET 3,(IX+d),B */
            case 0xD9: /* SET 3,(IX+d),C */
            case 0xDA: /* SET 3,(IX+d),D */
            case 0xDB: /* SET 3,(IX+d),E */
            case 0xDC: /* SET 3,(IX+d),H */
            case 0xDD: /* SET 3,(IX+d),L */
            case 0xDE: /* SET 3,(IX+d)   */
            case 0xDF: /* SET 3,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x08;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xE0: /* SET 4,(IX+d),B */
            case 0xE1: /* SET 4,(IX+d),C */
            case 0xE2: /* SET 4,(IX+d),D */
            case 0xE3: /* SET 4,(IX+d),E */
            case 0xE4: /* SET 4,(IX+d),H */
            case 0xE5: /* SET 4,(IX+d),L */
            case 0xE6: /* SET 4,(IX+d)   */
            case 0xE7: /* SET 4,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x10;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xE8: /* SET 5,(IX+d),B */
            case 0xE9: /* SET 5,(IX+d),C */
            case 0xEA: /* SET 5,(IX+d),D */
            case 0xEB: /* SET 5,(IX+d),E */
            case 0xEC: /* SET 5,(IX+d),H */
            case 0xED: /* SET 5,(IX+d),L */
            case 0xEE: /* SET 5,(IX+d)   */
            case 0xEF: /* SET 5,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x20;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xF0: /* SET 6,(IX+d),B */
            case 0xF1: /* SET 6,(IX+d),C */
            case 0xF2: /* SET 6,(IX+d),D */
            case 0xF3: /* SET 6,(IX+d),E */
            case 0xF4: /* SET 6,(IX+d),H */
            case 0xF5: /* SET 6,(IX+d),L */
            case 0xF6: /* SET 6,(IX+d)   */
            case 0xF7: /* SET 6,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x40;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
            case 0xF8: /* SET 7,(IX+d),B */
            case 0xF9: /* SET 7,(IX+d),C */
            case 0xFA: /* SET 7,(IX+d),D */
            case 0xFB: /* SET 7,(IX+d),E */
            case 0xFC: /* SET 7,(IX+d),H */
            case 0xFD: /* SET 7,(IX+d),L */
            case 0xFE: /* SET 7,(IX+d)   */
            case 0xFF: /* SET 7,(IX+d),A */
            {
                int work8 = MemIoImpl.peek8(address) | 0x80;
                MemIoImpl.addressOnBus(address, 1);
                MemIoImpl.poke8(address, work8);
                copyToRegister(opCode, work8);
                break;
            }
        }
    }

    // Subconjunto de instrucciones 0xED
    private void decodeED(int opCode) {
        switch (opCode) {
            case 0x40: {     /* IN B,(C) */
                step(2, "IN B,(C)");

                memptr = getRegBC();
                regB = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regB];
                flagQ = true;
                break;
            }
            case 0x41: {     /* OUT (C),B */
                step(2, "OUT (C),B");

                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regB);
                break;
            }
            case 0x42: {     /* SBC HL,BC */
                step(2, "SBC HL,BC");

                MemIoImpl.addressOnBus(getPairIR(), 7);
                sbc16(getRegBC());
                break;
            }
            case 0x43: {     /* LD (nn),BC */
                step(4, "LD (nn),BC");

                memptr = MemIoImpl.peek16(regPC);
                MemIoImpl.poke16(memptr++, getRegBC());
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x44:
            case 0x4C:
            case 0x54:
            case 0x5C:
            case 0x64:
            case 0x6C:
            case 0x74:
            case 0x7C: {     /* NEG */
                step(2, "NEG");

                int aux = regA;
                regA = 0;
                sub(aux);
                break;
            }
            case 0x45:
            case 0x4D:       /* RETI */
            case 0x55:
            case 0x5D:
            case 0x65:
            case 0x6D:
            case 0x75:
            case 0x7D: {     /* RETN */
                step(2, "RETN");

                ffIFF1 = ffIFF2;
                regPC = memptr = pop();
                break;
            }
            case 0x46:
            case 0x4E:
            case 0x66:
            case 0x6E: {     /* IM 0 */
                step(2, "IM 0");

                setIM(IntMode.IM0);
                break;
            }
            case 0x47: {     /* LD I,A */
                step(2, "LD I,A");

                /*
                 * El contended-tstate se produce con el contenido de I *antes*
                 * de ser copiado el del registro A. Detalle importante.
                 */
                MemIoImpl.addressOnBus(getPairIR(), 1);
                regI = regA;
                break;
            }
            case 0x48: {     /* IN C,(C) */
                step(2, "IN C,(C)");

                memptr = getRegBC();
                regC = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regC];
                flagQ = true;
                break;
            }
            case 0x49: {     /* OUT (C),C */
                step(2, "OUT (C),C");

                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regC);
                break;
            }
            case 0x4A: {     /* ADC HL,BC */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                adc16(getRegBC());
                break;
            }
            case 0x4B: {     /* LD BC,(nn) */
                memptr = MemIoImpl.peek16(regPC);
                setRegBC(MemIoImpl.peek16(memptr++));
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x4F: {     /* LD R,A */
                MemIoImpl.addressOnBus(getPairIR(), 1);
                setRegR(regA);
                break;
            }
            case 0x50: {     /* IN D,(C) */
                memptr = getRegBC();
                regD = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regD];
                flagQ = true;
                break;
            }
            case 0x51: {     /* OUT (C),D */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regD);
                break;
            }
            case 0x52: {     /* SBC HL,DE */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                sbc16(getRegDE());
                break;
            }
            case 0x53: {     /* LD (nn),DE */
                memptr = MemIoImpl.peek16(regPC);
                MemIoImpl.poke16(memptr++, getRegDE());
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x56:
            case 0x76: {     /* IM 1 */
                setIM(IntMode.IM1);
                break;
            }
            case 0x57: {     /* LD A,I */
                MemIoImpl.addressOnBus(getPairIR(), 1);
                regA = regI;
                sz5h3pnFlags = sz53n_addTable[regA];
                if (ffIFF2 && !MemIoImpl.isActiveINT()) {
                    sz5h3pnFlags |= PARITY_MASK;
                }
                flagQ = true;
                break;
            }
            case 0x58: {     /* IN E,(C) */
                memptr = getRegBC();
                regE = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regE];
                flagQ = true;
                break;
            }
            case 0x59: {     /* OUT (C),E */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regE);
                break;
            }
            case 0x5A: {     /* ADC HL,DE */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                adc16(getRegDE());
                break;
            }
            case 0x5B: {     /* LD DE,(nn) */
                memptr = MemIoImpl.peek16(regPC);
                setRegDE(MemIoImpl.peek16(memptr++));
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x5E:
            case 0x7E: {     /* IM 2 */
                setIM(IntMode.IM2);
                break;
            }
            case 0x5F: {     /* LD A,R */
                MemIoImpl.addressOnBus(getPairIR(), 1);
                regA = getRegR();
                sz5h3pnFlags = sz53n_addTable[regA];
                if (ffIFF2 && !MemIoImpl.isActiveINT()) {
                    sz5h3pnFlags |= PARITY_MASK;
                }
                flagQ = true;
                break;
            }
            case 0x60: {     /* IN H,(C) */
                memptr = getRegBC();
                regH = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regH];
                flagQ = true;
                break;
            }
            case 0x61: {     /* OUT (C),H */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regH);
                break;
            }
            case 0x62: {     /* SBC HL,HL */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                sbc16(getRegHL());
                break;
            }
            case 0x63: {     /* LD (nn),HL */
                memptr = MemIoImpl.peek16(regPC);
                MemIoImpl.poke16(memptr++, getRegHL());
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x67: {     /* RRD */
                rrd();
                break;
            }
            case 0x68: {     /* IN L,(C) */
                memptr = getRegBC();
                regL = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regL];
                flagQ = true;
                break;
            }
            case 0x69: {     /* OUT (C),L */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regL);
                break;
            }
            case 0x6A: {     /* ADC HL,HL */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                adc16(getRegHL());
                break;
            }
            case 0x6B: {     /* LD HL,(nn) */
                memptr = MemIoImpl.peek16(regPC);
                setRegHL(MemIoImpl.peek16(memptr++));
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x6F: {     /* RLD */
                rld();
                break;
            }
            case 0x70: {     /* IN (C) */
                memptr = getRegBC();
                int inPort = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[inPort];
                flagQ = true;
                break;
            }
            case 0x71: {     /* OUT (C),0 */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, 0x00);
                break;
            }
            case 0x72: {     /* SBC HL,SP */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                sbc16(regSP);
                break;
            }
            case 0x73: {     /* LD (nn),SP */
                memptr = MemIoImpl.peek16(regPC);
                MemIoImpl.poke16(memptr++, regSP);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0x78: {     /* IN A,(C) */
                memptr = getRegBC();
                regA = MemIoImpl.inPort(memptr++);
                sz5h3pnFlags = sz53pn_addTable[regA];
                flagQ = true;
                break;
            }
            case 0x79: {     /* OUT (C),A */
                memptr = getRegBC();
                MemIoImpl.outPort(memptr++, regA);
                break;
            }
            case 0x7A: {     /* ADC HL,SP */
                MemIoImpl.addressOnBus(getPairIR(), 7);
                adc16(regSP);
                break;
            }
            case 0x7B: {     /* LD SP,(nn) */
                memptr = MemIoImpl.peek16(regPC);
                regSP = MemIoImpl.peek16(memptr++);
                regPC = (regPC + 2) & 0xffff;
                break;
            }
            case 0xA0: {     /* LDI */
                ldi();
                break;
            }
            case 0xA1: {     /* CPI */
                cpi();
                break;
            }
            case 0xA2: {     /* INI */
                ini();
                break;
            }
            case 0xA3: {     /* OUTI */
                outi();
                break;
            }
            case 0xA8: {     /* LDD */
                ldd();
                break;
            }
            case 0xA9: {     /* CPD */
                cpd();
                break;
            }
            case 0xAA: {     /* IND */
                ind();
                break;
            }
            case 0xAB: {     /* OUTD */
                outd();
                break;
            }
            case 0xB0: {     /* LDIR */
                ldi();
                if ((sz5h3pnFlags & PARITY_MASK) == PARITY_MASK) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegDE() - 1) & 0xffff, 5);
                    sz5h3pnFlags &= ~FLAG_53_MASK;
                    sz5h3pnFlags |= ((regPC >>> 8) & FLAG_53_MASK);
                }
                break;
            }
            case 0xB1: {     /* CPIR */
                cpi();
                if ((sz5h3pnFlags & PARITY_MASK) == PARITY_MASK
                    && (sz5h3pnFlags & ZERO_MASK) == 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegHL() - 1) & 0xffff, 5);
                    sz5h3pnFlags &= ~FLAG_53_MASK;
                    sz5h3pnFlags |= ((regPC >>> 8) & FLAG_53_MASK);
                }
                break;
            }
            case 0xB2: {     /* INIR */
                ini();
                if (regB != 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegHL() - 1) & 0xffff, 5);
                    adjustINxROUTxRFlags();
                }
                break;
            }
            case 0xB3: {     /* OTIR */
                outi();
                if (regB != 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus(getRegBC(), 5);
                    adjustINxROUTxRFlags();
                }
                break;
            }
            case 0xB8: {     /* LDDR */
                ldd();
                if ((sz5h3pnFlags & PARITY_MASK) == PARITY_MASK) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegDE() + 1) & 0xffff, 5);
                    sz5h3pnFlags &= ~FLAG_53_MASK;
                    sz5h3pnFlags |= ((regPC >>> 8) & FLAG_53_MASK);
                }
                break;
            }
            case 0xB9: {     /* CPDR */
                cpd();
                if ((sz5h3pnFlags & PARITY_MASK) == PARITY_MASK
                    && (sz5h3pnFlags & ZERO_MASK) == 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegHL() + 1) & 0xffff, 5);
                    sz5h3pnFlags &= ~FLAG_53_MASK;
                    sz5h3pnFlags |= ((regPC >>> 8) & FLAG_53_MASK);
                }
                break;
            }
            case 0xBA: {     /* INDR */
                ind();
                if (regB != 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus((getRegHL() + 1) & 0xffff, 5);
                    adjustINxROUTxRFlags();
                }
                break;
            }
            case 0xBB: {     /* OTDR */
                outd();
                if (regB != 0) {
                    regPC = (regPC - 2) & 0xffff;
                    memptr = regPC + 1;
                    MemIoImpl.addressOnBus(getRegBC(), 5);
                    adjustINxROUTxRFlags();
                }
                break;
            }
            case 0xDD:
                prefixOpcode = 0xDD;
                break;
            case 0xED:
                prefixOpcode = 0xED;
                break;
            case 0xFD:
                prefixOpcode = 0xFD;
                break;
            default: {
//                System.out.println("Error instrucción ED " + Integer.toHexString(opCode));
                break;
            }
        }
    }

    private void copyToRegister(int opCode, int value)
    {
        switch(opCode & 0x07)
        {
            case 0x00:
                regB = value;
                break;
            case 0x01:
                regC = value;
                break;
            case 0x02:
                regD = value;
                break;
            case 0x03:
                regE = value;
                break;
            case 0x04:
                regH = value;
                break;
            case 0x05:
                regL = value;
                break;
            case 0x07:
                regA = value;
            default:
                break;
        }
    }

    private void adjustINxROUTxRFlags()
    {
        sz5h3pnFlags &= ~FLAG_53_MASK;
        sz5h3pnFlags |= (regPC >>> 8) & FLAG_53_MASK;

        int pf = sz5h3pnFlags & PARITY_MASK;
        if (carryFlag) {
            int addsub = 1 - (sz5h3pnFlags & ADDSUB_MASK);
            pf ^= sz53pn_addTable[(regB + addsub) & 0x07] ^ PARITY_MASK;
            if ((regB & 0x0F) == (addsub != 1 ? 0x00 : 0x0F))
                sz5h3pnFlags |= HALFCARRY_MASK;
            else
                sz5h3pnFlags &= ~HALFCARRY_MASK;
        } else {
            pf ^= sz53pn_addTable[regB & 0x07] ^ PARITY_MASK;
            sz5h3pnFlags &= ~HALFCARRY_MASK;
        }

        if ((pf & PARITY_MASK) == PARITY_MASK)
            sz5h3pnFlags |= PARITY_MASK;
        else
            sz5h3pnFlags &= ~PARITY_MASK;
    }
}
