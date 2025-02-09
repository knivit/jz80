package com.tsoft.jz80.core;

import lombok.extern.slf4j.Slf4j;

import static com.tsoft.jz80.utils.HexUtils.hexW;

@Slf4j
public class Jz80Core implements NotifyOps {

    private final Z80 z80;
    private final MemIoOps memIo;
    private final byte[] z80Ram = new byte[0x10000];
    private volatile boolean finish;
    private StringBuffer buffer;

    public Jz80Core() {
        finish = false;
        buffer = new StringBuffer();
        memIo = new MemIoOps(0, 0);
        memIo.setRam(z80Ram);
        z80 = new Z80(memIo, this);
    }

    // Loads the dato into the Z80 memory
    public void load(int address, byte[] data) {
        if (data != null) {
            for (int i = 0; i < data.length; i ++) {
                z80Ram[address + i] = data[i];
            }
            log.debug("0x{} byte(s) loaded into [0x{}..0x{}]", hexW(data.length), hexW(address), hexW(address + data.length - 1));
        }
    }

    // Starts Z80 at the given address
    public void run(int start, int stop) {
        z80.reset();
        memIo.reset();

        if (stop != -1) {
            z80.setBreakpoint(stop, true);
        }

        z80.setRegPC(start);

        finish = false;
        while (!finish) {
            z80.execute();
        }
    }

    @Override
    public int breakpoint(int address, int opcode) {
        // Emulate CP/M Syscall at address 5
        switch (z80.getRegC()) {
            case 0 -> {
                // BDOS 0 System Reset
                log.info("Z80 reset after {} t-states", memIo.getTstates());
                finish = true;
            }
            case 2 -> log.info("{}", (char) z80.getRegE()); // BDOS 2 console char output
            case 9 -> {
                // BDOS 9 console string output (string terminated by "$")
                int strAddr = z80.getRegDE();
                while (z80Ram[strAddr] != '$') {
                    if (z80Ram[strAddr] == 0x0A) {
                        // Ignore line feed
                        strAddr++;
                    } else if (z80Ram[strAddr] == 0x0D) {
                        // Display the message and reset the buffer when a carriage return is detected
                        // TODO: capture the test outcome and fail the test if any of the outcomes was a failure.
                        log.info("{}", buffer);
                        buffer = new StringBuffer();
                        strAddr++;
                    } else {
                        // Append characters to the message
                        buffer.append((char) z80Ram[strAddr++]);
                    }
                }
            }
            default -> {
                log.info("BDOS Call {}", z80.getRegC());
                finish = true;
            }
        }
        return opcode;
    }

    @Override
    public void execDone() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }

}
