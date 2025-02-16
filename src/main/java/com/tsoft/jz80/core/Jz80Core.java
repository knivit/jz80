package com.tsoft.jz80.core;

import lombok.Getter;
import lombok.extern.slf4j.Slf4j;

import java.nio.file.Files;
import java.nio.file.Path;

import static com.tsoft.jz80.utils.HexUtils.hex16;

@Slf4j
public class Jz80Core implements NotifyOps {

    @Getter
    private final Z80 z80;

    @Getter
    private final MemIoOps memIo;

    //@Getter
    //private final byte[] z80Ram = new byte[0x10000];

    private int stepCount;
    private volatile boolean finish;
    private StringBuffer buffer;

    public Jz80Core() {
        finish = false;
        buffer = new StringBuffer();
        memIo = new MemIoOps(0x10000, 0x10000);
        //memIo.setRam(z80Ram);
        z80 = new Z80(memIo, this);
    }

    public byte[] getRam() {
        return memIo.getRam();
    }

    // Loads the data into the Z80 memory
    public void load(int address, byte[] data) {
        if (data != null) {
            address &= 0xffff;
            int start = address;
            for (int i = 0; i < data.length; i ++) {
                memIo.getRam()[address ++] = data[i];
                address = address & 0xffff;
            }
            log.debug("0x{} byte(s) loaded into [0x{}..0x{}]", hex16(data.length), hex16(start), hex16(address - 1));
        }
    }

    public void load(int address, Path file) {
        try {
            byte[] data = Files.readAllBytes(file);
            load(address, data);
        } catch (Exception ex) {
            throw new IllegalStateException(ex);
        }
    }

    // Starts Z80 at the given address
    public void run(int start, int stepCount) {
        z80.reset();
        memIo.reset();

        z80.setRegPC(start);

        finish = false;
        this.stepCount = stepCount;
        while (!finish) {
            z80.execute();
        }
    }

    @Override
    public int beforeStep(int address, int opcode) {
        finish = (stepCount <= 0);
        stepCount --;

/*
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
                while (memIo.getRam()[strAddr] != '$') {
                    if (memIo.getRam()[strAddr] == 0x0A) {
                        // Ignore line feed
                        strAddr++;
                    } else if (memIo.getRam()[strAddr] == 0x0D) {
                        // Display the message and reset the buffer when a carriage return is detected
                        // TODO: capture the test outcome and fail the test if any of the outcomes was a failure.
                        log.info("{}", buffer);
                        buffer = new StringBuffer();
                        strAddr++;
                    } else {
                        // Append characters to the message
                        buffer.append((char) memIo.getRam()[strAddr++]);
                    }
                }
            }
            default -> {
                log.info("BDOS Call {}", z80.getRegC());
                finish = true;
            }
        }*/
        return opcode;
    }

    @Override
    public void execDone() {
        throw new UnsupportedOperationException("Not implemented yet!");
    }
}
