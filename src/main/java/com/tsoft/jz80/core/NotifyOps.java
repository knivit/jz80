package com.tsoft.jz80.core;

public interface NotifyOps {

    int breakpoint(int address, int opcode);
    void execDone();
}
