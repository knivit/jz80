package com.tsoft.jz80.core;

public interface NotifyOps {

    int beforeStep(int address, int opcode);
    void execDone();
}
