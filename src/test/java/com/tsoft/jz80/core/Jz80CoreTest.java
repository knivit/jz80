package com.tsoft.jz80.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Jz80CoreTest {

    @Test
    void test() {
        Jz80Core z80 = new Jz80Core();
        z80.load(0, new byte[] { 0x0e, 0x1f, 0x21, 0x00, 0x00 });
        z80.run(0, 5);
    }

}