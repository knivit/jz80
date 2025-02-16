package com.tsoft.jz80.core;

import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static com.tsoft.jz80.utils.HexUtils.dump;

class Jz80CoreTest {

    @Test
    void test() {
        Jz80Core z80 = new Jz80Core();
        z80.load(0, new byte[] { 0x0e, 0x1f, 0x21, 0x00, 0x00 });
        z80.run(0, 2);
    }

    @Test
    void bruce_lee() {
        Jz80Core z80 = new Jz80Core();
        z80.load(-0x100, Path.of("D:/cygwin/home/tower/git/knivit/jz80/master/target/test-classes/brucelee.sna"));
        dump(z80.getRam(), 0xB98A, 256);
        z80.run(0xB98A, 100);
    }
}