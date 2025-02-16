package com.tsoft.jz80.utils;

public final class HexUtils {

    private static final char[] HEX_CHARS = new char[] { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F' };

    public static String hex8(int data) {
        char[] value = new char[3];
        value[0] = HEX_CHARS[(data >> 4) & 0x0f];
        value[1] = HEX_CHARS[data & 0x0f];
        value[2] = 'H';
        return new String(value);
    }

    public static String off8(int data) {
        int n = 0;
        char[] value;
        if (data > 127) {
            value = new char[4];
            value[0] = '-';
            data = data - 128;
            n = 1;
        } else {
            value = new char[3];
        }
        value[n] = HEX_CHARS[(data >> 4) & 0x0f];
        value[n + 1] = HEX_CHARS[data & 0x0f];
        value[n + 2] = 'H';
        return new String(value);
    }

    public static String hex16(int data) {
        char[] value = new char[5];
        value[0] = HEX_CHARS[(data >> 12) & 0x0f];
        value[1] = HEX_CHARS[(data >> 8) & 0x0f];
        value[2] = HEX_CHARS[(data >> 4) & 0x0f];
        value[3] = HEX_CHARS[data & 0x0f];
        value[4] = 'H';
        return new String(value);
    }

    public static String reg8(int data) {
        char[] value = new char[2];
        value[0] = HEX_CHARS[(data >> 4) & 0x0f];
        value[1] = HEX_CHARS[data & 0x0f];
        return new String(value);
    }

    public static String reg16(int data) {
        char[] value = new char[4];
        value[0] = HEX_CHARS[(data >> 12) & 0x0f];
        value[1] = HEX_CHARS[(data >> 8) & 0x0f];
        value[2] = HEX_CHARS[(data >> 4) & 0x0f];
        value[3] = HEX_CHARS[data & 0x0f];
        return new String(value);
    }

    public static void dump(byte[] ram, int start, int len) {
        int address = start & 0xfff0;
        len += start - address;

        System.out.println("     .0 .1 .2 .3 .4 .5 .6 .7 .8 .9 .A .B .C .D .E .F");
        while (len > 0) {
          System.out.print(reg16(address));
          for (int i = 0; i < 16; i ++) {
              String val = (address < start || len < 0) ? "  " : reg8(ram[address]);
              System.out.print(" " + val);
              address = (address + 1) & 0xffff;
              len--;
          }
          System.out.println();
        }
    }

    private HexUtils() { }
}
