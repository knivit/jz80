package com.tsoft.jz80.utils;

public final class HexUtils {

    private static final char[] HEX_CHARS = new char[] { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F' };

    public static String hexB(int data) {
        char[] value = new char[2];
        value[0] = HEX_CHARS[(data >> 4) & 0x0f];
        value[1] = HEX_CHARS[data & 0x0f];
        return new String(value);
    }

    public static String hexW(int data) {
        char[] value = new char[4];
        value[0] = HEX_CHARS[(data >> 12) & 0x0f];
        value[1] = HEX_CHARS[(data >> 8) & 0x0f];
        value[2] = HEX_CHARS[(data >> 4) & 0x0f];
        value[3] = HEX_CHARS[data & 0x0f];
        return new String(value);
    }

    private HexUtils() { }
}
