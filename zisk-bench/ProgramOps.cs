// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using Nethermind.Int256;

namespace ZiskExpBench;

static unsafe class Program
{
    [DllImport("__Internal")]
    private static extern void read_input(byte** buffer, nuint* size);

    [DllImport("__Internal")]
    private static extern void write_output(byte* output, nuint size);

    [DllImport("__Internal")]
    private static extern void sys_write(uint fd, byte* buffer, nuint size);

    static int Main()
    {
        byte* pointer = null;
        nuint size = 0;
        read_input(&pointer, &size);
        ReadOnlySpan<byte> input = new(pointer, (int)size);
        int op = BinaryPrimitives.ReadInt32LittleEndian(input);
        int reps = BinaryPrimitives.ReadInt32LittleEndian(input.Slice(4));
        UInt256 a = new(input.Slice(8, 32));
        UInt256 b = new(input.Slice(40, 32));
        UInt256 m = new(input.Slice(72, 32));
        UInt256 acc = default;
        for (int i = 0; i < reps; i++)
        {
            UInt256 r = Run(op, a, b, m);
            UInt256.AddOverflow(acc, r, out acc);
        }
        byte* output = stackalloc byte[32];
        acc.ToLittleEndian(new Span<byte>(output, 32));
        write_output(output, 32);
        byte* text = stackalloc byte[65];
        for (int i = 0; i < 32; i++)
        {
            text[2 * i] = (byte)"0123456789abcdef"[output[i] >> 4];
            text[2 * i + 1] = (byte)"0123456789abcdef"[output[i] & 15];
        }
        text[64] = (byte)'\n';
        sys_write(1, text, 65);
        return 0;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 Run(int op, in UInt256 a, in UInt256 b, in UInt256 m)
    {
        UInt256 r;
        switch (op)
        {
            case 1:
                UInt256.Multiply(a, b, out r);
                return r;
            case 2:
                UInt256.Divide(a, b, out r);
                return r;
            case 3:
                UInt256.Mod(a, b, out r);
                return r;
            case 4:
            {
                Int256 x = new(a);
                Int256 y = new(b);
                Int256.Mod(x, y, out Int256 s);
                return Unsafe.As<Int256, UInt256>(ref s);
            }
            case 5:
            {
                Int256 x = new(a);
                Int256 y = new(b);
                Int256.Divide(x, y, out Int256 s);
                return Unsafe.As<Int256, UInt256>(ref s);
            }
            case 6:
                UInt256.MultiplyMod(a, b, m, out r);
                return r;
            case 7:
                UInt256.AddMod(a, b, m, out r);
                return r;
            case 8:
                UInt256.Exp(a, b, out r);
                return r;
            default:
                return default;
        }
    }

    [UnmanagedCallersOnly(EntryPoint = "ZkvmThrow")]
    static void HandleException(void* exception) => Environment.Exit(1);
}
