// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
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
        int reps = BinaryPrimitives.ReadInt32LittleEndian(input.Slice(12));
        UInt256 b = new(input.Slice(16, 32));
        UInt256 e = new(input.Slice(48, 32));
        UInt256 acc = default;
        for (int i = 0; i < reps; i++)
        {
            UInt256.Exp(b, e, out UInt256 r);
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

    [UnmanagedCallersOnly(EntryPoint = "ZkvmThrow")]
    static void HandleException(void* exception) => Environment.Exit(1);
}
