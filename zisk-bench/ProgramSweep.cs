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

    static int Main()
    {
        byte* pointer = null;
        nuint size = 0;
        read_input(&pointer, &size);
        ReadOnlySpan<byte> input = new(pointer, (int)size);
        UInt256.ExpBenchCutoff = BinaryPrimitives.ReadInt32LittleEndian(input);
        UInt256.ExpBenchShortCutoff = BinaryPrimitives.ReadInt32LittleEndian(input.Slice(4));
        UInt256.ExpBenchWidth = BinaryPrimitives.ReadInt32LittleEndian(input.Slice(8));
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
        return 0;
    }

    [UnmanagedCallersOnly(EntryPoint = "ZkvmThrow")]
    static void HandleException(void* exception) => Environment.Exit(1);
}
