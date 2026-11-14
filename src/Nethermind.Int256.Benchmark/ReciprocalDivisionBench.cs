// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// DIV, MOD and MULMOD shapes that take one 128-by-64 quotient digit per step. ARM64 and the RISC-V zkVM compute
/// each digit with a reciprocal (<c>UDivRem2By1</c>); x64 uses the hardware divide.
/// </summary>
[MemoryDiagnoser]
public class ReciprocalDivisionBench
{
    private const int Count = 1024;

    private static readonly UInt256 Wad = 1_000_000_000_000_000_000UL;

    private readonly UInt256[] _x = new UInt256[Count];
    private readonly UInt256[] _y = new UInt256[Count];
    private readonly UInt256[] _m = new UInt256[Count];

    [Params("WadScaled", "WadWide", "Small", "Full256By64", "ShortBy128", "MulDivBy128", "Full256By128",
        "MulDivBy192", "Full256By192")]
    public string Shape { get; set; } = "WadScaled";

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0xD1A5);
        for (int i = 0; i < Count; i++)
        {
            UInt256 x;
            UInt256 y;
            int divisorBits;
            switch (Shape)
            {
                case "WadScaled":
                    y = Wad;
                    UInt256.Multiply(RandomBits(random, random.Next(20, 65)), Wad, out x);
                    break;
                case "WadWide":
                    y = Wad;
                    x = RandomBits(random, random.Next(129, 251));
                    break;
                case "Small":
                    y = RandomBits(random, random.Next(2, 17));
                    x = RandomBits(random, 256);
                    break;
                case "Full256By64":
                    y = RandomBits(random, random.Next(33, 65)) | UInt256.One;
                    x = RandomBits(random, 256);
                    break;
                case "ShortBy128":
                    divisorBits = random.Next(65, 121);
                    y = RandomBits(random, divisorBits);
                    x = RandomBits(random, random.Next(divisorBits + 1, 129));
                    break;
                case "MulDivBy128":
                    y = RandomBits(random, random.Next(65, 129));
                    x = RandomBits(random, random.Next(129, 193));
                    break;
                case "Full256By128":
                    y = RandomBits(random, random.Next(65, 129));
                    x = RandomBits(random, 256);
                    break;
                case "MulDivBy192":
                    divisorBits = random.Next(129, 181);
                    y = RandomBits(random, divisorBits);
                    x = RandomBits(random, random.Next(divisorBits + 1, 193));
                    break;
                default:
                    y = RandomBits(random, random.Next(129, 193));
                    x = RandomBits(random, 256);
                    break;
            }

            _x[i] = x;
            _y[i] = y;
            // MULMOD operands: a full-width product reduced by a 33- to 64-bit odd modulus.
            _m[i] = RandomBits(random, random.Next(33, 65)) | UInt256.One;
        }
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong Divide()
    {
        ulong acc = 0;
        for (int i = 0; i < Count; i++)
        {
            Divide(in _x[i], in _y[i], out UInt256 r);
            acc ^= r.u0 ^ r.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong Mod()
    {
        ulong acc = 0;
        for (int i = 0; i < Count; i++)
        {
            Mod(in _x[i], in _y[i], out UInt256 r);
            acc ^= r.u0 ^ r.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong MultiplyModBy64()
    {
        ulong acc = 0;
        for (int i = 0; i < Count; i++)
        {
            MultiplyMod(in _x[i], in _y[i], in _m[i], out UInt256 r);
            acc ^= r.u0;
        }
        return acc;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Divide(in UInt256 x, in UInt256 y, out UInt256 res) => UInt256.Divide(in x, in y, out res);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Mod(in UInt256 x, in UInt256 y, out UInt256 res) => UInt256.Mod(in x, in y, out res);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void MultiplyMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
        => UInt256.MultiplyMod(in x, in y, in m, out res);

    // A random value of exactly the given width: the top bit is set, the rest are random.
    private static UInt256 RandomBits(Random random, int bits)
    {
        Span<byte> bytes = stackalloc byte[32];
        random.NextBytes(bytes);
        UInt256 value = new(bytes, isBigEndian: false);
        if (bits < 256)
        {
            value &= (UInt256.One << bits) - UInt256.One;
        }
        return value | (UInt256.One << (bits - 1));
    }
}
