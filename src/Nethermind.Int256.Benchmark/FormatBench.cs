// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Decimal formatting before and after <see cref="ISpanFormattable"/>. Interpolation used to call
/// <c>ToString()</c> and copy the string in; it now formats straight into the handler's buffer. The signed
/// <c>ToString()</c> used to go through <see cref="BigInteger"/>. The legacy paths are inline copies.
/// Portable, so it is safe for the ARM benchmark CI suite (<c>--filter '*FormatBench*'</c>).
/// </summary>
[WarmupCount(3)]
[IterationCount(10)]
[MemoryDiagnoser]
[GroupBenchmarksBy(BenchmarkLogicalGroupRule.ByCategory)]
[CategoriesColumn]
public class FormatBench
{
    private const int OperationCount = 64;

    private readonly UInt256[] _unsigned = new UInt256[OperationCount];
    private readonly Int256[] _signed = new Int256[OperationCount];
    private readonly char[] _buffer = new char[128];

    /// <summary>One limb, as balances and gas mostly are, or all four.</summary>
    [Params("Narrow", "Wide")]
    public string Width { get; set; } = null!;

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0xF0_4D_A7);
        Span<byte> bytes = stackalloc byte[32];
        for (int i = 0; i < OperationCount; i++)
        {
            random.NextBytes(bytes);
            UInt256 value = Width == "Narrow" ? new UInt256((ulong)random.NextInt64()) : new UInt256(bytes);
            _unsigned[i] = value;
            // Half negative; Int256 from the top bit cleared keeps the magnitude in range.
            Int256 signed = new(value >> 1);
            if ((i & 1) == 1) signed.Neg(out signed);
            _signed[i] = signed;

            if (_unsigned[i].ToString() != LegacyToString(in _unsigned[i]) || _signed[i].ToString() != LegacyToString(in _signed[i]))
            {
                throw new InvalidOperationException($"Formatting diverged at {i}.");
            }
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 ToString")]
    public int UInt256ToStringLegacy()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += LegacyToString(in _unsigned[i]).Length;
        return length;
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 ToString")]
    public int UInt256ToString()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += _unsigned[i].ToString().Length;
        return length;
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 interpolation")]
    public int UInt256InterpolationLegacy()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += $"value {_unsigned[i].ToString()}".Length;
        return length;
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 interpolation")]
    public int UInt256Interpolation()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += $"value {_unsigned[i]}".Length;
        return length;
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 interpolation")]
    public int UInt256TryFormat()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++)
        {
            _unsigned[i].TryFormat(_buffer, out int written);
            length += written;
        }

        return length;
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 ToString")]
    public int Int256ToStringLegacy()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += LegacyToString(in _signed[i]).Length;
        return length;
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 ToString")]
    public int Int256ToString()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += _signed[i].ToString().Length;
        return length;
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 interpolation")]
    public int Int256InterpolationLegacy()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += $"value {LegacyToString(in _signed[i])}".Length;
        return length;
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 interpolation")]
    public int Int256Interpolation()
    {
        int length = 0;
        for (int i = 0; i < OperationCount; i++) length += $"value {_signed[i]}".Length;
        return length;
    }

    /// <summary>The digit loop <see cref="UInt256.ToString()"/> ran before it moved to the shared generic writer.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static string LegacyToString(in UInt256 value)
    {
        Span<char> buffer = stackalloc char[78];
        int position = 78;
        ulong l0 = value.u0, l1 = value.u1, l2 = value.u2, l3 = value.u3;
        while ((l1 | l2 | l3) != 0)
        {
            ulong chunk = DivideByChunk(ref l0, ref l1, ref l2, ref l3);
            for (int i = 0; i < 19; i++)
            {
                buffer[--position] = (char)('0' + (int)(chunk % 10));
                chunk /= 10;
            }
        }

        do
        {
            buffer[--position] = (char)('0' + (int)(l0 % 10));
            l0 /= 10;
        }
        while (l0 != 0);

        return new string(buffer[position..]);
    }

    private static ulong DivideByChunk(ref ulong l0, ref ulong l1, ref ulong l2, ref ulong l3)
    {
        const ulong Chunk = 10_000_000_000_000_000_000;
        UInt128 acc = l3;
        l3 = (ulong)(acc / Chunk);
        acc = ((UInt128)(ulong)(acc % Chunk) << 64) | l2;
        l2 = (ulong)(acc / Chunk);
        acc = ((UInt128)(ulong)(acc % Chunk) << 64) | l1;
        l1 = (ulong)(acc / Chunk);
        acc = ((UInt128)(ulong)(acc % Chunk) << 64) | l0;
        l0 = (ulong)(acc / Chunk);
        return (ulong)(acc % Chunk);
    }

    /// <summary>The signed <c>ToString()</c> before: the magnitude through <see cref="BigInteger"/>, then a '-'.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static string LegacyToString(in Int256 value)
    {
        if (value.IsNegative)
        {
            value.Neg(out Int256 magnitude);
            return "-" + ((BigInteger)(UInt256)magnitude).ToString((IFormatProvider?)null);
        }

        return ((BigInteger)(UInt256)value).ToString((IFormatProvider?)null);
    }
}
