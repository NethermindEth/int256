// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The signed operations the EVM reaches for: SDIV, SMOD, SAR, SLT/SGT, and the signed multiply. Each runs
/// over a batch so the timing is per operation rather than per invocation, and each is parameterised by the
/// operand signs, which is what used to decide how much work these took. Portable, so it is safe for the
/// ARM benchmark CI suite (<c>--filter '*SignedOps*'</c>).
/// </summary>
/// <remarks>
/// Operands live in 32-byte-aligned pinned buffers. A plain <c>Int256[]</c> of this size lands in the large
/// object heap at whatever offset it gets - 0, 8, 16 or 24 mod 32 in practice - and an unaligned operand
/// splits a cache line on half of its 32-byte reads, which shows up as a per-run bias of its own.
/// </remarks>
[WarmupCount(3)]
[IterationCount(10)]
public class SignedOpsBench
{
    private const int OperationCount = 256;

    private byte[] _aStore = null!;
    private byte[] _bStore = null!;
    private int _aOffset;
    private int _bOffset;
    private readonly int[] _counts = new int[OperationCount];

    /// <summary>Negative, non-negative, or half of each; "Mixed" is the case a branch on the sign mispredicts.</summary>
    [Params("Mixed", "Positive", "Negative")]
    public string Signs { get; set; } = null!;

    [GlobalSetup]
    public void Setup()
    {
        _aStore = AlignedStore(out _aOffset);
        _bStore = AlignedStore(out _bOffset);
        for (int i = 0; i < OperationCount; i++)
        {
            ulong seed = (ulong)i * 0x9E3779B97F4A7C15UL + 0xD1B54A32D192ED03UL;
            // Top limb below 2**63 keeps the magnitudes positive before the sign is applied.
            UInt256 a = new UInt256(seed | 2, seed ^ 0xA0761D6478BD642FUL, seed ^ 0xE7037ED1A0B428DBUL, (seed ^ 0x8EBC6AF09C88C6E3UL) >> 1);
            UInt256 b = new UInt256(~seed | 2, seed ^ 0x589965CC75374CC3UL, seed ^ 0x1D8E4E27C47D124FUL, (seed ^ 0xEB44ACCAB455D165UL) >> 1);
            A(i) = Signed(a, NegateAt(i, 0));
            B(i) = Signed(b, NegateAt(i, 1));
            _counts[i] = (int)(seed % 256);
        }
    }

    private static byte[] AlignedStore(out int offset)
    {
        byte[] buffer = GC.AllocateArray<byte>(OperationCount * 32 + 32, pinned: true);
        nint start = (nint)Unsafe.ByteOffset(ref Unsafe.NullRef<byte>(), ref buffer[0]);
        offset = (int)((32 - (start & 31)) & 31);
        return buffer;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private ref Int256 A(int index) => ref Unsafe.Add(ref Unsafe.As<byte, Int256>(ref _aStore[_aOffset]), index);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private ref Int256 B(int index) => ref Unsafe.Add(ref Unsafe.As<byte, Int256>(ref _bStore[_bOffset]), index);

    private bool NegateAt(int index, int operand) => Signs switch
    {
        "Positive" => false,
        "Negative" => true,
        _ => ((index >> operand) & 1) == 0,
    };

    private static Int256 Signed(in UInt256 magnitude, bool negative)
    {
        Int256 value = new Int256(magnitude);
        if (!negative)
        {
            return value;
        }

        value.Neg(out Int256 negated);
        return negated;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 Sar()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.RightShift(in A(i), _counts[i], out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 SarByOne()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.RightShift(in A(i), 1, out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 Divide()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.Divide(in A(i), in B(i), out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 Mod()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.Mod(in A(i), in B(i), out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 Multiply()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.Multiply(in A(i), in B(i), out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public Int256 Negate()
    {
        Int256 aggregate = default;
        for (int i = 0; i < OperationCount; i++)
        {
            Int256.Neg(in A(i), out Int256 result);
            Int256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public long CompareTo()
    {
        long aggregate = 0;
        for (int i = 0; i < OperationCount; i++)
        {
            aggregate += A(i).CompareTo(in B(i));
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public long LessThan()
    {
        long aggregate = 0;
        for (int i = 0; i < OperationCount; i++)
        {
            aggregate += A(i) < B(i) ? 1 : 0;
        }

        return aggregate;
    }
}
