// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

internal static class Int256NegativityBenchmarkData
{
    public static readonly Int256[] Values = CreateValues();
    public static readonly Int256[] Divisors =
    [
        new Int256(1),
        new Int256(-1),
        new Int256(2),
        new Int256(-2),
        new Int256(17),
        new Int256(-17),
        new Int256(BigInteger.One << 255),
        new Int256((BigInteger.One << 255) - 1),
    ];
    public static readonly Int256[] Moduli =
    [
        new Int256(1),
        new Int256(-1),
        new Int256(3),
        new Int256(-3),
        new Int256(17),
        new Int256(-17),
        new Int256((BigInteger.One << 255) - 1),
        new Int256(BigInteger.One << 255),
    ];
    public static readonly int[] Shifts = [0, 1, 7, 63, 64, 127, 128, 191, 192, 255, 256, 257];

    static Int256NegativityBenchmarkData()
    {
        ValidateLegacyImplementations();
    }

    private static Int256[] CreateValues()
    {
        BigInteger min = -(BigInteger.One << 255);
        BigInteger max = (BigInteger.One << 255) - 1;
        BigInteger[] values = [min, min + 1, -2, -1, 0, 1, 2, max - 1, max];
        Int256[] result = new Int256[values.Length + 16];
        for (int i = 0; i < values.Length; i++)
        {
            result[i] = new Int256(values[i]);
        }

        Random random = new(0x256);
        byte[] bytes = new byte[32];
        for (int i = values.Length; i < result.Length; i++)
        {
            random.NextBytes(bytes);
            BigInteger unsigned = new(bytes, isUnsigned: true, isBigEndian: false);
            BigInteger value = (unsigned & (BigInteger.One << 255)) == 0
                ? unsigned
                : unsigned - (BigInteger.One << 256);
            result[i] = new Int256(value);
        }

        return result;
    }

    // These helpers retain the Sign-based gates so each benchmark compares the old and new paths in one process.
    public static bool LegacyIsNegative(in Int256 value) => value.Sign < 0;

    public static void LegacyDivide(in Int256 n, in Int256 d, out Int256 res)
    {
        UInt256 value;
        UInt256 nValue = (UInt256)n;
        UInt256 dValue = (UInt256)d;
        if (n.Sign >= 0)
        {
            if (d.Sign >= 0)
            {
                UInt256.Divide(nValue, dValue, out value);
                res = new Int256(value);
                return;
            }

            Int256.Neg(d, out Int256 dNeg);
            UInt256.Divide(nValue, (UInt256)dNeg, out value);
            res = new Int256(value);
            Int256.Neg(res, out res);
            return;
        }

        Int256.Neg(n, out Int256 nNeg);
        if (d.Sign < 0)
        {
            Int256.Neg(d, out Int256 dNeg);
            UInt256.Divide((UInt256)nNeg, (UInt256)dNeg, out value);
            res = new Int256(value);
            return;
        }

        UInt256.Divide((UInt256)nNeg, dValue, out value);
        res = new Int256(value);
        Int256.Neg(res, out res);
    }

    public static void LegacyMod(in Int256 x, in Int256 y, out Int256 res)
    {
        Int256 xIn = x;
        Int256 yIn = y;
        int xSign = x.Sign;
        if (xSign == -1)
        {
            Int256.Neg(x, out xIn);
        }
        if (y.Sign == -1)
        {
            Int256.Neg(y, out yIn);
        }

        UInt256.Mod((UInt256)xIn, (UInt256)yIn, out UInt256 value);
        res = new Int256(value);
        if (xSign == -1)
        {
            Int256.Neg(res, out res);
        }
    }

    public static void LegacyRsh(in Int256 x, int n, out Int256 res)
    {
        UInt256 value = (UInt256)x;
        if (x.Sign >= 0)
        {
            value.RightShift(n, out UInt256 shifted);
            res = new Int256(shifted);
            return;
        }

        if (n % 64 == 0)
        {
            switch (n)
            {
                case 0:
                    res = x;
                    return;
                case 64:
                    res = new Int256(new UInt256(value.u1, value.u2, value.u3, ulong.MaxValue));
                    return;
                case 128:
                    res = new Int256(new UInt256(value.u2, value.u3, ulong.MaxValue, ulong.MaxValue));
                    return;
                case 192:
                    res = new Int256(new UInt256(value.u3, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));
                    return;
                default:
                    res = Int256.MinusOne;
                    return;
            }
        }

        ulong z0, z1, z2, z3;
        ulong a = UInt256.Lsh(ulong.MaxValue, 64 - (n % 64));
        if (n > 192)
        {
            if (n > 256)
            {
                res = Int256.MinusOne;
                return;
            }

            value = new UInt256(value.u3, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
            z1 = value.u1;
            z2 = value.u2;
            z3 = value.u3;
            n -= 192;
            goto Shift192;
        }
        if (n > 128)
        {
            value = new UInt256(value.u2, value.u3, ulong.MaxValue, ulong.MaxValue);
            z2 = value.u2;
            z3 = value.u3;
            n -= 128;
            goto Shift128;
        }
        if (n > 64)
        {
            value = new UInt256(value.u1, value.u2, value.u3, ulong.MaxValue);
            z3 = value.u3;
            n -= 64;
            goto Shift64;
        }

        z3 = UInt256.Rsh(value.u3, n) | a;
        a = UInt256.Lsh(value.u3, 64 - n);

    Shift64:
        z2 = UInt256.Rsh(value.u2, n) | a;
        a = UInt256.Lsh(value.u2, 64 - n);

    Shift128:
    Shift192:
        z1 = UInt256.Rsh(value.u1, n) | a;
        a = UInt256.Lsh(value.u1, 64 - n);
        z0 = UInt256.Rsh(value.u0, n) | a;

        res = new Int256(new UInt256(z0, z1, z2, z3));
    }

    private static void ValidateLegacyImplementations()
    {
        for (int i = 0; i < Values.Length; i++)
        {
            if (LegacyIsNegative(in Values[i]) != Values[i].IsNegative)
            {
                throw new InvalidOperationException("Negativity benchmark paths disagree.");
            }

            foreach (Int256 divisor in Divisors)
            {
                LegacyDivide(in Values[i], in divisor, out Int256 legacyDivide);
                Int256.Divide(in Values[i], in divisor, out Int256 currentDivide);
                if (!legacyDivide.Equals(currentDivide))
                {
                    throw new InvalidOperationException("Divide benchmark paths disagree.");
                }
            }

            foreach (Int256 modulus in Moduli)
            {
                LegacyMod(in Values[i], in modulus, out Int256 legacyMod);
                Int256.Mod(in Values[i], in modulus, out Int256 currentMod);
                if (!legacyMod.Equals(currentMod))
                {
                    throw new InvalidOperationException("Mod benchmark paths disagree.");
                }
            }

            foreach (int shift in Shifts)
            {
                LegacyRsh(in Values[i], shift, out Int256 legacyRsh);
                Int256.RightShift(in Values[i], shift, out Int256 currentRsh);
                if (!legacyRsh.Equals(currentRsh))
                {
                    throw new InvalidOperationException("Right-shift benchmark paths disagree.");
                }
            }
        }
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class Int256IsNegativeAB
{
    [Benchmark(Baseline = true)]
    public int Legacy_IsNegative()
    {
        int negatives = 0;
        foreach (Int256 value in Int256NegativityBenchmarkData.Values)
        {
            if (Int256NegativityBenchmarkData.LegacyIsNegative(in value))
            {
                negatives++;
            }
        }

        return negatives;
    }

    [Benchmark]
    public int Current_IsNegative()
    {
        int negatives = 0;
        foreach (Int256 value in Int256NegativityBenchmarkData.Values)
        {
            if (value.IsNegative)
            {
                negatives++;
            }
        }

        return negatives;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class Int256DivideSignGateAB
{
    [Benchmark(Baseline = true)]
    public Int256 Legacy_Divide()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        Int256[] divisors = Int256NegativityBenchmarkData.Divisors;
        for (int i = 0; i < values.Length; i++)
        {
            Int256NegativityBenchmarkData.LegacyDivide(in values[i], in divisors[i % divisors.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }

    [Benchmark]
    public Int256 Current_Divide()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        Int256[] divisors = Int256NegativityBenchmarkData.Divisors;
        for (int i = 0; i < values.Length; i++)
        {
            Int256.Divide(in values[i], in divisors[i % divisors.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class Int256ModSignGateAB
{
    [Benchmark(Baseline = true)]
    public Int256 Legacy_Mod()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        Int256[] moduli = Int256NegativityBenchmarkData.Moduli;
        for (int i = 0; i < values.Length; i++)
        {
            Int256NegativityBenchmarkData.LegacyMod(in values[i], in moduli[i % moduli.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }

    [Benchmark]
    public Int256 Current_Mod()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        Int256[] moduli = Int256NegativityBenchmarkData.Moduli;
        for (int i = 0; i < values.Length; i++)
        {
            Int256.Mod(in values[i], in moduli[i % moduli.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class Int256RshSignGateAB
{
    [Benchmark(Baseline = true)]
    public Int256 Legacy_Rsh()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        int[] shifts = Int256NegativityBenchmarkData.Shifts;
        for (int i = 0; i < values.Length; i++)
        {
            Int256NegativityBenchmarkData.LegacyRsh(in values[i], shifts[i % shifts.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }

    [Benchmark]
    public Int256 Current_Rsh()
    {
        Int256 accumulator = Int256.Zero;
        Int256[] values = Int256NegativityBenchmarkData.Values;
        int[] shifts = Int256NegativityBenchmarkData.Shifts;
        for (int i = 0; i < values.Length; i++)
        {
            Int256.RightShift(in values[i], shifts[i % shifts.Length], out Int256 result);
            Int256.Xor(in accumulator, in result, out accumulator);
        }

        return accumulator;
    }
}
