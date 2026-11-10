// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class ArithmeticDifferentialTests
{
    private const int Iterations = 200_000;
    private static readonly BigInteger Modulus = BigInteger.One << 256;
    private static readonly BigInteger Max = Modulus - 1;
    private static readonly BigInteger SignBit = BigInteger.One << 255;

    private static readonly BigInteger[] Edges =
    [
        BigInteger.Zero, BigInteger.One, 2, Max, Max - 1, SignBit, SignBit - 1, SignBit + 1,
        ulong.MaxValue, (BigInteger)ulong.MaxValue + 1, (BigInteger.One << 128) - 1, BigInteger.One << 128,
        (BigInteger.One << 192) - 1, BigInteger.One << 192, Max - ulong.MaxValue,
    ];

    [Test]
    public void Unsigned_division_family_matches_BigInteger()
    {
        Random random = new(0x1D17);
        for (int i = 0; i < Iterations; i++)
        {
            BigInteger x = Draw(random), y = Draw(random), m = Draw(random);
            UInt256 ux = FromBig(x), uy = FromBig(y), um = FromBig(m);

            if (!y.IsZero)
            {
                UInt256.Divide(in ux, in uy, out UInt256 quotient);
                Assert.That(ToBig(quotient), Is.EqualTo(x / y), $"{x} / {y}");
                UInt256.Mod(in ux, in uy, out UInt256 remainder);
                Assert.That(ToBig(remainder), Is.EqualTo(x % y), $"{x} % {y}");
            }

            if (!m.IsZero)
            {
                UInt256.AddMod(in ux, in uy, in um, out UInt256 sum);
                Assert.That(ToBig(sum), Is.EqualTo((x + y) % m), $"({x} + {y}) % {m}");
                UInt256.MultiplyMod(in ux, in uy, in um, out UInt256 product);
                Assert.That(ToBig(product), Is.EqualTo(x * y % m), $"({x} * {y}) % {m}");
            }
        }
    }

    [Test]
    public void Signed_division_family_matches_BigInteger()
    {
        Random random = new(0x5D1F);
        for (int i = 0; i < Iterations; i++)
        {
            BigInteger x = Draw(random), y = Draw(random);
            if (y.IsZero) continue;
            Int256 sx = new(FromBig(x)), sy = new(FromBig(y));
            BigInteger signedX = ToSigned(x), signedY = ToSigned(y);

            Int256.Divide(in sx, in sy, out Int256 quotient);
            Assert.That(ToBig((UInt256)quotient), Is.EqualTo(Wrap(BigInteger.Divide(signedX, signedY))), $"{signedX} / {signedY}");
            Int256.Mod(in sx, in sy, out Int256 remainder);
            Assert.That(ToBig((UInt256)remainder), Is.EqualTo(Wrap(BigInteger.Remainder(signedX, signedY))), $"{signedX} % {signedY}");
            Assert.That(sx < sy, Is.EqualTo(signedX < signedY));
            Assert.That(sx > sy, Is.EqualTo(signedX > signedY));
            Assert.That(Math.Sign(sx.CompareTo(sy)), Is.EqualTo(signedX.CompareTo(signedY)));
        }
    }

    // Values of 1 to 4 limbs, mostly short like EVM words, with fixed edges and their negations mixed in.
    private static BigInteger Draw(Random random)
    {
        int pick = random.Next(16);
        if (pick < 3) return Edges[random.Next(Edges.Length)];
        if (pick == 3) return Wrap(-Edges[random.Next(Edges.Length)]);
        int bits = pick < 10 ? 64 * random.Next(1, 3) : 64 * random.Next(1, 5);
        bits -= random.Next(64);
        byte[] bytes = new byte[33];
        random.NextBytes(bytes);
        bytes[32] = 0;
        BigInteger value = new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
        return random.Next(4) == 0 ? Wrap(-value) : value;
    }

    private static BigInteger Wrap(BigInteger v) => ((v % Modulus) + Modulus) % Modulus;

    private static BigInteger ToSigned(BigInteger v) => v >= SignBit ? v - Modulus : v;

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
