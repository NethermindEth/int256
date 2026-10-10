// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.CompilerServices;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Shifts and wrapping subtraction as a hot consumer (an EVM opcode handler) compiles them: inlined into the caller,
/// often writing the result over an operand's slot.
/// </summary>
/// <remarks>
/// The callers below are <see cref="MethodImplOptions.AggressiveOptimization"/>, so they are compiled fully optimised on
/// first call and the library methods inline into them. A test body starts at Tier0, where nothing inlines, and would
/// exercise only the out-of-line copies.
/// </remarks>
public class InlineShiftSubtractTests
{
    private static readonly BigInteger Mask = (BigInteger.One << 256) - 1;

    // Slot offsets inside a byte buffer, two of them off 8-byte alignment, as an EVM stack slot can be.
    private static readonly int[] SlotOffsets = [0, 1, 8, 13];

    // Counts far outside -300..300: the contract holds for the whole int range, and the ends alone do not pin it
    // (int.MaxValue is 511 mod 512, so a count wrapped modulo 512 still gives zero there).
    private static readonly int[] FarCounts =
    [
        int.MinValue, int.MinValue + 1, int.MinValue + 64, -1024, -513, -512,
        511, 512, 513, 1000, 1024, 1 << 20, (1 << 26) + 1, int.MaxValue - 63, int.MaxValue,
    ];

    private static IEnumerable<UInt256> Values()
    {
        yield return UInt256.Zero;
        yield return UInt256.One;
        yield return UInt256.MaxValue;
        yield return new UInt256(0, 0, 0, 1UL << 63);
        yield return new UInt256(1UL << 63, 1UL << 63, 1UL << 63, 1UL << 63);
        yield return new UInt256(ulong.MaxValue, 0, 0, 0);
        yield return new UInt256(0, ulong.MaxValue, 0, 0);
        yield return new UInt256(0, 0, ulong.MaxValue, 0);
        yield return new UInt256(0, 0, 0, ulong.MaxValue);
        yield return new UInt256(0x5555555555555555UL, 0xAAAAAAAAAAAAAAAAUL, 0x5555555555555555UL, 0xAAAAAAAAAAAAAAAAUL);
        yield return new UInt256(0x0123456789abcdefUL, 0xfedcba9876543210UL, 0x0f1e2d3c4b5a6978UL, 0x8796a5b4c3d2e1f0UL);
        Random random = new(0x1_5B5B);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 64; i++)
        {
            random.NextBytes(bytes);
            yield return new UInt256(bytes, isBigEndian: true);
        }
    }

    [Test]
    public void Inlined_shifts_match_BigInteger_for_every_count()
    {
        foreach (UInt256 value in Values())
        {
            foreach (int n in ShiftCounts())
            {
                UInt256 left = ExpectedShift(value, n, left: true);
                UInt256 right = ExpectedShift(value, n, left: false);

                Check(Lsh(value, n), left, "Lsh", value, n);
                Check(Rsh(value, n), right, "Rsh", value, n);
                Check(LeftShift(value, n), left, "LeftShift", value, n);
                Check(RightShift(value, n), right, "RightShift", value, n);
                Check(ShiftLeftOperator(value, n), left, "<<", value, n);
                Check(ShiftRightOperator(value, n), right, ">>", value, n);
            }
        }
    }

    [Test]
    public void Inlined_shifts_in_place_match_BigInteger_for_every_count()
    {
        byte[] buffer = new byte[64];
        foreach (UInt256 value in Values())
        {
            foreach (int n in ShiftCounts())
            {
                UInt256 left = ExpectedShift(value, n, left: true);
                UInt256 right = ExpectedShift(value, n, left: false);

                Check(LshLocalInPlace(value, n), left, "Lsh into its local", value, n);
                Check(RshLocalInPlace(value, n), right, "Rsh into its local", value, n);
                foreach (int offset in SlotOffsets)
                {
                    ref UInt256 slot = ref Slot(buffer, offset);
                    slot = value;
                    LshInPlace(ref slot, n);
                    Check(slot, left, $"Lsh into its slot at +{offset}", value, n);
                    slot = value;
                    RshInPlace(ref slot, n);
                    Check(slot, right, $"Rsh into its slot at +{offset}", value, n);
                    slot = value;
                    LeftShiftInPlace(ref slot, n);
                    Check(slot, left, $"LeftShift into its slot at +{offset}", value, n);
                    slot = value;
                    RightShiftInPlace(ref slot, n);
                    Check(slot, right, $"RightShift into its slot at +{offset}", value, n);
                }
            }
        }
    }

    [Test]
    public void Inlined_subtract_matches_BigInteger_across_borrow_chains_and_wraparound()
    {
        foreach ((UInt256 a, UInt256 b) in SubtractPairs())
        {
            BigInteger difference = (BigInteger)a - (BigInteger)b;
            UInt256 expected = (UInt256)(difference & Mask);
            bool underflow = difference.Sign < 0;

            CheckDifference(Subtract(a, b), expected, "Subtract", a, b);
            CheckDifference(SubtractInstance(a, b), expected, "instance Subtract", a, b);
            CheckDifference(SubtractUnderflow(a, b, out bool flag), expected, "SubtractUnderflow", a, b);
            if (flag != underflow) Assert.Fail($"SubtractUnderflow(0x{a.ToString("X")}, 0x{b.ToString("X")}) reported {flag}");
            if (!underflow) CheckDifference(SubtractOperator(a, b), expected, "operator -", a, b);
        }
    }

    [Test]
    public void Inlined_subtract_in_place_matches_BigInteger()
    {
        byte[] buffer = new byte[96];
        foreach ((UInt256 a, UInt256 b) in SubtractPairs())
        {
            UInt256 expected = (UInt256)(((BigInteger)a - (BigInteger)b) & Mask);

            CheckDifference(SubtractIntoMinuendLocal(a, b), expected, "into the minuend's local", a, b);
            CheckDifference(SubtractIntoSubtrahendLocal(a, b), expected, "into the subtrahend's local", a, b);
            foreach (int offset in SlotOffsets)
            {
                // Stack layout of SUB: the subtrahend is the top word, the minuend the word above it, and the difference
                // replaces the top word.
                ref UInt256 top = ref Slot(buffer, offset);
                Unsafe.Add(ref top, 1) = a;
                top = b;
                SubtractIntoTop(ref top);
                CheckDifference(top, expected, $"into the subtrahend's slot at +{offset}", a, b);
                Unsafe.Add(ref top, 1) = a;
                top = b;
                SubtractIntoMinuend(ref top);
                CheckDifference(Unsafe.Add(ref top, 1), expected, $"into the minuend's slot at +{offset}", a, b);
            }
        }

        foreach (UInt256 value in Values())
        {
            ref UInt256 slot = ref Slot(buffer, 13);
            slot = value;
            SubtractFromItself(ref slot);
            CheckDifference(slot, UInt256.Zero, "x - x into x", value, value);
        }
    }

    /// <summary>The library's own call tree under these entry points is force-inlined, so consumers can rely on it.</summary>
    /// <remarks>
    /// Methods from the runtime (intrinsics, <see cref="Unsafe"/>) are the JIT's to inline and are left to the disassembly
    /// check; an IL body of at most 16 bytes is inlined by the JIT without the attribute.
    /// </remarks>
    [Test]
    public void Shift_and_subtract_call_trees_are_force_inlined()
    {
        Type byRef = typeof(UInt256).MakeByRefType();
        MethodInfo[] entryPoints =
        [
            typeof(UInt256).GetMethod(nameof(UInt256.Lsh), [byRef, typeof(int), byRef])!,
            typeof(UInt256).GetMethod(nameof(UInt256.Rsh), [byRef, typeof(int), byRef])!,
            typeof(UInt256).GetMethod(nameof(UInt256.LeftShift), [typeof(int), byRef])!,
            typeof(UInt256).GetMethod(nameof(UInt256.RightShift), [typeof(int), byRef])!,
            typeof(UInt256).GetMethod("op_LeftShift", [byRef, typeof(int)])!,
            typeof(UInt256).GetMethod("op_RightShift", [byRef, typeof(int)])!,
            typeof(UInt256).GetMethod(nameof(UInt256.Subtract), [byRef, byRef, byRef])!,
            typeof(UInt256).GetMethod(nameof(UInt256.Subtract), [byRef, byRef])!,
        ];

        HashSet<MethodBase> visited = [];
        List<string> outOfLine = [];
        foreach (MethodInfo entryPoint in entryPoints)
        {
            Assert.That(entryPoint, Is.Not.Null);
            Walk(entryPoint, entryPoint.Name);
        }

        Assert.That(outOfLine, Is.Empty);

        void Walk(MethodBase method, string path)
        {
            if (!visited.Add(method)) return;
            bool forced = (method.MethodImplementationFlags & MethodImplAttributes.AggressiveInlining) != 0;
            if (!forced && method.GetMethodBody()!.GetILAsByteArray()!.Length > 16) outOfLine.Add(path);
            foreach (MethodBase callee in Callees(method))
            {
                if (callee.DeclaringType?.Assembly == typeof(UInt256).Assembly) Walk(callee, $"{path} -> {callee.Name}");
            }
        }
    }

    private static IEnumerable<int> ShiftCounts()
    {
        for (int n = -300; n <= 300; n++) yield return n;
        foreach (int n in FarCounts) yield return n;
    }

    private static UInt256 ExpectedShift(UInt256 value, int n, bool left)
    {
        // Negative counts are not a designed contract but are pinned (see UInt256ShiftTests): a negative multiple of 64
        // gives zero, any other negative count shifts by n & 63 with no word shift.
        if (n < 0)
        {
            n &= 63;
            if (n == 0) return UInt256.Zero;
        }
        else if (n >= 256)
        {
            return UInt256.Zero;
        }

        BigInteger x = (BigInteger)value;
        return (UInt256)((left ? x << n : x >> n) & Mask);
    }

    private static IEnumerable<(UInt256 A, UInt256 B)> SubtractPairs()
    {
        // Every limb pattern from {0, 1, 2^63, max} on both sides: each borrow is generated, propagated through zero
        // limbs, or stopped, in every position, and a - b wraps whenever a < b.
        ulong[] limbs = [0, 1, 1UL << 63, ulong.MaxValue];
        List<UInt256> patterns = [];
        foreach (ulong u0 in limbs)
            foreach (ulong u1 in limbs)
                foreach (ulong u2 in limbs)
                    foreach (ulong u3 in limbs)
                        patterns.Add(new UInt256(u0, u1, u2, u3));

        foreach (UInt256 a in patterns)
            foreach (UInt256 b in patterns)
                yield return (a, b);

        UInt256[] values = Values().ToArray();
        foreach (UInt256 a in values)
            foreach (UInt256 b in values)
                yield return (a, b);
    }

    private static ref UInt256 Slot(byte[] buffer, int offset) => ref Unsafe.As<byte, UInt256>(ref buffer[offset]);

    private static void Check(in UInt256 actual, in UInt256 expected, string operation, in UInt256 value, int n)
    {
        if (actual != expected) Assert.Fail($"{operation}(0x{value.ToString("X")}, {n}) gave 0x{actual.ToString("X")}, expected 0x{expected.ToString("X")}");
    }

    private static void CheckDifference(in UInt256 actual, in UInt256 expected, string operation, in UInt256 a, in UInt256 b)
    {
        if (actual != expected) Assert.Fail($"{operation}: 0x{a.ToString("X")} - 0x{b.ToString("X")} gave 0x{actual.ToString("X")}, expected 0x{expected.ToString("X")}");
    }

    private const MethodImplOptions Optimized = MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization;

    [MethodImpl(Optimized)]
    private static UInt256 Lsh(UInt256 value, int n)
    {
        UInt256.Lsh(in value, n, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 Rsh(UInt256 value, int n)
    {
        UInt256.Rsh(in value, n, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 LeftShift(UInt256 value, int n)
    {
        value.LeftShift(n, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 RightShift(UInt256 value, int n)
    {
        value.RightShift(n, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 ShiftLeftOperator(UInt256 value, int n) => value << n;

    [MethodImpl(Optimized)]
    private static UInt256 ShiftRightOperator(UInt256 value, int n) => value >> n;

    [MethodImpl(Optimized)]
    private static UInt256 LshLocalInPlace(UInt256 value, int n)
    {
        UInt256.Lsh(in value, n, out value);
        return value;
    }

    [MethodImpl(Optimized)]
    private static UInt256 RshLocalInPlace(UInt256 value, int n)
    {
        UInt256.Rsh(in value, n, out value);
        return value;
    }

    [MethodImpl(Optimized)]
    private static void LshInPlace(ref UInt256 slot, int n) => UInt256.Lsh(in slot, n, out slot);

    [MethodImpl(Optimized)]
    private static void RshInPlace(ref UInt256 slot, int n) => UInt256.Rsh(in slot, n, out slot);

    [MethodImpl(Optimized)]
    private static void LeftShiftInPlace(ref UInt256 slot, int n) => slot.LeftShift(n, out slot);

    [MethodImpl(Optimized)]
    private static void RightShiftInPlace(ref UInt256 slot, int n) => slot.RightShift(n, out slot);

    [MethodImpl(Optimized)]
    private static UInt256 Subtract(UInt256 a, UInt256 b)
    {
        UInt256.Subtract(in a, in b, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 SubtractInstance(UInt256 a, UInt256 b)
    {
        a.Subtract(in b, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 SubtractUnderflow(UInt256 a, UInt256 b, out bool underflow)
    {
        underflow = UInt256.SubtractUnderflow(in a, in b, out UInt256 result);
        return result;
    }

    [MethodImpl(Optimized)]
    private static UInt256 SubtractOperator(UInt256 a, UInt256 b) => a - b;

    [MethodImpl(Optimized)]
    private static UInt256 SubtractIntoMinuendLocal(UInt256 a, UInt256 b)
    {
        UInt256.Subtract(in a, in b, out a);
        return a;
    }

    [MethodImpl(Optimized)]
    private static UInt256 SubtractIntoSubtrahendLocal(UInt256 a, UInt256 b)
    {
        UInt256.Subtract(in a, in b, out b);
        return b;
    }

    [MethodImpl(Optimized)]
    private static void SubtractIntoTop(ref UInt256 top) => UInt256.Subtract(in Unsafe.Add(ref top, 1), in top, out top);

    [MethodImpl(Optimized)]
    private static void SubtractIntoMinuend(ref UInt256 top)
        => UInt256.Subtract(in Unsafe.Add(ref top, 1), in top, out Unsafe.Add(ref top, 1));

    [MethodImpl(Optimized)]
    private static void SubtractFromItself(ref UInt256 slot) => UInt256.Subtract(in slot, in slot, out slot);

    private static readonly Dictionary<short, OpCode> OpCodesByValue = typeof(OpCodes)
        .GetFields(BindingFlags.Public | BindingFlags.Static)
        .Select(field => (OpCode)field.GetValue(null)!)
        .ToDictionary(op => op.Value);

    private static IEnumerable<MethodBase> Callees(MethodBase method)
    {
        byte[] il = method.GetMethodBody()!.GetILAsByteArray()!;
        for (int i = 0; i < il.Length;)
        {
            short value = il[i] == 0xFE ? unchecked((short)(0xFE00 | il[i + 1])) : il[i];
            i += il[i] == 0xFE ? 2 : 1;
            OpCode op = OpCodesByValue[value];
            if (op.OperandType == OperandType.InlineMethod)
                yield return method.Module.ResolveMethod(BitConverter.ToInt32(il, i))!;
            i += op.OperandType switch
            {
                OperandType.InlineNone => 0,
                OperandType.ShortInlineBrTarget or OperandType.ShortInlineI or OperandType.ShortInlineVar => 1,
                OperandType.InlineVar => 2,
                OperandType.InlineI8 or OperandType.InlineR => 8,
                OperandType.InlineSwitch => 4 + 4 * BitConverter.ToInt32(il, i),
                _ => 4,
            };
        }
    }
}
