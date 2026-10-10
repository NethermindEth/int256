// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class UInt256LayoutTests
{
    // Sequential layout makes field order the memory layout; span casts and Vector256 loads require u0..u3 at 0/8/16/24.
    [Test]
    public void Layout_is_four_contiguous_little_endian_limbs()
    {
        Assert.That(Unsafe.SizeOf<UInt256>(), Is.EqualTo(32));

        UInt256[] values = [new(1, 2, 3, 4)];
        ReadOnlySpan<ulong> limbs = MemoryMarshal.Cast<UInt256, ulong>(values);
        Assert.That(limbs.ToArray(), Is.EqualTo(new ulong[] { 1, 2, 3, 4 }));

        ref byte start = ref Unsafe.As<UInt256, byte>(ref values[0]);
        Assert.That(Offset(ref start, in values[0].u0), Is.EqualTo(0));
        Assert.That(Offset(ref start, in values[0].u1), Is.EqualTo(8));
        Assert.That(Offset(ref start, in values[0].u2), Is.EqualTo(16));
        Assert.That(Offset(ref start, in values[0].u3), Is.EqualTo(24));
    }

    private static int Offset(ref byte start, in ulong field)
        => (int)Unsafe.ByteOffset(ref start, ref Unsafe.As<ulong, byte>(ref Unsafe.AsRef(in field)));
}
