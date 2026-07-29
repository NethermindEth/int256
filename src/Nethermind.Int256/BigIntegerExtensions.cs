// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics;
using System.Numerics;

namespace Nethermind.Int256;

public static class BigIntegerExtensions
{
    public static byte[] ToBytes32(this BigInteger value, bool isBigEndian)
    {
        byte[] bytes32 = new byte[32];
        value.ToBytes32(bytes32.AsSpan(), isBigEndian);
        return bytes32;
    }

    /// <summary>
    /// Writes <paramref name="value"/> into <paramref name="target"/> as a 32-byte, big-endian,
    /// right-aligned (left-zero-padded) unsigned representation.
    /// </summary>
    /// <remarks>
    /// Allocation-free for values that fit in 32 bytes. Larger values fall back to the legacy
    /// allocating path, which throws (preserving historical behaviour).
    /// </remarks>
    /// <param name="value">The value to serialize.</param>
    /// <param name="target">The destination span; must be exactly 32 bytes long.</param>
    /// <param name="isBigEndian">Must be <see langword="true"/>; little-endian is not implemented.</param>
    /// <exception cref="NotImplementedException"><paramref name="isBigEndian"/> is <see langword="false"/>.</exception>
    /// <exception cref="ArgumentException"><paramref name="target"/> is not 32 bytes long.</exception>
    /// <exception cref="ArgumentOutOfRangeException"><paramref name="value"/> does not fit in 256 bits.</exception>
    /// <exception cref="OverflowException"><paramref name="value"/> is negative.</exception>
    public static void ToBytes32(this BigInteger value, Span<byte> target, bool isBigEndian)
    {
        if (!isBigEndian)
        {
            throw new NotImplementedException();
        }

        if (target.Length != 32)
        {
            throw new ArgumentException($"Target length should be 32 and is {target.Length}", nameof(target));
        }

        int byteCount = value.GetByteCount(isUnsigned: true);
        if (byteCount <= 32)
        {
            target.Slice(0, 32 - byteCount).Clear();
            bool written = value.TryWriteBytes(target.Slice(32 - byteCount), out _, isUnsigned: true, isBigEndian: true);
            Debug.Assert(written);
            return;
        }

        ReadOnlySpan<byte> bytes = value.ToByteArray(true, true);
        if (bytes.Length > 32)
        {
            bytes.Slice(bytes.Length - 32, bytes.Length).CopyTo(target);
        }
        else
        {
            bytes.CopyTo(target.Slice(32 - bytes.Length, bytes.Length));
        }
    }
}
