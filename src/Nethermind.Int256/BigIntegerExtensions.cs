// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
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
    /// Allocation-free for any value that fits in 32 bytes: the bytes are written directly into
    /// <paramref name="target"/> via <see cref="BigInteger.TryWriteBytes"/>. Values that do not fit
    /// in 256 bits fall back to the legacy allocating path, which throws (preserving historical
    /// behaviour). Negative values throw, as <c>isUnsigned: true</c> rejects them.
    /// </remarks>
    /// <param name="value">The value to serialize.</param>
    /// <param name="target">The destination span; must be exactly 32 bytes long.</param>
    /// <param name="isBigEndian">Must be <see langword="true"/>; little-endian is not implemented.</param>
    /// <exception cref="NotImplementedException"><paramref name="isBigEndian"/> is <see langword="false"/>.</exception>
    /// <exception cref="ArgumentException"><paramref name="target"/> is not 32 bytes long.</exception>
    /// <exception cref="ArgumentOutOfRangeException"><paramref name="value"/> does not fit in 256 bits.</exception>
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

        // Try to write the unsigned, big-endian representation directly into the target without
        // allocating an intermediate array. BigInteger.TryWriteBytes succeeds whenever the value
        // fits in 32 bytes; otherwise we fall back to the slower allocating path that preserves the
        // historical behaviour (including throwing for values that do not fit in 256 bits).
        if (value.TryWriteBytes(target, out int bytesWritten, isUnsigned: true, isBigEndian: true))
        {
            // TryWriteBytes left-aligns the written bytes; shift them to be right-aligned (big-endian
            // with leading zero padding) when the value is narrower than 32 bytes. CopyTo is
            // memmove-safe for the overlapping case, and the subsequent Clear only touches the
            // now-vacated leading bytes, which are disjoint from the shifted tail.
            if (bytesWritten < 32)
            {
                target.Slice(0, bytesWritten).CopyTo(target.Slice(32 - bytesWritten, bytesWritten));
                target.Slice(0, 32 - bytesWritten).Clear();
            }

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
