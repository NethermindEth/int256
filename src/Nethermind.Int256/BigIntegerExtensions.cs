using System;
using System.Numerics;

namespace Nethermind.Int256
{
    public static class BigIntegerExtensions
    {
        public static byte[] ToBytes32(this BigInteger value, bool isBigEndian)
        {
            byte[] bytes32 = new byte[32];
            value.ToBytes32(bytes32.AsSpan(), isBigEndian);
            return bytes32;
        }

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
}
