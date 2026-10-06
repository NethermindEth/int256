using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;
using System.Security.Cryptography;
using System.Text.Json;
using Nethermind.Int256;

internal static class Program
{
    private static readonly BigInteger Mask = (BigInteger.One << 256) - 1;

    // Keep the actual production entry visible to disassembly and prevent the
    // harness's concrete offsets from specializing its implementation.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Add(in UInt256 a, in UInt256 b, out UInt256 result) => UInt256.Add(in a, in b, out result);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Subtract(in UInt256 a, in UInt256 b, out UInt256 result) => UInt256.Subtract(in a, in b, out result);

    private static void Write(Span<byte> target, ulong[] limbs)
    {
        for (int i = 0; i < 4; i++)
            BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(8 * i, 8), limbs[i]);
    }

    private static int Main()
    {
        ulong[][] operands =
        [
            [1, 0, 0, 0],
            [ulong.MaxValue, ulong.MaxValue, 7, 11],
            [0, 0, 7, 11],
            [ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue],
            [23, 31, 43, 59],
        ];
        int[] separations = [-31, -8, -1, 0, 1, 8, 31, 64];
        int[] outputs = Enumerable.Range(-31, 63).Concat([64, 96]).ToArray();
        int count = 0;
        foreach (ulong[] first in operands)
        foreach (int residue in Enumerable.Range(0, 8))
        foreach (int separation in separations)
        foreach (int displacement in outputs)
        foreach (bool subtract in new[] { false, true })
        {
            int left = 64 + residue, right = left + separation, output = left + displacement;
            byte[] bytes = new byte[256];
            Array.Fill(bytes, (byte)0xA5);
            Write(bytes.AsSpan(left, 32), first);
            Write(bytes.AsSpan(right, 32), operands[(Array.IndexOf(operands, first) + 1) % operands.Length]);
            byte[] initial = (byte[])bytes.Clone();
            // Read expected operands only after both initial writes: overlapping
            // input views must share the same bytes, including initialization.
            BigInteger a = new(initial.AsSpan(left, 32), isUnsigned: true, isBigEndian: false);
            BigInteger b = new(initial.AsSpan(right, 32), isUnsigned: true, isBigEndian: false);
            BigInteger expected = (subtract ? a - b : a + b) & Mask;
            ref UInt256 aRef = ref Unsafe.As<byte, UInt256>(ref bytes[left]);
            ref UInt256 bRef = ref Unsafe.As<byte, UInt256>(ref bytes[right]);
            ref UInt256 result = ref Unsafe.As<byte, UInt256>(ref bytes[output]);
            if (subtract) Subtract(in aRef, in bRef, out result);
            else Add(in aRef, in bRef, out result);
            BigInteger actual = new(bytes.AsSpan(output, 32), isUnsigned: true, isBigEndian: false);
            bool footprint = bytes.AsSpan(0, output).SequenceEqual(initial.AsSpan(0, output)) &&
                bytes.AsSpan(output + 32).SequenceEqual(initial.AsSpan(output + 32));
            if (actual != expected || !footprint)
            {
                Console.Error.WriteLine($"Mismatch: subtract={subtract}, left={left}, right={right}, output={output}, expected={expected}, actual={actual}, footprint={footprint}");
                return 1;
            }
            count++;
        }
        Console.WriteLine(JsonSerializer.Serialize(new
        {
            status = "passed", cases = count,
            runtime = RuntimeInformation.FrameworkDescription,
            architecture = RuntimeInformation.ProcessArchitecture.ToString(),
            assemblySha256 = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(typeof(UInt256).Assembly.Location))).ToLowerInvariant(),
            sse42 = Sse42.IsSupported, avx2 = Avx2.IsSupported,
            avx512 = Avx512F.VL.IsSupported, advSimd = AdvSimd.IsSupported,
            scope = "Supplementary native Add/Subtract byte-offset and overlap checks; not a kernel proof or portable CLI guarantee",
        }));
        return 0;
    }
}
