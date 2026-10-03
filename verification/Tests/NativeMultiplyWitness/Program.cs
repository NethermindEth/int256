using System;
using System.IO;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;
using System.Security.Cryptography;
using System.Text.Json;
using Nethermind.Int256;

namespace UInt256Verification.NativeMultiplyWitness;

internal static class Program
{
    private static int Main()
    {
        UInt256 one = new(1ul, 0ul, 0ul, 0ul);
        Overlap union = new() { Input = new UInt256(0ul, 1ul, 0ul, 0ul) };
        UInt256 initial = union.Input;
        UInt256.Multiply(in one, in union.Input, out union.Output);
        ulong[] expected = [0, 1, 0, 0];
        ulong[] actual = [union.Output.u0, union.Output.u1, union.Output.u2, union.Output.u3];
        bool correct = actual.AsSpan().SequenceEqual(expected) && union.Input.u0 == initial.u0;
        string assembly = typeof(UInt256).Assembly.Location;
        Console.WriteLine(JsonSerializer.Serialize(new
        {
            assembly,
            sha256 = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(assembly))),
            runtime = RuntimeInformation.FrameworkDescription,
            architecture = RuntimeInformation.ProcessArchitecture.ToString(),
            features = new
            {
                Vector256 = Vector256.IsHardwareAccelerated,
                Bmi2X64 = Bmi2.X64.IsSupported,
                ArmBase64 = ArmBase.Arm64.IsSupported,
                Avx2 = Avx2.IsSupported,
                Avx512DQVL = Avx512DQ.VL.IsSupported,
            },
            initialLeft = new ulong[] { one.u0, one.u1, one.u2, one.u3 },
            initialRight = new ulong[] { initial.u0, initial.u1, initial.u2, initial.u3 },
            rightOffset = 0,
            outputOffset = 8,
            expected,
            actual,
            outsideOutputPreserved = union.Input.u0 == initial.u0,
            correct,
        }));
        return correct ? 0 : 1;
    }

    [StructLayout(LayoutKind.Explicit, Size = 40)]
    private struct Overlap
    {
        [FieldOffset(0)] public UInt256 Input;
        [FieldOffset(8)] public UInt256 Output;
    }
}
