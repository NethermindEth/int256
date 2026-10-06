using System;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Text.Json;

internal static class Program
{
    private static int Main()
    {
        Overlap value = new() { Input = new Words { B = 1 } };
        Copy(in value.Input, out value.Output);
        ulong[] expected = [0, 1, 0, 0];
        ulong[] actual = [value.Output.A, value.Output.B, value.Output.C, value.Output.D];
        bool correct = actual.AsSpan().SequenceEqual(expected) && value.Input.A == 0;
        Console.WriteLine(JsonSerializer.Serialize(new
        {
            runtime = RuntimeInformation.FrameworkDescription,
            architecture = RuntimeInformation.ProcessArchitecture.ToString(),
            vector256 = Vector256.IsHardwareAccelerated,
            inputOffset = 0,
            outputOffset = 8,
            expected,
            actual,
            outsideOutputPreserved = value.Input.A == 0,
            cil = Convert.ToHexString(typeof(Program).GetMethod(nameof(Copy),
                BindingFlags.Static | BindingFlags.NonPublic)!.GetMethodBody()!.GetILAsByteArray()!),
            correct,
        }));
        return correct ? 0 : 1;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Copy(in Words input, out Words output) => output = input;

    [StructLayout(LayoutKind.Sequential)]
    private struct Words
    {
        public ulong A, B, C, D;
    }

    [StructLayout(LayoutKind.Explicit, Size = 40)]
    private struct Overlap
    {
        [FieldOffset(0)] public Words Input;
        [FieldOffset(8)] public Words Output;
    }
}
