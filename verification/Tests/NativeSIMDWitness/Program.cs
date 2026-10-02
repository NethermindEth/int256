using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;
using System.Text.Json;

internal static class Program
{
    private delegate void Operation<T>(in T left, in T right, out T result);

    private static object Capabilities() => new
    {
        architecture = RuntimeInformation.ProcessArchitecture.ToString(),
        runtime = RuntimeInformation.FrameworkDescription,
        pointerBytes = IntPtr.Size,
        littleEndian = BitConverter.IsLittleEndian,
        avx2 = Avx2.IsSupported,
        avx512F = Avx512F.IsSupported,
        avx512VL = Avx512F.VL.IsSupported,
        bmi1 = Bmi1.IsSupported,
        avx = Avx.IsSupported,
        sse2 = Sse2.IsSupported,
        ssse3 = Ssse3.IsSupported,
        sse42 = Sse42.IsSupported,
        advSimd = AdvSimd.IsSupported
    };

    private static bool Matches(string profile) => IntPtr.Size == 8 && BitConverter.IsLittleEndian && profile switch
    {
        "scalar" => !Avx2.IsSupported && !AdvSimd.IsSupported && !Sse42.IsSupported,
        "arm64-advsimd" => RuntimeInformation.ProcessArchitecture == Architecture.Arm64 && AdvSimd.IsSupported && !Avx2.IsSupported,
        "x64-sse42" => RuntimeInformation.ProcessArchitecture == Architecture.X64 && !Avx2.IsSupported &&
            Sse42.IsSupported && Sse2.IsSupported && Ssse3.IsSupported,
        "x64-avx2" => Avx2.IsSupported && Avx.IsSupported && !Avx512F.VL.IsSupported && !Bmi1.IsSupported,
        "x64-avx2-bmi1" => Avx2.IsSupported && Avx.IsSupported && !Avx512F.VL.IsSupported && Bmi1.IsSupported,
        "x64-avx512" => Avx2.IsSupported && Avx.IsSupported && Avx512F.IsSupported && Avx512F.VL.IsSupported && !Bmi1.IsSupported,
        "x64-avx512-bmi1" => Avx2.IsSupported && Avx.IsSupported && Avx512F.IsSupported && Avx512F.VL.IsSupported && Bmi1.IsSupported,
        _ => throw new ArgumentException("Unknown native witness profile")
    };

    private static int Main(string[] args)
    {
        if (args.Length == 0)
        {
            Console.WriteLine(JsonSerializer.Serialize(Capabilities()));
            return 0;
        }
        if (args.Length != 6) throw new ArgumentException("Usage: NativeSIMDWitness assembly method profile initialHex outputOffset witnessAddress:byte|positive");
        if (!Matches(args[2]))
        {
            Console.WriteLine(JsonSerializer.Serialize(new { status = "unsupported", capabilities = Capabilities() }));
            return 77;
        }
        Type type = Assembly.LoadFrom(Path.GetFullPath(args[0])).GetType("Nethermind.Int256.UInt256", throwOnError: true)!;
        MethodInfo runner = typeof(Program).GetMethod(nameof(Run), BindingFlags.Static | BindingFlags.NonPublic)!;
        return (int)runner.MakeGenericMethod(type).Invoke(null, [type, args])!;
    }

    private static int Run<T>(Type type, string[] args) where T : unmanaged
    {
        if (Unsafe.SizeOf<T>() != 32) throw new InvalidDataException("Unexpected UInt256 size");
        Type reference = type.MakeByRefType();
        MethodInfo method = type.GetMethod(args[1], BindingFlags.Public | BindingFlags.Static, [reference, reference, reference])
            ?? throw new MissingMethodException("Exact public three-reference entry missing");
        if (method.ReturnType != typeof(void) || !method.GetParameters()[0].IsIn ||
            !method.GetParameters()[1].IsIn || !method.GetParameters()[2].IsOut)
            throw new InvalidDataException("Unexpected public calling contract");
        Operation<T> operation = method.CreateDelegate<Operation<T>>();
        byte[] memory = Convert.FromHexString(args[3]);
        byte[] initial = (byte[])memory.Clone();
        int output = int.Parse(args[4]);
        if (memory.Length < 96 || output < 0 || output + 32 > memory.Length)
            throw new ArgumentException("Invalid witness byte map");
        BigInteger left = new(initial.AsSpan(0, 32), isUnsigned: true, isBigEndian: false);
        BigInteger right = new(initial.AsSpan(64, 32), isUnsigned: true, isBigEndian: false);
        BigInteger modulus = BigInteger.One << 256;
        BigInteger value = args[1] switch
        {
            "Add" => (left + right) % modulus,
            "Subtract" => (left - right + modulus) % modulus,
            _ => throw new ArgumentException("Unknown witness method")
        };
        byte[] expected = new byte[32];
        if (!value.TryWriteBytes(expected, out _, isUnsigned: true, isBigEndian: false))
            throw new InvalidDataException("Expected value exceeded 256 bits");
        ref T a = ref Unsafe.As<byte, T>(ref memory[0]);
        ref T b = ref Unsafe.As<byte, T>(ref memory[64]);
        ref T result = ref Unsafe.As<byte, T>(ref memory[output]);
        operation(in a, in b, out result);
        bool arithmetic = memory.AsSpan(output, 32).SequenceEqual(expected);
        bool preservation = Enumerable.Range(0, memory.Length).All(i =>
            (i >= output && i < output + 32) || memory[i] == initial[i]);
        bool accepted;
        if (args[5] == "positive") accepted = arithmetic && preservation;
        else
        {
            string[] witness = args[5].Split(':');
            int address = int.Parse(witness[0]);
            accepted = !arithmetic && preservation && memory[address] == byte.Parse(witness[1]);
        }
        Console.WriteLine(JsonSerializer.Serialize(new
        {
            status = accepted ? "matched" : "mismatch", capabilities = Capabilities(),
            method = args[1], profile = args[2], initial = Convert.ToHexString(initial), output,
            actual = Convert.ToHexString(memory), expected = Convert.ToHexString(expected), arithmetic, preservation
        }));
        return accepted ? 0 : 1;
    }
}
