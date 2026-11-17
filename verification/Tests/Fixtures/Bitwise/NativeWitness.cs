using System.Runtime.CompilerServices;
using Nethermind.Int256;

bool early = args.Single() == "BitwiseEarlyStore";
foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
foreach (bool returned in new[] { false, true })
{
    if (early && returned) continue;
    byte[] bytes = new byte[192];
    ulong[] initial = early ? [1, 2, 4, 8] : [1, 0, 0, 0];
    for (int i = 0; i < 4; i++)
    {
        Unsafe.WriteUnaligned(ref bytes[16 + i * 8], initial[i]);
        Unsafe.WriteUnaligned(ref bytes[64 + i * 8], initial[i]);
    }
    byte[] before = (byte[])bytes.Clone();
    ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[16]);
    ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[64]);
    int output = early ? 24 : 104;
    ref UInt256 destination = ref Unsafe.As<byte, UInt256>(ref bytes[output]);
    UInt256 result;
    if (returned)
        result = operation switch { "And" => left & right, "Or" => left | right, "Xor" => left ^ right, _ => ~left };
    else
    {
        switch (operation)
        {
            case "And": UInt256.And(in left, in right, out destination); break;
            case "Or": UInt256.Or(in left, in right, out destination); break;
            case "Xor": UInt256.Xor(in left, in right, out destination); break;
            default: UInt256.Not(in left, out destination); break;
        }
        result = destination;
    }
    ulong[] expected = early ? operation switch
    {
        "And" => [1, 0, 0, 0], "Or" => [1, 3, 7, 15], "Xor" => [0, 2, 6, 14],
        _ => [ulong.MaxValue - 1, 1, ulong.MaxValue - 1, 1]
    } : operation switch { "And" or "Or" => [0, 0, 0, 0], _ => [1, 0, 0, 0] };
    ulong[] observed = [result.u0, result.u1, result.u2, result.u3];
    if (!observed.SequenceEqual(expected))
        throw new InvalidOperationException($"Native witness differs: {operation}/{returned}: {string.Join(',', observed)}");
    for (int i = 0; i < bytes.Length; i++)
        if ((returned || i < output || i >= output + 32) && bytes[i] != before[i])
            throw new InvalidOperationException($"Caller byte changed: {operation}/{returned}/{i}");
    Console.WriteLine($"PASS native {operation}/{returned}/{args[0]}");
}
