#if EXTRACTED_HELPER
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static Vector128<ulong> ExtractPair(Vector128<ulong> low, Vector128<ulong> high)
        => AdvSimd.ExtractVector128(low, high, 1);

    private static Vector128<ulong> MergePropagation(Vector128<ulong> low, Vector128<ulong> high)
        => low | high;

    private static uint AccumulateCascade(uint propagated, uint generated)
        => propagated + 2 * generated;
}
#endif
