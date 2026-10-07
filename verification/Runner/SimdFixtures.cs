// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

namespace UInt256Verification;

internal static class SimdFixtures
{
    internal static bool Positive(string name, string method, string profile) => name switch
    {
        "Baseline" or "Renamed" or "ExtractedHelper" or "FeatureExpressions" => true,
        "EquivalentMask" => profile is "x64-avx2" or "x64-avx2-bmi1",
        "LaneLocals" or "ReversedStore" => profile is "arm64-advsimd" or "x64-sse42",
        "InlineCarry" => profile == "x64-sse42" || method == "Subtract" && profile == "arm64-advsimd",
        _ => false
    };

    internal static bool Negative(string name, string method, string profile) => name switch
    {
        "WrongAlignment" => profile is "arm64-advsimd" or "x64-sse42",
        "WrongTop" => profile == "arm64-advsimd" || method == "Subtract" && profile == "x64-sse42",
        "WrongBlend" => profile is "x64-avx2" or "x64-avx2-bmi1",
        "WrongAvxAlignment" or "WrongTernary" => profile is "x64-avx512" or "x64-avx512-bmi1",
        _ => profile is "x64-avx2" or "x64-avx2-bmi1" or "x64-avx512" or "x64-avx512-bmi1"
    };

    internal static (ulong[] Left, ulong[] Right, int Output, int Address, int Actual) Witness(string name, string method)
    {
        if (method is not ("Add" or "Subtract")) throw new ArgumentException("Unknown SIMD witness method");
        bool add = method == "Add";
        const ulong max = ulong.MaxValue;
        if (name is "WrongAlignment" or "WrongAvxAlignment" or "WrongBlend" or "WrongTernary")
            return (add ? [max, 2, 4, 6] : [0, 2, 4, 6], [1, 1, 1, 1], 64,
                name == "WrongAlignment" ? 80 : 72, name == "WrongAlignment" ? (add ? 6 : 2) : (add ? 3 : 1));
        if (name is "WrongPredicate" or "WrongTable" or "WrongScale" or "EarlyReread")
        {
            int output = name == "EarlyReread" ? 8 : 128;
            return (add ? [max, max, 0, 0] : [0, 1, 2, 2], add ? [1, 0, 1, 1] : [1, 1, 1, 1], output,
                output + (name == "WrongScale" ? 8 : 16), name == "WrongScale" ? (add ? 255 : 0) : 1);
        }
        if (name == "WrongTop") return (add ? [max, max, max, 0] : [0, 0, 0, 2], [1, 0, 0, 1], 128, 152, 1);
        throw new ArgumentException("Unknown SIMD witness case");
    }
}
