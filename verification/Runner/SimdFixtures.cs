// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class SimdFixtures
{
    internal static void TargetChanged(string name, string method, string profile, JsonObject before, JsonObject after)
    {
        JsonArray Instructions(JsonNode body) => new(body["instructions"]!.AsArray().Select(item => (JsonNode)new JsonArray(
            item!["opcode"]!.DeepClone(), item["operand"]?.DeepClone())).ToArray());
        if (name == "FeatureExpressions")
        {
            int Getters(JsonObject artifact)
            {
                var live = artifact["coverage"]!.AsArray().ToDictionary(item => Catalog.Text(item!["method"]),
                    item => item!["reachable"]!.AsArray().Select(value => value!.GetValue<int>()).ToHashSet());
                return artifact["methods"]!.AsArray().Sum(body => body!["instructions"]!.AsArray().Count(op =>
                    live[Catalog.Text(body["signature"])].Contains(op!["Offset"]!.GetValue<int>()) && Catalog.Text(op["opcode"]) == "call"
                    && op["operand"]!.ToString().Contains("::get_IsSupported()", StringComparison.Ordinal)));
            }
            if (Getters(after) <= Getters(before)) throw new InvalidOperationException("Feature rewrite did not change reachable feature expressions");
            return;
        }
        if (name == "Renamed")
        {
            JsonArray Bodies(JsonObject artifact) => new(artifact["methods"]!.AsArray().Select(body => (JsonNode)Instructions(body!)).ToArray());
            if (JsonNode.DeepEquals(Bodies(before), Bodies(after))) throw new InvalidOperationException("Renaming did not change a reachable call operand");
            return;
        }
        string target = name switch
        {
            "ReversedStore" => "StoreLimbs",
            "EquivalentMask" => method == "Add" ? "PrepareAdd" : "SubtractImpl",
            "ExtractedHelper" when profile is not ("arm64-advsimd" or "x64-sse42") => method == "Add" ? "FinishAdd" : "SubtractImpl",
            _ => method == "Add" ? "AddVector128" : "SubtractVector128"
        };
        JsonArray Body(JsonObject artifact)
        {
            JsonNode[] found = artifact["methods"]!.AsArray().Where(body => Catalog.Text(body!["signature"]).Contains($"::{target}(", StringComparison.Ordinal)).Select(body => body!).ToArray();
            if (found.Length != 1) throw new InvalidOperationException($"Missing/ambiguous targeted fixture method {target}");
            return Instructions(found[0]);
        }
        if (JsonNode.DeepEquals(Body(before), Body(after))) throw new InvalidOperationException($"{name}: targeted reachable CIL {target} did not change");
    }

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
