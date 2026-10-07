// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class EqualityFixtures
{
    private static readonly string[] References = ["EqUInt256UInt256", "NeUInt256UInt256", "EqualsUInt256Ref", "EqualsUInt256Value"];
    internal static JsonObject Shape(Catalog catalog, string method)
    {
        JsonObject calling = catalog.Manifest(method)["callingConvention"]!.AsObject();
        bool isStatic = calling["static"]!.GetValue<bool>();
        JsonObject result = new() { ["kind"] = method == "EqualsUInt256Value" ? "snapshot" : "reference",
            ["negate"] = method.StartsWith("Ne", StringComparison.Ordinal), ["instance"] = !isStatic };
        if (References.Contains(method)) return result;
        var scalars = new Dictionary<string, (string Kind, int Width, string CSharp)>
        {
            ["System.Int32"] = ("s32", 32, "int"), ["System.UInt32"] = ("u32", 32, "uint"),
            ["System.Int64"] = ("s64", 64, "long"), ["System.UInt64"] = ("u64", 64, "ulong")
        };
        JsonArray parameters = calling["parameters"]!.AsArray();
        string? scalar = parameters.Select(item => Catalog.Text(item!["type"])).FirstOrDefault(scalars.ContainsKey);
        if (scalar is null) throw new InvalidOperationException("Unsupported equality fixture calling convention");
        var shape = scalars[scalar];
        result["kind"] = "scalar"; result["scalarKind"] = shape.Kind; result["width"] = shape.Width; result["csharp"] = shape.CSharp;
        result["scalarFirst"] = isStatic && Catalog.Text(parameters[0]!["type"]) == scalar;
        return result;
    }
    internal static Dictionary<string, string> Substitutions(Catalog catalog, string method, JsonObject data)
    {
        var shape = Shape(catalog, method);
        string left = data["leftBase"]!.ToString(), right = data["rightBase"]!.ToString();
        const string common = "Extracted.program Extracted.entryIndex initial";
        bool negate = shape["negate"]!.GetValue<bool>();
        string arguments, contract, expectation;
        if (Catalog.Text(shape["kind"]) == "scalar")
        {
            string width = shape["width"]!.ToString(), kind = Catalog.Text(shape["scalarKind"]);
            string word = $"(BitVec.ofNat {width} {data["scalarBits"]})", scalar = $"(Scalar.{kind} {word})", argument = $".i{width} {word}";
            bool first = shape["scalarFirst"]!.GetValue<bool>();
            arguments = first ? $"[{argument}, .object {left}]" : $"[.object {left}, {argument}]";
            contract = $"ScalarContract {common} {left} {scalar} {first.ToString().ToLowerInvariant()} {negate.ToString().ToLowerInvariant()}";
            expectation = $"((decide (((byteValue initial {left}).toNat : Int) = Scalar.number {scalar})) != {negate.ToString().ToLowerInvariant()})";
        }
        else if (Catalog.Text(shape["kind"]) == "snapshot")
        {
            string bits = $"(BitVec.ofNat 256 {data["snapshot"]})";
            arguments = $"[.object {left}, .v256 {bits}]";
            contract = $"SnapshotContract {common} {left} {bits}";
            expectation = $"decide (byteValue initial {left} = {bits})";
        }
        else
        {
            arguments = $"[.object {left}, .object {right}]";
            contract = $"{(negate ? "InequalityContract" : "Contract")} {common} {left} {right}";
            expectation = $"decide (byteValue initial {left} {(negate ? "≠" : "=")} byteValue initial {right})";
        }
        return new() { ["INITIAL"] = FixtureChecks.InitialBytes(data["initialBytes"]!.AsObject().Select(pair => KeyValuePair.Create(pair.Key, pair.Value!.ToString()))),
            ["ARGUMENTS"] = arguments, ["CONTRACT"] = contract, ["EXPECTATION"] = expectation,
            ["ACTUAL"] = data["actualResult"]!.GetValue<bool>() ? "1" : "0", ["EXPECTED"] = data["expectedResult"]!.GetValue<bool>().ToString().ToLowerInvariant() };
    }
    internal static string NativeSource(Catalog catalog, string method, JsonObject data)
    {
        var shape = Shape(catalog, method);
        bool instance = shape["instance"]!.GetValue<bool>(); string expression, op = shape["negate"]!.GetValue<bool>() ? "!=" : "==";
        if (Catalog.Text(shape["kind"]) == "scalar")
        {
            string scalar = $"unchecked(({Catalog.Text(shape["csharp"])}){data["scalarBits"]}UL)";
            expression = instance ? $"left.Equals({scalar})" : shape["scalarFirst"]!.GetValue<bool>() ? $"{scalar} {op} left" : $"left {op} {scalar}";
        }
        else if (Catalog.Text(shape["kind"]) == "snapshot")
        {
            BigInteger value = BigInteger.Parse(data["snapshot"]!.ToString(), CultureInfo.InvariantCulture);
            string words = string.Join(", ", Enumerable.Range(0, 4).Select(i => $"{(value >> (64 * i)) & ((BigInteger.One << 64) - 1)}UL"));
            expression = $"left.Equals(new UInt256({words}))";
        }
        else expression = instance ? "left.Equals(in right)" : $"left {op} right";
        string assignments = string.Join('\n', data["initialBytes"]!.AsObject().Select(pair => $"bytes[{pair.Key}] = {pair.Value};"));
        return $$"""
            using System;
            using System.Runtime.CompilerServices;
            using Nethermind.Int256;
            byte[] bytes = new byte[128];
            {{assignments}}
            byte[] original = (byte[])bytes.Clone();
            ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{{data["leftBase"]}}]);
            ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{{data["rightBase"]}}]);
            bool result = {{expression}};
            Console.WriteLine($"Native equality witness: {result}; Vector256={System.Runtime.Intrinsics.Vector256.IsHardwareAccelerated}; SSE41={System.Runtime.Intrinsics.X86.Sse41.IsSupported}");
            for (int i = 0; i < bytes.Length; ++i) if (bytes[i] != original[i]) return 2;
            return result == {{data["actualResult"]!.GetValue<bool>().ToString().ToLowerInvariant()}} ? 0 : 1;
            """ + "\n";
    }
    private static JsonObject Negatives(Workspace workspace) => JsonNode.Parse(File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Equality/Witnesses.json")))!["negativeCases"]!.AsObject();
    internal static bool Applicable(Workspace workspace, string name, string method, string profile)
    {
        JsonObject shape = Shape(workspace.Catalog, method);
        if (name is "Baseline" or "Renamed") return true;
        if (name is "EquivalentScalar" or "EquivalentReduction")
        {
            JsonObject features = workspace.Catalog.Profile(profile);
            bool vector = features["Vector256Accelerated"]!.GetValue<bool>(), sse = features["Sse41"]!.GetValue<bool>();
            return name == "EquivalentScalar" ? !vector && (!References.Contains(method) || !sse) : vector || References.Contains(method) && sse;
        }
        string group = Catalog.Text(Negatives(workspace)[name]!["group"]);
        return group == "reference" && References.Contains(method) || group == "snapshot" && Catalog.Text(shape["kind"]) == "snapshot"
            || group == "signed" && (shape["scalarKind"]?.GetValue<string>() ?? "").StartsWith('s') || group == "inequality" && shape["negate"]!.GetValue<bool>();
    }
    internal static JsonObject Witness(Workspace workspace, string name, string method)
    {
        JsonObject shape = Shape(workspace.Catalog, method), data = Negatives(workspace)[name]!.DeepClone().AsObject();
        if (data["widths"] is JsonObject widths)
        {
            int width = shape["width"]!.GetValue<int>();
            foreach (var pair in widths[width.ToString(CultureInfo.InvariantCulture)]!.AsObject()) data[pair.Key] = pair.Value?.DeepClone();
            data["changedSignature"] = $"System.Boolean Nethermind.Int256.UInt256::Equals(System.Int{width})";
        }
        BigInteger Number(int start) => Enumerable.Range(0, 32).Select(i => (BigInteger)(data["initialBytes"]![(start + i).ToString(CultureInfo.InvariantCulture)]?.GetValue<int>() ?? 0) << (8 * i)).Aggregate(BigInteger.Zero, (a, b) => a + b);
        BigInteger left = Number(data["leftBase"]!.GetValue<int>()); bool equal;
        if (Catalog.Text(shape["kind"]) == "scalar")
        {
            int width = shape["width"]!.GetValue<int>();
            BigInteger bits = BigInteger.Parse(data["scalarBits"]!.ToString(), CultureInfo.InvariantCulture);
            if (Catalog.Text(shape["scalarKind"]).StartsWith('s') && bits >= BigInteger.One << (width - 1)) bits -= BigInteger.One << width;
            equal = left == bits;
        }
        else
        {
            BigInteger right = Number(data["rightBase"]!.GetValue<int>());
            data["snapshot"] ??= JsonNode.Parse(right.ToString(CultureInfo.InvariantCulture));
            equal = left == (Catalog.Text(shape["kind"]) == "snapshot" ? BigInteger.Parse(data["snapshot"]!.ToString(), CultureInfo.InvariantCulture) : right);
        }
        bool negate = shape["negate"]!.GetValue<bool>();
        data["expectedResult"] = equal != negate;
        data["actualResult"] ??= JsonValue.Create(data["actualEquality"]?.GetValue<bool>() != negate);
        if (data["actualResult"]!.GetValue<bool>() == data["expectedResult"]!.GetValue<bool>()) throw new InvalidOperationException("Equality witness does not contradict the complete contract");
        return data;
    }
}
