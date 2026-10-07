// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class SafetyCatalog
{
    internal sealed record Scalar(int Width, bool Signed, bool First, string Relation)
    {
        internal bool Negate => Relation == "Ne";
    }

    internal static readonly Dictionary<string, (int Width, bool First)> MultiplyPrimitives =
        (from width in new[] { 32, 64 } from first in new[] { false, true }
         select (Name: "OperatorMultiply" + (first ? $"UInt{width}UInt256" : $"UInt256UInt{width}"), Width: width, First: first))
        .ToDictionary(x => x.Name, x => (x.Width, x.First));
    internal static readonly HashSet<string> MultiplyMethods = ["Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256", .. MultiplyPrimitives.Keys];
    internal static readonly HashSet<string> ClassifiedMethods = ["Add", "Subtract", "AddOverflow", "SubtractUnderflow"];
    internal static readonly HashSet<string> Unary = ["Not", "OperatorNot"];
    internal static readonly Dictionary<string, (string Operation, string Symbol)> Bitwise =
        (from prefix in new[] { "", "Operator" }
         from item in new[] { ("Xor", "xor", "^^^"), ("And", "and", "&&&"), ("Or", "or", "|||") }
         select (Name: prefix + item.Item1, Operation: item.Item2, Symbol: item.Item3))
        .ToDictionary(x => x.Name, x => (x.Operation, x.Symbol));
    internal static readonly Dictionary<string, (string Relation, string Audit)> Comparisons = new()
    {
        ["LtUInt256UInt256"] = ("less", "FamilySafetyAudit"), ["GtUInt256UInt256"] = ("greater", "GreaterFamilySafetyAudit"),
        ["LeUInt256UInt256"] = ("less_equal", "LessEqualFamilySafetyAudit"), ["GeUInt256UInt256"] = ("greater_equal", "GreaterEqualFamilySafetyAudit")
    };
    internal static readonly Dictionary<string, Scalar> Operators = Scalars(["Eq", "Ne"]);
    internal static readonly Dictionary<string, Scalar> PrimitiveComparisons = Scalars(["Lt", "Le", "Gt", "Ge"]);

    private static Dictionary<string, Scalar> Scalars(string[] relations)
    {
        Dictionary<string, Scalar> result = [];
        foreach ((string name, int width, bool signed) in new[] { ("Int32", 32, true), ("UInt32", 32, false), ("Int64", 64, true), ("UInt64", 64, false) })
            foreach (bool first in new[] { false, true })
                foreach (string relation in relations)
                {
                    if (name == "UInt64" && first && relation == "Le") continue;
                    result[relation + (first ? name + "UInt256" : "UInt256" + name)] = new(width, signed, first, relation);
                }
        return result;
    }

    private static JsonArray Names(IEnumerable<string> names) => new(names.Select(x => (JsonNode?)JsonValue.Create(x)).ToArray());
    private static JsonObject Coverage(string condition, JsonObject? family = null, string kind = "feature-family")
    {
        JsonObject result = new() { ["kind"] = kind, ["condition"] = condition };
        if (family is not null) result["family"] = family;
        return result;
    }
    private static JsonObject AllProfiles() => Coverage("Every valid profile; actual extracted operations are profile-independent", kind: "all-profiles");
    private static JsonObject Storage(string profile) => Coverage("Every valid profile with the same vector256Accelerated flag",
        new() { ["vector256Accelerated"] = profile == "x64-vector256" });
    private static JsonObject Reference(string profile)
    {
        JsonObject family = new() { ["vector256Accelerated"] = profile == "x64-vector256" };
        if (profile != "x64-vector256") family["sse41"] = profile == "x64-sse41";
        return Coverage("Every valid profile with the same vector256Accelerated flag and, when false, sse41 flag", family);
    }
    private static JsonObject Comparison(string profile)
    {
        JsonObject family = new() { ["avx512FVL"] = profile == "x64-avx512" };
        if (profile != "x64-avx512")
        {
            family["avx2"] = profile == "x64-avx2";
            if (profile != "x64-avx2") family["vector256Accelerated"] = profile == "x64-vector256";
        }
        return Coverage("Every valid profile with " + string.Join(", ", family.Select(pair => pair.Key + (pair.Value!.GetValue<bool>() ? " enabled" : " disabled"))), family);
    }

    internal static JsonObject Representative(string method, string profile)
    {
        JsonObject Gate(string contract, string target, string ns, IEnumerable<string> names, JsonObject? coverage = null, bool generated = false)
        {
            JsonObject gate = new()
            {
                ["semanticsVersion"] = "cil-allocation-safety-1", ["contract"] = "UInt256Model.Safety." + contract,
                ["callingConditions"] = "UInt256Model.Safety.CallingConditions", ["target"] = "+UInt256.Methods." + target + ":olean",
                ["theorems"] = Names(names.Select(name => ns + "." + name)), ["profile"] = profile, ["method"] = method,
                ["runtimeBoundary"] = "Tracked managed references; no native-code, GC-root-map or concurrency proof"
            };
            if (coverage is not null) gate["coverage"] = coverage;
            if (generated) gate["generatedAudit"] = true;
            return gate;
        }
        JsonObject Generated(string contract, JsonObject coverage) => Gate(contract, "SelectedSafetyGate", "UInt256Proof.SafetySelected",
            ["checked_contract", "checked_binding", "checked_family_contract"], coverage, true);
        bool storageProfile = profile is "scalar" or "x64-vector256";
        if (MultiplyMethods.Contains(method) && Catalog.MultiplyProfiles.Contains(profile))
            return Generated(MultiplyPrimitives.ContainsKey(method) ? "OrderedScalarContract" : method.StartsWith("Operator", StringComparison.Ordinal)
                ? "ReadOnlyContract" : "WrappingBinaryContract", Coverage("Every valid profile with the same multiplication class and vector256 storage flag"));
        (string Audit, string Contract, string Binding, bool Returns)? shift = method switch
        {
            "Lsh" => ("", "shift", "shift", false), "Rsh" => ("Right", "shift", "right_shift", false),
            "LeftShift" => ("Wrapper", "wrapper", "wrapper", false), "RightShift" => ("RightWrapper", "wrapper", "right_wrapper", false),
            "OperatorLsh" => ("Return", "return", "return", true), "OperatorRsh" => ("RightReturn", "return", "right_return", true), _ => null
        };
        if (shift is { } s && storageProfile)
            return Gate(s.Returns ? "ReadOnlyScalarContract" : "ShiftContract", "Shift." + s.Audit + "SafetyAudit", "UInt256Proof.Shift.Safety",
                [$"checked_{s.Contract}_contract", $"checked_{s.Binding}_binding", $"checked_{s.Binding}_family_binding"], Storage(profile));
        if (method == "LeUInt64UInt256" && profile == "scalar")
            return Gate("ScalarValueContract", "Compare.PrimitiveValueSafetyAudit", "UInt256Proof.Compare.PrimitiveValueSafety",
                ["checked_contract", "checked_binding", "checked_family_contract"], AllProfiles());
        if (ClassifiedMethods.Contains(method) && Catalog.Profiles.Contains(profile) && !(method == "Add" && profile == "scalar"))
        {
            bool subtract = method is "Subtract" or "SubtractUnderflow";
            bool wrapping = method is "Add" or "Subtract";
            bool vector128 = profile is "x64-sse42" or "arm64-advsimd";
            bool vector = profile.StartsWith("x64-avx", StringComparison.Ordinal);
            string target, ns, contractName, binding;
            string operation = wrapping ? "wrapping" : "underflow";
            if (subtract)
            {
                ns = "UInt256Proof.Subtract.Safety";
                target = vector128 ? "Subtract.Vector128" + (wrapping ? "SafetyAudit" : "UnderflowSafetyAudit")
                    : vector ? "Subtract.Vector" + (wrapping ? "Wrapping" : "Underflow") + "SafetyAudit"
                    : "Subtract." + (wrapping ? "SafetyAudit" : "UnderflowSafetyAudit");
                string prefix = vector128 ? "vector128_" : vector ? "vector_" : "";
                contractName = $"checked_{prefix}{operation}_contract";
                binding = $"checked_{prefix}{operation}_binding";
            }
            else if (profile == "scalar")
            {
                ns = "UInt256Proof.Safety"; target = "Add.OverflowSafetyAudit";
                contractName = "checked_overflow_contract"; binding = "checked_overflow_binding";
            }
            else
            {
                ns = "UInt256Proof.Add.Safety";
                string prefix = vector ? "vector" : profile == "x64-sse42" ? "sse" : "arm";
                string title = vector ? "Vector" : prefix.ToUpperInvariant();
                target = "Add." + title + (wrapping ? "SafetyAudit" : "OverflowSafetyAudit");
                contractName = vector ? (wrapping ? "checked_vector_parent_contract" : "checked_vector_reporting_contract")
                    : $"checked_{prefix}_{(wrapping ? "add" : "overflow")}_contract";
                binding = $"checked_{prefix}_{(wrapping ? "add" : "overflow")}_binding";
            }
            return Gate(wrapping ? "WrappingBinaryContract" : "ReportingBinaryContract", target, ns, [contractName, binding]);
        }
        if (PrimitiveComparisons.ContainsKey(method) && profile == "scalar") return Generated("ScalarOperatorContract", AllProfiles());
        if (method is "CompareToUInt256Ref" or "CompareToUInt256Value" && profile == "scalar")
        {
            bool value = method == "CompareToUInt256Value";
            string proof = value ? "threeWayValue" : "threeWay";
            return Gate(value ? "ReadOnlyValueContract" : "ReadOnlyContract", "Compare.ThreeWay" + (value ? "Value" : "") + "SafetyAudit",
                "UInt256Proof.Compare.Safety", new[] { "contract", "binding", "family" }.Select(x => $"checked_{proof}_{x}"), AllProfiles());
        }
        if (Comparisons.TryGetValue(method, out var comparison) && profile is "scalar" or "x64-vector256" or "x64-avx2" or "x64-avx512")
            return Gate("ReadOnlyContract", "Compare." + (profile == "x64-vector256" ? "Portable" : profile == "x64-avx512" ? "Native" : "") + comparison.Audit,
                "UInt256Proof.Compare.Safety", new[] { "contract", "binding", "family" }.Select(x => $"checked_{comparison.Relation}_{x}"), Comparison(profile));
        if ((Bitwise.ContainsKey(method) || Unary.Contains(method)) && storageProfile)
            return Generated(method.StartsWith("Operator", StringComparison.Ordinal) ? "ReadOnlyContract" : Unary.Contains(method)
                ? "InitializedUnaryContract" : "WrappingBinaryContract", Storage(profile));
        if (Operators.ContainsKey(method) && storageProfile) return Generated("ScalarOperatorContract", Storage(profile));
        bool equalityMethod = method is "EqUInt256UInt256" or "EqualsUInt256Ref" or "NeUInt256UInt256" or "EqualsUInt256Value";
        bool primitive = method is "EqualsUInt64" or "EqualsUInt32";
        bool signed = method is "EqualsInt64" or "EqualsInt32";
        bool vectorEquality = (equalityMethod || primitive || signed) && profile == "x64-vector256";
        bool sse = equalityMethod && profile == "x64-sse41";
        bool scalar = profile == "scalar" && (method == "Add" || equalityMethod || primitive || signed);
        if (!(scalar || vectorEquality || sse)) throw new InvalidOperationException($"Combined safety proof not yet available: {method}/{profile}");
        bool equality = method != "Add", inequality = method == "NeUInt256UInt256", byValue = method == "EqualsUInt256Value";
        string theorem = inequality ? "checked_inequality" : equality ? "checked_equality" : "checked_add";
        string audit = (vectorEquality ? "Vector" : sse ? "Sse" : "") + (inequality ? "NegationSafetyAudit" : "SafetyAudit");
        string contract = byValue ? "ReadOnlyValueContract" : equality ? "ReadOnlyContract" : "WrappingBinaryContract";
        if (byValue) { theorem = "checked_value"; audit = (vectorEquality ? "Vector" : sse ? "Sse" : "") + "ValueSafetyAudit"; }
        if (primitive)
        {
            theorem = "checked_primitive"; contract = "ReadOnlyScalarContract";
            audit = vectorEquality ? (method == "EqualsUInt64" ? "VectorPrimitive64SafetyAudit" : "VectorPrimitive32SafetyAudit")
                : method == "EqualsUInt32" ? "Primitive32SafetyAudit" : "PrimitiveSafetyAudit";
        }
        if (signed)
        {
            theorem = "checked_signed"; contract = "ReadOnlyScalarContract";
            audit = (vectorEquality ? "Vector" : "") + (method == "EqualsInt64" ? "Signed64SafetyAudit" : "Signed32SafetyAudit");
        }
        List<string> names = [theorem + "_contract", theorem + "_binding"];
        JsonObject? coverage = null;
        if (primitive || signed || equalityMethod)
        {
            names.Add(theorem + "_family");
            coverage = primitive || signed ? Storage(profile) : Reference(profile);
        }
        return Gate(contract, (equality ? "Equality." : "Add.") + audit,
            equality ? "UInt256Proof.Equality.Safety" : "UInt256Proof.Safety", names, coverage);
    }

    internal static JsonObject Gate(string method, string profile)
    {
        JsonObject gate = Representative(method, profile);
        gate["alignmentPolicy"] = JsonNode.Parse("""
            {"id":"coreclr-x64-arm64-ordinary-1","ordinaryAccessBytes":1,"targetArchitectures":["x64","arm64"],
             "memory":"Normal managed, stack and immutable static storage; alignment traps disabled",
             "excluded":["aligned memory APIs","volatile or atomic accesses","device memory"],"portableCliGuarantee":false,
             "runtimeSourceEvidence":"dotnet/runtime@4271d88e0aebf3d04f188f1334c2220d80555ef6","boundary":"verification/CIL/Safety/ALIGNMENT.md"}
            """);
        gate["modelLimitations"] = JsonNode.Parse("""
            [{"kind":"instruction-alignment","status":"target-runtime-assumption",
              "detail":"Ordinary byte-aligned accesses use the stated CoreCLR memory convention; JIT correspondence is not kernel-proved",
              "boundary":"verification/CIL/Safety/ALIGNMENT.md"}]
            """);
        if (ClassifiedMethods.Contains(method) && Catalog.Profiles.Contains(profile))
        {
            gate["target"] = "+UInt256.Methods.SelectedSafetyGate:olean";
            gate["generatedAudit"] = true;
            gate["theorems"]!.AsArray().Add("UInt256Proof.SafetySelected.checked_family_contract");
            gate["coverage"] = Coverage("Every valid profile with the same checked FeatureClass");
        }
        return gate;
    }
}
