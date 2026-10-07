// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class GateTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        void Changed(string method, string label, Action<JsonObject> change) => check($"gate rejects {method}: {label}", (catalog, _) =>
        {
            JsonObject entry = catalog.Entries()[method];
            change(entry);
            Program.Reject(() => AuditGates.Module(entry));
        });
        void Descriptor(string method, string key, JsonNode? value) => Changed(method, key + "=" + value, entry =>
            entry["verification"]!["template"]![key] = value?.DeepClone());

        check("generate every registered arithmetic gate", (catalog, _) =>
        {
            foreach (JsonObject entry in catalog.Entries().Values)
            {
                string text = AuditGates.Module(entry);
                Program.Require(text.Contains("#print axioms", StringComparison.Ordinal), "Missing axiom audit");
                Program.Require(!text.Contains('\r'), "Generated Lean must have stable LF endings");
            }
        });
        check("scalar comparison width, direction and signedness", (catalog, _) =>
        {
            string text = AuditGates.Module(catalog.Entries()["LtUInt256UInt64"]);
            foreach (string part in new[] { "(word : W64)", "(.u64 word) false", ".less", "#print axioms checked_profile_contract" })
                Program.Require(text.Contains(part, StringComparison.Ordinal), part);
        });
        foreach ((string key, JsonNode value) in new (string, JsonNode)[]
        {
            ("relation", JsonValue.Create("greater")!), ("scalarKind", JsonValue.Create("u32")!),
            ("scalarKind", JsonValue.Create("s64")!), ("scalarFirst", JsonValue.Create(true)!),
            ("relation", JsonValue.Create("less; sorry")!), ("proof", JsonValue.Create("sorry")!),
            ("scalarFirst", JsonValue.Create(0)!)
        }) Descriptor("LtUInt256UInt64", key, value);
        Changed("LtUInt256UInt64", "by-value operand", entry =>
            entry["callingConvention"]!["parameters"]![0]!["type"] = "Nethermind.Int256.UInt256");
        foreach (JsonNode? malformed in new JsonNode?[] { null, new JsonArray(), JsonValue.Create("scalar-comparison") })
            Changed("LtUInt256UInt64", "malformed descriptor " + malformed, entry => entry["verification"]!["template"] = malformed?.DeepClone());

        Descriptor("And", "operation", JsonValue.Create("or"));
        check("binary bitwise arithmetic binding", (catalog, _) =>
        {
            string text = AuditGates.Module(catalog.Entries()["And"]);
            Program.Require(text.Contains("Extracted.entryIndex .and", StringComparison.Ordinal), text);
            Program.Require(text.Contains("UInt256Proof.Bitwise.value_and", StringComparison.Ordinal), text);
        });
        Changed("And", "output direction", entry => entry["callingConvention"]!["parameters"]![2]!["isOut"] = false);
        Changed("And", "unproved all-profile claim", entry => entry["verification"]!["allProfiles"] = true);
        check("returning bitwise operation and storage family", (catalog, _) =>
        {
            foreach ((string name, string operation) in new[] { ("OperatorXor", "xor"), ("OperatorAnd", "and"), ("OperatorOr", "or"), ("OperatorNot", "not") })
            {
                string text = AuditGates.Module(catalog.Entries()[name]);
                Program.Require(text.Contains(operation == "not" ? "Bitwise.NotReturnContract" : $"Extracted.entryIndex .{operation}", StringComparison.Ordinal), name);
                Program.Require(text.Contains(operation == "not" ? "not_bitwise_return_execute initial, input" : $"Bitwise.value_{operation}", StringComparison.Ordinal), name);
                Program.Require(text.Contains("#print axioms checked_family_contract", StringComparison.Ordinal), name);
                Program.Require(text.Contains("storage_profile_agreement Extracted.program (by decide)", StringComparison.Ordinal), name);
            }
        });
        foreach (string method in new[] { "OperatorXor", "EqUInt256UInt64" })
        {
            Changed(method, "return type", entry => entry["callingConvention"]!["returns"] = "System.Void");
            Changed(method, "receiver", entry => entry["callingConvention"]!["static"] = false);
            Changed(method, "by-value", entry => entry["callingConvention"]!["parameters"]![0]!["type"] = "Nethermind.Int256.UInt256");
            Changed(method, "input direction", entry => entry["callingConvention"]!["parameters"]![0]!["isIn"] = false);
            Changed(method, "output direction", entry => entry["callingConvention"]!["parameters"]![0]!["isOut"] = true);
        }
        Descriptor("OperatorXor", "operation", JsonValue.Create("and"));
        Descriptor("OperatorXor", "operation", JsonValue.Create("xor; sorry"));
        foreach ((string key, JsonNode value) in new (string, JsonNode)[]
        {
            ("scalarKind", JsonValue.Create("s64")!), ("scalarKind", JsonValue.Create("u32")!),
            ("scalarKind", JsonValue.Create("u64; sorry")!), ("scalarFirst", JsonValue.Create(0)!),
            ("proof", JsonValue.Create("sorry")!)
        }) Descriptor("EqUInt256UInt64", key, value);
        Changed("EqUInt256UInt64", "unproved all-profile claim", entry => entry["verification"]!["allProfiles"] = true);
        foreach ((string scalar, string kind, string width) in new[]
        {
            ("UInt32", "u32", "W32"), ("UInt64", "u64", "W64"), ("Int32", "s32", "W32"), ("Int64", "s64", "W64")
        })
        {
            List<(string Name, bool First, bool Negate)> cases = [("Equals" + scalar, false, false)];
            foreach (string op in new[] { "Eq", "Ne" })
                foreach (bool first in new[] { false, true })
                    cases.Add(($"{op}{(first ? scalar : "UInt256")}{(first ? "UInt256" : scalar)}", first, op == "Ne"));
            foreach (var item in cases)
            {
                check("primitive equality " + item.Name, (catalog, _) =>
                {
                    JsonObject entry = catalog.Entries()[item.Name];
                    string text = AuditGates.Module(entry);
                    foreach (string part in new[] { $"(word : {width})", $"(.{kind} word) {item.First.ToString().ToLowerInvariant()} {item.Negate.ToString().ToLowerInvariant()}",
                        "Equality.ScalarContract", "#print axioms checked_family_contract", "storage_profile_agreement Extracted.program (by decide)" })
                        Program.Require(text.Contains(part, StringComparison.Ordinal), part);
                    foreach (string key in new[] { "scalarFirst", "instance", "negateResult" })
                    {
                        JsonObject changed = entry.DeepClone().AsObject();
                        changed["verification"]!["template"]![key] = !changed["verification"]!["template"]![key]!.GetValue<bool>();
                        Program.Reject(() => AuditGates.Module(changed));
                    }
                });
            }
        }
        check("handwritten contracts ignore manifest prose", (catalog, _) =>
        {
            foreach (JsonObject entry in catalog.Entries().Values.Where(entry => !entry["verification"]!.AsObject().ContainsKey("template")))
            {
                string original = AuditGates.Module(entry);
                entry["verification"]!["contract"] = "True";
                Program.Require(AuditGates.Module(entry) == original, "Manifest prose replaced an independent contract");
                foreach (string name in AuditGates.BoundAuditNames(entry))
                    Program.Require(original.Contains("#print axioms " + name.Split('.').Last(), StringComparison.Ordinal), name);
            }
        });
        check("relational family retains dispatch guards", (catalog, _) =>
        {
            JsonObject entry = catalog.Entries()["LtUInt256UInt256"];
            entry["verification"]!["contract"] = "True";
            string text = AuditGates.Module(entry);
            foreach (string part in new[] {
                "UInt256Model.Compare.Contract (reprofile Extracted.program profile)",
                "Extracted.entryIndex .less initial left right",
                "Extracted.profile.avx512FVL = profile.avx512FVL",
                "Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2",
                "Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → Extracted.profile.vector256Accelerated = profile.vector256Accelerated",
                "#print axioms bound_family_contract" })
                Program.Require(text.Contains(part, StringComparison.Ordinal), part);
        });
        check("independent handwritten contract types", (catalog, _) =>
        {
            foreach ((string name, string contract) in new[] {
                ("Lsh", "UInt256Proof.Shift.Contract .left"), ("OperatorRsh", "UInt256Proof.Shift.OperatorContract .right"),
                ("AddOverflow", "UInt256Proof.Reporting.Contract .add"), ("EqualsUInt256Value", "UInt256Model.Equality.SnapshotContract"),
                ("CompareToUInt256Ref", "UInt256Model.Compare.ThreeWayContract"), ("CompareToUInt256Value", "UInt256Model.Compare.ThreeWaySnapshotContract"),
                ("Multiply", "UInt256Proof.Multiply.Contract"), ("MultiplyInstance", "UInt256Proof.Multiply.Contract"),
                ("OperatorMultiplyUInt256UInt256", "UInt256Proof.Multiply.ReturnContract"),
                ("OperatorMultiplyUInt256UInt64", "UInt256Proof.Multiply.ScalarReturnContract"),
                ("OperatorMultiplyUInt64UInt256", "UInt256Proof.Multiply.ScalarReturnContract"),
                ("OperatorMultiplyUInt256UInt32", "UInt256Proof.Multiply.ScalarReturnContract"),
                ("OperatorMultiplyUInt32UInt256", "UInt256Proof.Multiply.ScalarReturnContract") })
            {
                JsonObject entry = catalog.Entries()[name];
                entry["verification"]!["contract"] = "True";
                string text = AuditGates.Module(entry);
                Program.Require(text.Contains(contract, StringComparison.Ordinal), name);
                Program.Require(text.Contains("#print axioms bound_contract", StringComparison.Ordinal), name);
                Program.Require(text.Contains(entry["verification"]!["auditedTheorems"]![0]!.GetValue<string>(), StringComparison.Ordinal), name);
                if (name is "CompareToUInt256Value" or "EqualsUInt256Value")
                    Program.Require(text.Contains("(right : BitVec 256)", StringComparison.Ordinal), name);
                if (name.StartsWith("OperatorMultiply", StringComparison.Ordinal) && name != "OperatorMultiplyUInt256UInt256")
                {
                    int width = name.Contains("UInt32", StringComparison.Ordinal) ? 32 : 64;
                    string first = name.StartsWith("OperatorMultiplyUInt256", StringComparison.Ordinal) ? "false" : "true";
                    Program.Require(text.Contains($"(word : W{width})", StringComparison.Ordinal), name);
                    Program.Require(text.Contains($"{width} {first} initial input word", StringComparison.Ordinal), name);
                }
                JsonNode? family = entry["verification"]!["familyCoverage"];
                Program.Require(text.Contains(family is null ? "#print axioms bound_all_profiles_contract" : "#print axioms bound_family_contract", StringComparison.Ordinal), name);
                if (family is not null) Program.Require(text.Contains(family["theorem"]!.GetValue<string>(), StringComparison.Ordinal), name);
            }
        });
        Changed("Lsh", "module injection", entry => entry["verification"]!["auditTarget"] = "+Bad\nimport Evil:olean");
        Changed("Lsh", "module trailing newline", entry => entry["verification"]!["auditTarget"] = "+Bad:olean\n");
        Changed("Lsh", "theorem injection", entry => entry["verification"]!["auditedTheorems"] = new JsonArray("True.intro; sorry"));
        Changed("Lsh", "theorem trailing newline", entry => entry["verification"]!["auditedTheorems"] = new JsonArray("True.intro\n"));
    }
}
