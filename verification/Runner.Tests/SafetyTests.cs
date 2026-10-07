// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class SafetyTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("safety registry exactly covers the production plan", (catalog, _) =>
        {
            HashSet<string> planned = catalog.Plan(catalog.MethodNames, safety: true)["include"]!.AsArray()
                .Select(job => Catalog.Text(job!["method"]) + "/" + Catalog.Text(job["profile"])).ToHashSet();
            Program.Require(planned.Count == 256, "Incomplete safety plan");
            foreach (string method in catalog.MethodNames.Append("Unknown"))
                foreach (string profile in catalog.ProfileNames.Append("unknown"))
                {
                    if (!planned.Contains(method + "/" + profile))
                    {
                        Program.Reject(() => SafetyCatalog.Gate(method, profile));
                        Program.Reject(() => SafetyGates.Module(catalog, method, profile));
                        continue;
                    }
                    JsonObject gate = SafetyCatalog.Gate(method, profile);
                    Program.Require(Catalog.Text(gate["method"]) == method && Catalog.Text(gate["profile"]) == profile, "Wrong identity");
                    Program.Require(gate["alignmentPolicy"]!["ordinaryAccessBytes"]!.GetValue<int>() == 1, "Arbitrary byte alignment lost");
                    Program.Require(!gate["alignmentPolicy"]!["portableCliGuarantee"]!.GetValue<bool>(), "Runtime assumption became a portable guarantee");
                    Program.Require(Catalog.Text(gate["modelLimitations"]![0]!["status"]) == "target-runtime-assumption", "Runtime limitation lost");
                    if (gate["generatedAudit"]?.GetValue<bool>() == true)
                    {
                        string text = SafetyGates.Module(catalog, method, profile);
                        Program.Require(!text.Contains('\r') && text.EndsWith('\n'), "Unstable line endings");
                        Program.Require(text.Contains("#print axioms checked_family_contract", StringComparison.Ordinal), "Family theorem unaudited");
                        Program.Require(text.Contains("Extracted.entryIndex", StringComparison.Ordinal), "Missing extracted entry binding");
                    }
                    else Program.Reject(() => SafetyGates.Module(catalog, method, profile));
                }
        });
        check("classified safety retains representative audits and guarded family transfer", (catalog, _) =>
        {
            foreach (string method in SafetyCatalog.ClassifiedMethods)
                foreach (string profile in Catalog.Profiles)
                {
                    JsonArray original = SafetyCatalog.Representative(method, profile)["theorems"]!.AsArray();
                    JsonArray names = SafetyCatalog.Gate(method, profile)["theorems"]!.AsArray();
                    Program.Require(names.Count == original.Count + 1 && names.Take(original.Count).Select(Catalog.Text).SequenceEqual(original.Select(Catalog.Text)), "Representative audit lost");
                    string text = SafetyGates.Module(catalog, method, profile);
                    Program.Require(text.Contains("same : profile.classify = Extracted.profile.classify", StringComparison.Ordinal), "Unconditional family transfer");
                    if (method is "AddOverflow" or "SubtractUnderflow")
                        Program.Require(text.Contains(method == "AddOverflow" ? "2^256 ≤ left.toNat + right.toNat" : "left.toNat < right.toNat", StringComparison.Ordinal), "Wrong reporting flag");
                }
        });
        check("scalar safety embeds width, order, signedness and polarity", (catalog, _) =>
        {
            Program.Require(SafetyCatalog.Operators.Count == 16 && SafetyCatalog.PrimitiveComparisons.Count == 31, "Scalar registry incomplete");
            foreach ((string method, SafetyCatalog.Scalar scalar) in SafetyCatalog.Operators.Concat(SafetyCatalog.PrimitiveComparisons))
            {
                string text = SafetyGates.Module(catalog, method, "scalar");
                string first = scalar.First ? "true" : "false", negate = scalar.Negate ? "true" : "false";
                Program.Require(text.Contains($"ScalarOperatorContract {first} {negate} CIL.Value.i{scalar.Width}", StringComparison.Ordinal), method);
                Program.Require(text.Contains(scalar.Signed ? ".toInt" : ".toNat : Int", StringComparison.Ordinal), method);
            }
        });
    }
}
