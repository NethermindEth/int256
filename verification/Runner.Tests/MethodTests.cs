// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Xml.Linq;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class MethodTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("method proof snapshots observe changed and removed sources without caching", (_, manifests) =>
        {
            string root = Path.Combine(Path.GetDirectoryName(manifests)!, "snapshot");
            Directory.CreateDirectory(Path.Combine(root, "verification"));
            foreach (string name in new[] { "global.json", ".editorconfig", "verification/lean-toolchain", "verification/Test.lean" }) File.WriteAllText(Path.Combine(root, name), "initial");
            Workspace workspace = new(root); var inputs = workspace.Inputs();
            string source = Path.Combine(workspace.Verification, "Test.lean");
            Program.Require(Workspace.CheckProofSnapshot(workspace.Verification, ["Test.lean"], inputs)["Test.lean"] == Workspace.Hash(source), "Snapshot identity changed");
            File.WriteAllText(source, "changed");
            Program.Require(workspace.Inputs()["verification/Test.lean"] != inputs["verification/Test.lean"], "Changed source cached");
            Program.Reject(() => Workspace.CheckProofSnapshot(workspace.Verification, ["Test.lean"], inputs));
            File.Delete(source);
            Program.Require(!workspace.Inputs().ContainsKey("verification/Test.lean"), "Deleted source cached");
            bool missingRejected = false;
            try { Workspace.CheckProofSnapshot(workspace.Verification, ["Test.lean"], inputs); }
            catch (FileNotFoundException) { missingRejected = true; }
            Program.Require(missingRejected, "Missing proof source accepted");
        });
        check("method family coverage retains every ordered representative and audited premise", (catalog, _) =>
        {
            foreach (string method in new[] { "Multiply", "LtUInt256UInt256" })
            {
                string[] representatives = method == "Multiply" ? Catalog.MultiplyProfiles : ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"];
                foreach (string[] actual in new[] { representatives, representatives[..^1], representatives.Reverse().ToArray(), representatives.Where((_, i) => i % 2 == 0).ToArray() })
                {
                    JsonObject entry = catalog.Entries()[method].DeepClone().AsObject();
                    entry["verification"]!["familyCoverage"]!["representatives"] = new JsonArray(actual.Select(s => (JsonNode)JsonValue.Create(s)!).ToArray());
                    if (actual.SequenceEqual(representatives)) catalog.Manifest(entry); else Program.Reject(() => catalog.Manifest(entry));
                }
            }
            foreach (string mutation in new[] { "unaudited", "one-profile", "unknown-kind", "nonstring-kind", "unknown-field", "universal" })
            {
                JsonObject entry = catalog.Entries()["Lsh"].DeepClone().AsObject(); JsonNode gate = entry["verification"]!, family = gate["familyCoverage"]!;
                switch (mutation)
                {
                    case "unaudited": family["theorem"] = "Unchecked"; break;
                    case "one-profile": family["representatives"] = new JsonArray("scalar"); break;
                    case "unknown-kind": family["kind"] = "assumed"; break;
                    case "nonstring-kind": family["kind"] = new JsonArray(); break;
                    case "unknown-field": family["assumption"] = true; break;
                    case "universal": gate["allProfiles"] = true; gate["profileCoverage"] = "all-valid-profiles"; gate["allProfilesTheorem"] = gate["auditedTheorems"]![1]!.DeepClone(); break;
                }
                Program.Reject(() => catalog.Manifest(entry));
            }
            foreach (string mutation in new[] { "missing", "unaudited", "duplicate", "nonboolean" })
            {
                JsonObject entry = catalog.Entries()["LtUInt256UInt64"].DeepClone().AsObject(), gate = entry["verification"]!.AsObject();
                switch (mutation)
                {
                    case "missing": gate.Remove("allProfilesTheorem"); break;
                    case "unaudited": gate["allProfilesTheorem"] = "UInt256Proof.Unchecked"; break;
                    case "duplicate": gate["allProfilesTheorem"] = gate["auditedTheorems"]![0]!.DeepClone(); gate["auditedTheorems"] = new JsonArray(gate["allProfilesTheorem"]!.DeepClone(), gate["allProfilesTheorem"]!.DeepClone()); break;
                    case "nonboolean": gate["allProfiles"] = 1; break;
                }
                Program.Reject(() => catalog.Manifest(entry));
            }
        });
        check("shared equality fixture metadata matches the compiled registry and rejects overrides", (catalog, _) =>
        {
            string directory = Path.Combine(Directory.GetCurrentDirectory(), "verification/Tests/Fixtures/Equality");
            string[] cases = XDocument.Load(Path.Combine(directory, "Cases.props")).Descendants("EqualityCase").Select(e => (string)e.Attribute("Include")!).ToArray();
            var entries = catalog.Entries().Values.Where(e => e["verification"]?["fixtureGroup"]?.GetValue<string>() == "Equality").ToArray();
            Program.Require(entries.Length == 24 && File.Exists(Path.Combine(directory, "Public.cs")), "Shared equality coverage/source missing");
            foreach (JsonObject entry in entries)
            {
                var gate = entry["verification"]!;
                Program.Require(gate["fixtureCases"]!.AsArray().Select(Catalog.Text).SequenceEqual(cases), "Fixture registry mismatch");
                Program.Require(gate["fixtureSources"]!.AsObject().Count == cases.Length && cases.All(c => Catalog.Text(gate["fixtureSources"]![c]) == "Public.cs"), "Fixture source mapping mismatch");
            }
            foreach (var (names, overridden) in new[] { (new[] { "Baseline", "Baseline" }, false), (new[] { "Baseline" }, true), (Array.Empty<string>(), false) })
            {
                JsonObject entry = new() { ["id"] = "EqUInt256UInt256", ["verification"] = new JsonObject { ["fixtureGroup"] = "Equality" } };
                JsonArray values = new(names.Select(s => (JsonNode)JsonValue.Create(s)!).ToArray());
                if (overridden) entry["verification"]!["fixtureCases"] = values.DeepClone();
                Program.Reject(() => Catalog.ResolveFixtureGroups([entry], new JsonObject { ["Equality"] = new JsonObject { ["cases"] = values, ["source"] = "Public.cs" } }));
            }
        });
        check("actual refutation templates remain freshness inputs and report paths remain distinct", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory()); var inputs = workspace.Inputs();
            foreach (string relative in new[] { "Compare/RefutationTemplate.lean.in", "Bitwise/RefutationTemplate.lean.in", "Shift/RefutationTemplate.lean.in", "Shift/OperatorRefutationTemplate.lean.in" })
            {
                string path = "verification/Tests/Fixtures/" + relative;
                Program.Require(inputs[path] == Workspace.Hash(Path.Combine(workspace.Root, path)), "Template omitted from freshness inputs");
            }
            Verifier verifier = new(workspace);
            foreach (string method in new[] { "../Add", "Unknown", "System.Void::Add" }) Program.Reject(() => verifier.OutputDirectory(method));
            string[] directories = workspace.Catalog.MethodNames.Select(m => verifier.OutputDirectory(m)).ToArray();
            Program.Require(directories.Distinct().Count() == directories.Length, "Distinct entries share reports");
        });
        check("named axiom audits accept wrapped and axiom-free output without hiding errors", (_, _) =>
        {
            const string name = "UInt256Proof.Compare.checked_three_way_all_profiles_contract";
            string[] approved = ["propext", "Classical.choice", "Quot.sound"];
            Program.Require(ProofAudits.Check($"info: Audit.lean:1:0: '{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n", [name], approved)[name].SequenceEqual(approved), "Wrapped audit rejected");
            Program.Require(ProofAudits.Check($"'{name}' does not depend on any axioms", [name], approved)[name].Length == 0, "Axiom-free audit rejected");
            foreach (string output in new[] { "'Gate' depends on axioms: [propext,\n sorryAx]", "'Gate' depends on axioms: [propext,\n propext]",
                "'Gate' depends on axioms: [propext,\nerror: missing close\n]", "'Gate' depends on axioms: [propext]\n'Gate' depends on axioms: [propext]" })
                Program.Reject(() => ProofAudits.Check(output, ["Gate"], ["propext"]));
        });
    }
}
