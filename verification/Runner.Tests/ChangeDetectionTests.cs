// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class ChangeDetectionTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("proof selection requires baseline evidence and treats non-source inputs conservatively", (_, _) =>
        {
            string paths = ""; List<string[]> commands = [];
            Workspace workspace = new(Directory.GetCurrentDirectory(), (command, _, _) => { commands.Add(command); return paths; });
            foreach (string baseline in new[] { "", new string('0', 40) }) Program.Require(ChangeDetection.NeedsProof(workspace, baseline).Required, "Missing baseline skipped");
            foreach (var (method, profile) in new[] { ("Unknown", "scalar"), ("Add", "unknown"), ("Add", "x64-bmi2") })
                Program.Reject(() => ChangeDetection.NeedsProof(workspace, "", method, profile));
            foreach (string changed in new[] { "", "src/UInt256.cs\0" })
            {
                paths = changed;
                Program.Require(ChangeDetection.NeedsProof(workspace, "base", evidence: (_, _, _) => false).Required, "Unverified baseline skipped");
            }
            paths = ""; bool selected = false;
            Program.Require(!ChangeDetection.NeedsProof(workspace, "base", "Subtract", "x64-avx2", (b, m, p) => selected = b == "base" && m == "Subtract" && p == "x64-avx2").Required && selected, "Wrong baseline selection");
            foreach (string path in new[] { "verification/CIL/Execution.lean", "verification/Extractor/Program.cs", "verification/Runner/ChangeDetection.cs", "src/Directory.Build.props", "global.json",
                ".github/workflows/verify-uint256-tests.yml", "verification/CIL/Features.lean", "verification/CIL/ProfileEquivalence.lean", "verification/Extractor/StaticData.cs", "verification/AggregateAudit.lean" })
                Program.Require(ChangeDetection.ProofInputsChanged(["src/UInt256.cs", path]), "Non-source input allowed a skip");
            Program.Require(!ChangeDetection.ProofInputsChanged(["src/UInt256.cs", "src/Helper.cs"]), "Ordinary C# changes cannot be compared");
            paths = "verification/Helper.cs\0src/Helper.cs\0";
            Program.Require(ChangeDetection.NeedsProof(workspace, "base", evidence: (_, _, _) => throw new InvalidOperationException("Must not request history")).Required
                && commands[^1].Contains("--no-renames"), "Rename hid verification input changes");
        });
        check("proof decisions compare both metadata and bytes using the selected dependency graph", (_, _) =>
        {
            foreach (var (method, profile) in Catalog.Profiles.Select(p => ("Subtract", p)).Append(("Add", "scalar")).Append(("LtUInt256UInt64", "x64-bmi2")))
            foreach (string change in new[] { "", "metadata", "program", "extraction", "sdk" })
            {
                List<string[]> commands = []; int extracted = 0;
                Workspace workspace = new(Directory.GetCurrentDirectory(), (command, _, _) =>
                {
                    commands.Add(command);
                    return command.Contains("diff") ? "src/UInt256.cs\0" : command.Contains("--version") ? change == "sdk" ? "wrong" : "10.0.401" : "";
                });
                (JsonObject, byte[]) Extract(string source, string work, string tool, string m, string p)
                {
                    Program.Require(m == method && p == profile, "Wrong selected graph"); extracted++;
                    if (change == "extraction") throw new InvalidOperationException("unsupported reachable instruction");
                    return (new JsonObject { ["layout"] = change == "metadata" && extracted == 2 ? 64 : 32 }, [change == "program" && extracted == 2 ? (byte)2 : (byte)1]);
                }
                if (change is "extraction" or "sdk") Program.Reject(() => ChangeDetection.NeedsProof(workspace, "base", method, profile, (_, _, _) => true, Extract));
                else Program.Require(ChangeDetection.NeedsProof(workspace, "base", method, profile, (_, _, _) => true, Extract).Required == (change != "") && extracted == 2, "Wrong proof decision");
                if (change != "sdk") Program.Require(commands.Any(c => c.Contains("checkout") && c.Contains("--detach") && c[^1] == "base"), "Baseline was not checked out exactly");
            }
        });
        check("change CLI validates selectors before forced runs and appends GitHub outputs", (_, manifests) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            string output = Path.Combine(Path.GetDirectoryName(manifests)!, "output"), summary = output + "-summary";
            Dictionary<string, string> env = new() { ["GITHUB_OUTPUT"] = output, ["GITHUB_STEP_SUMMARY"] = summary, ["VERIFY_BASE"] = "base" };
            string? Environment(string name) => env.GetValueOrDefault(name);
            foreach (string mode in new[] { "workflow_dispatch", "pull_request" })
            {
                env["VERIFY_EVENT"] = mode; env["VERIFY_BASE_BRANCH"] = "feature";
                ChangeDetection.Run(workspace, [], Environment, (_, _, _) => throw new InvalidOperationException("Forced proof must not compare"));
            }
            Program.Require(File.ReadAllText(output) == "required=true\nrequired=true\n", "Forced runs did not append required output");
            Program.Require(File.ReadAllText(summary).Contains("Production proof required:", StringComparison.Ordinal), "Required summary missing");
            env["VERIFY_EVENT"] = "push"; bool selected = false;
            ChangeDetection.Run(workspace, ["--method", "Subtract", "--profile", "x64-avx512-bmi1"], Environment, (b, m, p) =>
            { selected = b == "base" && m == "Subtract" && p == "x64-avx512-bmi1"; return (false, "Selected profile"); });
            Program.Require(selected && File.ReadAllText(output).EndsWith("required=false\n", StringComparison.Ordinal) && File.ReadAllText(summary).EndsWith("Production proof skipped: Selected profile.\n", StringComparison.Ordinal), "Selected profile/skip outputs changed");
            env["VERIFY_EVENT"] = "workflow_dispatch";
            foreach (string[] args in new[] { new[] { "--profile", "unknown" }, ["--profile", "x64-bmi2"], ["--method", "Unknown"], ["--method"], ["--unknown", "value"] })
                Program.Reject(() => ChangeDetection.Run(workspace, args, Environment));
        });
        check("change comparison ignores only assembly identity and method tokens", (_, _) =>
        {
            JsonObject baseline = JsonNode.Parse("""{"sha256":"old","assembly":"version1","layout":{"ClassSize":32},"methods":[{"token":1,"signature":"Add","instructions":["add"]},{"token":2,"signature":"Helper","instructions":["add"]}]}""")!.AsObject();
            JsonObject identity = baseline.DeepClone().AsObject(); identity["sha256"] = "new"; identity["assembly"] = "version2"; identity["methods"]![0]!["token"] = 100;
            Program.Require(JsonNode.DeepEquals(ChangeDetection.ComparisonArtifact(baseline), ChangeDetection.ComparisonArtifact(identity)), "Assembly/token changes altered comparison");
            foreach (Action<JsonObject> mutate in new Action<JsonObject>[] { a => a["layout"]!["ClassSize"] = 64,
                a => a["methods"]![1]!["instructions"] = new JsonArray("sub"), a => a["methods"]!.AsArray().Add(new JsonObject { ["signature"] = "NewHelper" }) })
            {
                var changed = baseline.DeepClone().AsObject(); mutate(changed);
                Program.Require(!JsonNode.DeepEquals(ChangeDetection.ComparisonArtifact(baseline), ChangeDetection.ComparisonArtifact(changed)), "Semantic metadata ignored");
            }
            Program.Require(baseline["methods"]![0]!.AsObject().ContainsKey("token"), "Comparison mutated its input");
        });
        check("change comparison retains profile, static data and exact intrinsic operands", (_, _) =>
        {
            JsonObject baseline = JsonNode.Parse("""{"sha256":"old","assembly":"version1","profile":{"Name":"x64-avx2","Bmi1":false},"queriedFeatures":["Avx2"],"staticData":[{"bytes":"0100","size":2,"packing":1}],"methods":[{"token":1,"signature":"Add","instructions":[{"opcode":"call","operand":"Avx2::Permute4x64","scope":"System.Runtime.Intrinsics"},{"opcode":"ldc.i4","operand":"144"}]}]}""")!.AsObject();
            foreach (Action<JsonObject> mutate in new Action<JsonObject>[] { a => a["profile"]!["Name"] = "x64-avx512", a => a["profile"]!["Bmi1"] = true,
                a => a["queriedFeatures"]!.AsArray().Add("Bmi1"), a => a["staticData"]![0]!["bytes"] = "0000", a => a["staticData"]![0]!["packing"] = 8,
                a => a["methods"]![0]!["instructions"]![0]!["operand"] = "Avx2::Blend", a => a["methods"]![0]!["instructions"]![0]!["scope"] = "Other.Assembly",
                a => a["methods"]![0]!["instructions"]![1]!["operand"] = "145" })
            {
                var changed = baseline.DeepClone().AsObject(); mutate(changed);
                Program.Require(!JsonNode.DeepEquals(ChangeDetection.ComparisonArtifact(baseline), ChangeDetection.ComparisonArtifact(changed)), "Profile/static/intrinsic metadata ignored");
            }
        });
        check("change extraction binds exact API, complete profile, calling convention and generated bytes", (_, manifests) =>
        {
            string work = Path.Combine(Path.GetDirectoryName(manifests)!, "extraction"), generated = Path.Combine(work, "generated");
            Directory.CreateDirectory(generated);
            List<string[]> calls = [];
            Workspace workspace = new(Directory.GetCurrentDirectory(), (command, _, _) => { calls.Add(command); return ""; });
            foreach (var (method, profile) in new[] { ("Add", "scalar"), ("Subtract", "x64-avx2"), ("LtUInt256UInt64", "x64-bmi2") })
            {
                JsonObject manifest = workspace.Catalog.Manifest(method);
                JsonObject body = new() { ["signature"] = manifest["entry"]!.DeepClone() };
                if (!Catalog.Legacy.Contains(method))
                {
                    JsonNode convention = manifest["callingConvention"]!;
                    body["isStatic"] = convention["static"]!.DeepClone(); body["returnType"] = convention["returns"]!.DeepClone(); body["hasThis"] = !convention["static"]!.GetValue<bool>();
                    body["parameters"] = new JsonArray(convention["parameters"]!.AsArray().Select(p => (JsonNode)new JsonObject { ["type"] = p!["type"]!.DeepClone(), ["IsIn"] = p["isIn"]!.DeepClone(), ["IsOut"] = p["isOut"]!.DeepClone() }).ToArray());
                }
                JsonObject original = new() { ["profile"] = workspace.Catalog.Profile(profile), ["entryIndex"] = 0, ["methods"] = new JsonArray(body) };
                File.WriteAllBytes(Path.Combine(generated, "Extracted.lean"), [0, 255, 13, 10]);
                string[] failures = ["", "profile-name", "profile-feature", "method", .. Catalog.Legacy.Contains(method) ? Array.Empty<string>() : ["direction"]];
                foreach (string failure in failures)
                {
                    JsonObject artifact = original.DeepClone().AsObject();
                    switch (failure)
                    {
                        case "profile-name": artifact["profile"]!["Name"] = "wrong"; break;
                        case "profile-feature": artifact["profile"]!["Bmi2"] = !artifact["profile"]!["Bmi2"]!.GetValue<bool>(); break;
                        case "method": artifact["methods"]![0]!["signature"] = "Other"; break;
                        case "direction": artifact["methods"]![0]!["parameters"]![0]!["IsIn"] = false; break;
                    }
                    File.WriteAllText(Path.Combine(generated, "artifact.json"), artifact.ToJsonString());
                    if (failure != "") Program.Reject(() => ChangeDetection.Extract(workspace, workspace.Root, work, "extractor.dll", method, profile));
                    else
                    {
                        var result = ChangeDetection.Extract(workspace, workspace.Root, work, "extractor.dll", method, profile);
                        Program.Require(result.Program.SequenceEqual(new byte[] { 0, 255, 13, 10 }), "Generated bytes were normalized");
                    }
                    string[] selection = calls[^1];
                    if (Catalog.Legacy.Contains(method)) Program.Require(selection.TakeLast(2).SequenceEqual(new[] { method, profile }), "Wrong legacy selection");
                    else Program.Require(selection.TakeLast(3).SequenceEqual(new[] { Catalog.Text(manifest["entry"]), "@" + Path.Combine(workspace.Verification, $"manifests/profiles/{profile}.json"), Path.Combine(workspace.Verification, "manifests/api-coverage.json") }), "Wrong exact selection");
                }
            }
            Program.Reject(() => ChangeDetection.Extract(workspace, workspace.Root, work, "extractor.dll", "Add", "x64-bmi2"));
        });
    }
}
