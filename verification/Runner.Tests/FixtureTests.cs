// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class FixtureTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("legacy fixture extraction preserves build flags and selected method", (_, manifests) =>
        {
            string root = Path.GetDirectoryName(manifests)!, destination = Path.Combine(root, "fixture");
            string source = Path.Combine(destination, "verification/Tests/Fixtures/Subtract/WrongBorrow.cs");
            Directory.CreateDirectory(Path.GetDirectoryName(source)!); File.WriteAllText(source, "fixture");
            int builds = 0, extracts = 0;
            Workspace workspace = new(root, (command, cwd, stage) =>
            {
                if (stage == "Fixture build")
                {
                    builds++;
                    Program.Require(cwd == destination && Path.GetFullPath(command.Single(argument => argument.StartsWith("-p:FixtureSource=", StringComparison.Ordinal))[17..]) == Path.GetFullPath(source) && command.Contains("-p:FixtureMethod=Subtract")
                        && command.Contains("-p:EnforceCodeStyleInBuild=true") && command.Contains("-p:GenerateDocumentationFile=true"), "Fixture build scope changed");
                }
                else
                {
                    extracts++;
                    Program.Require(cwd == root && command[^1] == "Subtract" && command.Contains(Path.Combine(root, "verification", "Extractor")), "Fixture extraction scope changed");
                }
                return "extracted";
            });
            var result = FixtureChecks.BuildExtract(workspace, destination, "WrongBorrow", "Subtract");
            Program.Require(builds == 1 && extracts == 1 && result.Output == "extracted", "Missing extraction output");
            Program.Reject(() => FixtureChecks.BuildFixture(workspace, destination, "Missing", "Subtract"));
        });
        check("legacy prerequisite rejects stale and fixture certificates", (catalog, manifests) =>
        {
            string root = Path.GetDirectoryName(manifests)!;
            Workspace workspace = VerifierTests.Setup(catalog, manifests);
            string generated = Path.Combine(workspace.Verification, "generated/subtract"); Directory.CreateDirectory(generated);
            Program.Reject(() => FixtureChecks.RequireProductionReport(workspace, "Subtract"));
            string program = Path.Combine(generated, "Extracted.lean"), proof = Path.Combine(workspace.Verification, "Proof.lean");
            File.WriteAllText(program, "program"); File.WriteAllText(proof, "proof");
            JsonObject report = new() { ["status"] = "verified", ["source"] = new JsonObject { ["kind"] = "production" },
                ["sourceInputs"] = System.Text.Json.JsonSerializer.SerializeToNode(workspace.Inputs()), ["generatedProgramSha256"] = Workspace.Hash(program),
                ["leanSourceSha256"] = new JsonObject { ["Proof.lean"] = Workspace.Hash(proof) } };
            void Write(JsonObject value) => File.WriteAllText(Path.Combine(generated, "report.json"), value.ToJsonString());
            Write(report); Program.Require(FixtureChecks.RequireProductionReport(workspace, "Subtract") == program, "Valid baseline rejected");
            foreach (string field in new[] { "status", "kind", "inputs", "program", "proof" })
            {
                var invalid = report.DeepClone().AsObject();
                if (field == "status") invalid["status"] = "failed";
                if (field == "kind") invalid["source"]!["kind"] = "fixture";
                if (field == "inputs") invalid["sourceInputs"] = new JsonObject();
                if (field == "program") invalid["generatedProgramSha256"] = "wrong";
                if (field == "proof") invalid["leanSourceSha256"]!["Proof.lean"] = "wrong";
                Write(invalid); Program.Reject(() => FixtureChecks.RequireProductionReport(workspace, "Subtract"));
            }
        });
        check("arithmetic refutations retain complete contracts and required audits", (_, manifests) =>
        {
            string root = Path.GetDirectoryName(manifests)!, template = Path.Combine(root, "verification/Tests/Fixtures/RefutationTemplate.lean.in");
            Directory.CreateDirectory(Path.GetDirectoryName(template)!);
            File.Copy(Path.Combine(Directory.GetCurrentDirectory(), "verification/Tests/Fixtures/RefutationTemplate.lean.in"), template);
            foreach (string method in new[] { "Add", "Subtract" })
            {
                string proof = Path.Combine(root, "refutation-" + method);
                Directory.CreateDirectory(Path.Combine(proof, "manifests"));
                File.Copy(Path.Combine(manifests, method.ToLowerInvariant() + ".json"), Path.Combine(proof, "manifests", method.ToLowerInvariant() + ".json"));
                string audit = "'UInt256Proof.model_not_correct' depends on axioms: [propext, Classical.choice, Quot.sound]";
                Workspace workspace = new(root, (command, cwd, _) =>
                {
                    Program.Require(cwd == proof && command.SequenceEqual(new[] { "lake", "build", "+Refutation:olean" }), "Arithmetic kernel command changed");
                    string source = File.ReadAllText(Path.Combine(proof, "Refutation.lean"));
                    string contract = method == "Add" ? "Contract" : "SubtractContract", operation = method == "Add" ? "+" : "-";
                    Program.Require(source.Contains($"¬ {contract} Extracted.program Extracted.entryIndex witnessBytes 0 32 64", StringComparison.Ordinal)
                        && source.Contains($"byteValue witnessBytes 0 {operation} byteValue witnessBytes 32", StringComparison.Ordinal)
                        && source.Contains("invoke_result_unique", StringComparison.Ordinal) && source.Contains("rintro ⟨fuel, final, hr, hm⟩", StringComparison.Ordinal), "Complete contract refutation changed");
                    return audit;
                });
                void Run(string selected) => FixtureChecks.ModelRefutation(workspace, proof, "lake", "if address = 0 then 1 else 0", "0", "32", "64", "72", "2", "3", selected);
                Run(method);
                audit = "'UInt256Proof.model_not_correct' depends on axioms: [sorryAx]";
                Program.Reject(() => Run(method));
                Program.Reject(() => Run("Multiply"));
            }
        });
        check("native witnesses require clean builds and successful execution", (_, manifests) =>
        {
            string root = Path.GetDirectoryName(manifests)!;
            foreach (string failure in new[] { "", "imports", "build", "execution" })
            {
                string destination = Path.Combine(root, "native-" + failure), assembly = Path.Combine(root, "a & b", "Nethermind.Int256.dll");
                Directory.CreateDirectory(destination);
                int executions = 0;
                Workspace workspace = new(root, (command, cwd, stage) =>
                {
                    Program.Require(cwd == destination, "Native working directory changed");
                    if (stage == "Native witness build")
                    {
                        Program.Require(command.Contains("-p:EnforceCodeStyleInBuild=true") && command.Contains("-p:GenerateDocumentationFile=true"), "Native analyzer flags missing");
                        var project = System.Xml.Linq.XDocument.Load(command[2]);
                        Program.Require(project.Descendants("HintPath").Single().Value == assembly, "Assembly reference was not XML escaped");
                        Program.Require(File.ReadAllText(Path.Combine(destination, "Witness/Program.cs")) == "source", "Witness source changed");
                        if (failure == "build") throw new InvalidOperationException("Build failed");
                        return failure == "imports" ? "IDE0005" : "";
                    }
                    executions++;
                    Program.Require(command.SequenceEqual(new[] { "dotnet", Path.Combine(destination, "Witness", "bin/Release/net10.0/Witness.dll") }), "Native execution command changed");
                    if (failure == "execution") throw new InvalidOperationException("Wrong native result");
                    return "";
                });
                void Run() => FixtureChecks.NativeWitness(workspace, destination, assembly, "source");
                if (failure.Length == 0) Run(); else Program.Reject(Run);
                Program.Require(executions == (failure is "imports" or "build" ? 0 : 1), "Executed witness after rejected build");
                Program.Reject(Run);
            }
        });
        check("negative fixture extraction retains registered sources and unchanged proof snapshots", (catalog, manifests) =>
        {
            const string method = "EqInt64UInt256";
            foreach (string failure in new[] { "", "unchanged-body", "unchanged-program", "changed-proof", "missing-proof", "wrong-target" })
            {
                Workspace commands = VerifierTests.Setup(catalog, manifests);
                Workspace workspace = new(commands.Root, (command, cwd, stage) =>
                {
                    string output = commands.Run(command, cwd, stage);
                    if (stage == "Extraction")
                    {
                        string path = Path.Combine(command[3], "artifact.json");
                        JsonObject artifact = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
                        artifact["methods"]![0]!["instructions"] = new JsonArray(new JsonObject { ["opcode"] = "ldc.i4", ["operand"] = failure == "unchanged-body" ? 0 : 1 });
                        File.WriteAllText(path, artifact.ToJsonString());
                        if (failure == "changed-proof") File.WriteAllText(Path.Combine(Path.GetDirectoryName(command[3])!, "Proof.lean"), "changed");
                    }
                    return output;
                });
                string signature = Catalog.Text(catalog.Manifest(method)["entry"]);
                string project = Path.Combine(workspace.Verification, "Tests/Fixtures/Equality/Nethermind.Int256.csproj");
                Program.Require(FixtureChecks.MutationSource(catalog, project, method, "WrongLane") == Path.Combine(Path.GetDirectoryName(project)!, "Public.cs"), "Shared source selection requires a marker file");
                JsonObject baseline = new() { ["artifact"] = new JsonObject { ["methods"] = new JsonArray(new JsonObject { ["signature"] = signature,
                    ["instructions"] = new JsonArray(new JsonObject { ["opcode"] = "ldc.i4", ["operand"] = 0 }) }) }, ["generatedProgramSha256"] = "different",
                    ["leanSourceSha256"] = new JsonObject { ["Proof.lean"] = Workspace.Hash(Path.Combine(workspace.Verification, "Proof.lean")) } };
                if (failure == "missing-proof") baseline["leanSourceSha256"]!["Missing.lean"] = "missing";
                if (failure == "unchanged-program")
                {
                    string extracted = Path.Combine(workspace.Root, "expected.lean"); File.WriteAllText(extracted, "extracted");
                    baseline["generatedProgramSha256"] = Workspace.Hash(extracted);
                }
                string work = Path.Combine(workspace.Root, "mutation-" + failure);
                void Run() => FixtureChecks.Mutation(workspace, work, project, "Renamed", method, "scalar", baseline, failure == "wrong-target" ? "missing" : null);
                if (failure.Length == 0)
                {
                    Run();
                    Program.Require(File.Exists(Path.Combine(work, "proof/generated/Extracted.lean")), "Fresh extraction missing");
                    Program.Reject(Run);
                }
                else Program.Reject(Run);
            }
        });
        check("refutation templates preserve substitution order and require checked theorem audits", (_, manifests) =>
        {
            Program.Require(FixtureChecks.ExpandRefutation("@FIRST@", new Dictionary<string, string> { ["FIRST"] = "@SECOND@", ["SECOND"] = "value" }) == "value", "Substitution order changed");
            Program.Reject(() => FixtureChecks.ExpandRefutation("@UNBOUND@", []));
            string proof = Path.GetDirectoryName(manifests)!, template = Path.Combine(proof, "Refutation.lean.in");
            File.WriteAllText(template, "theorem @NAME@ : @VALUE@ = @VALUE@ := rfl\n#print axioms @NAME@\n");
            string output = "'checked' does not depend on any axioms";
            bool failed = false;
            Workspace workspace = new(proof, (command, cwd, stage) =>
            {
                Program.Require(command.SequenceEqual(new[] { "lake", "build", "+Refutation:olean" }) && cwd == proof && stage == "Refutation checking", "Refutation command changed");
                if (failed) throw new InvalidOperationException("Kernel rejection");
                return output;
            });
            void Run(bool register = false) => FixtureChecks.Refutation(workspace, proof, "lake", template,
                new Dictionary<string, string> { ["NAME"] = "checked", ["VALUE"] = "18446744073709551615" }, "Refutation", "checked", ["propext"], register);
            Run(true);
            Program.Require(File.ReadAllText(Path.Combine(proof, "Refutation.lean")).Contains("18446744073709551615", StringComparison.Ordinal), "Large numeral changed");
            string configuration = File.ReadAllText(Path.Combine(proof, "lakefile.toml"));
            Run();
            Program.Require(File.ReadAllText(Path.Combine(proof, "lakefile.toml")) == configuration, "Unrequested library registration");
            foreach (string invalid in new[] { "", "'other' does not depend on any axioms", "'checked' depends on axioms: [sorryAx]", output + "\n" + output })
            {
                output = invalid;
                Program.Reject(() => Run());
            }
            failed = true;
            Program.Reject(() => Run());
        });
        check("SIMD fixture changes target the selected helper and reachable feature expressions", (_, _) =>
        {
            JsonObject Artifact(params string[] signatures) => new()
            {
                ["methods"] = new JsonArray(signatures.Select(signature => (JsonNode)new JsonObject { ["signature"] = signature,
                    ["instructions"] = new JsonArray(new JsonObject { ["opcode"] = "call", ["operand"] = "Feature::get_IsSupported()", ["Offset"] = 0 }) }).ToArray()),
                ["coverage"] = new JsonArray(signatures.Select(signature => (JsonNode)new JsonObject { ["method"] = signature, ["reachable"] = new JsonArray(0) }).ToArray())
            };
            foreach (string method in new[] { "Add", "Subtract" })
                foreach (string profile in new[] { "arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx512" })
                    foreach (string name in new[] { "LaneLocals", "InlineCarry", "EquivalentMask", "ExtractedHelper", "ReversedStore" })
                    {
                        string target = name == "ReversedStore" ? "StoreLimbs" : name == "EquivalentMask" ? (method == "Add" ? "PrepareAdd" : "SubtractImpl")
                            : name == "ExtractedHelper" && profile.StartsWith("x64-avx", StringComparison.Ordinal) ? (method == "Add" ? "FinishAdd" : "SubtractImpl")
                            : method == "Add" ? "AddVector128" : "SubtractVector128";
                        JsonObject before = Artifact($"::{target}(", "::Other(");
                        JsonObject after = before.DeepClone().AsObject();
                        after["methods"]![0]!["instructions"]![0]!["operand"] = "changed";
                        SimdFixtures.TargetChanged(name, method, profile, before, after);
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, before));
                        after = before.DeepClone().AsObject(); after["methods"]![1]!["instructions"]![0]!["operand"] = "changed";
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, after));
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, Artifact("::Other(")));
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, Artifact($"::{target}(", $"::{target}(")));
                    }
            JsonObject baseline = Artifact("::Entry("), changed = baseline.DeepClone().AsObject();
            changed["methods"]![0]!["signature"] = "::Renamed(";
            Program.Reject(() => SimdFixtures.TargetChanged("Renamed", "Add", "x64-avx2", baseline, changed));
            changed["methods"]![0]!["instructions"]![0]!["operand"] = "::NewCall(";
            SimdFixtures.TargetChanged("Renamed", "Add", "x64-avx2", baseline, changed);
            changed = baseline.DeepClone().AsObject();
            changed["methods"]![0]!["instructions"]!.AsArray().Add(new JsonObject { ["opcode"] = "call", ["operand"] = "Other::get_IsSupported()", ["Offset"] = 1 });
            Program.Reject(() => SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", baseline, changed));
            changed["coverage"]![0]!["reachable"]!.AsArray().Add(1);
            SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", baseline, changed);
            Program.Reject(() => SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", changed, baseline));
        });
        check("fixture changes require instructions in the intended reachable method", (_, _) =>
        {
            JsonObject baseline = JsonNode.Parse("""
                {"methods":[{"signature":"target","instructions":[{"opcode":"ldc.i4","operand":0}]},{"signature":"unrelated","instructions":[]}]}
                """)!.AsObject();
            foreach (string field in new[] { "opcode", "operand", "scope" })
            {
                JsonObject changed = baseline.DeepClone().AsObject();
                changed["methods"]![0]!["instructions"]![0]![field] = "changed";
                FixtureChecks.ChangedMethod(changed, baseline, "target");
            }
            foreach (string mutation in new[] { "metadata", "offset", "unrelated", "missing-target", "missing-baseline" })
            {
                JsonObject actual = baseline.DeepClone().AsObject(), original = baseline.DeepClone().AsObject();
                switch (mutation)
                {
                    case "metadata": actual["methods"]![0]!["token"] = 123; break;
                    case "offset": actual["methods"]![0]!["instructions"]![0]!["Offset"] = 123; break;
                    case "unrelated": actual["methods"]![1]!["instructions"]!.AsArray().Add(new JsonObject { ["opcode"] = "ret" }); break;
                    case "missing-target": actual["methods"]!.AsArray().RemoveAt(0); break;
                    case "missing-baseline": original["methods"]!.AsArray().RemoveAt(0); break;
                }
                Program.Reject(() => FixtureChecks.ChangedMethod(actual, original, "target"));
            }
        });
        check("fixture prerequisites bind production freshness, safety and unchanged proofs", (_, _) =>
        {
            JsonObject inputs = new() { ["source"] = "current" };
            JsonObject production = new() { ["source"] = new JsonObject { ["kind"] = "production" }, ["sourceInputs"] = inputs.DeepClone(),
                ["leanSourceSha256"] = new JsonObject { ["proof"] = "same" }, ["evidenceKind"] = "arithmetic-and-memory-safety", ["safety"] = SafetyCatalog.Gate("Lsh", "scalar") };
            JsonObject baseline = production.DeepClone().AsObject();
            baseline["source"]!["kind"] = "fixture";
            baseline["generatedProgramSha256"] = "baseline";
            JsonObject alternate = baseline.DeepClone().AsObject(); alternate["generatedProgramSha256"] = "alternate";
            FixtureChecks.Baseline(production, baseline, inputs);
            FixtureChecks.Alternative(baseline, alternate);
            FixtureChecks.SafetyReport(production, "Lsh", "scalar");
            Program.Reject(() => FixtureChecks.Production(baseline, inputs));
            Program.Reject(() => FixtureChecks.Production(production, new() { ["source"] = "stale" }));
            Program.Reject(() => FixtureChecks.SafetyReport(production, "Rsh", "scalar"));
            production.Remove("evidenceKind");
            Program.Reject(() => FixtureChecks.SafetyReport(production, "Lsh", "scalar"));
            Program.Reject(() => FixtureChecks.Alternative(baseline, baseline));
            baseline["leanSourceSha256"]!["proof"] = "different";
            Program.Reject(() => FixtureChecks.Baseline(production, baseline, inputs));
            Program.Reject(() => FixtureChecks.Alternative(baseline, alternate));
        });
    }
}
