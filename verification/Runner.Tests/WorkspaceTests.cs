// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class WorkspaceTests
{
    private static void Write(string root, string relative, string text = "source")
    {
        string path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, text);
    }

    private static string Root(string manifests)
    {
        string root = Path.Combine(Path.GetDirectoryName(manifests)!, "workspace");
        foreach (string file in new[] { "global.json", ".editorconfig", "verification/lean-toolchain", "verification/lakefile.toml",
            "verification/CIL/Test.lean", "src/Test.cs", ".github/workflows/verify-uint256.yml" }) Write(root, file);
        return root;
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("theorem audits require one complete approved axiom list", (_, _) =>
        {
            string name = "UInt256Proof.Checked", output = $"info: Audit.lean:1:0: '{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n";
            string[] approved = ["propext", "Classical.choice", "Quot.sound"];
            Program.Require(ProofAudits.Check(output, [name], approved)[name].SequenceEqual(approved), "Wrapped axiom list changed");
            Program.Require(ProofAudits.Check($"'{name}' does not depend on any axioms", [name], approved)[name].Length == 0, "Empty axiom audit rejected");
            foreach (string invalid in new[] { "", output + output, $"'{name}' depends on axioms: [sorryAx]", $"'{name}' depends on axioms: [propext, propext]",
                $"'{name}' depends on axioms: [propext,\nerror: diagnostic\n]", $"'{name}Other' does not depend on any axioms" })
                Program.Reject(() => ProofAudits.Check(invalid, [name], approved));
        });
        check("source hashes exclude build caches and include proof templates", (_, manifests) =>
        {
            string root = Root(manifests);
            Workspace workspace = new(root);
            var initial = workspace.Inputs();
            foreach (string directory in Workspace.BuildDirectories) Write(root, $"verification/{directory}/Bad.lean");
            Write(root, "verification/ignored.txt");
            Program.Require(Workspace.SameInputs(initial, workspace.Inputs()), "Build caches became source inputs");
            Write(root, "verification/Test.lean.in");
            Program.Require(workspace.Inputs().ContainsKey("verification/Test.lean.in"), "Refutation template omitted");
            Write(root, "src/Test.cs", "changed");
            Program.Require(initial["src/Test.cs"] != workspace.Inputs()["src/Test.cs"], "Source edit ignored");
        });
        check("proof session preserves only its checked dependencies", (_, manifests) =>
        {
            Workspace workspace = new(Root(manifests));
            var inputs = workspace.Inputs();
            using ProofSession session = new(workspace);
            string[] paths = session.Prepare(inputs);
            foreach (string file in new[] { "generated/Extracted.lean", "generated/artifact.json", "UInt256/Methods/SelectedGate.lean", "UInt256/Methods/SelectedSafetyGate.lean" })
                Write(session.Directory, file, "generated");
            Write(session.Directory, ".lake/build/lib/lean/Checked.olean", "checked in this session");
            session.Prepare(inputs);
            Program.Require(session.Uses == 2 && File.Exists(Path.Combine(session.Directory, ".lake/build/lib/lean/Checked.olean")), "Session discarded checked dependencies");
            Program.Require(!File.Exists(Path.Combine(session.Directory, "generated/Extracted.lean")), "Stale generated program survived");
            Program.Require(!File.Exists(Path.Combine(session.Directory, "UInt256/Methods/SelectedGate.lean")), "Stale typed gate survived");
            Exception? failure = null;
            Thread thread = new(() => { try { session.Prepare(inputs); } catch (Exception error) { failure = error; } });
            thread.Start(); thread.Join();
            Program.Require(failure is InvalidOperationException, "Another worker reused the session");
            Write(session.Directory, "CIL/Test.lean", "tampered");
            Program.Reject(() => Workspace.CheckProofSnapshot(session.Directory, paths, inputs));
            Program.Reject(() => session.Prepare(inputs));
            Write(workspace.Root, "src/Test.cs", "changed");
            Program.Reject(() => session.Prepare(workspace.Inputs()));
        });
        check("generated gates cannot overwrite handwritten proof sources", (_, manifests) =>
        {
            Workspace workspace = new(Root(manifests));
            Write(workspace.Root, "verification/UInt256/Methods/SelectedGate.lean");
            using ProofSession session = new(workspace);
            Program.Reject(() => session.Prepare(workspace.Inputs()));
        });
        check("transient source edits cannot enter a proof snapshot", (_, manifests) =>
        {
            Workspace workspace = new(Root(manifests));
            var inputs = workspace.Inputs();
            string source = Path.Combine(workspace.Verification, "CIL/Test.lean"), original = File.ReadAllText(source);
            using ProofSession proof = new(workspace);
            try
            {
                File.WriteAllText(source, "transient replacement");
                Program.Reject(() => workspace.CopyProofSources(proof.Directory, inputs));
            }
            finally { File.WriteAllText(source, original); }
            Program.Require(Workspace.SameInputs(inputs, workspace.Inputs()), "Test did not restore the transient edit");
            Program.Reject(() => Workspace.CheckProofSnapshot(proof.Directory, ["CIL/Test.lean"], inputs));
        });
        check("shared artifact bundle binds sources, binaries and production identity", (_, manifests) =>
        {
            string root = Root(manifests);
            List<string[]> commands = [];
            Workspace workspace = new(root, (command, cwd, _) =>
            {
                Program.Require(cwd == root, "Wrong build directory");
                commands.Add(command);
                string artifacts = command.Single(arg => arg.StartsWith("-p:ArtifactsPath=", StringComparison.Ordinal))[17..];
                Write(artifacts, commands.Count == 1 ? "bin/Nethermind.Int256/release/Nethermind.Int256.dll" : "bin/Extractor/release/Extractor.dll", "binary");
                return "built";
            });
            ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, Path.Combine(root, "work"), "Add");
            workspace.ValidateBundle(bundle, bundle.SourceInputs, production: true);
            Program.Require(commands.Count == 2 && commands.All(command => command.Contains("--no-incremental")), "Build reused unchecked incremental outputs");
            Program.Require(commands[0].Contains("-p:EnableZkEvm=false") && commands[1].Contains("-p:EnforceCodeStyleInBuild=true"), "Build configuration lost");
            Program.Reject(() => workspace.ValidateBundle(bundle with { Fixture = "Baseline" }, bundle.SourceInputs, production: true));
            Program.Reject(() => workspace.ValidateBundle(bundle with { Project = "fixture.csproj" }, bundle.SourceInputs, production: true));
            File.WriteAllText(bundle.Extractor, "tampered");
            Program.Reject(() => workspace.ValidateBundle(bundle, bundle.SourceInputs));
            File.WriteAllText(bundle.Extractor, "binary");
            File.WriteAllText(bundle.Assembly, "tampered");
            Program.Reject(() => workspace.ValidateBundle(bundle, bundle.SourceInputs));
            File.WriteAllText(bundle.Assembly, "binary");
            Write(root, "src/Test.cs", "changed");
            Program.Reject(() => workspace.ValidateBundle(bundle, bundle.SourceInputs));
        });
        check("extraction rejects mismatched assembly, entry, profile and ABI", (catalog, manifests) =>
        {
            string root = Root(manifests);
            foreach (string source in Directory.EnumerateFiles(manifests, "*", SearchOption.AllDirectories))
                Write(root, "verification/manifests/" + Path.GetRelativePath(manifests, source), File.ReadAllText(source));
            string assembly = Path.Combine(root, "work/assembly.dll"), extractor = Path.Combine(root, "work/extractor.dll");
            Write(root, "work/assembly.dll", "binary"); Write(root, "work/extractor.dll", "tool");
            JsonObject manifest = catalog.Manifest("EqInt64UInt256"), convention = manifest["callingConvention"]!.AsObject();
            JsonArray parameters = [];
            foreach (JsonNode? p in convention["parameters"]!.AsArray())
                parameters.Add(new JsonObject { ["type"] = p!["type"]!.DeepClone(), ["IsIn"] = p["isIn"]!.DeepClone(), ["IsOut"] = p["isOut"]!.DeepClone() });
            JsonObject entry = new() { ["signature"] = manifest["entry"]!.DeepClone(), ["isStatic"] = true, ["hasThis"] = false,
                ["returnType"] = convention["returns"]!.DeepClone(), ["parameters"] = parameters };
            JsonObject artifact = new() { ["sha256"] = Workspace.Hash(assembly), ["entryIndex"] = 0, ["methods"] = new JsonArray(entry), ["profile"] = catalog.Profile("scalar") };
            Action<JsonObject> mutate = _ => { };
            Workspace workspace = new(root, (command, _, _) =>
            {
                Program.Require(command[4] == Catalog.Text(manifest["entry"]) && command[5] == "scalar", "Wrong extraction selector");
                JsonObject output = artifact.DeepClone().AsObject();
                mutate(output);
                Write(command[3], "artifact.json", output.ToJsonString());
                return "extracted";
            });
            ArtifactBundle bundle = new(assembly, extractor, [], workspace.Inputs(), Workspace.Hash(assembly), Workspace.Hash(extractor), workspace.ProductionProject, null);
            string generated = Path.Combine(root, "work/generated");
            workspace.Extract(bundle, generated, "EqInt64UInt256", "scalar");
            foreach (Action<JsonObject> change in new Action<JsonObject>[] {
                output => output["sha256"] = "wrong", output => output["methods"]![0]!["signature"] = "wrong",
                output => output["profile"]!["Bmi1"] = true, output => output["methods"]![0]!["hasThis"] = true,
                output => output["methods"]![0]!["parameters"]![0]!["IsOut"] = true,
                _ => Write(root, "src/Test.cs", "changed during extraction") })
            {
                mutate = change;
                Program.Reject(() => workspace.Extract(bundle, generated, "EqInt64UInt256", "scalar"));
            }
        });
    }
}
