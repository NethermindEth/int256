// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class ProfileExtractorChecks
{
    internal static void RequireRejection(string output, string diagnostic)
    {
        if (!output.Contains(diagnostic, StringComparison.Ordinal))
            throw new InvalidOperationException($"Fixture failed outside the expected extractor rejection: {diagnostic}");
        if (new[] { "BadImageFormatException", "OutOfMemoryException", "StackOverflowException", "maximum number of heartbeats" }
            .Any(marker => output.Contains(marker, StringComparison.Ordinal)))
            throw new InvalidOperationException("Malformed fixture or resource exhaustion is not the expected rejection");
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("profile extractor requires exact rejection without malformed artifacts or exhaustion", (_, _) =>
        {
            RequireRejection("prefix expected suffix", "expected");
            Program.Reject(() => RequireRejection("other failure", "expected"));
            foreach (string marker in new[] { "BadImageFormatException", "OutOfMemoryException", "StackOverflowException", "maximum number of heartbeats" })
                Program.Reject(() => RequireRejection("expected " + marker, "expected"));
        });
    }

    internal static void Run(Workspace workspace)
    {
        string work = Path.Combine(Path.GetTempPath(), "int256-profile-extractor-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(work);
        try { Run(workspace, work); }
        finally { Directory.Delete(work, recursive: true); }
    }

    private static void Run(Workspace workspace, string work)
    {
        string project = Path.Combine(workspace.Verification, "Tests/Fixtures/Profiles/Nethermind.Int256.csproj");
        string Build(string source, string artifacts, string[] properties, bool succeeds = true)
        {
            string[] command = ["dotnet", "build", source, "-c", "Release", "--nologo", $"-p:ArtifactsPath={artifacts}",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", .. properties];
            return succeeds ? workspace.Run(command, workspace.Root) : workspace.RunRejected(command, workspace.Root, "Profile fixture build rejection");
        }
        Build(Path.Combine(workspace.Verification, "Extractor/Extractor.csproj"), Path.Combine(work, "extractor"), []);
        string extractor = Path.Combine(work, "extractor/bin/Extractor/release/Extractor.dll");
        Build(Path.Combine(workspace.Verification, "Tests/ProfileMetadataFixture/ProfileMetadataFixture.csproj"), Path.Combine(work, "metadata"), []);
        string metadata = Path.Combine(work, "metadata/bin/ProfileMetadataFixture/release/ProfileMetadataFixture.dll");
        Dictionary<string, string> assemblies = [];
        string Fixture(string name)
        {
            if (!assemblies.TryGetValue(name, out string? assembly))
            {
                string artifacts = Path.Combine(work, name);
                Build(project, artifacts, [$"-p:FixtureName={name}"]);
                assemblies[name] = assembly = Path.Combine(artifacts, "bin/Nethermind.Int256/release/Nethermind.Int256.dll");
            }
            return assembly;
        }
        (string Directory, JsonObject Artifact) Extract(string assembly, string label, string profile = "scalar", string? rejection = null)
        {
            string output = Path.Combine(work, "generated", label, profile);
            string[] command = ["dotnet", extractor, assembly, output, "Add", profile];
            if (rejection is not null)
            {
                RequireRejection(workspace.RunRejected(command, workspace.Root, "Profile extractor rejection"), rejection);
                return (output, new JsonObject());
            }
            workspace.Run(command, workspace.Root);
            JsonObject artifact = JsonNode.Parse(File.ReadAllText(Path.Combine(output, "artifact.json")))!.AsObject();
            Program.Require(Catalog.Text(artifact["profile"]!["Name"]) == profile && Catalog.Text(artifact["sha256"]) == Workspace.Hash(assembly), "Profile or assembly identity mismatch in fresh extraction");
            return (output, artifact);
        }
        string Mutate(string mode, string source)
        {
            string changed = Path.Combine(work, mode + ".dll");
            workspace.Run(["dotnet", metadata, mode, source, changed], workspace.Root);
            Program.Require(Workspace.Hash(changed) != Workspace.Hash(source), "Metadata fixture did not change the artifact");
            return changed;
        }
        string known = Fixture("KnownFeature");
        foreach (string profile in Catalog.Profiles)
        {
            var (output, artifact) = Extract(known, "known", profile);
            string program = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
            Program.Require(program.Contains(".feature .avx2", StringComparison.Ordinal) && !program.Contains(".featureDisabled", StringComparison.Ordinal), "Feature getter was not preserved as a typed operation");
            JsonNode probe = artifact["methods"]!.AsArray().First(m => Catalog.Text(m!["signature"]).Contains("::Probe(", StringComparison.Ordinal))!;
            JsonNode coverage = artifact["coverage"]!.AsArray().First(c => Catalog.Text(c!["method"]) == Catalog.Text(probe["signature"]))!;
            JsonArray instructions = probe["instructions"]!.AsArray();
            int index = Enumerable.Range(0, instructions.Count).First(i => instructions[i]!["operand"]?.ToString() == "System.Boolean System.Runtime.Intrinsics.X86.Avx2::get_IsSupported()");
            JsonNode branch = instructions[index + 1]!;
            string opcode = Catalog.Text(branch["opcode"]);
            Program.Require(new[] { "brfalse", "brfalse.s", "brtrue", "brtrue.s" }.Contains(opcode), "Versioned feature fixture branch structure changed");
            bool taken = artifact["profile"]!["Avx2"]!.GetValue<bool>() == opcode.StartsWith("brtrue", StringComparison.Ordinal);
            int selected = taken ? int.Parse(branch["operand"]!.ToString(), System.Globalization.CultureInfo.InvariantCulture) : instructions[index + 2]!["Offset"]!.GetValue<int>();
            Program.Require(coverage["reachable"]!.AsArray().Any(offset => offset!.GetValue<int>() == selected), "Reachability disagrees with the fixed execution profile");
        }
        Console.WriteLine("PASS: every named profile preserves and consistently evaluates the exact getter");
        foreach (string profile in Catalog.Profiles)
        {
            Extract(Fixture("PortableVector"), "portable", profile);
            bool supported = profile.StartsWith("x64-avx512", StringComparison.Ordinal);
            Extract(Fixture("UnguardedAvx512"), "unguarded", profile, supported ? null : "Reachable intrinsic lacks Avx512FVL");
            Extract(Fixture("WeakAvx512Guard"), "weak-guard", profile, profile.StartsWith("x64-avx2", StringComparison.Ordinal) ? "Reachable intrinsic lacks Avx512FVL" : null);
            Extract(Fixture("MergedAvx512Guard"), "merged-guard", profile, supported ? null : "Reachable intrinsic lacks Avx512FVL");
        }
        Console.WriteLine("PASS: portable vectors accepted; absent/weak/data-dependent ISA guards rejected");
        workspace.Run(["lake", "build", "+CIL.ProfileEquivalence:olean", "+CIL.SymbolicExecution:olean"], workspace.Verification);
        string guarded = Fixture("GuardedAvx512");
        List<(string Label, string Assembly)> variants = [("guarded", guarded), ("inherited", Fixture("InheritedAvx2Guard"))];
        foreach (string mode in new[] { "guard-cached", "guard-negated", "guard-and" }) variants.Add((mode, Mutate(mode, guarded)));
        foreach (var (label, assembly) in variants)
        foreach (string profile in Catalog.Profiles)
        {
            var (output, artifact) = Extract(assembly, label, profile);
            workspace.Run(["lake", "lean", Path.Combine(output, "Extracted.lean")], workspace.Verification);
            var live = artifact["coverage"]!.AsArray().ToDictionary(c => Catalog.Text(c!["method"]), c => c!["reachable"]!.AsArray().Select(n => n!.GetValue<int>()).ToHashSet());
            bool calls = artifact["methods"]!.AsArray().Any(method => method!["instructions"]!.AsArray().Any(op =>
                live[Catalog.Text(method["signature"])].Contains(op!["Offset"]!.GetValue<int>()) && Catalog.Text(op["opcode"]) == "call" &&
                (op["operand"]!.ToString().Contains("::TernaryLogic(", StringComparison.Ordinal) || op["operand"]!.ToString().Contains("::Permute4x64(", StringComparison.Ordinal))));
            Program.Require(calls == profile.StartsWith("x64-avx512", StringComparison.Ordinal), "Fixed guard did not select the expected intrinsic path");
        }
        Console.WriteLine("PASS: cached, negated, compound and inherited ISA guards with checked family certificates");
        foreach (var (name, profile, diagnostic) in new[] {
            ("UnknownFeature", "scalar", "Unclassified feature getter"),
            ("UnclassifiedFeature", "scalar", "New feature query invalidates the declared behaviour classification"),
            ("UnsupportedIntrinsic", "x64-avx2", "Unsupported external dependency"),
            ("UnsupportedUnsafe", "x64-avx2", "Unsupported external dependency"),
            ("StaticInitializer", "x64-avx2", "Unmodelled static initialisation"),
            ("GenericHelper", "scalar", "Unsupported method metadata") })
        {
            Extract(Fixture(name), name, profile, diagnostic);
            Console.WriteLine($"PASS: {name} rejected for its expected infrastructure reason");
        }
        Extract(known, "invalid-profile", "missing-profile", "Unknown execution profile");
        RequireRejection(Build(project, Path.Combine(work, "unknown-fixture"), ["-p:FixtureName=MissingFixture"], false), "Unknown profile fixture");
        string staticAssembly = Fixture("StaticData");
        var (baselineDirectory, baseline) = Extract(staticAssembly, "static", "x64-avx2");
        Program.Require(baseline["staticData"]!.AsArray().Count == 1 && Catalog.Text(baseline["staticData"]![0]!["bytes"]) == "0100000000000000020000000000000003000000000000000400000000000000", "Extraction did not bind the actual versioned RVA data");
        foreach (var (mode, source, profile, diagnostic) in new[] {
            ("feature-scope", known, "scalar", "Unsupported feature getter"),
            ("generic-feature", known, "scalar", "Unsupported feature getter"),
            ("intrinsic-scope", staticAssembly, "x64-avx2", "Unsupported type identity"),
            ("generic-argument-scope", staticAssembly, "x64-avx2", "Unsupported type identity"),
            ("vector-class-encoding", staticAssembly, "x64-avx2", "Unsupported type identity"),
            ("operand-type-scope", staticAssembly, "x64-avx2", "Unsupported type identity"),
            ("field-type-scope", known, "scalar", "Unsupported type identity"),
            ("getter-return-scope", known, "scalar", "Unsupported type identity"),
            ("uint256-size", staticAssembly, "x64-avx2", "Unsupported UInt256 layout"),
            ("uint256-base-scope", staticAssembly, "x64-avx2", "Unsupported UInt256 layout"),
            ("static-base-scope", staticAssembly, "x64-avx2", "Unsupported static data or initialisation"),
            ("static-memberref-scope", staticAssembly, "x64-avx2", "Unsupported static data or initialisation"),
            ("static-mutable", staticAssembly, "x64-avx2", "Unsupported static data or initialisation"),
            ("static-initializer", staticAssembly, "x64-avx2", "Unsupported static data or initialisation") })
        {
            Extract(Mutate(mode, source), mode, profile, diagnostic);
            Console.WriteLine($"PASS: {mode} rejected for its expected infrastructure reason");
        }
        var (changedDirectory, changedArtifact) = Extract(Mutate("static-byte", staticAssembly), "static-byte", "x64-avx2");
        Program.Require(Catalog.Text(changedArtifact["staticData"]![0]!["bytes"]) == "00" + Catalog.Text(baseline["staticData"]![0]!["bytes"])[2..]
            && Workspace.Hash(Path.Combine(changedDirectory, "Extracted.lean")) != Workspace.Hash(Path.Combine(baselineDirectory, "Extracted.lean")), "Changed actual RVA bytes were replaced or omitted from the program");
        Console.WriteLine("PASS: changed immutable bytes change both artifact data and the extracted program");
    }
}
