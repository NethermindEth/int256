// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.RegularExpressions;
using System.Diagnostics;
using System.Text.Json;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class FoundationChecks
{
    internal static readonly string[] Targets = ["Tests.VectorSemantics", "Tests.VectorMemory", "Tests.ProfileSemantics", "Tests.SIMDArithmetic",
        "Tests.AggregateSemantics", "Tests.ExpansionIntrinsics", "CIL.FeatureCoverage"];
    internal static readonly string[] Required = [
        "CIL.Vector.ternary_add", "CIL.Vector.ternary_subtract", "CIL.Vector.pack256_lanes", "CIL.Vector.avx2_blend_incoming",
        "CIL.Vector.arithmetic_sign_mask", "UInt256Proof.readBytes_writeBytes", "UInt256Proof.captured256_survives_store", "UInt256Proof.vector_store4",
        "UInt256Proof.ProfileChecks.fixed_query", "CIL.invoke_representative_eq", "CIL.invoke_same_family_eq", "UInt256Proof.SIMD.packed_cascade",
        "UInt256Proof.SIMD.read_lookup", "UInt256Proof.SIMD.readStaticBytes_sequential", "UInt256Proof.SIMD.ternary_carry_mask", "UInt256Proof.SIMD.ternary_borrow_mask",
        "UInt256Proof.SIMD.carry_generated_propagated", "UInt256Proof.SIMD.borrow_generated_propagated", "UInt256Proof.SIMD.cascade_flags",
        "UInt256Proof.SIMD.add_cascade_words", "UInt256Proof.SIMD.subtract_cascade_words", "UInt256Proof.SIMD.add_cascade_vector", "UInt256Proof.SIMD.subtract_cascade_vector",
        "UInt256Proof.add_contract_profiles", "UInt256Proof.subtract_contract_profiles", "CIL.FeatureProfile.mem_allValid", "CIL.Representative.group_contract"];

    internal static void ParserChecks()
    {
        Program.Require(ProofAudits.CheckAll("'a' depends on axioms: [propext,\n Quot.sound]", ["propext", "Quot.sound"], ["a"])["a"].Length == 2, "Wrapped audit rejected");
        Program.Require(ProofAudits.CheckAll("'a' depends on axioms: [propext]\n'b' depends on axioms: []", ["propext"], ["a", "b"])["b"].Length == 0, "Empty audit rejected");
        foreach (string text in new[] { "", "'a' depends on axioms: []\n'a' depends on axioms: []", "'a' depends on axioms: [bad]",
            "'a' depends on axioms: []\n'b' depends on axioms: [bad]", "'a' depends on axioms: [propext, propext]" })
            Program.Reject(() => ProofAudits.CheckAll(text, ["propext"], ["a"]));
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("safety foundation preserves isolated sources and fails on stale or incomplete evidence", (_, manifests) =>
        {
            foreach (string failure in new[] { "", "audit", "axiom", "source", "snapshot", "toolchain" })
            {
                string root = Path.Combine(Path.GetDirectoryName(manifests)!, failure + "-foundation");
                foreach (string path in new[] { "global.json", ".editorconfig", "verification/lean-toolchain", "verification/CIL/Test.lean",
                    "verification/UInt256/Safety/Test.lean", "verification/UInt256/Representation.lean", "verification/UInt256/RepresentationLemmas.lean",
                    "verification/Tests/MemorySafety.lean", "verification/Tests/MemorySafetyInstructions.lean", "verification/Runner.Tests/MemorySafetyAudits.json" })
                {
                    string target = Path.Combine(root, path);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.WriteAllText(target, path.EndsWith("Audits.json", StringComparison.Ordinal) ? "[\"required\"]" : "source");
                }
                string? proofDirectory = null;
                Workspace workspace = new(root, (command, cwd, _) =>
                {
                    if (command.Contains("--version")) return failure == "toolchain" ? "Lean (version 4.35.0)" : "Lean (version 4.34.1)";
                    proofDirectory = cwd;
                    Program.Require(cwd != root && !Directory.Exists(Path.Combine(cwd, ".lake")), "Foundation reused an existing proof cache");
                    Program.Require(command.SequenceEqual(new[] { "lake", "build", "+Tests.MemorySafetyInstructions:olean" }), "Foundation target changed");
                    if (failure == "snapshot") File.WriteAllText(Path.Combine(cwd, "CIL/Test.lean"), "changed");
                    if (failure == "source") File.WriteAllText(Path.Combine(root, "verification/CIL/Test.lean"), "changed");
                    return failure == "audit" ? "" : $"'required' depends on axioms: [{(failure == "axiom" ? "sorryAx" : "propext")}]";
                });
                if (failure.Length == 0) RunSafety(workspace);
                else Program.Reject(() => RunSafety(workspace));
                Program.Require(proofDirectory is null || !Directory.Exists(proofDirectory), "Foundation left a proof workspace behind");
            }
        });
    }

    internal static void Run(Workspace workspace)
    {
        ParserChecks();
        string[] approved = workspace.Catalog.Manifest("Add")["approvedAxioms"]!.AsArray().Select(Catalog.Text).ToArray();
        if (!approved.ToHashSet().SetEquals(workspace.Catalog.Manifest("Subtract")["approvedAxioms"]!.AsArray().Select(Catalog.Text)))
            throw new InvalidOperationException("Foundation axiom approvals differ between method manifests");
        var inputs = workspace.Inputs();
        string lean = workspace.Run(["lake", "env", "lean", "--version"], workspace.Verification);
        if (!Regex.IsMatch(lean, @"version 4\.34\.1\b")) throw new InvalidOperationException("Unexpected foundation Lean toolchain");
        string output = workspace.Run(["lake", "-d", workspace.Verification, "build", .. Targets.Select(target => $"+{target}:olean")], workspace.Root, "Foundation checking");
        var audits = ProofAudits.CheckAll(output, approved, Required);
        if (!Workspace.SameInputs(inputs, workspace.Inputs())) throw new InvalidOperationException("Inputs changed during foundation checking");
        Console.WriteLine($"Checked {Targets.Length} foundation modules and {audits.Count} transitive axiom audits");
    }

    internal static void RunSafety(Workspace workspace)
    {
        var inputs = workspace.Inputs();
        string[] names = JsonSerializer.Deserialize<string[]>(File.ReadAllText(Path.Combine(workspace.Verification, "Runner.Tests/MemorySafetyAudits.json")))!;
        if (names.Length == 0 || names.Distinct(StringComparer.Ordinal).Count() != names.Length)
            throw new InvalidOperationException("Missing or duplicate memory-safety audits");
        string lean = workspace.Run(["lake", "env", "lean", "--version"], workspace.Verification);
        if (!Regex.IsMatch(lean, @"version 4\.34\.1\b")) throw new InvalidOperationException("Unexpected foundation Lean toolchain");
        Stopwatch timer = Stopwatch.StartNew();
        string[] sources = [.. Workspace.SourceFiles(Path.Combine(workspace.Verification, "CIL"), [".lean"]),
            .. Workspace.SourceFiles(Path.Combine(workspace.Verification, "UInt256/Safety"), [".lean"]),
            .. new[] { "UInt256/Representation.lean", "UInt256/RepresentationLemmas.lean", "lean-toolchain",
                "Tests/MemorySafety.lean", "Tests/MemorySafetyInstructions.lean" }.Select(path => Path.Combine(workspace.Verification, path))];
        string[] paths = sources.Select(path => Workspace.Relative(workspace.Verification, path)).ToArray();
        using ProofSession proof = new(workspace);
        foreach (string path in paths)
        {
            string target = Path.Combine(proof.Directory, path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(workspace.Verification, path), target);
        }
        Workspace.CheckProofSnapshot(proof.Directory, paths, inputs);
        File.WriteAllText(Path.Combine(proof.Directory, "lakefile.toml"),
            "name = \"memory_safety_foundation\"\nversion = \"0.1.0\"\n[[lean_lib]]\nname = \"CIL\"\n[[lean_lib]]\nname = \"UInt256\"\n" +
            "[[lean_lib]]\nname = \"Tests.MemorySafety\"\n[[lean_lib]]\nname = \"Tests.MemorySafetyInstructions\"\n");
        string output = workspace.Run(["lake", "build", "+Tests.MemorySafetyInstructions:olean"], proof.Directory, "Safety foundation checking");
        var audits = ProofAudits.Check(output, names, ["propext", "Classical.choice", "Quot.sound"]);
        Workspace.CheckProofSnapshot(proof.Directory, paths, inputs);
        if (!Workspace.SameInputs(inputs, workspace.Inputs())) throw new InvalidOperationException("Safety source inputs changed during foundation checking");
        Console.WriteLine(JsonSerializer.Serialize(new { kind = "safety-foundation", productionCombined = false,
            elapsedSeconds = timer.Elapsed.TotalSeconds, sourceHashes = inputs, audits }, new JsonSerializerOptions { WriteIndented = true }));
    }
}
