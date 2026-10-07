// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.RegularExpressions;
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
}
