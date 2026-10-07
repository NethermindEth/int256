// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class GateBindingChecks
{
    private const string Weakened = "namespace GateBinding\ntheorem weakened : True := True.intro\n#print axioms weakened\nend GateBinding\n";

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("gate binding rejects clean axioms outside the exact theorem body", (_, _) =>
        {
            const string path = "Gate.lean", source = "theorem bound : False := by\n  exact True.intro\n#print axioms bound\n";
            const string valid = "'GateBinding.weakened' does not depend on any axioms\nerror: Gate.lean:2:3: type mismatch\nerror: build failed\n";
            Rejection(valid, source, path, "bound");
            foreach (string invalid in new[] { valid.Replace("Gate.lean", "Other.lean"), valid.Replace(":2:3:", ":3:3:"), valid.Replace(":2:3:", ":0:3:"),
                valid.Replace("does not depend on any axioms", "depends on axioms: [sorryAx]"), "'GateBinding.weakened' does not depend on any axioms",
                valid + "error: Other.lean:1:1: unknown import\n", valid + "maximum number of heartbeats" })
                Program.Reject(() => Rejection(invalid, source, path, "bound"));
            Program.Reject(() => Rejection(valid, source.Replace("#print axioms bound", "#print axioms other"), path, "bound"));
        });
    }

    internal static void Rejection(string output, string source, string path, string binding)
    {
        RejectionChecks.Resources(output);
        string[] lines = source.ReplaceLineEndings("\n").Split('\n');
        int start = Array.FindIndex(lines, line => line.StartsWith($"theorem {binding}", StringComparison.Ordinal)) + 1;
        int end = Array.FindIndex(lines, line => line == $"#print axioms {binding}") + 1;
        MatchCollection errors = Regex.Matches(output.Replace('\\', '/'), @"error: ([^\n]+\.lean):(\d+):\d+:");
        if (start == 0 || end <= start || !output.Contains("'GateBinding.weakened' does not depend on any axioms", StringComparison.Ordinal)
            || errors.Count == 0 || errors.Any(error => error.Groups[1].Value != path || int.Parse(error.Groups[2].Value) < start || int.Parse(error.Groups[2].Value) >= end))
            throw new InvalidOperationException("Weak theorem did not fail its exact contract binding");
    }

    internal static void Run(Workspace workspace, bool isolated)
    {
        if (!isolated)
        {
            using ProofSession source = new(workspace);
            workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", workspace.Root, source.Directory], workspace.Root);
            workspace.CopyRegressionSource(source.Directory);
            Run(new Workspace(source.Directory), true);
            return;
        }
        Verifier verifier = new(workspace);
        verifier.Verify(new("Lsh", Safety: true));
        var inputs = workspace.Inputs();
        using ProofSession proof = new(workspace);
        string[] copied = proof.Prepare(inputs);
        Directory.CreateDirectory(Path.Combine(proof.Directory, "generated"));
        File.Copy(Path.Combine(verifier.OutputDirectory("Lsh"), "safety/Extracted.lean"), Path.Combine(proof.Directory, "generated/Extracted.lean"));
        JsonObject entry = workspace.Catalog.Entries()["Lsh"];
        const string selected = "UInt256/Methods/SelectedGate.lean";
        string target = Path.Combine(proof.Directory, selected);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.WriteAllText(target, AuditGates.Module(entry));
        string[] command = ["lake", "build", "+UInt256.Methods.SelectedGate:olean"];
        workspace.Run(command, proof.Directory, "Binding baseline");
        foreach (bool family in new[] { false, true })
        {
            JsonObject changed = entry.DeepClone().AsObject(), gate = changed["verification"]!.AsObject();
            JsonArray names = gate["auditedTheorems"]!.AsArray();
            int index = family ? names.Select(Catalog.Text).ToList().IndexOf(Catalog.Text(gate["familyCoverage"]!["theorem"])) : 0;
            if (index < 0) throw new InvalidOperationException("Missing family audit");
            names[index] = "GateBinding.weakened";
            if (family) gate["familyCoverage"]!["theorem"] = "GateBinding.weakened";
            string module = AuditGates.Module(changed).Replace("namespace UInt256Proof.Selected", Weakened + "namespace UInt256Proof.Selected", StringComparison.Ordinal);
            File.WriteAllText(target, module);
            Rejection(workspace.RunRejected(command, proof.Directory, "Binding rejection"), module, selected, family ? "bound_family_contract" : "bound_contract");
            Console.WriteLine($"PASS: clean-axiom {(family ? "family" : "selected")} theorem cannot replace the public contract");
        }
        const string safetyPath = "UInt256/Methods/Shift/SafetyAudit.lean";
        string safetyTarget = Path.Combine(proof.Directory, safetyPath);
        byte[] originalBytes = File.ReadAllBytes(safetyTarget);
        string original = Encoding.UTF8.GetString(originalBytes).ReplaceLineEndings("\n");
        command = ["lake", "build", "+UInt256.Methods.Shift.SafetyAudit:olean"];
        workspace.Run(command, proof.Directory, "Safety binding baseline");
        try
        {
            foreach (bool family in new[] { false, true })
            {
                string contract = "UInt256Proof.Shift.Safety." + (family ? "checked_shift_family_contract" : "checked_shift_contract");
                if (original.Split(contract, StringSplitOptions.None).Length != 2) throw new InvalidOperationException("Expected one safety contract application");
                int insertion = original.IndexOf("\ntheorem ", StringComparison.Ordinal);
                if (insertion < 0) throw new InvalidOperationException("Missing safety binding theorem");
                string module = original.Insert(insertion + 1, Weakened).Replace(contract, "GateBinding.weakened", StringComparison.Ordinal);
                File.WriteAllText(safetyTarget, module);
                string binding = "UInt256Proof.Shift.Safety." + (family ? "checked_shift_family_binding" : "checked_shift_binding");
                Rejection(workspace.RunRejected(command, proof.Directory, "Safety binding rejection"), module, safetyPath, binding);
                Console.WriteLine($"PASS: clean-axiom safety {(family ? "family" : "selected")} theorem cannot replace the combined contract");
            }
        }
        finally { File.WriteAllBytes(safetyTarget, originalBytes); }
        workspace.Run(command, proof.Directory, "Restored safety binding");
        Workspace.CheckProofSnapshot(proof.Directory, copied, inputs);
        if (!Workspace.SameInputs(inputs, workspace.Inputs())) throw new InvalidOperationException("Inputs changed during binding checks");
    }
}
