#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
using System.Xml.Linq;

const string usage = "Usage: SafetyRegression.cs [verification-directory] [--case C]";
string? directory = null, selected = null;
for (int i = 0; i < args.Length; i++)
{
    if (args[i] == "--case" && i + 1 < args.Length) selected = args[++i];
    else if (directory is null && !args[i].StartsWith("--", StringComparison.Ordinal)) directory = args[i];
    else throw new ArgumentException(usage);
}
string root = Path.GetFullPath(directory ?? "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Safety");
const string productionTheorem = "UInt256Proof.Add.scalar_correctness";
XElement[] registry = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("SafetyCase").ToArray();
if (selected is not null && registry.All(entry => (string)entry.Attribute("Include")! != selected)) throw new ArgumentException("Unknown safety case: " + selected);
RegressionBatch batch = await RegressionBatch.Start(root, "safety-regressions");
string productionProof = Path.Combine(batch.Consumer, "proofs/AddScalar.lean");
foreach (XElement entry in registry)
{
    string name = (string)entry.Attribute("Include")!, suite = (string)entry.Attribute("Suite")!;
    if (selected is not null && selected != name) continue;
    if (suite == "upstream")
    {
        Console.WriteLine($"UPSTREAM {name}: extractor behaviour belongs to LeanCIL; see Tests/Fixtures/Safety/README.md");
        continue;
    }
    string extraction = await batch.Extract(await batch.Build("Safety", name), "Add", "scalar", name, fresh: true);
    string inputBase = (string?)entry.Attribute("InputBase") ?? "0", input = $"⟨0, {inputBase}⟩", arguments = $"{input} {input} ⟨1, 0⟩";
    bool negative = suite == "negative";
    string theorem;
    // Method indices are assigned per extraction, so methods are named in the registry.
    string Method(string name) => File.ReadLines(Path.Combine(extraction, "Extracted.lean"))
        .Select(line => System.Text.RegularExpressions.Regex.Match(line, $@"^def method(\d+)Signature : String := "".*::{name}\("))
        .Single(match => match.Success).Groups[1].Value;
    if (negative)
    {
        // The fault is pinned to its method, instruction, rule, reference and width.
        string located = $"⟨{Method((string)entry.Attribute("FaultMethod")!)}, {(string)entry.Attribute("FaultInstruction")!}, {(string)entry.Attribute("Fault")!}⟩";
        theorem = $"""
            theorem refuted : ¬ WrappingBinaryContract (· + ·) Extracted.program 0 :=
              UInt256Model.Safety.ContractRefutation.checked_binary_fault_refuted Extracted.program 0 1024 (· + ·) memory
                {arguments} {located} call (by decide) (by rfl)
            """;
    }
    else
    {
        // The public result ignores the probe, so the probe's own value is pinned separately.
        string probe = Method("Probe");
        theorem = $"""
            theorem accepted : CallingConditions Extracted.program memory [{input}, {input}] [⟨1, 0⟩] ∧
                (invoke Extracted.program 1024 0 (binaryArguments {arguments}) memory).map
                  (fun outcome => (inputValue outcome.1 ⟨1, 0⟩, outcome.2)) =
                  .ok (inputValue memory {input} + inputValue memory {input}, []) ∧
                (invoke Extracted.program 1024 {probe} [.reference (.address {input})] memory).map Prod.snd =
                  .ok [.scalar (.i64 {(string)entry.Attribute("ProbeValue")!})] := ⟨call, by rfl, by rfl⟩
            """;
    }
    string source = File.ReadAllText(Path.Combine(fixtures, "WitnessTemplate.lean.in"))
        .Replace("@INPUT_SIZE@", (string?)entry.Attribute("InputSize") ?? "32").Replace("@INPUT_BASE@", inputBase).Replace("@THEOREM@", theorem);
    batch.Checks.Add(new("Safety/" + name, extraction, batch.Proof("SafetyFixture" + name, source),
        negative ? "SafetyWitness.refuted" : "SafetyWitness.accepted",
        negative ? "checked fault refutation and production proof rejection"
            : "checked valid call returns the initial-input sum",
        negative ? productionProof : null, negative ? productionTheorem : null));
}
await batch.Finish();
