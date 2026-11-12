#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs

if (args.Length > 2) throw new ArgumentException("Usage: ShiftPositiveRegression.cs [verification-directory] [all|scalar|x64-v3]");
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selection = args.Length > 1 ? args[1] : "all";
string[] profiles = selection switch
{
    "all" => ["scalar", "x64-v3"],
    "scalar" or "x64-v3" => [selection],
    _ => throw new ArgumentException("Unknown profile: " + selection),
};
const string fixture = "LshHelper";
string[] methods = ["Lsh", "LeftShift", "OperatorLsh"];

// Freeze the complete consumer source snapshot before issuing any certificates.
RegressionBatch batch = await RegressionBatch.Start(root, "shift-positive-regressions");
Dictionary<string, string> assemblies = [];
foreach (string variant in new[] { "Baseline", fixture }) assemblies[variant] = await batch.Build("Shift", variant);

Task<string> Extract(string variant, string method, string profile) =>
    batch.Extract(assemblies[variant], method, profile, Path.Combine(profile, variant, method), fresh: true);

// The assembly digest always differs between builds; only the extracted program text decides equivalence.
static string ProgramText(string extraction) => string.Join('\n', File.ReadAllLines(Path.Combine(extraction, "Extracted.lean"))
    .Where(line => !line.StartsWith("def assemblySha256", StringComparison.Ordinal)));

foreach (string profile in profiles)
foreach (string method in methods)
{
    string name = $"{method}/{profile}/{fixture}";
    string log = Path.Combine(batch.Work, profile, $"{method}-{fixture}.log");
    Directory.CreateDirectory(Path.GetDirectoryName(log)!);
    string proof = Path.Combine(batch.Consumer, "Tests/Fixtures/Shift", fixture,
        $"{method}_{profile.Replace('-', '_')}.lean");
    if (!File.Exists(proof))
    {
        batch.Pending(name, "no fixture proof");
        continue;
    }
    try
    {
        string extraction = await Extract(fixture, method, profile);
        if (ProgramText(await Extract("Baseline", method, profile)) == ProgramText(extraction))
            throw new InvalidOperationException("Fixture extraction does not differ from Baseline: " + extraction);
        batch.Checks.Add(new(name, extraction, proof, "UInt256Proof.Shift.Fixture.correctness",
            "full positive certificate"));
    }
    catch (InvalidOperationException exception)
    {
        File.WriteAllText(log, exception.Message);
        batch.Fail(name, "see " + log);
    }
}
await batch.Finish();
