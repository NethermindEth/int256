// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using UInt256Verification;

namespace UInt256VerificationTests;

internal static class AddNegativeChecks
{
    private static void Isolate(Workspace workspace, Action<string, string> check)
    {
        string destination = Path.Combine(Path.GetTempPath(), "int256-add-negative-" + Guid.NewGuid().ToString("N"));
        try { check(destination, workspace.CopyRegressionSource(destination)); }
        finally { if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true); }
    }

    internal static void Run(Workspace workspace)
    {
        string baseline = FixtureChecks.RequireProductionReport(workspace, "Add");
        workspace.Run(["lake", "build", "Audit"], workspace.Verification);
        Isolate(workspace, (destination, proof) =>
        {
            var fixture = FixtureChecks.BuildExtract(workspace, destination, "WrongAliasing", "Add");
            FixtureChecks.NativeWitness(workspace, destination, fixture.Assembly, """
                using System;
                using Nethermind.Int256;
                UInt256 a = new(42, 1, 0, 0), b = new(1, 0, 0, 0);
                UInt256.Add(in a, in b, out a);
                Console.WriteLine($"Aliasing witness: limbs {a.u0},{a.u1},{a.u2},{a.u3}; expected 43,1,0,0");
                if (a.u0 != 1 || a.u1 != 1 || a.u2 != 0 || a.u3 != 0) Environment.Exit(1);
                """ + "\n");
            FixtureChecks.ModelRefutation(workspace, proof, "lake", "if address = 0 then 42 else if address = 8 ∨ address = 32 then 1 else 0", "0", "32", "8", "16", "0", "1", "Add");
            RejectionChecks.Semantic(workspace.RunRejected(["lake", "build", "Audit"], proof, "Add aliasing rejection"), "UInt256/Methods/Add/Entry.lean");
            Console.WriteLine("PASS: early output write has a concrete aliasing counterexample and fails the proof");
        });
        Isolate(workspace, (destination, proof) =>
        {
            var fixture = FixtureChecks.BuildExtract(workspace, destination, "WrongCarry", "Add");
            Program.Require(Workspace.Hash(Path.Combine(fixture.Generated, "Extracted.lean")) != Workspace.Hash(baseline), "Mutation did not change imported program");
            FixtureChecks.NativeWitness(workspace, destination, fixture.Assembly, """
                using System;
                using Nethermind.Int256;
                UInt256 a = new(ulong.MaxValue, 1, 0, 0), b = new(1, 1, 0, 0);
                UInt256.Add(a, b, out UInt256 r);
                Console.WriteLine($"Mutation witness: limbs {r.u0},{r.u1},{r.u2},{r.u3}; expected 0,3,0,0");
                if (r.u0 != 0 || r.u1 != 2 || r.u2 != 0 || r.u3 != 0) Environment.Exit(1);
                """ + "\n");
            FixtureChecks.ModelRefutation(workspace, proof, "lake", "if address < 8 then 255 else if address = 8 ∨ address = 32 ∨ address = 40 then 1 else 0", "0", "32", "64", "72", "2", "3", "Add");
            RejectionChecks.Semantic(workspace.RunRejected(["lake", "build", "Audit"], proof, "Add carry rejection"), "UInt256/Methods/Add/Entry.lean");
            Console.WriteLine("PASS: compilable wrong arithmetic changes extraction and fails the correctness proof");
            foreach (string name in new[] { "Extracted.lean", "artifact.json", "report.json" })
                File.Copy(Path.Combine(workspace.Verification, "generated", name), Path.Combine(fixture.Generated, name), true);
            string rejected = workspace.RunRejected(["dotnet", "run", "--project", Path.Combine(proof, "Runner/Verification.csproj"), "-c", "Release", "--", "verify", "--fixture", "WrongCarry"], destination, "Stale Add fixture public rejection");
            RejectionChecks.Semantic(rejected, "UInt256/Methods/Add/Entry.lean");
            Program.Require(rejected.Contains("Verification failed:", StringComparison.Ordinal), "Stale regression did not reach fresh proof checking");
            Program.Require(!File.Exists(Path.Combine(fixture.Generated, "report.json")), "Stale successful report survived failed verification");
            Console.WriteLine("PASS: stale extraction and report cannot verify a changed assembly");
        });
        string ExtractRejected(string assembly, string generated) => workspace.RunRejected(["dotnet", "run", "--project", Path.Combine(workspace.Verification, "Extractor"), "-c", "Release", "--", assembly, generated], workspace.Root, "Add infrastructure extraction rejection");
        Isolate(workspace, (destination, proof) =>
        {
            string assembly = FixtureChecks.BuildFixture(workspace, destination, "Unsupported", "Add");
            string rejected = ExtractRejected(assembly, Path.Combine(proof, "generated"));
            Program.Require(rejected.Contains("Unsupported instruction:", StringComparison.Ordinal) && rejected.Contains("div.un", StringComparison.Ordinal), "Unsupported CIL failed for an unexpected reason");
            Console.WriteLine("PASS: reachable unsupported div.un rejected explicitly");
        });
        workspace.Run(["lake", "build", "Tests.SummaryTransactions"], workspace.Verification);
        foreach (string name in new[] { "ThrowingInitializer", "BeforeFieldInit" })
            Isolate(workspace, (destination, proof) =>
            {
                string assembly = FixtureChecks.BuildFixture(workspace, destination, name, "Add");
                if (name == "ThrowingInitializer") FixtureChecks.NativeWitness(workspace, destination, assembly, """
                    using System;
                    using Nethermind.Int256;
                    UInt256 a = new(1, 1, 0, 0), b = new(2, 1, 0, 0);
                    try { UInt256.Add(in a, in b, out _); Environment.Exit(1); }
                    catch (TypeInitializationException e) when (e.InnerException is InvalidOperationException)
                    { Console.WriteLine("PASS: real execution throws during helper type initialisation"); }
                    """ + "\n");
                string rejected = ExtractRejected(assembly, Path.Combine(proof, "generated"));
                Program.Require(rejected.Contains("Unmodelled static initialisation: Nethermind.Int256.ArithmeticHelper", StringComparison.Ordinal), "Initialisation fixture rejected for an unexpected reason");
                Program.Require(!File.Exists(Path.Combine(proof, "generated/Extracted.lean")), "Unsafe initialisation produced an extracted program");
                Console.WriteLine($"PASS: {name} rejected before method-body extraction");
            });
        string metadata = Path.Combine(workspace.Verification, "Tests/RegressionFixture");
        workspace.Run(["dotnet", "build", metadata, "-c", "Release", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], workspace.Root);
        Isolate(workspace, (destination, _) =>
        {
            string assembly = FixtureChecks.BuildFixture(workspace, destination, "Baseline", "Add");
            foreach (var (mode, diagnostic) in new[] { ("unresolved", "MissingAddHelper"), ("recursion", "Recursive managed dependency"), ("layout", "Unsupported field"),
                ("cycle", "Malformed or cyclic control flow"), ("framework", "Unsupported assembly identity"), ("configuration", "Unsupported assembly identity") })
            {
                string mutated = Path.Combine(destination, mode + ".dll");
                workspace.Run(["dotnet", "run", "--project", metadata, "-c", "Release", "--no-build", "--", mode, assembly, mutated], workspace.Root);
                Program.Require(ExtractRejected(mutated, Path.Combine(destination, mode)).Contains(diagnostic, StringComparison.Ordinal), $"{mode} fixture failed for an unexpected reason");
                Console.WriteLine($"PASS: {mode} extraction fixture rejected explicitly");
            }
        });
        workspace.Run(["lake", "build", "Audit"], workspace.Verification);
    }
}
