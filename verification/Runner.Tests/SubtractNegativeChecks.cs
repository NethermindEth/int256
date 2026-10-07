// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using UInt256Verification;

namespace UInt256VerificationTests;

internal static class SubtractNegativeChecks
{
    internal static void Run(Workspace workspace)
    {
        FixtureChecks.RequireProductionReport(workspace, "Subtract");
        Check("WrongBorrow", new Dictionary<int, int> { [32] = 1, [40] = 1 }, 0, 32, 64, 72, 255, 254);
        Check("WrongAliasing", new Dictionary<int, int> { [0] = 5, [8] = 7, [64] = 1, [72] = 1 }, 0, 64, 8, 16, 3, 6);

        void Check(string name, Dictionary<int, int> bytes, int left, int right, int output, int address, int actual, int expected)
        {
            string destination = Path.Combine(Path.GetTempPath(), "int256-subtract-negative-" + name + "-" + Guid.NewGuid().ToString("N"));
            try
            {
                workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", workspace.Root, destination], workspace.Root);
                string proof = workspace.CopyRegressionSource(destination);
                var fixture = FixtureChecks.BuildExtract(workspace, destination, name, "Subtract");
                string assignments = string.Concat(bytes.Select(pair => $"bytes[{pair.Key}] = {pair.Value};"));
                FixtureChecks.NativeWitness(workspace, destination, fixture.Assembly, $$"""
                    using System; using System.Runtime.CompilerServices; using Nethermind.Int256;
                    byte[] bytes = new byte[128];{{assignments}}
                    ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{{left}}]);
                    ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{{right}}]);
                    ref UInt256 output = ref Unsafe.As<byte, UInt256>(ref bytes[{{output}}]);
                    UInt256.Subtract(in left, in right, out output);
                    if (bytes[{{address}}] != {{actual}}) Environment.Exit(1);
                    Console.WriteLine("PASS: native {{name}} witness: actual {{actual}}, expected {{expected}}");
                    """);
                string initial = string.Concat(bytes.OrderBy(pair => pair.Key).Select(pair => $"if address = {pair.Key} then {pair.Value} else ")) + "0";
                FixtureChecks.ModelRefutation(workspace, proof, "lake", initial, left.ToString(), right.ToString(), output.ToString(),
                    address.ToString(), actual.ToString(), expected.ToString(), "Subtract");
                string stale = Path.Combine(proof, "generated/subtract");
                Directory.CreateDirectory(stale);
                foreach (string artifact in new[] { "Extracted.lean", "artifact.json", "report.json" })
                    File.Copy(Path.Combine(workspace.Verification, "generated/subtract", artifact), Path.Combine(stale, artifact), true);
                string rejected = workspace.RunRejected(["dotnet", "run", "--project", Path.Combine(proof, "Runner/Verification.csproj"), "-c", "Release", "--",
                    "--root", destination, "verify", "--method", "Subtract", "--fixture", name], destination, "Subtraction negative public verifier");
                RejectionChecks.Semantic(rejected, "UInt256/Methods/Subtract/Entry.lean");
                if (!rejected.Contains("Verification failed:", StringComparison.Ordinal)) throw new InvalidOperationException("Negative fixture did not reach the public verifier failure");
                if (File.Exists(Path.Combine(stale, "report.json"))) throw new InvalidOperationException("Failed fixture retained a success report");
                Console.WriteLine($"PASS: {name} rejected at the final entry proof");
            }
            finally
            {
                if (Directory.Exists(destination)) Directory.Delete(destination, true);
            }
        }
    }
}
