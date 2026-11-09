#!/usr/bin/env dotnet
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
if (args.Length > 1) throw new ArgumentException("Usage: BitwisePositiveRegression.cs [verification-directory]");
const string fixture = "BitwiseHelper";
string work = Path.Combine(root, "artifacts/bitwise-positive-regressions", fixture);
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string fixtures = Path.Combine(root, "Tests/Fixtures/Bitwise");
Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false) =>
    VerificationSupport.RunChecked(root, executable, arguments, disableIntrinsics);
await VerificationSupport.PrepareConsumer(root, consumer);
string build = Path.Combine(work, "build");
await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release",
    "-p:FixtureCase=" + fixture, "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
    "-p:BaseIntermediateOutputPath=" + Path.Combine(build, "obj") + Path.DirectorySeparatorChar,
    "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
List<(string Directory, string Proof, string Id, string Profile)> jobs = [];
foreach (string profile in new[] { "scalar", "x64-v3" })
foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
foreach (bool returned in new[] { false, true })
{
    bool unary = operation == "Not";
    string id = (returned ? "Operator" : "") + operation;
    string extraction = Path.Combine(work, id, profile);
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == id)!["signature"]!.GetValue<string>();
    await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature,
        extraction, File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json")) ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile]);
    string operationTerm = unary ? "(~~~·)" : "(applyBinary ." + operation.ToLowerInvariant() + ")";
    string arguments = unary ? "" : "." + operation.ToLowerInvariant() + " ";
    string kind = unary ? "unary" : "binary";
    string contract = returned ? "AggregateReturn." + (unary ? "UnaryContract" : "BinaryContract") : unary ? "WrappingUnaryContract" : "WrappingBinaryContract";
    string child = $"UInt256Proof.Bitwise.Helper.{kind}_{(returned ? "result" : "correctness")} {arguments}Extracted.profile Extracted.program {(returned ? "1 2 3" : "0 1 2")} (by rfl) (by rfl) (by rfl)";
    string term = returned ? $"AggregateReturn.{kind}_checked {operationTerm} Extracted.profile Extracted.program 0 1 (by rfl) ({child})" : child;
    string supportModule = unary ? "HelperUnary" : "HelperWords";
    string proof = $$"""
        import Extracted
        import UInt256.Methods.Bitwise.{{supportModule}}
        import UInt256.Safety.AggregateReturn
        namespace HelperFixture
        open UInt256Proof.Bitwise UInt256Model.Safety UInt256Model.Bitwise
        theorem correct : {{contract}} {{operationTerm}} Extracted.program 0 :=
          {{term}}
        #print axioms correct
        end HelperFixture
        """;
    string proofPath = Path.Combine(consumer, "proofs", "Helper" + id + profile.Replace('-', '_') + ".lean");
    File.WriteAllText(proofPath, proof);
    jobs.Add((extraction, proofPath, id, profile));
}
Console.WriteLine($"Prepared {jobs.Count} positive {fixture} checks with a stable consumer snapshot.");
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck($"{job.Id}/{job.Profile}/{fixture}",
    job.Directory, job.Proof, "HelperFixture.correct", "full-contract certificate"))]);
if (failed.Count != 0) throw new InvalidOperationException("FAILED: " + string.Join(", ", failed));
