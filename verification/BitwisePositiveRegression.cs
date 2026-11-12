#!/usr/bin/env dotnet
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
if (args.Length > 1) throw new ArgumentException("Usage: BitwisePositiveRegression.cs [verification-directory]");
const string fixture = "BitwiseHelper";
RegressionBatch batch = await RegressionBatch.Start(root, "bitwise-positive-regressions/" + fixture);
string assembly = await batch.Build("Bitwise", fixture);
foreach (string profile in new[] { "scalar", "x64-v3" })
foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
foreach (bool returned in new[] { false, true })
{
    bool unary = operation == "Not";
    string id = (returned ? "Operator" : "") + operation;
    string extraction = await batch.Extract(assembly, id, profile, Path.Combine(id, profile));
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
        end HelperFixture
        """;
    batch.Checks.Add(new($"{id}/{profile}/{fixture}", extraction,
        batch.Proof("Helper" + id + profile.Replace('-', '_'), proof), "HelperFixture.correct",
        "full-contract certificate"));
}
Console.WriteLine($"Prepared {batch.Checks.Count} positive {fixture} checks with a stable consumer snapshot.");
await batch.FinishOrThrow();
