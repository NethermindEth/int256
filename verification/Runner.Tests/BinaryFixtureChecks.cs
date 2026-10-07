// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class BinaryFixtureChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("returned bitwise witnesses preserve unary/binary contracts and caller bytes", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Bitwise/Witnesses.json")))!.AsObject();
            string template = File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Bitwise/ReturnRefutationTemplate.lean.in"));
            foreach (string method in new[] { "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot" })
            foreach (string name in witnesses["returnNegativeCases"]!.AsArray().Select(Catalog.Text))
            {
                var witness = ReturnWitness(method, witnesses["negativeCases"]![name]!.AsObject());
                string proof = FixtureChecks.ExpandRefutation(template, witness.Substitutions);
                Program.Require(proof.Contains(method == "OperatorNot" ? "NotReturnContract" : "ReturnContract", StringComparison.Ordinal)
                    && proof.Contains("#print axioms refuted", StringComparison.Ordinal), "Returned-value contract/audit lost");
                Program.Require(witness.Native.Contains("bytes.AsSpan().SequenceEqual(before)", StringComparison.Ordinal), "Native caller-memory preservation lost");
                Program.Require(witness.Substitutions["ACTUAL"] != witness.Substitutions["EXPECTED"], "Indistinguishable returned-value witness");
                if (method == "OperatorNot") Program.Require(witness.Substitutions["EXPECTED"] == "115792089237316195423570985008687907853269984665640564039457584007913129639934", "Complement witness lost precision");
            }
            Program.Reject(() => RunReturn(workspace, ["--method", "Xor"]));
            Program.Reject(() => RunReturn(workspace, ["--profile", "missing"]));
            Program.Reject(() => RunReturn(workspace, ["--unknown"]));
        });
        check("comparison and bitwise fixtures retain profiles, witnesses and full-contract bindings", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            foreach (string group in new[] { "Compare", "Bitwise" })
            {
                Program.Require(Cases(workspace, group, "scalar").Count == 2 && Cases(workspace, group, "x64-vector256").Count == (group == "Compare" ? 3 : 2), "Accelerated witness selection changed");
                string template = File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures", group, "RefutationTemplate.lean.in"));
                foreach (var pair in Cases(workspace, group, "x64-vector256"))
                {
                    var witness = pair.Value!.AsObject();
                    var substitutions = Substitutions(group, witness);
                    string proof = FixtureChecks.ExpandRefutation(template, substitutions), native = NativeSource(group, witness);
                    Program.Require(proof.Contains("refuted", StringComparison.Ordinal) && !proof.Contains("@", StringComparison.Ordinal), "Incomplete refutation expansion");
                    Program.Require(native.Contains(group == "Compare" ? "bool result = left < right" : "UInt256.Xor(in left, in right, out output)", StringComparison.Ordinal), "Native operation changed");
                    Program.Require(substitutions["ACTUAL"] != substitutions["EXPECTED"], "Indistinguishable witness");
                }
            }
            Program.Require(Settings("Compare").Method == "LtUInt256UInt256" && Settings("Bitwise").Method == "Xor", "Public operation selection changed");
            Program.Reject(() => Settings("Unknown"));
            Program.Reject(() => Run(workspace, "Compare", ["--profile", "missing"]));
            Program.Reject(() => Run(workspace, "Bitwise", ["--unknown"]));
        });
    }
    internal static (string Method, string Positive, string Module, string Diagnostic) Settings(string group) => group switch
    {
        "Compare" => ("LtUInt256UInt256", "ComparisonAlternative", "UInt256/Methods/Compare/Less.lean", "omega could not prove the goal:"),
        "Bitwise" => ("Xor", "BitwiseHelper", "UInt256/Methods/Bitwise/Xor.lean", "Tactic `introN` failed:.*|Tactic `apply` failed:.*|`simp` made no progress"),
        _ => throw new ArgumentException("Unknown binary fixture group")
    };
    internal static JsonObject Cases(Workspace workspace, string group, string profile)
    {
        JsonObject cases = JsonNode.Parse(File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures", group, "Witnesses.json")))!["negativeCases"]!.AsObject();
        bool vector = workspace.Catalog.Profile(profile)["Vector256Accelerated"]!.GetValue<bool>();
        return new JsonObject(cases.Where(pair => Catalog.Text(pair.Value!["profiles"]) == "all" || vector).Select(pair => KeyValuePair.Create(pair.Key, (JsonNode?)pair.Value!.DeepClone())));
    }
    internal static Dictionary<string, string> Substitutions(string group, JsonObject witness)
    {
        Dictionary<string, string> values = new()
        {
            ["INITIAL"] = FixtureChecks.InitialBytes(witness["initialBytes"]!.AsObject().Select(pair => KeyValuePair.Create(pair.Key, pair.Value!.ToString()))),
            ["LEFT"] = witness["leftBase"]!.ToString(), ["RIGHT"] = witness["rightBase"]!.ToString()
        };
        if (group == "Compare")
        {
            values["ACTUAL"] = witness["actualResult"]!.ToString(); values["EXPECTED"] = witness["expectedResult"]!.GetValue<int>() != 0 ? "true" : "false";
        }
        else
        {
            values["OUT"] = witness["outputBase"]!.ToString(); values["ADDRESS"] = witness["witnessAddress"]!.ToString();
            values["ACTUAL"] = witness["actualByte"]!.ToString(); values["EXPECTED"] = witness["expectedByte"]!.ToString();
        }
        return values;
    }
    internal static string NativeSource(string group, JsonObject witness)
    {
        string assignments = string.Join('\n', witness["initialBytes"]!.AsObject().Select(pair => $"bytes[{pair.Key}] = {pair.Value};"));
        string header = "using System;\nusing System.Runtime.CompilerServices;\nusing Nethermind.Int256;\n";
        return header + (group == "Compare" ? $$"""
            byte[] bytes = new byte[128];
            {{assignments}}
            UInt256 left = Unsafe.ReadUnaligned<UInt256>(ref bytes[{{witness["leftBase"]}}]);
            UInt256 right = Unsafe.ReadUnaligned<UInt256>(ref bytes[{{witness["rightBase"]}}]);
            bool result = left < right;
            Console.WriteLine($"Native comparison witness: {result}");
            return result == {{(witness["actualResult"]!.GetValue<int>() != 0 ? "true" : "false")}} ? 0 : 1;
            """ : $$"""
            byte[] bytes = new byte[192];
            {{assignments}}
            ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{{witness["leftBase"]}}]);
            ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{{witness["rightBase"]}}]);
            ref UInt256 output = ref Unsafe.As<byte, UInt256>(ref bytes[{{witness["outputBase"]}}]);
            UInt256.Xor(in left, in right, out output);
            byte result = bytes[{{witness["witnessAddress"]}}];
            Console.WriteLine($"Native bitwise witness: {result}");
            return result == {{witness["actualByte"]}} ? 0 : 1;
            """) + "\n";
    }
    internal static (string Dependency, string? Operation, string Symbol) ReturnSettings(string method) => method switch
    {
        "OperatorXor" => ("Xor", "xor", "^"), "OperatorAnd" => ("And", "and", "&"),
        "OperatorOr" => ("Or", "or", "|"), "OperatorNot" => ("Not", null, "~"),
        _ => throw new ArgumentException("Unknown returning bitwise method")
    };
    internal static (Dictionary<string, string> Substitutions, string Native) ReturnWitness(string method, JsonObject witness)
    {
        var settings = ReturnSettings(method);
        string left = witness["leftBase"]!.ToString(), right = witness["rightBase"]!.ToString();
        string actual = method is "OperatorAnd" or "OperatorOr" ? "0" : method == "OperatorNot" ? "1" : witness["actualReturn"]!.ToString();
        string expected = method is "OperatorAnd" or "OperatorOr" ? "1" : method == "OperatorNot" ? ((System.Numerics.BigInteger.One << 256) - 2).ToString() : witness["expectedReturn"]!.ToString();
        bool unary = settings.Operation is null;
        Dictionary<string, string> substitutions = new()
        {
            ["INITIAL"] = FixtureChecks.InitialBytes(witness["initialBytes"]!.AsObject().Select(pair => KeyValuePair.Create(pair.Key, pair.Value!.ToString()))),
            ["LEFT"] = left, ["RIGHT"] = right, ["ACTUAL"] = actual, ["EXPECTED"] = expected,
            ["ARGUMENTS"] = unary ? $"[.object {left}]" : $"[.object {left},.object {right}]",
            ["EXPECTED_EXPRESSION"] = unary ? $"~~~byteValue initial {left}" : $"UInt256Model.Bitwise.applyBinary .{settings.Operation} (byteValue initial {left}) (byteValue initial {right})",
            ["CONTRACT"] = unary ? $"UInt256Model.Bitwise.NotReturnContract Extracted.program Extracted.entryIndex initial {left}"
                : $"UInt256Model.Bitwise.ReturnContract Extracted.program Extracted.entryIndex .{settings.Operation} initial {left} {right}",
            ["PARAMETERS"] = unary ? $"initial {left}" : $".{settings.Operation} initial {left} {right}",
            ["REFUTATION"] = "UInt256Proof.Bitwise." + (unary ? "not_return_observation_refuted" : "return_observation_refuted")
        };
        string assignments = string.Join('\n', witness["initialBytes"]!.AsObject().Select(pair => $"bytes[{pair.Key}] = {pair.Value};"));
        string source = $$"""
            using System;
            using System.Runtime.CompilerServices;
            using Nethermind.Int256;
            byte[] bytes = new byte[192];
            {{assignments}}
            byte[] before = (byte[])bytes.Clone();
            ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{{left}}]);
            ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{{right}}]);
            UInt256 result = {{(unary ? "~left" : "left " + settings.Symbol + " right")}};
            Console.WriteLine($"Native returned bitwise witness: {result.u0}");
            return result.u0 == {{actual}} && result.u1 == 0 && result.u2 == 0 && result.u3 == 0
                && bytes.AsSpan().SequenceEqual(before) ? 0 : 1;
            """ + "\n";
        return (substitutions, source);
    }
    internal static void RunReturn(Workspace workspace, string[] arguments)
    {
        string method = "OperatorXor", profile = "scalar"; bool isolated = false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i] == "--workspace") isolated = true;
            else if (arguments[i] == "--method" && i + 1 < arguments.Length) method = arguments[++i];
            else if (arguments[i] == "--profile" && i + 1 < arguments.Length) profile = arguments[++i];
            else throw new ArgumentException("Unknown or incomplete returning bitwise option");
        var settings = ReturnSettings(method);
        workspace.Catalog.Profile(profile);
        if (!isolated)
        {
            Isolate(workspace, child => RunReturn(child, ["--method", method, "--profile", profile, "--workspace"]));
            return;
        }
        var baseline = FixtureChecks.SelectedBaseline(workspace, method, profile, "BitwiseHelper", false);
        workspace.Run([.. baseline.Command, "--fixture", "BitwiseEarlyStore"], workspace.Root);
        JsonObject positive = JsonNode.Parse(File.ReadAllText(baseline.ReportPath))!.AsObject();
        if (!JsonNode.DeepEquals(positive["leanSourceSha256"], baseline.Baseline["leanSourceSha256"])) throw new InvalidOperationException("Private output fixture changed handwritten proofs");
        string intended = Catalog.Text(workspace.Catalog.Manifest(settings.Dependency)["entry"]);
        JsonNode Instructions(JsonObject report) => report["artifact"]!["methods"]!.AsArray().First(body => Catalog.Text(body!["signature"]) == intended)!["instructions"]!;
        if (JsonNode.DeepEquals(Instructions(positive), Instructions(baseline.Baseline))) throw new InvalidOperationException("Private output fixture did not change the actual selected dependency");
        Console.WriteLine("PASS: early output stores preserve returned arithmetic and caller bytes");
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Bitwise");
        JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(directory, "Witnesses.json")))!.AsObject();
        foreach (string name in witnesses["returnNegativeCases"]!.AsArray().Select(Catalog.Text))
        {
            string work = Path.Combine(workspace.Root, "artifacts/bitwise-return-negatives", method, name);
            if (Directory.Exists(work)) throw new InvalidOperationException("Returning bitwise fixture workspace must be fresh");
            Directory.CreateDirectory(work);
            string target = settings.Operation == "xor" ? intended : $"System.UInt64 Nethermind.Int256.UInt256::Word{settings.Dependency}(System.UInt64" + (settings.Operation is null ? ")" : ",System.UInt64)");
            var mutation = FixtureChecks.Mutation(workspace, work, Path.Combine(directory, "Nethermind.Int256.csproj"), name, method, profile, baseline.Baseline, target);
            var witness = ReturnWitness(method, witnesses["negativeCases"]![name]!.AsObject());
            FixtureChecks.Refutation(workspace, mutation.Proof, "lake", Path.Combine(directory, "ReturnRefutationTemplate.lean.in"), witness.Substitutions,
                "ReturnRefutation", "UInt256Proof.Bitwise.ReturnWitness.refuted", workspace.Catalog.Manifest(method)["approvedAxioms"]!.AsArray().Select(Catalog.Text), true);
            FixtureChecks.NativeWitness(workspace, work, mutation.Bundle.Assembly, witness.Native);
            string rejected = workspace.RunRejected([.. baseline.Command, "--fixture", name], workspace.Root, "Returned bitwise public rejection");
            RejectionChecks.Diagnostic(rejected, "UInt256/Methods/SelectedGate.lean", "Tactic `first` failed:.*|Tactic `introN` failed:.*|Tactic `apply` failed:.*");
            if (File.Exists(baseline.ReportPath)) throw new InvalidOperationException("Failed returned-value verification retained a report");
            Console.WriteLine($"PASS: {name}, returned-value full-contract refutation and public rejection");
        }
    }
    private static void Isolate(Workspace workspace, Action<Workspace> run)
    {
        string destination = Path.Combine(Path.GetTempPath(), "int256-binary-fixtures-" + Guid.NewGuid().ToString("N"));
        try
        {
            workspace.Run(["git", "clone", "--shared", "--no-checkout", workspace.Root, destination], workspace.Root);
            workspace.CopyRegressionSource(destination);
            run(new Workspace(destination));
        }
        finally { if (Directory.Exists(destination)) Directory.Delete(destination, true); }
    }
    internal static void Run(Workspace workspace, string group, string[] arguments)
    {
        var settings = Settings(group);
        string profile = "scalar"; bool isolated = false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i] == "--workspace") isolated = true;
            else if (arguments[i] == "--profile" && i + 1 < arguments.Length) profile = arguments[++i];
            else throw new ArgumentException("Unknown or incomplete binary fixture option");
        JsonObject cases = Cases(workspace, group, profile);
        if (!isolated)
        {
            Isolate(workspace, child => Run(child, group, ["--profile", profile, "--workspace"]));
            return;
        }
        var baseline = FixtureChecks.SelectedBaseline(workspace, settings.Method, profile, settings.Positive, false);
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures", group), project = Path.Combine(directory, "Nethermind.Int256.csproj");
        var approved = workspace.Catalog.Manifest(settings.Method)["approvedAxioms"]!.AsArray().Select(Catalog.Text).ToArray();
        foreach (var pair in cases)
        {
            string name = pair.Key, work = Path.Combine(workspace.Root, "artifacts", group == "Compare" ? "comparison-negatives" : "bitwise-negatives", name);
            if (Directory.Exists(work)) throw new InvalidOperationException("Negative fixture workspace must be fresh");
            Directory.CreateDirectory(work);
            JsonObject witness = pair.Value!.AsObject();
            var mutation = FixtureChecks.Mutation(workspace, work, project, name, settings.Method, profile, baseline.Baseline, null);
            FixtureChecks.Refutation(workspace, mutation.Proof, "lake", Path.Combine(directory, "RefutationTemplate.lean.in"), Substitutions(group, witness),
                "Refutation", $"UInt256Proof.{group}.Witness.refuted", approved, true);
            if (Catalog.Text(witness["profiles"]) == "all") FixtureChecks.NativeWitness(workspace, work, mutation.Bundle.Assembly, NativeSource(group, witness));
            string rejected = workspace.RunRejected([.. baseline.Command, "--fixture", name], workspace.Root, "Binary fixture public rejection");
            RejectionChecks.Diagnostic(rejected, settings.Module, settings.Diagnostic);
            if (File.Exists(baseline.ReportPath)) throw new InvalidOperationException("Failed verification retained a successful report");
            Console.WriteLine($"PASS: {name}, independent full-contract refutation and public rejection");
        }
    }
}
