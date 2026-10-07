// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class BinaryFixtureChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
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
            string destination = Path.Combine(Path.GetTempPath(), "int256-binary-fixtures-" + Guid.NewGuid().ToString("N"));
            try
            {
                workspace.Run(["git", "clone", "--shared", "--no-checkout", workspace.Root, destination], workspace.Root);
                workspace.CopyRegressionSource(destination);
                Run(new Workspace(destination), group, ["--profile", profile, "--workspace"]);
            }
            finally { if (Directory.Exists(destination)) Directory.Delete(destination, true); }
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
