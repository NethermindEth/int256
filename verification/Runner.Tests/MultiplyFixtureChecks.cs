// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class MultiplyFixtureChecks
{
    private const string Arguments = "Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&";
    internal static string Intended(string name) => name switch
    {
        "WrongCarry" => "System.UInt64 Nethermind.Int256.UInt256::AddAndCountCarry(System.UInt64,System.UInt64,System.UInt64&)",
        "WrongCrossProduct" => $"System.Void Nethermind.Int256.UInt256::MultiplyLimbs2x2({Arguments})",
        "WrongHighLow" => $"System.Void Nethermind.Int256.UInt256::Multiply({Arguments})",
        "WrongAliasing" => "System.Void Nethermind.Int256.UInt256::MultiplyByUInt64(Nethermind.Int256.UInt256&,System.UInt64,Nethermind.Int256.UInt256&)",
        "WrongBmiHigh" => "System.UInt64 Nethermind.Int256.UInt256::Multiply64(System.UInt64,System.UInt64,System.UInt64&)",
        _ => throw new ArgumentException("Unknown multiplication mutation")
    };
    internal static Dictionary<string, string> Substitutions(JsonObject witness)
    {
        Dictionary<string, string> result = new()
        {
            ["INITIAL"] = FixtureChecks.InitialBytes(witness["initialBytes"]!.AsObject().Select(pair => KeyValuePair.Create(pair.Key, pair.Value!.ToString())))
        };
        foreach (var pair in new Dictionary<string, string> { ["LEFT"] = "leftBase", ["RIGHT"] = "rightBase", ["OUTPUT"] = "outputBase",
            ["ADDRESS"] = "address", ["ACTUAL"] = "actualByte", ["EXPECTED"] = "expectedByte" }) result[pair.Key] = witness[pair.Value]!.ToString();
        return result;
    }
    internal static JsonObject[] Cases(Workspace workspace, string profile) => JsonNode.Parse(File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Multiply/witnesses.json")))!.AsArray()
        .Where(item => Catalog.Text(item!["profile"]) == profile).Select(item => item!.AsObject()).ToArray();
    internal static void Run(Workspace workspace, string[] arguments)
    {
        string profile = "scalar"; bool isolated = false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i] == "--workspace") isolated = true;
            else if (arguments[i] == "--profile" && i + 1 < arguments.Length) profile = arguments[++i];
            else throw new ArgumentException("Unknown or incomplete multiplication fixture option");
        workspace.Catalog.Profile(profile);
        if (!isolated)
        {
            BinaryFixtureChecks.Isolate(workspace, child => Run(child, ["--profile", profile, "--workspace"]));
            return;
        }
        var baseline = FixtureChecks.SelectedBaseline(workspace, "Multiply", profile, "AlternativeOrder", false);
        JsonObject Read() => JsonNode.Parse(File.ReadAllText(baseline.ReportPath))!.AsObject();
        string intended = $"System.Void Nethermind.Int256.UInt256::MultiplyLimbs4x4({Arguments})";
        FixtureChecks.ChangedMethod(Read()["artifact"]!.AsObject(), baseline.Baseline["artifact"]!.AsObject(), intended);
        workspace.Run([.. baseline.Command, "--fixture", "ExtractedHelper"], workspace.Root);
        JsonObject helper = Read();
        FixtureChecks.Alternative(baseline.Baseline, helper);
        FixtureChecks.ChangedMethod(helper["artifact"]!.AsObject(), baseline.Baseline["artifact"]!.AsObject(), intended);
        Console.WriteLine($"PASS: Multiply/{profile}, both equivalent implementation variants");
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Multiply");
        foreach (JsonObject witness in Cases(workspace, profile))
        {
            string name = Catalog.Text(witness["case"]), work = Path.Combine(workspace.Root, "artifacts/multiply-negatives", profile, name);
            if (Directory.Exists(work)) throw new InvalidOperationException("Multiplication fixture workspace must be fresh");
            Directory.CreateDirectory(work);
            var mutation = FixtureChecks.Mutation(workspace, work, Path.Combine(directory, "Nethermind.Int256.csproj"), name, "Multiply", profile, baseline.Baseline, Intended(name));
            FixtureChecks.Refutation(workspace, mutation.Proof, "lake", Path.Combine(directory, "RefutationTemplate.lean.in"), Substitutions(witness),
                "UInt256.Methods.Multiply.Witness", "UInt256Proof.Multiply.Witness.refuted", workspace.Catalog.Manifest("Multiply")["approvedAxioms"]!.AsArray().Select(Catalog.Text), false);
            string rejected = workspace.RunRejected([.. baseline.Command, "--fixture", name], workspace.Root, "Multiplication fixture public rejection");
            RejectionChecks.Diagnostic(rejected, "UInt256/Methods/Multiply/Entry.lean",
                "unsolved goals|`simp` made no progress|omega could not prove the goal:|Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce");
            if (File.Exists(baseline.ReportPath)) throw new InvalidOperationException("Failed verification retained a successful report");
            Console.WriteLine($"PASS: Multiply/{profile}/{name}, full-contract refutation and public rejection");
        }
    }
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("multiplication fixtures retain exact mutation targets and profile-specific witnesses", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            Program.Require(Cases(workspace, "scalar").Length == 4 && Cases(workspace, "x64-bmi2").Length == 1 && Cases(workspace, "x64-vector256").Length == 0, "Multiplication witness profile scope changed");
            string template = File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Multiply/RefutationTemplate.lean.in"));
            foreach (var witness in Cases(workspace, "scalar").Concat(Cases(workspace, "x64-bmi2")))
            {
                string name = Catalog.Text(witness["case"]);
                Program.Require(Intended(name).Contains("Nethermind.Int256.UInt256::", StringComparison.Ordinal), "Missing intended helper signature");
                var values = Substitutions(witness);
                Program.Require(values["ACTUAL"] != values["EXPECTED"], "Indistinguishable multiplication witness");
                string source = FixtureChecks.ExpandRefutation(template, values);
                Program.Require(source.Contains("#print axioms UInt256Proof.Multiply.Witness.refuted", StringComparison.Ordinal), "Missing full-contract axiom audit");
            }
            Program.Reject(() => Intended("Unknown"));
            Program.Reject(() => Run(workspace, ["--profile", "missing"]));
            Program.Reject(() => Run(workspace, ["--unknown"]));
        });
    }
}
