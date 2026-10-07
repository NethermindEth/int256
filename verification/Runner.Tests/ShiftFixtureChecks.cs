// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class ShiftFixtureChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("shift fixture scope preserves direction, return contracts and exact rejection modules", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            foreach (string method in new[] { "Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh" })
            {
                bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
                string direction = Direction(method);
                var cases = Cases(workspace, method);
                Program.Require(cases.Count == (direction == "right" ? 1 : returned ? 2 : 3), "Shift witness selection changed");
                if (returned) Program.Require(!cases.ContainsKey("LshEarlyStore"), "Private output rewrite incorrectly classified as negative");
                string template = File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Shift", returned ? "OperatorRefutationTemplate.lean.in" : "RefutationTemplate.lean.in"));
                foreach (var pair in cases)
                {
                    JsonObject witness = pair.Value!.AsObject();
                    var values = Substitutions(witness, returned);
                    Program.Require(values["ACTUAL"] == witness[returned ? "operatorActual" : "actualByte"]!.ToString()
                        && values["EXPECTED"] == witness[returned ? "operatorExpected" : "expectedByte"]!.ToString(), "Witness integer precision changed");
                    string proof = FixtureChecks.ExpandRefutation(template, values);
                    Program.Require(proof.Contains("#print axioms UInt256Proof.Shift.Witness.refuted", StringComparison.Ordinal), "Refutation axiom audit missing");
                }
            }
            Program.Require(Module("left", false).EndsWith("/Entry.lean", StringComparison.Ordinal) && Module("right", false).EndsWith("/RshExecution.lean", StringComparison.Ordinal)
                && Module("left", true).EndsWith("/OperatorLshExecution.lean", StringComparison.Ordinal) && Module("right", true).EndsWith("/OperatorRshExecution.lean", StringComparison.Ordinal), "Diagnostic rejection moved from intended execution module");
            Program.Reject(() => Run(workspace, ["--method", "missing"]));
            Program.Reject(() => Run(workspace, ["--profile", "missing"]));
            Program.Reject(() => Run(workspace, ["--unknown"]));
        });
    }
    internal static string Direction(string method) => method switch
    {
        "Lsh" or "LeftShift" or "OperatorLsh" => "left",
        "Rsh" or "RightShift" or "OperatorRsh" => "right",
        _ => throw new ArgumentException("Unknown shift method")
    };
    internal static string Module(string direction, bool returned) => "UInt256/Methods/Shift/" +
        (returned ? direction == "left" ? "OperatorLshExecution" : "OperatorRshExecution" : direction == "left" ? "Entry" : "RshExecution") + ".lean";
    internal static Dictionary<string, string> Substitutions(JsonObject witness, bool returned)
    {
        Dictionary<string, string> result = new()
        {
            ["INITIAL"] = FixtureChecks.InitialBytes(witness["initialBytes"]!.AsObject().Select(pair => KeyValuePair.Create(pair.Key, pair.Value!.ToString())))
        };
        foreach (var pair in new Dictionary<string, string> { ["DIRECTION"] = "direction", ["INPUT"] = "inputBase", ["OUTPUT"] = "outputBase",
            ["COUNT"] = "count", ["ADDRESS"] = "address", ["ACTUAL"] = returned ? "operatorActual" : "actualByte", ["EXPECTED"] = returned ? "operatorExpected" : "expectedByte" })
            result[pair.Key] = witness[pair.Value]!.ToString();
        return result;
    }
    internal static JsonObject Cases(Workspace workspace, string method)
    {
        string direction = Direction(method); bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
        JsonObject cases = JsonNode.Parse(File.ReadAllText(Path.Combine(workspace.Verification, "Tests/Fixtures/Shift/Witnesses.json")))!["negativeCases"]!.AsObject();
        return new JsonObject(cases.Where(pair => Catalog.Text(pair.Value!["direction"]) == direction && (!returned || pair.Value!["operatorActual"] is not null))
            .Select(pair => KeyValuePair.Create(pair.Key, (JsonNode?)pair.Value!.DeepClone())));
    }
    internal static void Run(Workspace workspace, string[] arguments)
    {
        string method = "Lsh", profile = "scalar"; bool safety = false, isolated = false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i] == "--workspace") isolated = true;
            else if (arguments[i] == "--safety") safety = true;
            else if (arguments[i] == "--method" && i + 1 < arguments.Length) method = arguments[++i];
            else if (arguments[i] == "--profile" && i + 1 < arguments.Length) profile = arguments[++i];
            else throw new ArgumentException("Unknown or incomplete shift fixture option");
        string direction = Direction(method); bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
        workspace.Catalog.Profile(profile);
        if (!isolated)
        {
            BinaryFixtureChecks.Isolate(workspace, child => Run(child, ["--method", method, "--profile", profile, "--workspace", .. safety ? new[] { "--safety" } : []]));
            return;
        }
        var baseline = FixtureChecks.SelectedBaseline(workspace, method, profile, direction == "left" ? "LshHelper" : null, safety);
        if (method == "OperatorLsh")
        {
            workspace.Run([.. baseline.Command, "--fixture", "LshEarlyStore"], workspace.Root);
            FixtureChecks.Alternative(baseline.Baseline, JsonNode.Parse(File.ReadAllText(baseline.ReportPath))!.AsObject());
            Console.WriteLine("PASS: OperatorLsh/LshEarlyStore, private output preserves the public contract");
        }
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Shift");
        string intended = Catalog.Text(workspace.Catalog.Manifest(direction == "left" ? "Lsh" : "Rsh")["entry"]);
        foreach (var pair in Cases(workspace, method))
        {
            string name = pair.Key, work = Path.Combine(workspace.Root, "artifacts/shift-negatives", method, name);
            if (Directory.Exists(work)) throw new InvalidOperationException("Shift fixture workspace must be fresh");
            Directory.CreateDirectory(work);
            var mutation = FixtureChecks.Mutation(workspace, work, Path.Combine(directory, "Nethermind.Int256.csproj"), name, method, profile, baseline.Baseline, intended);
            FixtureChecks.Refutation(workspace, mutation.Proof, "lake", Path.Combine(directory, returned ? "OperatorRefutationTemplate.lean.in" : "RefutationTemplate.lean.in"),
                Substitutions(pair.Value!.AsObject(), returned), "UInt256.Methods.Shift.Witness", "UInt256Proof.Shift.Witness.refuted",
                workspace.Catalog.Manifest(method)["approvedAxioms"]!.AsArray().Select(Catalog.Text), false);
            string rejected = workspace.RunRejected([.. baseline.Command, "--fixture", name], workspace.Root, "Shift fixture public rejection");
            RejectionChecks.Diagnostic(rejected, Module(direction, returned),
                "unsolved goals|`simp` made no progress|omega could not prove the goal:|Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce");
            if (File.Exists(baseline.ReportPath)) throw new InvalidOperationException("Failed verification retained a successful report");
            Console.WriteLine($"PASS: {method}/{name}, full-contract refutation and public rejection");
        }
    }
}
