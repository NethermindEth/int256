// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Xml.Linq;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class EqualityFixtureChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("equality refutations retain scalar, reference and snapshot contracts and native memory checks", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Equality");
            var names = JsonNode.Parse(File.ReadAllText(Path.Combine(directory, "Witnesses.json")))!["negativeCases"]!.AsObject().Select(pair => pair.Key).ToArray();
            string template = File.ReadAllText(Path.Combine(directory, "RefutationTemplate.lean.in"));
            int checkedCases = 0;
            foreach (string method in workspace.Catalog.MethodNames.Where(name => name.StartsWith("Eq", StringComparison.Ordinal) || name.StartsWith("Ne", StringComparison.Ordinal)))
            foreach (string name in names)
            {
                if (!EqualityFixtures.Applicable(workspace, name, method, "scalar")) continue;
                var data = EqualityFixtures.Witness(workspace, name, method);
                var values = EqualityFixtures.Substitutions(workspace.Catalog, method, data);
                string source = FixtureChecks.ExpandRefutation(template, values), native = EqualityFixtures.NativeSource(workspace.Catalog, method, data);
                Program.Require(source.Contains("#print axioms refuted", StringComparison.Ordinal) && values["CONTRACT"].Contains("Extracted.program Extracted.entryIndex initial", StringComparison.Ordinal), "Full extracted-program contract/audit missing");
                Program.Require(native.Contains("bytes[i] != original[i]", StringComparison.Ordinal), "Native caller memory check missing");
                checkedCases++;
            }
            Program.Require(checkedCases == 32, "Equality witness coverage changed");
            Program.Reject(() => Run(workspace, ["--method", "Add"]));
            Program.Reject(() => Run(workspace, ["--profile", "missing"]));
            Program.Reject(() => Run(workspace, ["--case", "WrongSignedEmbedding"]));
        });
    }
    internal static void Run(Workspace workspace, string[] arguments)
    {
        string method = "EqUInt256UInt256", profile = "scalar", selected = "all"; bool isolated = false;
        for (int i = 0; i < arguments.Length; i++)
            if (arguments[i] == "--workspace") isolated = true;
            else if (arguments[i] == "--method" && i + 1 < arguments.Length) method = arguments[++i];
            else if (arguments[i] == "--profile" && i + 1 < arguments.Length) profile = arguments[++i];
            else if (arguments[i] == "--case" && i + 1 < arguments.Length) selected = arguments[++i];
            else throw new ArgumentException("Unknown or incomplete equality fixture option");
        if (!workspace.Catalog.MethodNames.Contains(method) || !(method.StartsWith("Eq", StringComparison.Ordinal) || method.StartsWith("Ne", StringComparison.Ordinal)))
            throw new ArgumentException("Unknown equality method");
        workspace.Catalog.Profile(profile);
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Equality");
        var cases = XDocument.Load(Path.Combine(directory, "Cases.props")).Descendants("EqualityCase").ToArray();
        if (selected != "all" && (!cases.Any(item => (string?)item.Attribute("Include") == selected) || !EqualityFixtures.Applicable(workspace, selected, method, profile)))
            throw new ArgumentException("Fixture case does not apply to this exact method/profile");
        if (!isolated)
        {
            BinaryFixtureChecks.Isolate(workspace, child => Run(child, ["--method", method, "--profile", profile, "--case", selected, "--workspace"]));
            return;
        }
        var baseline = FixtureChecks.SelectedBaseline(workspace, method, profile, null, false);
        foreach (var item in cases)
        {
            string name = (string)item.Attribute("Include")!;
            if (name == "Baseline" || selected != "all" && selected != name || !EqualityFixtures.Applicable(workspace, name, method, profile)) continue;
            if ((string?)item.Attribute("Suite") == "positive")
            {
                workspace.Run([.. baseline.Command, "--fixture", name], workspace.Root);
                FixtureChecks.Alternative(baseline.Baseline, JsonNode.Parse(File.ReadAllText(baseline.ReportPath))!.AsObject());
                Console.WriteLine($"PASS: {method}/{profile}/{name}, same complete public proof");
                continue;
            }
            JsonObject data = EqualityFixtures.Witness(workspace, name, method);
            string work = Path.Combine(workspace.Root, "artifacts/equality-fixtures", method, name);
            if (Directory.Exists(work)) throw new InvalidOperationException("Equality fixture workspace must be fresh");
            Directory.CreateDirectory(work);
            var mutation = FixtureChecks.Mutation(workspace, work, Path.Combine(directory, "Nethermind.Int256.csproj"), name, method, profile, baseline.Baseline, data["changedSignature"]?.GetValue<string>());
            FixtureChecks.Refutation(workspace, mutation.Proof, "lake", Path.Combine(directory, "RefutationTemplate.lean.in"), EqualityFixtures.Substitutions(workspace.Catalog, method, data),
                "Refutation", "UInt256Proof.Equality.Witness.refuted", workspace.Catalog.Manifest(method)["approvedAxioms"]!.AsArray().Select(Catalog.Text), true);
            FixtureChecks.NativeWitness(workspace, work, mutation.Bundle.Assembly, EqualityFixtures.NativeSource(workspace.Catalog, method, data));
            string rejected = workspace.RunRejected([.. baseline.Command, "--fixture", name], workspace.Root, "Equality fixture public rejection");
            string module = Catalog.Text(EqualityFixtures.Shape(workspace.Catalog, method)["kind"]) == "scalar" ? "SelectedGate"
                : method == "EqualsUInt256Value" ? "Equality/Snapshot" : method.StartsWith("Ne", StringComparison.Ordinal) ? "Equality/Unequal" : "Equality/Equal";
            RejectionChecks.Diagnostic(rejected, $"UInt256/Methods/{module}.lean", "unsolved goals|`simp` made no progress|Tactic `[^`]+` failed:.*|omega could not prove the goal:");
            if (File.Exists(baseline.ReportPath)) throw new InvalidOperationException("Rejected equality fixture retained a success report");
            Console.WriteLine($"PASS: {method}/{profile}/{name}, full-contract refutation and public rejection");
        }
    }
}
