// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class RobustnessChecks
{
    internal static readonly string[] AddCases = ["Baseline", "CarryOr", "Renamed", "FullyInlined", "StraightLine", "ExtractedHelper", "ExpandedHardware", "ExternalHelper", "ReversedStore"];
    internal static readonly string[] SubtractCases = ["Baseline", "BorrowAlternative", "Renamed", "FullyInlined", "ExtractedHelper"];

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("robustness options retain baseline, registry order and method scope", (_, _) =>
        {
            Program.Require(Options([]).Cases.SequenceEqual(AddCases), "Default suite changed");
            Program.Require(Options(["--method", "Subtract"]).Cases.SequenceEqual(SubtractCases), "Subtract suite changed");
            var selected = Options(["--case", "Renamed", "--case", "CarryOr", "--safety"]);
            Program.Require(selected.Cases.SequenceEqual(new[] { "Baseline", "CarryOr", "Renamed" }) && selected.Safety && selected.Selected, "Subset lost baseline/order/safety");
            foreach (string[] invalid in new[] { new[] { "--method", "Other" }, new[] { "--method" }, new[] { "--unknown", "x" }, new[] { "--method", "Subtract", "--case", "CarryOr" } })
                Program.Reject(() => Options(invalid));
        });
        check("robustness fixtures enforce structure, summary fallback and unchanged proofs", (_, _) =>
        {
            foreach (string method in new[] { "Add", "Subtract" })
                foreach (string name in method == "Add" ? AddCases : SubtractCases)
                {
                    string signature = name == "ExtractedHelper" ? (method == "Add" ? "::AddPair(" : "::DifferencePair(") : "::Renamed(";
                    JsonArray instructions = new(Enumerable.Range(0, 8).Select(_ => (JsonNode)new JsonObject { ["opcode"] = "brtrue", ["operand"] = 0 }).ToArray());
                    JsonObject report = new() { ["status"] = "verified", ["source"] = new JsonObject { ["kind"] = "fixture" },
                        ["summaryRejections"] = new JsonArray(), ["leanSourceSha256"] = new JsonObject { ["proof"] = "same" },
                        ["evidenceKind"] = "arithmetic-and-memory-safety", ["safety"] = SafetyCatalog.Gate(method, "scalar"),
                        ["artifact"] = new JsonObject { ["methods"] = new JsonArray(new JsonObject { ["signature"] = signature, ["instructions"] = instructions }),
                            ["coverage"] = new JsonArray(new JsonObject { ["excluded"] = new JsonArray(Enumerable.Range(0, 513).Select(i => (JsonNode)JsonValue.Create(i)!).ToArray()) }) } };
                    string program = name is "FullyInlined" or "StraightLine" ? "" : string.Join('\n',
                        (method == "Add" ? new[] { "addScalar", "addScalarUInt64", "addWithCarry", "storeLimbs" } : new[] { "subtractScalarUInt64", "subtractWithBorrow", "storeLimbs" }).Select(role => $"def {role}Index := 0"));
                    string log = name == "ReversedStore" ? "Optional summary candidate Extracted.storeLimbsIndex was not proved" : "";
                    Check(report, program, log, method, name, true, null);
                    Program.Reject(() => Check(report, program, log, method, name, true, report));
                    JsonObject changed = report.DeepClone().AsObject(); changed["leanSourceSha256"]!["proof"] = "other";
                    Program.Reject(() => Check(report, program, log, method, name, true, changed));
                    changed = report.DeepClone().AsObject(); changed["source"]!["kind"] = "production";
                    Program.Reject(() => Check(changed, program, log, method, name, true, null));
                    changed = report.DeepClone().AsObject(); changed.Remove("evidenceKind");
                    Program.Reject(() => Check(changed, program, log, method, name, true, null));
                    if (name == "ReversedStore") Program.Reject(() => Check(report, program, "", method, name, true, null));
                    else if (name is not ("FullyInlined" or "StraightLine"))
                    {
                        Program.Reject(() => Check(report, program, "Optional summary candidate failed", method, name, true, null));
                        Program.Reject(() => Check(report, "", log, method, name, true, null));
                        changed = report.DeepClone().AsObject(); changed["summaryRejections"]!.AsArray().Add("rejected");
                        Program.Reject(() => Check(changed, program, log, method, name, true, null));
                    }
                    changed = report.DeepClone().AsObject();
                    if (name is "FullyInlined" or "StraightLine") changed["artifact"]!["methods"]!.AsArray().Add(report["artifact"]!["methods"]![0]!.DeepClone());
                    if (name == "Renamed") changed["artifact"]!["methods"]![0]!["signature"] = "::StoreLimbs(";
                    if (name == "ExtractedHelper") changed["artifact"]!["methods"]![0]!["signature"] = "::Wrong(";
                    if (name == "ExpandedHardware") changed["artifact"]!["coverage"]![0]!["excluded"]!.AsArray().RemoveAt(0);
                    if (name is "FullyInlined" or "StraightLine" or "Renamed" or "ExtractedHelper" or "ExpandedHardware")
                        Program.Reject(() => Check(changed, program, log, method, name, true, null));
                    if (name == "FullyInlined")
                    {
                        changed = report.DeepClone().AsObject(); changed["artifact"]!["methods"]![0]!["instructions"] = new JsonArray();
                        Program.Reject(() => Check(changed, program, log, method, name, true, null));
                        Program.Reject(() => Check(report, "def storeLimbsIndex := 0", log, method, name, true, null));
                    }
                }
        });
    }

    internal static (string Method, bool Safety, string[] Cases, bool Selected) Options(IReadOnlyList<string> arguments)
    {
        string method = "Add";
        bool safety = false;
        HashSet<string> selected = [];
        for (int i = 0; i < arguments.Count; i++)
        {
            string flag = arguments[i];
            if (flag == "--safety") { safety = true; continue; }
            if (++i == arguments.Count) throw new ArgumentException("Missing robustness option value");
            if (flag == "--method") method = arguments[i];
            else if (flag == "--case") selected.Add(arguments[i]);
            else throw new ArgumentException("Unknown robustness option");
        }
        string[] cases = method switch { "Add" => AddCases, "Subtract" => SubtractCases, _ => throw new ArgumentException("Unknown robustness method") };
        if (selected.Except(cases).Any()) throw new ArgumentException("Fixture does not apply to selected method");
        return (method, safety, cases.Where(name => selected.Count == 0 || name == "Baseline" || selected.Contains(name)).ToArray(), selected.Count != 0);
    }

    internal static void Check(JsonObject report, string program, string output, string method, string name, bool safety, JsonObject? baseline)
    {
        bool inlined = name is "FullyInlined" or "StraightLine";
        if (!inlined && name != "ReversedStore" && output.Contains("Optional summary candidate", StringComparison.Ordinal))
            throw new InvalidOperationException("Applicable fixture summary was unexpectedly rejected");
        if (name == "ReversedStore" && !output.Contains("Optional summary candidate Extracted.storeLimbsIndex was not proved", StringComparison.Ordinal))
            throw new InvalidOperationException("Reversed storage fixture did not exercise rejected-summary fallback");
        if (safety) FixtureChecks.SafetyReport(report, method, "scalar");
        string[] roles = method == "Add" ? ["addScalar", "addScalarUInt64", "addWithCarry", "storeLimbs"] : ["subtractScalarUInt64", "subtractWithBorrow", "storeLimbs"];
        foreach (string role in roles)
            if (program.Contains($"def {role}Index :=", StringComparison.Ordinal) == inlined)
                throw new InvalidOperationException("Fixture optional helper candidates do not match expected structure");
        if (!inlined && name != "ReversedStore" && report["summaryRejections"]!.AsArray().Count != 0)
            throw new InvalidOperationException("Required fixture summaries were not proved");
        if (Catalog.Text(report["status"]) != "verified" || Catalog.Text(report["source"]!["kind"]) != "fixture")
            throw new InvalidOperationException("Wrong fixture verification source or status");
        JsonArray methods = report["artifact"]!["methods"]!.AsArray();
        if (baseline is not null)
        {
            if (!JsonNode.DeepEquals(report["leanSourceSha256"], baseline["leanSourceSha256"]))
                throw new InvalidOperationException("Handwritten proof sources differ between fixtures");
            JsonArray Instructions(JsonNode artifact) => new(artifact["methods"]!.AsArray().Select(body => (JsonNode)new JsonArray(
                body!["instructions"]!.AsArray().Select(item => (JsonNode)new JsonArray(item!["opcode"]!.DeepClone(), item["operand"]?.DeepClone())).ToArray())).ToArray());
            if (JsonNode.DeepEquals(Instructions(report["artifact"]!), Instructions(baseline["artifact"]!)))
                throw new InvalidOperationException("Fixture instructions did not change");
        }
        if (inlined && methods.Count != 1) throw new InvalidOperationException("Complete inlining retained managed helpers");
        if (name == "FullyInlined" && methods.SelectMany(body => body!["instructions"]!.AsArray()).Count(item =>
            new[] { "brtrue", "brfalse", "beq", "bne", "bge", "blt" }.Any(prefix => Catalog.Text(item!["opcode"]).StartsWith(prefix, StringComparison.Ordinal))) < (method == "Add" ? 8 : 4))
            throw new InvalidOperationException("Complete inlining lost small-operand dispatch");
        if (name == "ExtractedHelper" && !methods.Any(body => Catalog.Text(body!["signature"]).Contains(method == "Add" ? "::AddPair(" : "::DifferencePair(", StringComparison.Ordinal)))
            throw new InvalidOperationException("New helper was not discovered");
        string[] old = method == "Add" ? ["AddScalar", "AddScalarUInt64", "AddWithCarry", "StoreLimbs"] : ["SubtractImpl", "SubtractScalar", "SubtractScalarUInt64", "SubtractWithBorrow", "StoreLimbs"];
        if (name == "Renamed" && methods.Any(body => old.Any(name => Catalog.Text(body!["signature"]).Contains($"::{name}(", StringComparison.Ordinal))))
            throw new InvalidOperationException("Renaming fixture retained old helper names");
        if (name == "ExpandedHardware" && report["artifact"]!["coverage"]!.AsArray().Sum(item => item!["excluded"]!.AsArray().Count) <= 512)
            throw new InvalidOperationException("Excluded hardware expansion did not exceed old budget");
    }

    private static void CopyTree(string source, string destination)
    {
        Directory.CreateDirectory(destination);
        foreach (string path in Directory.EnumerateFiles(source)) File.Copy(path, Path.Combine(destination, Path.GetFileName(path)));
        foreach (string path in Directory.EnumerateDirectories(source))
            if (!Workspace.BuildDirectories.Contains(Path.GetFileName(path)) && Path.GetFileName(path) != "TestResults") CopyTree(path, Path.Combine(destination, Path.GetFileName(path)));
    }

    internal static void Run(Workspace workspace, IReadOnlyList<string> arguments)
    {
        var options = Options(arguments);
        var inputs = workspace.Inputs();
        JsonObject? baseline = null;
        JsonArray results = [];
        foreach (string name in options.Cases)
        {
            Stopwatch timer = Stopwatch.StartNew();
            using ProofSession temporary = new(workspace);
            string root = temporary.Directory;
            workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", workspace.Root, root], workspace.Root);
            foreach (string directory in new[] { "src", "verification" }) CopyTree(Path.Combine(workspace.Root, directory), Path.Combine(root, directory));
            foreach (string path in Directory.EnumerateFiles(workspace.Root).Where(path => Path.GetFileName(path) is "global.json" or "README.md" or ".editorconfig" || Path.GetExtension(path).ToLowerInvariant() is ".props" or ".targets" or ".config"))
                File.Copy(path, Path.Combine(root, Path.GetFileName(path)));
            string workflows = Path.Combine(root, ".github/workflows"); Directory.CreateDirectory(workflows);
            foreach (string path in Directory.EnumerateFiles(Path.Combine(workspace.Root, ".github/workflows"), "verify-uint256*.yml")) File.Copy(path, Path.Combine(workflows, Path.GetFileName(path)));
            Workspace isolated = new(root);
            if (!Workspace.SameInputs(inputs, isolated.Inputs())) throw new InvalidOperationException("Fixture source snapshot changed");
            StringBuilder log = new();
            Workspace captured = new(root, (command, cwd, stage) => { string output = isolated.Run(command, cwd, stage); log.Append(output); return output; });
            Verifier verifier = new(captured);
            JsonObject report = verifier.Verify(new(options.Method, Safety: options.Safety, Fixture: name));
            string generated = verifier.OutputDirectory(options.Method);
            if (options.Safety) generated = Path.Combine(generated, "safety");
            Check(report, File.ReadAllText(Path.Combine(generated, "Extracted.lean")), log.ToString(), options.Method, name, options.Safety, baseline);
            baseline ??= report;
            if (!Workspace.SameInputs(inputs, isolated.Inputs()) || !Workspace.SameInputs(inputs, workspace.Inputs())) throw new InvalidOperationException("Fixture source inputs changed");
            double seconds = Math.Round(timer.Elapsed.TotalSeconds, 3);
            results.Add(new JsonObject { ["fixture"] = name, ["seconds"] = seconds, ["assemblySha256"] = report["artifact"]!["sha256"]!.DeepClone(),
                ["programSha256"] = report["generatedProgramSha256"]!.DeepClone(), ["managedMethods"] = report["artifact"]!["methods"]!.AsArray().Count });
            Console.WriteLine($"PASS: {name}, identical proof sources, {seconds}s");
        }
        Console.WriteLine(new JsonObject { ["proofSources"] = baseline!["leanSourceSha256"]!.DeepClone(), ["fixtures"] = results,
            ["combinedSafety"] = options.Safety, ["scope"] = options.Selected ? "selected" : "full" }.ToJsonString(new JsonSerializerOptions { WriteIndented = true }));
    }
}
