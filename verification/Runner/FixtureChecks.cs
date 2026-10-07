// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace UInt256Verification;

internal static class FixtureChecks
{
    internal static void ModelRefutation(Workspace workspace, string proof, string lake, string initial, string left, string right,
        string output, string address, string actual, string expected, string method)
    {
        if (method is not ("Add" or "Subtract")) throw new ArgumentException("Unknown arithmetic refutation method");
        Dictionary<string, string> substitutions = new()
        {
            ["METHOD"] = method, ["INITIAL"] = initial, ["LEFT"] = left, ["RIGHT"] = right, ["OUT"] = output,
            ["ADDRESS"] = address, ["ACTUAL"] = actual, ["EXPECTED"] = expected,
            ["CONTRACT"] = method == "Add" ? "Contract" : "SubtractContract", ["OPERATION"] = method == "Add" ? "+" : "-"
        };
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(proof, "manifests", method.ToLowerInvariant() + ".json")))!;
        Refutation(workspace, proof, lake, Path.Combine(workspace.Verification, "Tests/Fixtures/RefutationTemplate.lean.in"), substitutions,
            "Refutation", "UInt256Proof.model_not_correct", manifest["approvedAxioms"]!.AsArray().Select(Catalog.Text), true);
    }

    internal static void NativeWitness(Workspace workspace, string destination, string assembly, string source)
    {
        string witness = Path.Combine(destination, "Witness");
        if (Directory.Exists(witness) || File.Exists(witness)) throw new InvalidOperationException("Native witness directory must be fresh");
        Directory.CreateDirectory(witness);
        string project = Path.Combine(witness, "Witness.csproj");
        var document = new System.Xml.Linq.XElement("Project", new System.Xml.Linq.XAttribute("Sdk", "Microsoft.NET.Sdk"),
            new System.Xml.Linq.XElement("PropertyGroup", new System.Xml.Linq.XElement("OutputType", "Exe"), new System.Xml.Linq.XElement("TargetFramework", "net10.0")),
            new System.Xml.Linq.XElement("ItemGroup", new System.Xml.Linq.XElement("Reference", new System.Xml.Linq.XAttribute("Include", "Nethermind.Int256"),
                new System.Xml.Linq.XElement("HintPath", Path.GetFullPath(assembly)))));
        File.WriteAllText(project, document.ToString());
        File.WriteAllText(Path.Combine(witness, "Program.cs"), source);
        string output = workspace.Run(["dotnet", "build", project, "-c", "Release", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], destination, "Native witness build");
        if (output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException("Native witness contains unused imports");
        workspace.Run(["dotnet", Path.Combine(witness, "bin/Release/net10.0/Witness.dll")], destination, "Native witness execution");
    }

    internal static string MutationSource(Catalog catalog, string project, string method, string name) => Path.Combine(Path.GetDirectoryName(project)!,
        catalog.Manifest(method)["verification"]?["fixtureSources"]?[name]?.GetValue<string>() ?? name + ".cs");

    internal static (ArtifactBundle Bundle, string Proof) Mutation(Workspace workspace, string work, string project, string name, string method,
        string profile, JsonObject baseline, string? intended)
    {
        string proof = Path.Combine(work, "proof");
        if (Directory.Exists(proof) || File.Exists(proof)) throw new InvalidOperationException("Mutation proof directory must be fresh");
        ArtifactBundle bundle = workspace.BuildArtifact(project, work, method, MutationSource(workspace.Catalog, project, method, name), true, name);
        Directory.CreateDirectory(proof);
        string[] paths = workspace.CopyProofSources(proof, bundle.SourceInputs);
        string generated = Path.Combine(proof, "generated");
        JsonObject artifact = workspace.Extract(bundle, generated, method, profile);
        ChangedMethod(artifact, baseline["artifact"]!.AsObject(), intended ?? Catalog.Text(workspace.Catalog.Manifest(method)["entry"]));
        if (Workspace.Hash(Path.Combine(generated, "Extracted.lean")) == Catalog.Text(baseline["generatedProgramSha256"]))
            throw new InvalidOperationException("Mutation did not change the extracted program");
        JsonObject hashes = baseline["leanSourceSha256"]!.AsObject();
        var actual = Workspace.SourceFiles(proof, [".lean"]).Select(path => (Path: Workspace.Relative(proof, path), Hash: Workspace.Hash(path)))
            .Where(pair => hashes.ContainsKey(pair.Path)).ToDictionary(pair => pair.Path, pair => pair.Hash);
        if (!Workspace.SameInputs(actual, hashes.ToDictionary(pair => pair.Key, pair => Catalog.Text(pair.Value))))
            throw new InvalidOperationException("Mutation changed handwritten proofs");
        Workspace.CheckProofSnapshot(proof, paths, bundle.SourceInputs);
        workspace.ValidateBundle(bundle, bundle.SourceInputs);
        return (bundle, proof);
    }

    internal static string ExpandRefutation(string source, IEnumerable<KeyValuePair<string, string>> substitutions)
    {
        foreach (var pair in substitutions) source = source.Replace($"@{pair.Key}@", pair.Value, StringComparison.Ordinal);
        if (Regex.IsMatch(source, "@[A-Z_]+@")) throw new InvalidOperationException("Unresolved refutation template input");
        return source;
    }

    internal static void Refutation(Workspace workspace, string proof, string lake, string template, IEnumerable<KeyValuePair<string, string>> substitutions,
        string module, string theorem, IEnumerable<string> approved, bool register)
    {
        string source = ExpandRefutation(File.ReadAllText(template).ReplaceLineEndings("\n"), substitutions);
        File.WriteAllText(Path.Combine(proof, module.Replace('.', '/') + ".lean"), source.ReplaceLineEndings(Environment.NewLine));
        if (register) File.AppendAllText(Path.Combine(proof, "lakefile.toml"), $"\n[[lean_lib]]\nname = \"{module}\"\n".ReplaceLineEndings(Environment.NewLine));
        string output = workspace.Run([lake, "build", $"+{module}:olean"], proof, "Refutation checking");
        ProofAudits.Check(output, [theorem], approved);
    }

    internal static void ChangedMethod(JsonObject artifact, JsonObject baseline, string signature)
    {
        JsonArray Instructions(JsonObject source)
        {
            JsonObject body = source["methods"]!.AsArray().Select(node => node!.AsObject())
                .FirstOrDefault(body => Catalog.Text(body["signature"]) == signature)
                ?? throw new InvalidOperationException($"Fixture omitted the intended compiled operation: {signature}");
            return new JsonArray(body["instructions"]!.AsArray().Select(item => (JsonNode)new JsonArray(
                item!["opcode"]?.DeepClone(), item["scope"]?.DeepClone(), item["operand"]?.DeepClone())).ToArray());
        }
        if (JsonNode.DeepEquals(Instructions(artifact), Instructions(baseline)))
            throw new InvalidOperationException("Fixture did not change the intended compiled operation");
    }

    internal static void SafetyReport(JsonObject report, string method, string profile)
    {
        if (report["evidenceKind"]?.GetValue<string>() != "arithmetic-and-memory-safety" || !JsonNode.DeepEquals(report["safety"], SafetyCatalog.Gate(method, profile)))
            throw new InvalidOperationException("Fixture prerequisite lacks the selected combined safety evidence");
    }

    internal static void Production(JsonObject production, JsonObject inputs)
    {
        if (Catalog.Text(production["source"]?["kind"]) != "production" || !JsonNode.DeepEquals(production["sourceInputs"], inputs))
            throw new InvalidOperationException("Fresh production prerequisite was not established");
    }

    internal static void Baseline(JsonObject production, JsonObject baseline, JsonObject inputs)
    {
        Production(production, inputs);
        if (!JsonNode.DeepEquals(baseline["leanSourceSha256"], production["leanSourceSha256"]))
            throw new InvalidOperationException("Fixture baseline changed handwritten proofs");
    }

    internal static void Alternative(JsonObject baseline, JsonObject alternative)
    {
        if (!JsonNode.DeepEquals(alternative["leanSourceSha256"], baseline["leanSourceSha256"]))
            throw new InvalidOperationException("Equivalent fixture changed handwritten proofs");
        if (JsonNode.DeepEquals(alternative["generatedProgramSha256"], baseline["generatedProgramSha256"]))
            throw new InvalidOperationException("Equivalent fixture did not change its actual extracted program");
    }
}
