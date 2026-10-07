// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class CompiledSafetyChecks
{
    internal static readonly Dictionary<string, string?> Cases = new()
    {
        ["AlignedLoad"] = null, ["Interior"] = "values == [.scalar (.i64 1)]", ["UnalignedVector"] = "values == [.scalar (.i64 1)]",
        ["ReusedLocal"] = null, ["EndThenInterior"] = "values == [.scalar (.i64 1)]",
        ["Overread"] = ".memory .outsideAllocation (.address ⟨0, 32⟩) 8", ["InvalidThenRepaired"] = ".memory .invalidReference (.address ⟨0, 0⟩) 0",
        ["AggregateHome"] = "values == [.scalar (.i64 17)]", ["AggregateOverread"] = ".memory .outsideAllocation (.address ⟨2, 32⟩) 8",
        ["StaticLookup"] = "values == [.scalar (.i64 42)]", ["StaticOverread"] = ".memory .outsideAllocation (.address ⟨1, 0⟩) 32",
        ["InitializedVector"] = "values == [.scalar (.i64 7)]", ["UninitializedVector"] = ".memory .uninitialized (.address ⟨1, 0⟩) 32",
        ["MaskedVectorOverread"] = ".memory .outsideAllocation (.address ⟨0, 8⟩) 32", ["VectorOutsideView"] = ".memory .unreadable (.address ⟨0, 8⟩) 32",
        ["WriteThenRestore"] = ".memory .unwritable (.address ⟨0, 0⟩) 8", ["InvalidNativeOffset"] = ".memory .invalidReference (.address ⟨0, 0⟩) 0", ["EscapedLocal"] = null
    };
    internal static readonly HashSet<string> Positive = ["UnalignedVector", "Interior", "EndThenInterior", "AggregateHome", "StaticLookup", "InitializedVector"];
    internal static string? Unsupported(string name) => name switch
    {
        "EscapedLocal" or "ReusedLocal" => "Unsupported method metadata: System.UInt64& Nethermind.Int256.UInt256::Expired()",
        "AlignedLoad" => "Unsupported external dependency: System.Void* System.Runtime.CompilerServices.Unsafe::AsPointer<Nethermind.Int256.UInt256>(!!0&)",
        _ => null
    };
    private const string Probe = "System.UInt64 Nethermind.Int256.UInt256::Probe(Nethermind.Int256.UInt256&)";

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("compiled safety templates retain valid starts, full refutations and unsupported boundaries", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Safety");
            Program.Require(Cases.Count == 18 && Positive.Count == 6, "Safety fixture coverage changed");
            foreach (string name in Cases.Keys)
            {
                if (Unsupported(name) is not null)
                {
                    Program.Reject(() => ProofSource(directory, 3, name, 0, 4, 7));
                    continue;
                }
                string source = ProofSource(directory, 3, name, 0, 4, 7);
                Program.Require(source.Contains("#print axioms actual_probe", StringComparison.Ordinal) && source.Contains("StaticWorldValid", StringComparison.Ordinal), "Probe starting-state/audit missing");
                Program.Require(source.Contains("∀ fuel result", StringComparison.Ordinal) == !Positive.Contains(name), "Full-contract refutation classification changed");
                if (!Positive.Contains(name)) Program.Require(source.Contains("#print axioms public_counterexample", StringComparison.Ordinal) && source.Contains(".error ⟨4, 7,", StringComparison.Ordinal), "Public fault binding/audit missing");
            }
            Program.Reject(() => Run(workspace, ["--case", "missing"]));
            Program.Reject(() => Run(workspace, ["--work", workspace.Root]));
            Program.Reject(() => Inspect(new JsonObject { ["methods"] = new JsonArray() }, "Interior"));
        });
    }

    internal static string ProofSource(string directory, int index, string name, int entry, int faultMethod, int faultPc)
    {
        if (!Cases.TryGetValue(name, out string? rule) || rule is null) throw new ArgumentException("Unsupported extraction cannot supply a semantic proof");
        string publicRefutation = "";
        if (!Positive.Contains(name))
        {
            string publicRule = rule.Replace("⟨2, 32⟩", "⟨3, 32⟩", StringComparison.Ordinal);
            if (name is "StaticOverread" or "UninitializedVector") publicRule = publicRule.Replace("⟨1, 0⟩", "⟨2, 0⟩", StringComparison.Ordinal);
            publicRefutation = FixtureChecks.ExpandRefutation(File.ReadAllText(Path.Combine(directory, "PublicRefutation.lean.in")).ReplaceLineEndings("\n"),
                new Dictionary<string, string> { ["ENTRY"] = $"{entry}", ["FAULT"] = $"⟨{faultMethod}, {faultPc}, {publicRule}⟩" });
        }
        string match = Positive.Contains(name) ? $"| .ok (_, values) => {rule}\n  | .error _ => false" : $"| .error fault => fault.fault == {rule}\n  | .ok _ => false";
        return FixtureChecks.ExpandRefutation(File.ReadAllText(Path.Combine(directory, "ProbeAudit.lean.in")).ReplaceLineEndings("\n"), new Dictionary<string, string>
        {
            ["SIZE"] = name is "VectorOutsideView" or "UnalignedVector" ? "40" : "32", ["INPUT_BASE"] = name == "UnalignedVector" ? "8" : "0",
            ["INDEX"] = $"{index}", ["MATCH"] = match, ["PUBLIC_REFUTATION"] = publicRefutation
        });
    }

    internal static (int Index, JsonNode Body, int FaultMethod, int FaultPc) Inspect(JsonObject artifact, string name)
    {
        JsonArray methods = artifact["methods"]!.AsArray();
        int[] matches = Enumerable.Range(0, methods.Count).Where(i => Catalog.Text(methods[i]!["signature"]) == Probe).ToArray();
        Program.Require(matches.Length == 1, "Compiled fixture lacks the intended reachable probe");
        int index = matches[0], faultMethod = index;
        JsonNode body = methods[index]!;
        JsonArray instructions = body["instructions"]!.AsArray(), examined = instructions;
        string Op(JsonNode? node) => Catalog.Text(node!["opcode"]);
        string Operand(JsonNode? node) => node!["operand"]?.ToString() ?? "";
        if (name.StartsWith("Aggregate", StringComparison.Ordinal))
        {
            int[] snapshots = Enumerable.Range(0, methods.Count).Where(i => Catalog.Text(methods[i]!["signature"]) == "System.UInt64 Nethermind.Int256.UInt256::ReadSnapshot(Nethermind.Int256.UInt256)").ToArray();
            Program.Require(snapshots.Length == 1 && instructions.Any(i => Op(i) == "newobj"), "Compiler removed the constructor/snapshot helper");
            faultMethod = snapshots[0]; examined = methods[faultMethod]!["instructions"]!.AsArray();
            Program.Require(examined.Any(i => Op(i) is "ldarga" or "ldarga.s"), "Compiler removed aggregate argument address access");
            if (name == "AggregateHome") Program.Require(examined.Any(i => Op(i) == "stind.i8"), "Compiler removed private snapshot mutation");
        }
        bool vectorInitialization = name is "InitializedVector" or "UninitializedVector";
        int expectedAdds = name is "AggregateHome" or "WriteThenRestore" or "InvalidNativeOffset" or "UnalignedVector" || name.StartsWith("Static", StringComparison.Ordinal) || vectorInitialization ? 0
            : name is "InvalidThenRepaired" or "EndThenInterior" ? 2 : 1;
        Program.Require(examined.Count(i => Op(i) == "call" && Operand(i).Contains("Unsafe::Add<System.UInt64>", StringComparison.Ordinal)) == expectedAdds, "Compiler changed the intended reference arithmetic");
        bool VectorLoad(JsonNode? i) => Op(i) == "ldobj" && Operand(i).Contains("Vector256", StringComparison.Ordinal);
        if (name.StartsWith("Static", StringComparison.Ordinal))
        {
            JsonArray data = artifact["staticData"]!.AsArray(); int width = name == "StaticLookup" ? 32 : 16;
            Program.Require(data.Count == 1 && data[0]!["size"]!.GetValue<int>() == width && data[0]!["packing"]!.GetValue<int>() == 1 && Catalog.Text(data[0]!["bytes"]).Length == 2 * width, "Compiled static fixture lacks the intended extracted RVA layout");
            Program.Require(examined.Any(VectorLoad), "Compiler removed the vector read from static bytes");
        }
        else if (name == "UnalignedVector") Program.Require(examined.Any(VectorLoad), "Compiler removed the unaligned vector read");
        else if (name == "InvalidNativeOffset") Program.Require(examined.Any(i => Op(i) == "call" && Operand(i).Contains("Unsafe::Add<System.Runtime.Intrinsics.Vector256", StringComparison.Ordinal) && Operand(i).Contains("System.UIntPtr", StringComparison.Ordinal)), "Compiler removed native-width vector reference arithmetic");
        else if (name == "WriteThenRestore")
        {
            int[] stores = Enumerable.Range(0, examined.Count).Where(i => Op(examined[i]) == "stind.i8").ToArray();
            Program.Require(stores.Length == 2 && examined.Take(stores[0]).Any(i => Op(i) == "xor"), "Compiler removed the modifying write and restoring write");
        }
        else if (name is "MaskedVectorOverread" or "VectorOutsideView")
        {
            int load = Enumerable.Range(0, examined.Count).FirstOrDefault(i => VectorLoad(examined[i]), -1);
            int mask = Enumerable.Range(0, examined.Count).FirstOrDefault(i => Op(examined[i]) == "call" && Operand(examined[i]).Contains("op_BitwiseAnd", StringComparison.Ordinal), -1);
            Program.Require(load >= 0 && mask >= 0 && load < mask, "Compiler removed the vector load followed by lane masking");
        }
        else if (vectorInitialization)
        {
            Program.Require(!body["InitLocals"]!.GetValue<bool>() && examined.Any(i => Op(i) == "call" && Operand(i).Contains("Unsafe::SkipInit", StringComparison.Ordinal)), "Compiled initialization fixture lacks genuinely uninitialized storage");
            Program.Require(examined.Count(i => Op(i) == "stind.i8") == (name == "InitializedVector" ? 4 : 1), "Compiler changed the intended initialization writes");
            Program.Require(examined.Any(VectorLoad), "Compiler removed the full vector read");
        }
        else if (name != "AggregateHome") Program.Require(examined.Any(i => Op(i) == "ldind.i8"), "Compiler removed the actual memory load");
        JsonArray entry = methods[artifact["entryIndex"]!.GetValue<int>()]!["instructions"]!.AsArray();
        int call = Enumerable.Range(0, entry.Count).FirstOrDefault(i => Operand(entry[i]) == Probe, -1);
        Program.Require(call >= 0 && call + 1 < entry.Count && Op(entry[call + 1]) == "pop", "Entry does not call and discard the compiled probe result");
        int faultPc = Enumerable.Range(0, examined.Count).FirstOrDefault(pc =>
            name == "InvalidNativeOffset" && Op(examined[pc]) == "call" && Operand(examined[pc]).Contains("Unsafe::Add<System.Runtime.Intrinsics.Vector256", StringComparison.Ordinal)
            || name == "InvalidThenRepaired" && Op(examined[pc]) == "call" && Operand(examined[pc]).Contains("Unsafe::Add<System.UInt64>", StringComparison.Ordinal)
            || name is "StaticOverread" or "UninitializedVector" or "MaskedVectorOverread" or "VectorOutsideView" && Op(examined[pc]) == "ldobj"
            || name == "WriteThenRestore" && Op(examined[pc]) == "stind.i8"
            || name is not ("InvalidThenRepaired" or "StaticOverread" or "WriteThenRestore") && Op(examined[pc]) == "ldind.i8", -1);
        Program.Require(Positive.Contains(name) || faultPc >= 0, "Compiled negative fixture lacks the intended fault site");
        return (index, body, faultMethod, faultPc);
    }

    internal static void Run(Workspace workspace, string[] arguments)
    {
        string? output = null, retained = null; List<string> cases = [];
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i + 1 >= arguments.Length) throw new ArgumentException("Incomplete compiled safety option");
            switch (arguments[i])
            {
                case "--output": output = Path.GetFullPath(arguments[++i]); break;
                case "--work": retained = Path.GetFullPath(arguments[++i]); break;
                case "--case": string name = arguments[++i]; if (!Cases.ContainsKey(name)) throw new ArgumentException("Unknown safety fixture"); if (!cases.Contains(name)) cases.Add(name); break;
                default: throw new ArgumentException("Unknown compiled safety option");
            }
        }
        if (output is not null) File.Delete(output);
        if (cases.Count == 0) cases.AddRange(Cases.Keys);
        if (retained is not null && (Directory.Exists(retained) || File.Exists(retained))) throw new ArgumentException("Retained safety workspace must be new");
        string work = retained ?? Path.Combine(Path.GetTempPath(), "int256-compiled-safety-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(work);
        try { Run(workspace, work, cases, output); }
        finally { if (retained is null) Directory.Delete(work, recursive: true); }
    }

    private static void Run(Workspace workspace, string work, List<string> cases, string? output)
    {
        var inputs = workspace.Inputs();
        void CheckInputs() => Program.Require(inputs.OrderBy(p => p.Key).SequenceEqual(workspace.Inputs().OrderBy(p => p.Key)), "Compiled safety probe inputs changed");
        string directory = Path.Combine(workspace.Verification, "Tests/Fixtures/Safety"), project = Path.Combine(directory, "Nethermind.Int256.csproj");
        var bundle = workspace.BuildArtifact(project, Path.Combine(work, "shared"), "Add", project, true, cases[0]);
        List<JsonObject> receipts = [];
        foreach (string name in cases)
        {
            CheckInputs();
            string artifacts = Path.Combine(work, name, "artifacts"), assembly = bundle.Assembly;
            if (name != cases[0])
            {
                workspace.Run(["dotnet", "build", project, "-c", "Release", "--no-incremental", $"-p:FixtureCase={name}", $"-p:ArtifactsPath={artifacts}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], workspace.Root);
                assembly = Path.Combine(artifacts, "bin/Nethermind.Int256/release/Nethermind.Int256.dll");
            }
            string proof = Path.Combine(work, name, "proof"); Directory.CreateDirectory(proof);
            foreach (string source in Workspace.SourceFiles(Path.Combine(workspace.Verification, "CIL"), [".lean"]))
            {
                string destination = Path.Combine(proof, Path.GetRelativePath(workspace.Verification, source));
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!); File.Copy(source, destination);
            }
            File.Copy(Path.Combine(workspace.Verification, "lean-toolchain"), Path.Combine(proof, "lean-toolchain"));
            string configuration = Path.Combine(proof, "lakefile.toml");
            File.WriteAllText(configuration, "name = \"compiled_safety_probe\"\nversion = \"0.1.0\"\n[[lean_lib]]\nname = \"CIL\"\n[[lean_lib]]\nname = \"Extracted\"\nsrcDir = \"generated\"\n[[lean_lib]]\nname = \"ProbeAudit\"\n");
            string generated = Path.Combine(proof, "generated"), artifactPath = Path.Combine(generated, "artifact.json");
            string[] command = ["dotnet", bundle.Extractor, assembly, generated, "Add", "scalar"];
            JsonObject receipt = new() { ["case"] = name, ["assemblySha256"] = Workspace.Hash(assembly), ["extractorSha256"] = bundle.ExtractorSha256 };
            if (Unsupported(name) is string diagnostic)
            {
                string extraction = workspace.RunRejected(command, workspace.Root, "Unsupported safety extraction");
                Program.Require(extraction.Contains(diagnostic, StringComparison.Ordinal) && !File.Exists(artifactPath), "Unsupported safety fixture failed for an unrelated reason or issued an artifact");
                receipt["unsupportedFeature"] = name == "AlignedLoad" ? "raw-pointer conversion for aligned SIMD load" : "byref-returning helper";
                receipt["diagnostic"] = diagnostic; receipt["publicRefutation"] = false; receipts.Add(receipt);
                Console.WriteLine($"PASS: explicitly unsupported {name}"); continue;
            }
            workspace.Run(command, workspace.Root);
            JsonObject artifact = JsonNode.Parse(File.ReadAllText(artifactPath))!.AsObject();
            var (index, body, faultMethod, faultPc) = Inspect(artifact, name);
            string binding = Path.Combine(proof, "ProbeAudit.lean");
            File.WriteAllText(binding, ProofSource(directory, index, name, artifact["entryIndex"]!.GetValue<int>(), faultMethod, faultPc).ReplaceLineEndings(Environment.NewLine));
            bool adjacent = name == "Overread", publicRefutation = !Positive.Contains(name);
            if (adjacent)
            {
                File.Copy(Path.Combine(directory, "AdjacentAudit.lean"), Path.Combine(proof, "AdjacentAudit.lean"));
                File.AppendAllText(configuration, "\n[[lean_lib]]\nname = \"AdjacentAudit\"\n");
            }
            string result = workspace.Run(["lake", "build", adjacent ? "+AdjacentAudit:olean" : "+ProbeAudit:olean"], proof);
            List<string> names = ["CompiledSafety.actual_probe"];
            if (publicRefutation) names.Add("CompiledSafety.public_counterexample");
            if (adjacent) names.AddRange(new[] { "adjacent_public_placement", "adjacent_boundary_same_address", "adjacent_access_distinguished", "adjacent_compiled_counterexample", "result_only_same_bytes", "result_only_observation" }.Select(n => "CompiledSafety." + n));
            receipt["audits"] = JsonSerializer.SerializeToNode(ProofAudits.Check(result, names, ["propext", "Classical.choice", "Quot.sound"]));
            receipt["generatedProgramSha256"] = Workspace.Hash(Path.Combine(generated, "Extracted.lean")); receipt["bindingSha256"] = Workspace.Hash(binding);
            receipt["probe"] = body.DeepClone(); receipt["publicRefutation"] = publicRefutation;
            if (adjacent)
            {
                receipt["adjacentPlacementChecked"] = true; receipt["arithmeticCorrectUnsafeChecked"] = true;
                receipt["adjacentBindingSha256"] = Workspace.Hash(Path.Combine(proof, "AdjacentAudit.lean"));
            }
            receipts.Add(receipt); Console.WriteLine($"PASS: compiled {name} probe");
        }
        CheckInputs();
        if (output is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(output)!);
            File.WriteAllText(output, JsonSerializer.Serialize(new { kind = "compiled-safety-probes", productionCombined = false,
                fullPublicRefutation = receipts.Any(r => r["publicRefutation"]!.GetValue<bool>()), cases, startingStateChecked = cases.All(name => Unsupported(name) is null), sourceInputs = inputs, receipts }, new JsonSerializerOptions { WriteIndented = true }));
        }
    }
}
