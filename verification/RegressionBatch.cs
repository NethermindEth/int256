// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Globalization;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

// Proof must verify on Extraction; a Rejected proof must then fail proof checking there and leave no certificate.
internal sealed record RegressionCheck(string Name, string Extraction, string Proof, string Theorem, string Passed,
    string? RejectedProof = null, string? RejectedTheorem = null);

// One runner's fixture builds, extractions and proofs over one consumer snapshot, verified in one batch.
internal sealed class RegressionBatch
{
    internal readonly string Root, Work, Consumer, Tool;
    internal readonly List<RegressionCheck> Checks = [];
    internal readonly List<string> Failed = [], Incomplete = [];

    RegressionBatch(string root, string work)
    {
        Root = root;
        Work = Path.Combine(root, "artifacts/" + work);
        Consumer = Path.Combine(Work, "consumer");
        Tool = Path.Combine(root, VerificationSupport.Tool);
    }

    // The snapshot holds every generated binding and template before a runner adds its fixture proofs.
    internal static async Task<RegressionBatch> Start(string root, string work)
    {
        RegressionBatch batch = new(root, work);
        await VerificationSupport.PrepareConsumer(root, batch.Consumer);
        return batch;
    }

    internal Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false) =>
        VerificationSupport.RunChecked(Root, executable, arguments, disableIntrinsics);

    // Each case builds into its own tree, so one fixture assembly cannot stand in for another.
    internal async Task<string> Build(string group, string fixture, string? directory = null)
    {
        string build = Path.Combine(Work, "build", directory ?? fixture);
        string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
        await Run("dotnet", ["build", Path.Combine(Root, "Tests/Fixtures", group, "Nethermind.Int256.csproj"),
            "-c", "Release", "-p:FixtureCase=" + fixture,
            "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
            "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
            "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
        return Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
    }

    // A profile with a file under manifests/profiles is custom; the extractor knows the others by name.
    internal async Task<string> Extract(string assembly, string method, string profile, string extraction,
        bool fresh = false, string[]? options = null)
    {
        extraction = Path.Combine(Work, extraction);
        if (fresh && Directory.Exists(extraction)) Directory.Delete(extraction, true);
        string custom = Path.Combine(Root, "manifests/profiles", profile + ".json");
        await Run("dotnet", [Tool, "extract", assembly, VerificationSupport.Signature(Root, method), extraction,
            File.Exists(custom) ? "@" + custom : profile, .. options ?? []]);
        return extraction;
    }

    // PrepareConsumer builds the production assembly while it materializes the method templates.
    internal Task<string> ExtractProduction(string method, string profile) => Extract(
        Path.Combine(Root, "../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll"), method, profile,
        Path.Combine("production", method, profile), options: ["--assume-initialized", "Nethermind.Int256.UInt256"]);

    // A generated proof must join the snapshot before the batch starts, or the verifier never sees it.
    internal string Proof(string name, string source)
    {
        string path = Path.Combine(Consumer, "proofs", name + ".lean");
        File.WriteAllText(path, source);
        return path;
    }

    internal void Pending(string name, string reason)
    {
        Console.WriteLine($"PENDING {name}: {reason}");
        Incomplete.Add(name);
    }

    internal void Fail(string name, string reason)
    {
        Console.WriteLine($"FAIL {name}: {reason}");
        Failed.Add(name);
    }

    internal static string InitialBytes<TOffset, TValue>(IEnumerable<(TOffset Offset, TValue Value)> cells) =>
        string.Concat(cells.Select(cell => $"offset = {cell.Offset} then {cell.Value} else if id = 0 ∧ ")) +
        "False then 0 else 0";

    internal static string InitialBytes(JsonObject bytes) =>
        InitialBytes(bytes.Select(pair => (pair.Key, pair.Value!.GetValue<int>())));

    // The little-endian 256-bit value at a witness address; bytes the witness omits are zero.
    internal static BigInteger Number(JsonObject initial, int start)
    {
        int Cell(int index) => initial[(start + index).ToString(CultureInfo.InvariantCulture)]?.GetValue<int>() ?? 0;
        return Enumerable.Range(0, 32)
            .Aggregate(BigInteger.Zero, (sum, index) => sum + ((BigInteger)Cell(index) << (8 * index)));
    }

    // Method bodies only; assembly identity and metadata tokens do not affect the checked program.
    internal static string Bodies(string extraction) => string.Join('\n', Regex.Matches(
        File.ReadAllText(Path.Combine(extraction, "Extracted.lean")), @"^def method\d+ : Method := .*?(?=^def )",
        RegexOptions.Multiline | RegexOptions.Singleline).Select(match => match.Value));

    internal static string Statement(string proof, string theorem)
    {
        Match match = Regex.Match(File.ReadAllText(proof), @"theorem\s+" + Regex.Escape(theorem) + @"\s*:(.*?):=",
            RegexOptions.Singleline);
        if (!match.Success) throw new InvalidOperationException($"Theorem {theorem} not found in {proof}");
        return Regex.Replace(match.Groups[1].Value.Trim(), @"\s+", " ");
    }

    // The witness memory makes one output byte differ from the wrapping result of the initial operands.
    internal string ByteRefutation(JsonNode witness, string operation)
    {
        int left = witness["leftBase"]!.GetValue<int>(), right = witness["rightBase"]!.GetValue<int>();
        int outputBase = witness["outputBase"]!.GetValue<int>();
        int byteIndex = witness["address"]!.GetValue<int>() - outputBase;
        return File.ReadAllText(Path.Combine(Root, "Tests/Fixtures/Common/CheckedRefutationTemplate.lean.in"))
            .Replace("@INITIAL@", InitialBytes(witness["initialBytes"]!.AsObject()))
            .Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]").Replace("@OUTPUTS@", $"[⟨0,{outputBase}⟩]")
            .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩")
            .Replace("@OUTPUT_CASE@", "subst output; rfl")
            .Replace("@CONTRACT@", "WrappingBinaryContract").Replace("@OPERATION@", operation)
            .Replace("@REFERENCES@", $"⟨0,{left}⟩ ⟨0,{right}⟩ ⟨0,{outputBase}⟩")
            .Replace("@BYTE_INDEX@", byteIndex.ToString(CultureInfo.InvariantCulture))
            .Replace("@ACTUAL@", witness["actualByte"]!.GetValue<int>().ToString(CultureInfo.InvariantCulture));
    }

    // Baseline keeps the production program and proof, a refactor changes the program and states the production
    // contract in its own proof (null for a mutation), and a mutation is refuted and rejects the production proof.
    internal void GateFixture(string family, Gate production, string statement, string fixture, string extraction,
        bool unchanged, string? fixtureProof, Func<string> refutation)
    {
        string name = $"{production.Method}/{production.Profile}/{fixture}", theorem = family + "Fixture.correct";
        if (unchanged != (fixture == "Baseline"))
            Fail(name, unchanged ? "fixture did not change the extracted program"
                : "baseline differs from the production program");
        else if (fixture == "Baseline")
            Checks.Add(new(name, extraction, production.Proof, production.Theorem, "checked production contract"));
        else if (fixtureProof is null)
            Checks.Add(new(name, extraction, Proof(
                $"{family}Fixture{fixture}{production.Method}{production.Profile.Replace("-", "")}", refutation()),
                family + "Witness.refuted", "checked contract refutation and production proof rejection",
                production.Proof, production.Theorem));
        else if (!File.Exists(fixtureProof)) Pending(name, "no fixture proof yet");
        else if (Statement(fixtureProof, theorem) != statement)
            throw new InvalidOperationException($"Fixture proof {fixtureProof} does not state the production contract");
        else Checks.Add(new(name, extraction, fixtureProof, theorem, "checked production contract"));
    }

    // One LeanCIL session shares the snapshot, support build and kernel replay; failed checks join Failed.
    async Task Verify()
    {
        if (Checks.Count == 0) return;
        // Only the last request for an output keeps its certificate, so checks must not share an extraction.
        if (Checks.GroupBy(check => Path.GetFullPath(check.Extraction), StringComparer.OrdinalIgnoreCase)
            .Any(extraction => extraction.Count() > 1))
            throw new InvalidOperationException("Regression checks share an extraction directory");
        Directory.CreateDirectory(Work);
        string manifest = Path.Combine(Work, "verify-batch.json"), log = Path.Combine(Work, "verify-batch.log");
        string results = Path.Combine(Work, "verify-batch-results.json");
        File.Delete(results);
        List<object> requests = [];
        foreach (RegressionCheck check in Checks)
        {
            requests.Add(new { output = check.Extraction, proof = check.Proof, theorem = check.Theorem });
            if (check.RejectedProof is not null)
                requests.Add(new { output = check.Extraction, proof = check.RejectedProof, theorem = check.RejectedTheorem!, expect = "rejected" });
        }
        VerificationSupport.WriteBatch(manifest, Consumer, requests);
        Console.WriteLine($"VERIFY {Checks.Count} checks ({requests.Count} requests) in one batch; log: {log}");
        string output;
        // A batch with an unmet expectation exits nonzero; its results file decides each check below.
        try
        {
            string workspaces = Math.Max(1, Environment.ProcessorCount / 4).ToString(CultureInfo.InvariantCulture);
            output = await VerificationSupport.Run(Root, "dotnet", [Tool, "verify-batch", manifest, "--results",
                results, "--parallel", workspaces], capture: true, combineOutput: true);
        }
        catch (InvalidOperationException unmet) { output = unmet.Message; }
        File.WriteAllText(log, output);
        if (output.Contains("IDE0005", StringComparison.Ordinal))
            throw new InvalidOperationException("Analyzer warning in the tool build: " + log);
        JsonElement[] outcomes = VerificationSupport.BatchOutcomes(results);
        // Results follow request order; a request without a result fails its check.
        int next = 0;
        foreach (RegressionCheck check in Checks)
        {
            int count = check.RejectedProof is null ? 1 : 2;
            List<string> problems = [];
            for (int index = next; index < next + count; index++)
            {
                string expected = index == next ? "verified" : "rejected";
                if (index >= outcomes.Length) problems.Add($"{expected}: verify-batch produced no result");
                else if (outcomes[index].GetProperty("status").GetString() != expected)
                    problems.Add($"expected {expected}, {outcomes[index].GetProperty("stage").GetString()}: {outcomes[index].GetProperty("error")}");
            }
            next += count;
            bool certified = File.Exists(Path.Combine(check.Extraction, "verified.json"));
            if (check.RejectedProof is null ? !certified : certified)
                problems.Add(certified ? "a rejected proof left a certificate" : "verification succeeded without a certificate");
            if (problems.Count == 0)
            {
                Console.WriteLine($"PASS {check.Name}: {check.Passed}");
                continue;
            }
            string detail = Path.Combine(Work, check.Name.Replace('/', '-') + ".log");
            File.WriteAllText(detail, string.Join(Environment.NewLine, problems));
            Failed.Add(check.Name);
            Console.WriteLine($"FAIL {check.Name}: see {detail}");
        }
    }

    // A pending fixture fails the run like a failed check, so missing proofs cannot pass unnoticed.
    internal async Task Finish(bool summary = false)
    {
        await Verify();
        if (summary)
        {
            int passed = Checks.Count - Failed.Count(Checks.Select(check => check.Name).Contains);
            Console.WriteLine($"SUMMARY: {passed} passed, {Failed.Count} failed, {Incomplete.Count} pending");
        }
        if (Incomplete.Count != 0) Console.WriteLine("INCOMPLETE: " + string.Join(", ", Incomplete));
        if (Failed.Count != 0)
            Console.WriteLine("FAILED: " + string.Join(", ", summary ? Failed.Order(StringComparer.Ordinal) : Failed));
        Environment.ExitCode = Incomplete.Count == 0 && Failed.Count == 0 ? 0 : 1;
    }

    internal async Task FinishOrThrow()
    {
        await Verify();
        if (Failed.Count != 0) throw new InvalidOperationException("FAILED: " + string.Join(", ", Failed));
    }
}
