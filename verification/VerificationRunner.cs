// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Diagnostics;
using System.Globalization;
using System.Text.Json;
using System.Text.RegularExpressions;

internal sealed record VerificationOptions(string Action, string[] Methods, string Profile, string? Proof = null, string? Theorem = null,
    int? Parallel = null, BatchGroup[]? Groups = null);

internal static class VerificationRunner
{
    internal static async Task Run(string root, VerificationOptions options, Func<string, string[], Task> command)
    {
        if (options.Action is not ("contracts" or "verify" or "extract")) throw new ArgumentException("Expected contracts, extract or verify");
        await command("lake", ["update"]);
        const string tool = ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll";
        if (options.Action == "contracts")
        {
            // The streamed build surfaces sorry warnings; the audit then kernel-replays the oleans without running UInt256 code.
            await command("lake", ["build"]);
            await command("dotnet", ["build", ".lake/packages/leancil/Extractor", "-c", "Release"]);
            await command("dotnet", [tool, "audit-library", "--project", ".", .. AuditArguments]);
            Console.WriteLine("UInt256 contracts and supporting lemmas checked. No compiled-method certificate was produced.");
            return;
        }
        BatchGroup[] groups = options.Groups ?? [new(options.Profile, options.Methods)];
        if (groups.Length == 0 || groups.Any(group => group.Methods.Length == 0)) throw new ArgumentException("Select at least one method");
        if ((groups.Length > 1 || groups[0].Methods.Length > 1) && (options.Proof is not null || options.Theorem is not null))
            throw new ArgumentException("Explicit proofs require a single method");
        if (groups.Any(group => !Regex.IsMatch(group.Profile, @"\A[a-zA-Z0-9-]+\z"))) throw new ArgumentException("Expected a profile name");
        if (groups.Select(group => group.Profile).Distinct(StringComparer.Ordinal).Count() != groups.Length)
            throw new ArgumentException("Each profile may appear in only one group");
        using JsonDocument inventory = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")));
        Gate[] gates = VerificationSupport.Gates(root);
        await command("dotnet", ["build", ".lake/packages/leancil/Extractor", "-c", "Release"]);
        // Docs beside the dll and PDB, from the same compile; the assembly is byte-identical without them.
        await command("dotnet", ["build", "../src/Nethermind.Int256/Nethermind.Int256.csproj", "-c", "Release",
            "-p:GenerateDocumentationFile=true", "-p:WarningsNotAsErrors=CS1591", "-nowarn:CS1591"]);
        Stopwatch elapsed = Stopwatch.StartNew();
        List<string> failures = [];
        List<Request> ready = [];
        foreach (var group in groups)
            await ExtractGroup(root, options with { Profile = group.Profile, Methods = group.Methods },
                inventory, gates, ready, failures, command, tool);
        // The verifier builds the union of all selected proof support once, across profiles too.
        if (ready.Count > 0) await VerifyBatch(root, options, ready, failures, command, tool);
        int total = groups.Sum(group => group.Methods.Length);
        Console.WriteLine($"{options.Action} finished in {elapsed.Elapsed.TotalSeconds:F1}s: {total - failures.Count} passed, {failures.Count} failed");
        if (failures.Count > 0) throw new InvalidOperationException(string.Join(Environment.NewLine, failures));
    }

    // UInt256 roots every library module; both namespaces must match a theorem, and only the core axioms are allowed.
    internal static readonly string[] AuditArguments =
        ["--module", "UInt256", "--prefix", "UInt256Model", "--prefix", "UInt256Proof", "--axioms", "propext,Quot.sound,Classical.choice"];

    static async Task ExtractGroup(string root, VerificationOptions options, JsonDocument inventory, Gate[] gates,
        List<Request> ready, List<string> failures, Func<string, string[], Task> command, string tool)
    {
        foreach (string method in options.Methods)
        {
            Console.WriteLine($"START extract {method}/{options.Profile}");
            try
            {
                JsonElement[] targets = inventory.RootElement.GetProperty("methods").EnumerateArray()
                    .Where(target => target.GetProperty("id").GetString() == method).ToArray();
                if (targets.Length != 1) throw new ArgumentException($"Unknown or ambiguous method ID: {method}");
                string profile = options.Profile;
                string output = $"artifacts/{method}/{profile}";
                string certificate = Path.Combine(root, output, "verified.json");
                if (File.Exists(certificate)) File.Delete(certificate);
                string? proof = options.Proof, theorem = options.Theorem;
                if (options.Action == "verify")
                {
                    if (proof is null && theorem is null)
                    {
                        Gate? gate = gates.SingleOrDefault(gate => gate.Method == method && gate.Profile == profile);
                        proof = gate?.Proof;
                        theorem = gate?.Theorem;
                    }
                    if (string.IsNullOrWhiteSpace(proof) || string.IsNullOrWhiteSpace(theorem))
                        throw new ArgumentException("No proof is registered. Supply both --proof and --theorem");
                    if (!File.Exists(Path.GetFullPath(proof, root))) throw new FileNotFoundException("Proof file not found", proof);
                }
                string profileArgument = File.Exists(Path.Combine(root, $"manifests/profiles/{profile}.json")) ? $"@manifests/profiles/{profile}.json" : profile;
                await command("dotnet", [tool, "extract", "../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll",
                    targets[0].GetProperty("signature").GetString()!, output, profileArgument, "--assume-initialized", "Nethermind.Int256.UInt256"]);
                if (options.Action == "verify") ready.Add(new(method, profile, output, proof!, theorem!));
                else Console.WriteLine($"PASS extract {method}/{profile}");
            }
            catch (Exception exception)
            {
                failures.Add($"{method}/{options.Profile}: {exception.Message}");
                Console.Error.WriteLine(failures[^1]);
            }
        }
    }

    sealed record Request(string Method, string Profile, string Output, string Proof, string Theorem);

    // One LeanCIL session shares the source snapshot, support build and kernel replay across requests.
    static async Task VerifyBatch(string root, VerificationOptions options, List<Request> batch, List<string> failures,
        Func<string, string[], Task> command, string tool)
    {
        var batchName = options.Groups is { Length: > 1 } ? "profiles" : options.Groups?[0].Profile ?? options.Profile;
        string manifest = Path.Combine(root, $"artifacts/verify-batch-{batchName}.json");
        string results = Path.Combine(root, $"artifacts/verify-batch-{batchName}-results.json");
        Directory.CreateDirectory(Path.GetDirectoryName(manifest)!);
        File.Delete(results);
        File.WriteAllText(manifest, JsonSerializer.Serialize(new
        {
            schema = 1,
            proofRoot = Path.GetFullPath(root),
            requests = batch.Select(request => new
            {
                output = Path.GetFullPath(request.Output, root),
                proof = Path.GetFullPath(request.Proof, root),
                theorem = request.Theorem,
            }),
        }));
        List<string> arguments = [tool, "verify-batch", manifest, "--results", results];
        if (options.Parallel is int parallel) arguments.AddRange(["--parallel", parallel.ToString(CultureInfo.InvariantCulture)]);
        string? error = null;
        try
        {
            await command("dotnet", [.. arguments]);
        }
        catch (Exception exception) { error = exception.Message; }
        JsonElement[] outcomes = [];
        if (File.Exists(results))
        {
            using JsonDocument document = JsonDocument.Parse(File.ReadAllText(results));
            outcomes = [.. document.RootElement.EnumerateArray().Select(outcome => outcome.Clone())];
        }
        // Results follow request order; a request without a verified result fails, including when the tool wrote none.
        for (int index = 0; index < batch.Count; index++)
        {
            string method = batch[index].Method;
            var profile = batch[index].Profile;
            if (index < outcomes.Length && outcomes[index].GetProperty("status").GetString() == "verified")
            {
                Console.WriteLine($"PASS verify {method}/{profile}");
                continue;
            }
            string reason = index < outcomes.Length
                ? $"{outcomes[index].GetProperty("stage").GetString()}: {outcomes[index].GetProperty("error").GetString()}"
                : error ?? "verify-batch produced no result";
            failures.Add($"{method}/{profile}: {reason}");
            Console.Error.WriteLine(failures[^1]);
        }
    }
}
