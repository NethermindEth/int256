// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Diagnostics;
using System.Text.Json;
using System.Text.RegularExpressions;

internal sealed record VerificationOptions(string Action, string[] Methods, string Profile, string? Proof = null, string? Theorem = null);

internal static class VerificationRunner
{
    internal static async Task Run(string root, VerificationOptions options, Func<string, string[], Task> command)
    {
        await command("lake", ["update"]);
        if (options.Action == "contracts")
        {
            await command("lake", ["build"]);
            await command("lake", ["env", "lean", "Audit.lean"]);
            Console.WriteLine("UInt256 contracts and supporting lemmas checked. No compiled-method certificate was produced.");
            return;
        }
        if (options.Action is not ("verify" or "extract")) throw new ArgumentException("Expected contracts, extract or verify");
        if (options.Methods.Length == 0) throw new ArgumentException("Select at least one method");
        if (options.Methods.Length > 1 && (options.Proof is not null || options.Theorem is not null))
            throw new ArgumentException("Explicit proofs require a single method");
        if (!Regex.IsMatch(options.Profile, @"\A[a-zA-Z0-9-]+\z")) throw new ArgumentException("Expected a profile name");
        using JsonDocument inventory = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")));
        Gate[] gates = VerificationSupport.Gates(root);
        await command("dotnet", ["build", ".lake/packages/leancil/Extractor", "-c", "Release"]);
        await command("dotnet", ["build", "../src/Nethermind.Int256/Nethermind.Int256.csproj", "-c", "Release"]);
        List<string> failures = [];
        const string tool = ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll";
        foreach (string method in options.Methods)
        {
            Stopwatch elapsed = Stopwatch.StartNew();
            Console.WriteLine($"START {options.Action} {method}/{options.Profile}");
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
                if (options.Action == "verify")
                    await command("dotnet", [tool, "verify", output, "--proof", proof!, "--theorem", theorem!, "--proof-root", root]);
                Console.WriteLine($"PASS {options.Action} {method}/{profile} ({elapsed.Elapsed.TotalSeconds:F1}s)");
            }
            catch (Exception exception)
            {
                failures.Add($"{method}/{options.Profile}: {exception.Message}");
                Console.Error.WriteLine(failures[^1]);
            }
        }
        if (failures.Count > 0) throw new InvalidOperationException(string.Join(Environment.NewLine, failures));
    }
}
