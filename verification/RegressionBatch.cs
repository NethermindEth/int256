// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Diagnostics;
using System.Globalization;
using System.Text.Json;

// Proof must verify on Extraction; a Rejected proof must then fail proof checking there and leave no certificate.
internal sealed record RegressionCheck(string Name, string Extraction, string Proof, string Theorem, string Passed,
    string? RejectedProof = null, string? RejectedTheorem = null);

internal static class RegressionBatch
{
    // One LeanCIL session shares the snapshot, support build and kernel replay; returns the names of failed checks.
    internal static async Task<List<string>> Verify(string root, string tool, string work, string consumer, IReadOnlyList<RegressionCheck> checks)
    {
        List<string> failed = [];
        if (checks.Count == 0) return failed;
        // Only the last request for an output keeps its certificate, so checks must not share an extraction.
        if (checks.GroupBy(check => Path.GetFullPath(check.Extraction), StringComparer.OrdinalIgnoreCase).Any(group => group.Count() > 1))
            throw new InvalidOperationException("Regression checks share an extraction directory");
        Directory.CreateDirectory(work);
        string manifest = Path.Combine(work, "verify-batch.json"), results = Path.Combine(work, "verify-batch-results.json");
        string log = Path.Combine(work, "verify-batch.log");
        File.Delete(results);
        List<object> requests = [];
        foreach (RegressionCheck check in checks)
        {
            requests.Add(new { output = check.Extraction, proof = check.Proof, theorem = check.Theorem });
            if (check.RejectedProof is not null)
                requests.Add(new { output = check.Extraction, proof = check.RejectedProof, theorem = check.RejectedTheorem!, expect = "rejected" });
        }
        File.WriteAllText(manifest, JsonSerializer.Serialize(new { schema = 1, proofRoot = consumer, requests }));
        ProcessStartInfo start = new("dotnet") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
        foreach (string argument in new[] { tool, "verify-batch", manifest, "--results", results,
            "--parallel", Math.Max(1, Environment.ProcessorCount / 4).ToString(CultureInfo.InvariantCulture) })
            start.ArgumentList.Add(argument);
        Console.WriteLine($"VERIFY {checks.Count} checks ({requests.Count} requests) in one batch; log: {log}");
        using (Process process = Process.Start(start) ?? throw new InvalidOperationException("dotnet"))
        {
            Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            string output = await stdout + await stderr;
            File.WriteAllText(log, output);
            if (output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException("Analyzer warning in the tool build: " + log);
        }
        JsonElement[] outcomes = [];
        if (File.Exists(results))
        {
            using JsonDocument document = JsonDocument.Parse(File.ReadAllText(results));
            outcomes = [.. document.RootElement.EnumerateArray().Select(outcome => outcome.Clone())];
        }
        // Results follow request order; a request without a result fails its check.
        int next = 0;
        foreach (RegressionCheck check in checks)
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
            string detail = Path.Combine(work, check.Name.Replace('/', '-') + ".log");
            File.WriteAllText(detail, string.Join(Environment.NewLine, problems));
            failed.Add(check.Name);
            Console.WriteLine($"FAIL {check.Name}: see {detail}");
        }
        return failed;
    }
}
