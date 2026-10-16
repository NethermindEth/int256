#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include ConsumerSupportSelection.cs

using System.Text.Json;
using System.Text.RegularExpressions;

string repository = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "";
string output = Environment.GetEnvironmentVariable("GITHUB_OUTPUT") ?? throw new InvalidOperationException("GITHUB_OUTPUT is required");
if (!Regex.IsMatch(repository, @"\A[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\z"))
    throw new ArgumentException("Invalid GITHUB_REPOSITORY");

// Only successful pushes to this repository's trusted main branch may certify
// support for another run. PR artifacts never supply the trusted digest.
ConsumerSupport? support = null;
try
{
    string runsJson = await VerificationSupport.Run(VerificationSupport.Root, "gh",
        ["api", $"repos/{repository}/actions/workflows/verification.yml/runs?event=push&branch=main&status=success&per_page=1"], true);
    using JsonDocument runs = JsonDocument.Parse(runsJson);
    if (ConsumerSupportSelection.TrustedRun(runs.RootElement, repository) is long run)
    {
        string artifactsJson = await VerificationSupport.Run(VerificationSupport.Root, "gh",
            ["api", $"repos/{repository}/actions/runs/{run}/artifacts?per_page=100"], true);
        using JsonDocument artifacts = JsonDocument.Parse(artifactsJson);
        support = ConsumerSupportSelection.Select(run, artifacts.RootElement);
    }
}
catch (Exception error) when (error is InvalidOperationException or JsonException)
{
    Console.WriteLine("Previous consumer support unavailable; verification will check fresh proofs.");
}
File.AppendAllText(output, $"run-id={support?.Run}\nartifact-id={support?.Artifact}\nsha256={support?.Digest}\n");
Console.WriteLine(support is null ? "No reusable main-branch artifact found." : $"Consumer support from main run {support.Run}, artifact {support.Artifact}.");
