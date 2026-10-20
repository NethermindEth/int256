#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include VerificationSelection.cs

using System.Text.Json;

List<string> paths = [];
bool all = false;
string? eventName = null, first = null, last = null, output = null;
for (int index = 0; index < args.Length; index++)
{
    string option = args[index];
    if (option == "--all") { all = true; continue; }
    if (++index == args.Length) throw new ArgumentException($"Missing value for {option}");
    switch (option)
    {
        case "--changed-path": paths.Add(args[index]); break;
        case "--event": eventName = args[index]; break;
        case "--base": first = args[index]; break;
        case "--head": last = args[index]; break;
        case "--output": output = args[index]; break;
        default: throw new ArgumentException($"Unknown option: {option}");
    }
}
if (eventName == "pull_request")
{
    if (string.IsNullOrWhiteSpace(first) || string.IsNullOrWhiteSpace(last)) throw new ArgumentException("PR selection requires --base and --head");
    string changed = await VerificationSupport.Run(VerificationSupport.Root, "git", ["diff", "--name-only", "--no-renames", "-z", $"{first}...{last}"], true);
    paths.AddRange(changed.Split('\0', StringSplitOptions.RemoveEmptyEntries));
}
else if (eventName is not null) all = true;
Selection selection = VerificationSelection.Select(VerificationSupport.Root, paths, all);
Console.WriteLine(JsonSerializer.Serialize(selection, VerificationSupport.Json));
if (output is not null)
{
    // A placeholder keeps GitHub's matrix valid when the entire job is skipped.
    Batch[] batches = selection.Batches.Length == 0 ? [new("none", false, [new("scalar", [])])] : selection.Batches;
    File.AppendAllText(output, $"contracts={selection.Contracts.ToString().ToLowerInvariant()}\n" +
        $"count={selection.Include.Length}\n" +
        "matrix=" + JsonSerializer.Serialize(new { include = batches }, VerificationSupport.Json) + "\n");
}
