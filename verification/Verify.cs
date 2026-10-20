#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include VerificationRunner.cs

using System.Text.Json;

if (string.IsNullOrEmpty(Environment.GetEnvironmentVariable("LEAN_NUM_THREADS")))
    Environment.SetEnvironmentVariable("LEAN_NUM_THREADS", "2");

string action = "contracts", profile = "scalar";
string? proof = null, theorem = null;
int? parallel = null;
List<string> methods = [];
BatchGroup[]? groups = null;
bool methodsSpecified = false;
for (int index = 0; index < args.Length; index++)
{
    string option = args[index];
    if (++index == args.Length) throw new ArgumentException($"Missing value for {option}");
    switch (option)
    {
        case "--action": action = args[index].ToLowerInvariant(); break;
        case "--method": methodsSpecified = true; methods.Add(args[index]); break;
        case "--methods-json": methodsSpecified = true; methods.AddRange(JsonSerializer.Deserialize<string[]>(args[index])!); break;
        case "--groups-json": groups = JsonSerializer.Deserialize<BatchGroup[]>(args[index], VerificationSupport.Json)!; break;
        case "--profile": profile = args[index]; break;
        case "--proof": proof = args[index]; break;
        case "--theorem": theorem = args[index]; break;
        case "--parallel": parallel = int.Parse(args[index], System.Globalization.CultureInfo.InvariantCulture); break;
        default: throw new ArgumentException($"Unknown option: {option}");
    }
}
if (groups is not null && methodsSpecified) throw new ArgumentException("Use either --groups-json or --method");
if (!methodsSpecified) methods.Add("Add");
await VerificationRunner.Run(VerificationSupport.Root, new(action, methods.ToArray(), profile, proof, theorem, parallel, groups),
    async (command, arguments) => { await VerificationSupport.Run(VerificationSupport.Root, command, arguments); });
