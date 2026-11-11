#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false

using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Text.Json;
using System.Text.RegularExpressions;

var root = Path.GetDirectoryName(Source())!;
var check = args is ["--check"];
var prepare = args is ["--prepare"];
if (args.Length != 0 && !check && !prepare)
    throw new ArgumentException("Expected no arguments, --check or --prepare");
if (prepare)
{
    Run("lake", "update");
    Run("dotnet", "build", ".lake/packages/leancil/Extractor", "-c", "Release");
    Run("dotnet", "build", "../src/Nethermind.Int256/Nethermind.Int256.csproj", "-c", "Release",
        "-p:GenerateDocumentationFile=true", "-p:WarningsNotAsErrors=CS1591", "-nowarn:CS1591");
}
var tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
var assembly = Path.GetFullPath(Path.Combine(root,
    "../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll"));
var output = Path.Combine(root, "artifacts/generated-templates");
Directory.CreateDirectory(output);
var methods = Run("dotnet", tool, "list", assembly).Split('\n', StringSplitOptions.TrimEntries);
List<string> extractions = [];
Generate("Add", "AddScalar", ["scalar", "arm64-advsimd", "x64-sse42"]);
Generate("PrepareAdd", "PrepareAdd", ["x64-v3", "x64-v4"]);
Generate("Subtract", "SubtractScalar", ["scalar", "arm64-advsimd", "x64-sse42"]);
Generate("Multiply", "Multiply", ["scalar", "arm64-advsimd", "x64-v3", "x64-v4"],
    "System.Void Nethermind.Int256.UInt256::Multiply(Nethermind.Int256.UInt256&," +
    "Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)");
Generate("LeftShift", "LeftShift", ["scalar"],
    "System.Void Nethermind.Int256.UInt256::LeftShift(System.Int32,Nethermind.Int256.UInt256&)");
Generate("RightShift", "RightShift", ["scalar"],
    "System.Void Nethermind.Int256.UInt256::RightShift(System.Int32,Nethermind.Int256.UInt256&)");
Generate("AddWide", "Add", ["x64-v3", "x64-v4"],
    "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&," +
    "Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)");
Generate("AddOverflowWide", "AddOverflow", ["x64-v3", "x64-v4"],
    "System.Boolean Nethermind.Int256.UInt256::AddOverflow(Nethermind.Int256.UInt256&," +
    "Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)");
Generate("SubtractWide", "SubtractImpl", ["x64-v3", "x64-v4"]);
WriteTemplates();

void Generate(string name, string method, string[] profiles, string? signature = null)
{
    var selector = methods.Single(line => signature is null
        ? line.Contains("::" + method + "(", StringComparison.Ordinal) : line == signature);
    var selected = profiles.Select(profile => Path.Combine(output, name + "-" + profile)).ToArray();
    for (var index = 0; index < profiles.Length; index++)
        Run("dotnet", tool, "extract", assembly, selector, selected[index], profiles[index],
            "--assume-initialized", "Nethermind.Int256.UInt256");
    extractions.AddRange(selected);
}

void WriteTemplates()
{
    var shared = Path.Combine(output, "Method");
    Run("dotnet", [tool, "templates", shared, .. extractions]);
    using var manifest = JsonDocument.Parse(File.ReadAllText(Path.Combine(shared, "templates.json")));
    if (manifest.RootElement.GetProperty("schema").GetInt32() != 1)
        throw new InvalidOperationException("Unsupported template schema");
    var source = File.ReadAllText(Path.Combine(shared, "Templates.lean"))
        .Replace("namespace Templates\n", "namespace UInt256Proof.Generated.Method\n", StringComparison.Ordinal)
        .Replace("\nend Templates", "\nend UInt256Proof.Generated.Method", StringComparison.Ordinal);
    var lines = source.Split('\n');
    var emittedMethods = Regex.Matches(source, @"(?m)^@\[cil_code\] def (method[0-9]+) ")
        .Select(match => match.Groups[1].Value).ToArray();
    if (emittedMethods.Length != manifest.RootElement.GetProperty("methods").GetArrayLength() || emittedMethods.Length == 0)
        throw new InvalidOperationException("Unexpected generated method declarations");
    foreach (var methodName in emittedMethods)
        if (lines.Count(line => line.TrimEnd() == "cil_instruction_equations " + methodName) != 1 ||
            !lines.Any(line => line.StartsWith("#print axioms " + methodName + "_instruction", StringComparison.Ordinal)))
            throw new InvalidOperationException("Missing generated instruction equations: " + methodName);
    Write("MethodTemplates", string.Join('\n', lines.Where(line => !IsEquation(line))));
}

static bool IsEquation(string line)
{
    if (!line.StartsWith("cil_instruction_equations ", StringComparison.Ordinal) &&
        !line.StartsWith("#print axioms ", StringComparison.Ordinal)) return false;
    if (!Regex.IsMatch(line, @"\A(?:cil_instruction_equations method[0-9]+|" +
            @"#print axioms method[0-9]+_instruction[0-9]+)\r?\z", RegexOptions.CultureInvariant))
        throw new InvalidOperationException("Unexpected equation declaration: " + line);
    return true;
}

void Write(string module, string source)
{
    source = source.ReplaceLineEndings("\n");
    source = "-- Generated by verification/GenerateTemplates.cs; edit the generator, not this file.\n" + source;
    var destination = Path.Combine(root, "UInt256/Generated", module + ".lean");
    if (check)
    {
        if (!File.Exists(destination) || File.ReadAllText(destination).ReplaceLineEndings("\n") != source)
            throw new InvalidOperationException("Generated template differs: " + destination);
    }
    else
    {
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.WriteAllText(destination, source);
    }
    Console.WriteLine((check ? "Matched " : "Generated ") + destination);
}

string Run(string executable, params string[] arguments)
{
    var start = new ProcessStartInfo(executable)
    {
        WorkingDirectory = root, UseShellExecute = false, CreateNoWindow = true,
        RedirectStandardOutput = true, RedirectStandardError = true
    };
    foreach (var argument in arguments) start.ArgumentList.Add(argument);
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start " + executable);
    var stdout = process.StandardOutput.ReadToEndAsync();
    var stderr = process.StandardError.ReadToEndAsync();
    process.WaitForExit();
    var result = stdout.GetAwaiter().GetResult();
    var error = stderr.GetAwaiter().GetResult();
    if (process.ExitCode != 0) throw new InvalidOperationException(result + error);
    Console.Write(result);
    return result;
}

static string Source([CallerFilePath] string path = "") => path;
