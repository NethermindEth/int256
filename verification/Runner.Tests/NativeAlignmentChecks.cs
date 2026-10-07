// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Diagnostics;
using System.Text.Json;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class NativeAlignmentChecks
{
    internal static readonly Dictionary<string, bool[]> Profiles = new()
    {
        ["scalar"] = [false, false, false, false], ["x64-sse42"] = [true, false, false, false],
        ["x64-avx2"] = [true, true, false, false], ["x64-avx512"] = [true, true, true, false],
        ["arm64-advsimd"] = [false, false, false, true]
    };

    internal static Dictionary<string, string> EnvironmentFor(string profile)
    {
        if (!Profiles.ContainsKey(profile)) throw new ArgumentException("Unknown native profile");
        Dictionary<string, string> environment = [];
        foreach (string prefix in new[] { "DOTNET_", "COMPlus_" })
        {
            environment[prefix + "TieredCompilation"] = "0";
            environment[prefix + "EnableHWIntrinsic"] = profile == "scalar" ? "0" : "1";
            environment[prefix + "EnableAVX"] = environment[prefix + "EnableAVX2"] = profile == "x64-sse42" ? "0" : "1";
            environment[prefix + "EnableAVX512"] = profile == "x64-avx512" ? "1" : "0";
        }
        return environment;
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("native alignment binds exact DLL and reports unsupported hardware separately", (_, manifests) =>
        {
            string root = Path.GetDirectoryName(manifests)!, assembly = Path.Combine(root, "native.dll"), output = Path.Combine(root, "receipt.json");
            foreach (string failure in new[] { "", "identity", "cases", "status", "unavailable", "changed-dll", "process" })
            {
                File.WriteAllText(assembly, "binary"); File.WriteAllText(output, "stale receipt");
                Workspace workspace = new(root, (command, _, _) =>
                {
                    Program.Require(command.Contains($"-p:VerifiedAssembly={assembly}") && command.Contains("-p:EnforceCodeStyleInBuild=true"), "Witness build lost exact DLL or analyzer");
                    return "built";
                });
                string Witness(string driver, string cwd, Dictionary<string, string> environment)
                {
                    Program.Require(cwd == root && driver.EndsWith("NativeAlignmentWitness.dll", StringComparison.Ordinal), "Wrong native command");
                    Program.Require(environment["DOTNET_EnableHWIntrinsic"] == "0" && environment["COMPlus_EnableHWIntrinsic"] == "0", "Scalar environment lost");
                    if (failure == "process") throw new InvalidOperationException("Native witness failed");
                    JsonObject record = new() { ["status"] = "passed", ["cases"] = 41600, ["assemblySha256"] = Workspace.Hash(assembly),
                        ["architecture"] = "X64", ["runtime"] = ".NET test", ["sse42"] = false, ["avx2"] = false, ["avx512"] = false, ["advSimd"] = false };
                    if (failure == "identity") record["assemblySha256"] = "other";
                    if (failure == "cases") record["cases"] = 1;
                    if (failure == "status") record["status"] = "failed";
                    if (failure == "unavailable") record["architecture"] = "X86";
                    if (failure == "changed-dll") File.WriteAllText(assembly, "changed");
                    return record.ToJsonString();
                }
                string[] arguments = ["--assembly", assembly, "--output", output, "--profile", "scalar"];
                if (failure.Length == 0)
                {
                    Run(workspace, arguments, Witness);
                    JsonObject receipt = JsonNode.Parse(File.ReadAllText(output))!.AsObject();
                    Program.Require(Catalog.Text(receipt["kind"]) == "native-samples" && Catalog.Text(receipt["samples"]![0]!["status"]) == "passed", "Wrong native receipt scope");
                    string nested = Path.Combine(root, "new-receipts", "native.json");
                    Run(workspace, ["--assembly", assembly, "--output", nested, "--profile", "scalar"], Witness);
                    Program.Require(File.Exists(nested), "New receipt directory was not created");
                }
                else
                {
                    Program.Reject(() => Run(workspace, arguments, Witness));
                    Program.Require(!File.Exists(output), "Failed native check retained old success");
                }
            }
            Program.Reject(() => Run(new(root), ["--assembly", assembly, "--output", assembly]));
            Program.Require(File.ReadAllText(assembly) == "binary", "Output collision overwrote the assembly");
            foreach (string profile in Profiles.Keys)
            {
                var environment = EnvironmentFor(profile);
                Program.Require(environment["DOTNET_EnableAVX"] == (profile == "x64-sse42" ? "0" : "1"), "Legacy SSE encoding control lost");
                Program.Require(environment["DOTNET_EnableAVX512"] == (profile == "x64-avx512" ? "1" : "0"), "AVX512 control lost");
                foreach (var pair in environment.Where(pair => pair.Key.StartsWith("DOTNET_", StringComparison.Ordinal)))
                    Program.Require(environment[pair.Key.Replace("DOTNET_", "COMPlus_", StringComparison.Ordinal)] == pair.Value, "Runtime environment prefixes disagree");
            }
        });
    }

    internal static void Classify(JsonObject record, string profile, string identity)
    {
        if (Catalog.Text(record["status"]) != "passed" || record["cases"]?.GetValue<int>() != 41600 || Catalog.Text(record["assemblySha256"]) != identity)
            throw new InvalidOperationException("Invalid native witness result");
        string architecture = Catalog.Text(record["architecture"]);
        bool[] flags = new[] { "sse42", "avx2", "avx512", "advSimd" }.Select(key => record[key]!.GetValue<bool>()).ToArray();
        bool supported = architecture is "X64" or "Arm64" && flags.SequenceEqual(Profiles[profile]);
        if (profile.StartsWith("x64-", StringComparison.Ordinal)) supported &= architecture == "X64";
        if (profile.StartsWith("arm64-", StringComparison.Ordinal)) supported &= architecture == "Arm64";
        record["profile"] = profile;
        record["status"] = supported ? "passed" : "unavailable";
    }

    internal static void Run(Workspace workspace, IReadOnlyList<string> arguments, Func<string, string, Dictionary<string, string>, string>? witness = null)
    {
        string? assembly = null, output = null;
        List<string> profiles = [];
        for (int i = 0; i < arguments.Count; i++)
        {
            string flag = arguments[i];
            if (++i == arguments.Count) throw new ArgumentException("Missing native option value");
            string value = arguments[i];
            switch (flag)
            {
                case "--assembly" when assembly is null: assembly = Path.GetFullPath(value); break;
                case "--output" when output is null: output = Path.GetFullPath(value); break;
                case "--profile" when Profiles.ContainsKey(value): profiles.Add(value); break;
                default: throw new ArgumentException("Unknown or repeated native option");
            }
        }
        if (assembly is null) throw new ArgumentException("--assembly is required");
        if (output is not null && string.Equals(output, assembly, OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal))
            throw new ArgumentException("Output must not overwrite the tested assembly");
        if (output is not null && Directory.Exists(Path.GetDirectoryName(output))) File.Delete(output);
        string identity = Workspace.Hash(assembly);
        JsonArray records = [];
        using ProofSession work = new(workspace);
        workspace.Run(["dotnet", "build", Path.Combine(workspace.Verification, "Tests/NativeAlignmentWitness/NativeAlignmentWitness.csproj"),
            "-c", "Release", "--nologo", $"-p:VerifiedAssembly={assembly}", $"-p:ArtifactsPath={work.Directory}",
            "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], workspace.Root, "Native witness build");
        string driver = Path.Combine(work.Directory, "bin/NativeAlignmentWitness/release/NativeAlignmentWitness.dll");
        foreach (string profile in profiles.Count == 0 ? Profiles.Keys.ToList() : profiles)
        {
            JsonObject record = JsonNode.Parse((witness ?? RunWitness)(driver, workspace.Root, EnvironmentFor(profile)))!.AsObject();
            Classify(record, profile, identity);
            records.Add(record);
            Console.WriteLine($"{Catalog.Text(record["status"]).ToUpperInvariant()}: {profile} ({record["architecture"]}, {record["runtime"]})");
        }
        if (Workspace.Hash(assembly) != identity) throw new InvalidOperationException("Tested assembly changed during native checks");
        if (!records.Any(record => Catalog.Text(record!["status"]) == "passed")) throw new InvalidOperationException("No requested native profile was available");
        if (output is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(output)!);
            File.WriteAllText(output, new JsonObject { ["kind"] = "native-samples", ["samples"] = records }.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
        }
    }

    private static string RunWitness(string driver, string root, Dictionary<string, string> environment)
    {
        var result = Execute(driver, [], root, environment);
        if (result.Code != 0) throw new InvalidOperationException($"Native witness failed ({result.Code}): {result.Error}\n{result.Output}");
        return result.Output;
    }

    internal static (int Code, string Output, string Error) Execute(string driver, IEnumerable<string> arguments, string root, Dictionary<string, string> environment)
    {
        ProcessStartInfo start = new("dotnet") { WorkingDirectory = root, UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true };
        start.ArgumentList.Add(driver);
        foreach (string argument in arguments) start.ArgumentList.Add(argument);
        foreach (var pair in environment) start.Environment[pair.Key] = pair.Value;
        using Process process = Process.Start(start) ?? throw new InvalidOperationException("Cannot start native witness");
        Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        string result = stdout.GetAwaiter().GetResult(), errors = stderr.GetAwaiter().GetResult();
        return (process.ExitCode, result, errors);
    }
}
