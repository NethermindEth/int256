// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Buffers.Binary;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class NativeSimdChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("native SIMD samples retain vector propagation, overlap and real counterexamples", (_, _) =>
        {
            string verification = Path.Combine(Directory.GetCurrentDirectory(), "verification");
            foreach (string method in new[] { "Add", "Subtract" })
            {
                var samples = Samples("Baseline", method).ToArray();
                Program.Require(samples.Length == 20 && samples.Select(sample => (sample.Name, sample.Output)).Distinct().Count() == 20, "Incomplete native sample matrix");
                foreach (var sample in samples)
                {
                    byte[] bytes = Convert.FromHexString(InitialBytes(sample.Left, sample.Right));
                    Program.Require(bytes.Length == 192 && bytes.AsSpan(32, 32).IndexOfAnyExcept((byte)0) == -1 && bytes.AsSpan(96).IndexOfAnyExcept((byte)0) == -1, "Native initial memory changed");
                    for (int i = 0; i < 4; i++) Program.Require(BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(i * 8)) == sample.Left[i]
                        && BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(64 + i * 8)) == sample.Right[i], "Native input limbs changed");
                    if (sample.Name != "small-operand") Program.Require(sample.Left.Skip(1).Any(word => word != 0) && sample.Right.Skip(1).Any(word => word != 0), "Vector sample selects a small-operand helper");
                }
                foreach (string name in Verifier.SimdRegistry(verification)["SIMD_NEGATIVES"])
                {
                    var witness = SimdFixtures.Witness(name, method);
                    BigInteger Number(ulong[] words) => words.Select((word, i) => (BigInteger)word << (64 * i)).Aggregate(BigInteger.Zero, (a, b) => a + b);
                    BigInteger result = method == "Add" ? Number(witness.Left) + Number(witness.Right) : Number(witness.Left) - Number(witness.Right);
                    int expected = (int)((result >> (8 * (witness.Address - witness.Output))) & 255);
                    Program.Require(expected != witness.Actual, "Negative sample does not distinguish the mathematical contract");
                }
                Program.Reject(() => SimdFixtures.Witness("Unknown", method));
            }
            foreach (string profile in Catalog.Profiles.Skip(1))
            {
                var environment = EnvironmentFor(profile);
                Program.Require(environment["DOTNET_EnableBMI1"] == (profile.EndsWith("bmi1", StringComparison.Ordinal) ? "1" : "0"), "Independent BMI1 choice lost");
                foreach (var pair in environment.Where(pair => pair.Key.StartsWith("DOTNET_", StringComparison.Ordinal)))
                    Program.Require(environment[pair.Key.Replace("DOTNET_", "COMPlus_", StringComparison.Ordinal)] == pair.Value, "Runtime environment prefixes disagree");
            }
        });
    }
    internal static Dictionary<string, string> EnvironmentFor(string profile)
    {
        Dictionary<string, string> environment = [];
        foreach (string prefix in new[] { "DOTNET_", "COMPlus_" })
        {
            environment[prefix + "EnableHWIntrinsic"] = "1";
            environment[prefix + "EnableAVX2"] = profile == "x64-sse42" ? "0" : "1";
            environment[prefix + "EnableAVX512"] = profile.Contains("avx512", StringComparison.Ordinal) ? "1" : "0";
            environment[prefix + "EnableBMI1"] = profile.EndsWith("bmi1", StringComparison.Ordinal) ? "1" : "0";
        }
        return environment;
    }

    internal static IEnumerable<(string Name, ulong[] Left, ulong[] Right, int Output, string Expected)> Samples(string name, string method)
    {
        if (name != "Baseline")
        {
            var witness = SimdFixtures.Witness(name, method);
            yield return (name, witness.Left, witness.Right, witness.Output, $"{witness.Address}:{witness.Actual}");
            yield break;
        }
        const ulong max = ulong.MaxValue;
        (string Name, ulong[] Left, ulong[] Right)[] vectors = [
            ("small-operand", [max, max, max, max], [1, 0, 0, 0]), ("vector-fast", [11, 13, 17, 19], [2, 3, 5, 7]),
            ("cross-half", method == "Add" ? [2, max, 5, 7] : [10, 0, 5, 7], method == "Add" ? [3, 1, 1, 2] : [1, 1, 1, 2]),
            ("cascade", method == "Add" ? [max, max, max, 5] : [0, 0, 0, 5], [1, 0, 0, 2])];
        foreach (var vector in vectors)
            foreach (int output in new[] { 0, 8, 64, 72, 128 }) yield return (vector.Name, vector.Left, vector.Right, output, "positive");
    }

    internal static string InitialBytes(ulong[] left, ulong[] right)
    {
        byte[] memory = new byte[192];
        for (int i = 0; i < 4; i++)
        {
            BinaryPrimitives.WriteUInt64LittleEndian(memory.AsSpan(i * 8), left[i]);
            BinaryPrimitives.WriteUInt64LittleEndian(memory.AsSpan(64 + i * 8), right[i]);
        }
        return Convert.ToHexStringLower(memory);
    }

    internal static void Run(Workspace workspace, IReadOnlyList<string> arguments)
    {
        string? output = null;
        List<string> profiles = [];
        for (int i = 0; i < arguments.Count; i++)
        {
            string flag = arguments[i];
            if (++i == arguments.Count) throw new ArgumentException("Missing native SIMD option value");
            string value = arguments[i];
            if (flag == "--output" && output is null) output = Path.GetFullPath(value);
            else if (flag == "--profile" && Catalog.Profiles.Skip(1).Contains(value)) profiles.Add(value);
            else throw new ArgumentException("Unknown native SIMD option or profile");
        }
        if (profiles.Count == 0) profiles.AddRange(Catalog.Profiles.Skip(1));
        if (output is not null && Directory.Exists(Path.GetDirectoryName(output))) File.Delete(output);
        using ProofSession work = new(workspace);
        void Build(string project, string artifacts, params string[] properties) => workspace.Run(["dotnet", "build", project, "-c", "Release", "--nologo",
            $"-p:ArtifactsPath={artifacts}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", .. properties], workspace.Root, "Native SIMD build");
        Build(Path.Combine(workspace.Verification, "Tests/NativeSIMDWitness/NativeSIMDWitness.csproj"), Path.Combine(work.Directory, "driver"));
        string driver = Path.Combine(work.Directory, "driver/bin/NativeSIMDWitness/release/NativeSIMDWitness.dll");
        Dictionary<(string, string), string> assemblies = [];
        string[] negatives = Verifier.SimdRegistry(workspace.Verification)["SIMD_NEGATIVES"];
        JsonArray records = [];
        foreach (string profile in profiles)
        {
            bool available = true;
            foreach (string method in new[] { "Add", "Subtract" })
            {
                foreach (string name in new[] { "Baseline" }.Concat(negatives.Where(name => SimdFixtures.Negative(name, method, profile))))
                {
                    if (!assemblies.TryGetValue((name, method), out string? assembly))
                    {
                        string artifacts = Path.Combine(work.Directory, name, method);
                        Build(Path.Combine(workspace.Verification, "Tests/Fixtures/SIMD/Nethermind.Int256.csproj"), artifacts, $"-p:FixtureCase={name}", $"-p:FixtureMethod={method}");
                        assemblies[(name, method)] = assembly = Path.Combine(artifacts, "bin/Nethermind.Int256/release/Nethermind.Int256.dll");
                    }
                    foreach (var sample in Samples(name, method))
                    {
                        var result = NativeAlignmentChecks.Execute(driver, [assembly, method, profile, InitialBytes(sample.Left, sample.Right), sample.Output.ToString(), sample.Expected], workspace.Root, EnvironmentFor(profile));
                        if (result.Code is not (0 or 77)) throw new InvalidOperationException($"Native {name}/{method}/{profile} failed: {result.Output}\n{result.Error}");
                        JsonObject record = JsonNode.Parse(result.Output)!.AsObject();
                        record["case"] = name; record["method"] = method; record["profile"] = profile; record["sample"] = sample.Name;
                        record["assemblySha256"] = Workspace.Hash(assembly); record["witness"] = sample.Expected;
                        records.Add(record);
                        if (result.Code == 77) { available = false; Console.WriteLine($"SKIP: {profile}; actual runtime flags do not match"); break; }
                    }
                    if (!available) break;
                    Console.WriteLine($"PASS: native {name}/{method}/{profile}");
                }
                if (!available) break;
            }
        }
        if (output is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(output)!);
            File.WriteAllText(output, new JsonObject { ["kind"] = "native-samples", ["samples"] = records }.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
        }
        Console.WriteLine($"Native samples: {records.Count(record => Catalog.Text(record!["status"]) == "matched")} matched, {records.Count(record => Catalog.Text(record!["status"]) == "unsupported")} unavailable profiles");
    }
}
