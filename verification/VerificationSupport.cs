// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Text.Json;
using System.Text.Json.Nodes;

internal static class VerificationSupport
{
    internal static string Root => Path.GetDirectoryName(Source())!;
    private static string Source([CallerFilePath] string path = "") => path;
    internal static readonly JsonSerializerOptions Json = new() { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };

    internal static Gate[] Gates(string root) =>
        JsonSerializer.Deserialize<Registry>(File.ReadAllText(Path.Combine(root, "manifests/gates.json")), Json)!.Gates;

    internal static async Task<string> Run(string root, string command, string[] arguments, bool capture = false,
        bool combineOutput = false, bool disableIntrinsics = false)
    {
        ProcessStartInfo start = new(command)
        {
            WorkingDirectory = root,
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true
        };
        foreach (string argument in arguments) start.ArgumentList.Add(argument);
        if (disableIntrinsics) start.Environment["DOTNET_EnableHWIntrinsic"] = "0";
        using Process process = Process.Start(start) ?? throw new InvalidOperationException($"Could not start {command}");
        Queue<string> tail = new();
        Task<string> stdout = capture ? process.StandardOutput.ReadToEndAsync() : Forward(process.StandardOutput, Console.Out, tail);
        Task<string> stderr = capture ? process.StandardError.ReadToEndAsync() : Forward(process.StandardError, Console.Error, tail);
        await process.WaitForExitAsync();
        string output = await stdout;
        string error = await stderr;
        // Forwarded output is not captured, so the failure names the tool's last lines, where its diagnosis is.
        if (process.ExitCode != 0)
            throw new InvalidOperationException($"{command} failed with exit code {process.ExitCode}: " +
                (capture ? output + error : string.Join(Environment.NewLine, tail)));
        return combineOutput ? output + error : output;
    }

    internal static async Task<string> RunChecked(string root, string command, IEnumerable<string> arguments,
        bool disableIntrinsics = false)
    {
        string output = await Run(root, command, [.. arguments], capture: true, combineOutput: true,
            disableIntrinsics: disableIntrinsics);
        if (output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
        return output;
    }

    internal static async Task PrepareConsumer(string root, string consumer)
    {
        ProofBindings.Prepare(root);
        CopySources(root, consumer);
        JsonArray packages = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "lake-manifest.json")))!["packages"]!.AsArray();
        string packageRoot = Path.GetFullPath(Path.Combine(consumer, ".lake/packages"));
        foreach (JsonNode? package in packages)
        {
            string name = package!["name"]!.GetValue<string>(), revision = package["rev"]!.GetValue<string>();
            string destination = Path.GetFullPath(Path.Combine(packageRoot, name));
            if (!destination.StartsWith(packageRoot + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new InvalidOperationException("Package path escapes the consumer snapshot: " + name);
            await DropStaleClone(destination, revision);
            if (!Directory.Exists(destination))
            {
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                await RunChecked(root, "git", ["clone", "--no-hardlinks", "--no-checkout",
                    Path.Combine(root, ".lake/packages", name), destination]);
            }
            await RunChecked(root, "git", ["-C", destination, "checkout", "--detach", revision]);
        }
    }

    private static void CopySources(string source, string destination)
    {
        Directory.CreateDirectory(destination);
        foreach (string file in Directory.EnumerateFiles(source))
            if (Path.GetExtension(file) is ".lean" or ".json" or ".toml" || Path.GetFileName(file) == "lean-toolchain")
                File.Copy(file, Path.Combine(destination, Path.GetFileName(file)), true);
        foreach (string directory in Directory.EnumerateDirectories(source))
        {
            string name = Path.GetFileName(directory);
            if (name is ".lake" or ".git" or "artifacts" or "generated" or "bin" or "obj" or ".work") continue;
            if ((File.GetAttributes(directory) & FileAttributes.ReparsePoint) != 0)
                throw new InvalidOperationException("Source snapshot cannot contain links: " + directory);
            CopySources(directory, Path.Combine(destination, name));
        }
    }

    // A partial source clone cannot serve fetches for a newer pinned revision.
    private static async Task DropStaleClone(string repository, string revision)
    {
        if (!Directory.Exists(repository)) return;
        ProcessStartInfo start = new("git")
        {
            RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false, CreateNoWindow = true
        };
        foreach (string argument in new[] { "-C", repository, "cat-file", "-e", revision + "^{commit}" })
            start.ArgumentList.Add(argument);
        using Process probe = Process.Start(start) ?? throw new InvalidOperationException("git");
        await Task.WhenAll(probe.StandardOutput.ReadToEndAsync(), probe.StandardError.ReadToEndAsync(), probe.WaitForExitAsync());
        if (probe.ExitCode == 0) return;
        foreach (string file in Directory.EnumerateFiles(repository, "*", SearchOption.AllDirectories))
            File.SetAttributes(file, FileAttributes.Normal);
        Directory.Delete(repository, true);
    }

    const int FailureTailLines = 8;

    private static async Task<string> Forward(StreamReader reader, TextWriter writer, Queue<string> tail)
    {
        while (await reader.ReadLineAsync() is string line)
        {
            await writer.WriteLineAsync(line);
            await writer.FlushAsync();
            if (line.Trim().Length == 0) continue;
            lock (tail)
            {
                tail.Enqueue(line);
                if (tail.Count > FailureTailLines) tail.Dequeue();
            }
        }
        return "";
    }

    private sealed record Registry(Gate[] Gates);
}

internal sealed record Gate(string Method, string Profile, string Proof, string Theorem);
internal sealed record BatchGroup(string Profile, string[] Methods);
internal sealed record Batch(string Id, BatchGroup[] Groups);
internal sealed record Selection(bool Contracts, Gate[] Include, Batch[] Batches);
