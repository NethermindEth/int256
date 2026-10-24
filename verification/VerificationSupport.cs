// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Text.Json;

internal static class VerificationSupport
{
    internal static string Root => Path.GetDirectoryName(Source())!;
    private static string Source([CallerFilePath] string path = "") => path;
    internal static readonly JsonSerializerOptions Json = new() { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };

    internal static Gate[] Gates(string root) =>
        JsonSerializer.Deserialize<Registry>(File.ReadAllText(Path.Combine(root, "manifests/gates.json")), Json)!.Gates;

    internal static async Task<string> Run(string root, string command, string[] arguments, bool capture = false)
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
                (capture ? error : string.Join(Environment.NewLine, tail)));
        return output;
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
