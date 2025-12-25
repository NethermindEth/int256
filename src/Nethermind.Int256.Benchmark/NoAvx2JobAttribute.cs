using System;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public class NoAvx2JobAttribute : EnvJobAttribute
{
    public NoAvx2JobAttribute(RuntimeMoniker runtimeMoniker, int launchCount = -1, int warmupCount = -1, int iterationCount = -1, int invocationCount = -1, string id = null, bool baseline = false)
        : base(CreateJob(id, launchCount, warmupCount, iterationCount, invocationCount, null, baseline, runtimeMoniker)
              .WithEnvironmentVariable("DOTNET_EnableAVX2", "0")
              .WithEnvironmentVariable("DOTNET_EnableAVX512", "0"))
    {

    }
}
