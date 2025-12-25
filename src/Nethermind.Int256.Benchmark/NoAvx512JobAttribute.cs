using System;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public class NoAvx512JobAttribute : EnvJobAttribute
{
    public NoAvx512JobAttribute(RuntimeMoniker runtimeMoniker, int launchCount = -1, int warmupCount = -1, int iterationCount = -1, int invocationCount = -1, string id = null, bool baseline = false)
        : base(CreateJob(id, launchCount, warmupCount, iterationCount, invocationCount, null, baseline, runtimeMoniker)
              .WithEnvironmentVariable("DOTNET_EnableAVX512", "0"))
    {

    }
}
