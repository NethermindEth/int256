// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public class NoIntrinsicsJobAttribute : EnvJobAttribute
{
    public NoIntrinsicsJobAttribute(RuntimeMoniker runtimeMoniker, int launchCount = -1, int warmupCount = -1, int iterationCount = -1, int invocationCount = -1, string id = null, bool baseline = false)
        : base(CreateJob(id, launchCount, warmupCount, iterationCount, invocationCount, null, baseline, runtimeMoniker)
              .WithEnvironmentVariable("DOTNET_EnableHWIntrinsic", "0"))
    {

    }
}
