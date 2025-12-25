using System;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Engines;
using BenchmarkDotNet.Environments;

namespace Nethermind.Int256.Benchmark
{
    public class NoAvx512JobAttribute : JobConfigBaseAttribute
    {
        public NoAvx512JobAttribute(RuntimeMoniker runtimeMoniker, int launchCount = -1, int warmupCount = -1, int iterationCount = -1, int invocationCount = -1, string id = null, bool baseline = false)
            : base(CreateJob(id, launchCount, warmupCount, iterationCount, invocationCount, null, baseline, runtimeMoniker)
                  .WithEnvironmentVariable("DOTNET_EnableAVX512", "0"))
        {

        }

        private static Job CreateJob(string id, int launchCount, int warmupCount, int iterationCount, int invocationCount, RunStrategy? runStrategy, bool baseline, RuntimeMoniker runtimeMoniker = RuntimeMoniker.HostProcess)
        {
            Job job = new Job(id);
            int num = 0;
            if (launchCount != -1)
            {
                job.Run.LaunchCount = launchCount;
                num++;
            }

            if (warmupCount != -1)
            {
                job.Run.WarmupCount = warmupCount;
                num++;
            }

            if (iterationCount != -1)
            {
                job.Run.IterationCount = iterationCount;
                num++;
            }

            if (invocationCount != -1)
            {
                job.Run.InvocationCount = invocationCount;
                num++;
                int num2 = job.Run.ResolveValue(RunMode.UnrollFactorCharacteristic, EnvironmentResolver.Instance);
                if (invocationCount % num2 != 0)
                {
                    job.Run.UnrollFactor = 1;
                    num++;
                }
            }

            if (runStrategy.HasValue)
            {
                job.Run.RunStrategy = runStrategy.Value;
                num++;
            }

            if (baseline)
            {
                job.Meta.Baseline = true;
            }

            if (runtimeMoniker != 0)
            {
                job.Environment.Runtime = runtimeMoniker.GetRuntime();
                num++;
            }

            if (id == null && num == 1 && runtimeMoniker != 0)
            {
                job = job.WithId(runtimeMoniker.GetRuntime().Name);
            }

            return job.Freeze();
        }
    }
}
