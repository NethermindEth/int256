using System;

using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Engines;
using BenchmarkDotNet.Environments;

namespace Nethermind.Int256.Benchmark
{
    public class NoIntrinsicsJobAttribute : JobConfigBaseAttribute
    {
        public NoIntrinsicsJobAttribute(RuntimeMoniker runtimeMoniker, int launchCount = -1, int warmupCount = -1, int iterationCount = -1, int invocationCount = -1, string id = null, bool baseline = false)
            : base(CreateJob(id, launchCount, warmupCount, iterationCount, invocationCount, null, baseline, runtimeMoniker)
                  .WithEnvironmentVariable("DOTNET_EnableHWIntrinsic", "0"))
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
    internal static class RuntimeMonikerExtensions
    {
        internal static Runtime GetRuntime(this RuntimeMoniker runtimeMoniker)
        {
            switch (runtimeMoniker)
            {
                case RuntimeMoniker.Net461:
                    return ClrRuntime.Net461;
                case RuntimeMoniker.Net462:
                    return ClrRuntime.Net462;
                case RuntimeMoniker.Net47:
                    return ClrRuntime.Net47;
                case RuntimeMoniker.Net471:
                    return ClrRuntime.Net471;
                case RuntimeMoniker.Net472:
                    return ClrRuntime.Net472;
                case RuntimeMoniker.Net48:
                    return ClrRuntime.Net48;
                case RuntimeMoniker.Net481:
                    return ClrRuntime.Net481;
                case RuntimeMoniker.NetCoreApp20:
                    return CoreRuntime.Core20;
                case RuntimeMoniker.NetCoreApp21:
                    return CoreRuntime.Core21;
                case RuntimeMoniker.NetCoreApp22:
                    return CoreRuntime.Core22;
                case RuntimeMoniker.NetCoreApp30:
                    return CoreRuntime.Core30;
                case RuntimeMoniker.NetCoreApp31:
                    return CoreRuntime.Core31;
                case RuntimeMoniker.Net50:
#pragma warning disable CS0618 // Type or member is obsolete
                case RuntimeMoniker.NetCoreApp50:
#pragma warning restore CS0618 // Type or member is obsolete
                    return CoreRuntime.Core50;
                case RuntimeMoniker.Net60:
                    return CoreRuntime.Core60;
                case RuntimeMoniker.Net70:
                    return CoreRuntime.Core70;
                case RuntimeMoniker.Net80:
                    return CoreRuntime.Core80;
                case RuntimeMoniker.Mono:
                    return MonoRuntime.Default;
                case RuntimeMoniker.NativeAot60:
                    return NativeAotRuntime.Net60;
                case RuntimeMoniker.NativeAot70:
                    return NativeAotRuntime.Net70;
                case RuntimeMoniker.NativeAot80:
                    return NativeAotRuntime.Net80;
                case RuntimeMoniker.Mono60:
                    return MonoRuntime.Mono60;
                case RuntimeMoniker.Mono70:
                    return MonoRuntime.Mono70;
                default:
                    throw new ArgumentOutOfRangeException(nameof(runtimeMoniker), runtimeMoniker, "Runtime Moniker not supported");
            }
        }
    }
}
