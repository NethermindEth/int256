using System.Diagnostics;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Running;

namespace Nethermind.Int256.Benchmark
{
    class Program
    {
        static void Main(string[] args)
        {
// #if DEBUG
//         => BenchmarkSwitcher.FromAssembly(typeof(Program).Assembly).Run(args, new DebugInProcessConfig());
// #else
            
            IConfig config = Debugger.IsAttached ? new DebugInProcessConfig() : DefaultConfig.Instance;
            BenchmarkRunner.Run<AddUnsigned>(config);
            BenchmarkRunner.Run<SubtractUnsigned>(config);
        }
    }
}