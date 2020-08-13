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
            BenchmarkRunner.Run<AddModUnsinged>(config);
            BenchmarkRunner.Run<SubtractModUnsinged>(config);
            BenchmarkRunner.Run<MultiplyUnsigned>(config);
            BenchmarkRunner.Run<MultiplyModUnsigned>(config);
            BenchmarkRunner.Run<DivideUnsigned>(config);
            BenchmarkRunner.Run<ExpUnsigned>(config);
            BenchmarkRunner.Run<ExpModUnsigned>(config);
            BenchmarkRunner.Run<LeftShiftUnsigned>(config);
            BenchmarkRunner.Run<RightShiftUnsigned>(config);

            BenchmarkRunner.Run<AddSigned>(config);
            BenchmarkRunner.Run<SubtractSigned>(config);
            BenchmarkRunner.Run<AddModSinged>(config);
            BenchmarkRunner.Run<SubtractModSigned>(config);
            BenchmarkRunner.Run<MultiplySigned>(config);
            BenchmarkRunner.Run<MultiplyModSigned>(config);
            BenchmarkRunner.Run<DivideSigned>(config);
            BenchmarkRunner.Run<ExpSigned>(config);
            BenchmarkRunner.Run<ExpModSigned>(config);
            BenchmarkRunner.Run<LeftShiftSigned>(config);
            BenchmarkRunner.Run<RightShiftSigned>(config);
        }
    }
}
