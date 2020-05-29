using System.Collections.Generic;
using System.Numerics;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using Nethermind.Int256.Test;

namespace Nethermind.Int256.Benchmark
{
    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class AddUnsigned
    {
        [ParamsSource(nameof(Values))]
        public BigInteger A;

        [ParamsSource(nameof(Values))]
        public BigInteger B;
        
        public UInt256 UInt256A;
        
        public UInt256 UInt256B;

        // public IEnumerable<BigInteger> Values => UnaryOps.TestCases;
        public IEnumerable<BigInteger> Values
        {
            get { yield return TestNumbers.UInt256Max; }
        }

        [GlobalSetup]
        public void Setup()
        {
            UInt256A = (UInt256) A;
            UInt256B = (UInt256) B;
        }

        [Benchmark(Baseline = true)]
        public BigInteger Add_BigInteger()
        {
            return A + B;
        }
        
        [Benchmark]
        public UInt256 Add_Int256()
        {
            UInt256.Add(UInt256A, UInt256B, out UInt256 res);
            return res;
        }
    }
}