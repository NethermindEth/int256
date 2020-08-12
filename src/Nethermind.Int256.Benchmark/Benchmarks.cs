using System.Collections.Generic;
using System.Numerics;
using System.Linq;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using Nethermind.Int256.Test;

namespace Nethermind.Int256.Benchmark
{
    public class UnsingedBenchmarkBase
    {
        public IEnumerable<BigInteger> Values => System.Linq.Enumerable.Concat(new[] { Numbers.UInt256Max }, UnaryOps.RandomUnsinged(2));

        public IEnumerable<UInt256> ValuesUint256 => Values.Select(x => (UInt256)x);

        public IEnumerable<int> ValuesInt => UnaryOps.RandomInt(3);

        public IEnumerable<UInt256> ValuesIntUint256 => ValuesInt.Select(x => (UInt256)x);
    }

    public class UnsignedIntTwoParamBenchmarkBase : UnsingedBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger A;

        [ParamsSource(nameof(ValuesUint256))]
        public UInt256 UInt256A;

        [ParamsSource(nameof(ValuesInt))]
        public int D;

        [ParamsSource(nameof(ValuesIntUint256))]
        public UInt256 UInt256D;
    }

    public class UnsignedTwoParamBenchmarkBase : UnsingedBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger A;

        [ParamsSource(nameof(Values))]
        public BigInteger B;

        [ParamsSource(nameof(ValuesUint256))]
        public UInt256 UInt256A;

        [ParamsSource(nameof(ValuesUint256))]
        public UInt256 UInt256B;
    }

    public class UnsignedThreeParamBenchmarkBase : UnsignedTwoParamBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger C;

        [ParamsSource(nameof(ValuesUint256))]
        public UInt256 UInt256C;
    }

    public class SignedBenchmarkBase
    {
        public IEnumerable<BigInteger> Values => System.Linq.Enumerable.Concat(new[] { Numbers.UInt256Max }, UnaryOps.RandomUnsinged(2));

        public IEnumerable<Int256> ValuesInt256 => Values.Select(x => (Int256)x);

        public IEnumerable<int> ValuesInt => UnaryOps.RandomInt(3);

        public IEnumerable<Int256> ValuesIntInt256 => ValuesInt.Select(x => (Int256)x);
    }

    public class SignedTwoParamBenchmarkBase : SignedBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger A;

        [ParamsSource(nameof(Values))]
        public BigInteger B;

        [ParamsSource(nameof(ValuesInt256))]
        public Int256 Int256A;

        [ParamsSource(nameof(ValuesInt256))]
        public Int256 Int256B;
    }

    public class SignedThreeParamBenchmarkBase : SignedTwoParamBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger C;

        [ParamsSource(nameof(ValuesInt256))]
        public Int256 Int256C;
    }

    public class SignedIntTwoParamBenchmarkBase : SignedBenchmarkBase
    {
        [ParamsSource(nameof(Values))]
        public BigInteger A;

        [ParamsSource(nameof(ValuesInt256))]
        public Int256 Int256A;

        [ParamsSource(nameof(ValuesInt))]
        public int D;

        [ParamsSource(nameof(ValuesIntInt256))]
        public Int256 Int256D;
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class AddUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Add_BigInteger()
        {
            return (A + B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Add_Int256()
        {
            UInt256.Add(UInt256A, UInt256B, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class AddSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Add_BigInteger()
        {
            return (A + B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Add_Int256()
        {
            Int256.Add(Int256A, Int256B, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class SubtractUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Subtract_BigInteger()
        {
            return (A - B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Subtract_Int256()
        {
            UInt256.Subtract(UInt256A, UInt256B, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class SubtractSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Subtract_BigInteger()
        {
            return (A - B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Subtract_Int256()
        {
            Int256.Subtract(Int256A, Int256B, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class AddModUnsinged : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger AddMod_BigInteger()
        {
            return ((A + B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 AddMod_Int256()
        {
            UInt256.AddMod(UInt256A, UInt256B, UInt256C, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class AddModSinged : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger AddMod_BigInteger()
        {
            return ((A + B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 AddMod_Int256()
        {
            Int256.AddMod(Int256A, Int256B, Int256C, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class SubtractModUnsinged : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger SubtractMod_BigInteger()
        {
            return ((A - B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 AddMod_Int256()
        {
            UInt256.SubtractMod(UInt256A, UInt256B, UInt256C, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class SubtractModSigned : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger SubtractMod_BigInteger()
        {
            return ((A - B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 AddMod_Int256()
        {
            Int256.SubtractMod(Int256A, Int256B, Int256C, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class MultiplyUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Multiply_BigInteger()
        {
            return (A * B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Multiply_Int256()
        {
            UInt256.Multiply(UInt256A, UInt256B, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class MultiplySigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Multiply_BigInteger()
        {
            return (A * B) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Multiply_Int256()
        {
            Int256.Multiply(Int256A, Int256B, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class MultiplyModUnsigned : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger MultiplyMod_BigInteger()
        {
            return ((A * B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Multiply_Int256()
        {
            UInt256.MultiplyMod(UInt256A, UInt256B, UInt256C, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class MultiplyModSigned : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger MultiplyMod_BigInteger()
        {
            return ((A * B) % C) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Multiply_Int256()
        {
            Int256.MultiplyMod(Int256A, Int256B, Int256C, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class DivideUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Divide_BigInteger()
        {
            return (A / B);
        }

        [Benchmark]
        public UInt256 Multiply_Int256()
        {
            UInt256.Divide(UInt256A, UInt256B, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class DivideSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Divide_BigInteger()
        {
            return (A / B);
        }

        [Benchmark]
        public Int256 Multiply_Int256()
        {
            Int256.Divide(Int256A, Int256B, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class ExpUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.Pow(A, D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public UInt256 ExpMod_Int256()
        {
            UInt256.Exp(UInt256A, UInt256D, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class ExpSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.Pow(A, D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public Int256 ExpMod_Int256()
        {
            Int256.Exp(Int256A, Int256D, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class ExpModUnsigned : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.ModPow(A, B, C) % Numbers.TwoTo64;
        }

        [Benchmark]
        public UInt256 ExpMod_Int256()
        {
            UInt256.ExpMod(UInt256A, UInt256B, UInt256C, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class ExpModSigned : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.ModPow(A, B, C) % Numbers.TwoTo64;
        }

        [Benchmark]
        public Int256 ExpMod_Int256()
        {
            Int256.ExpMod(Int256A, Int256B, Int256C, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class LeftShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger LeftShift_BigInteger()
        {
            return (A << D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public UInt256 LeftShift_Int256()
        {
            UInt256A.LeftShift(D, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class LeftShiftSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger LeftShift_BigInteger()
        {
            return (A << D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public Int256 LeftShift_Int256()
        {
            Int256A.LeftShift(D, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class RightShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger RightShift_BigInteger()
        {
            return (A >> D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public UInt256 RightShift_Int256()
        {
            UInt256A.RightShift(D, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp31)]
    [MemoryDiagnoser]
    public class RightShiftSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger LeftShift_BigInteger()
        {
            return (A >> D) % Numbers.TwoTo64;
        }

        [Benchmark]
        public Int256 RightShift_Int256()
        {
            Int256A.RightShift(D, out Int256 res);
            return res;
        }
    }
}
