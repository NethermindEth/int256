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
        public IEnumerable<BigInteger> Values => Enumerable.Concat(new[] { Numbers.UInt256Max }, UnaryOps.RandomUnsigned(1));

        public IEnumerable<UInt256> ValuesUint256 => Values.Select(x => (UInt256)x);

        public IEnumerable<(BigInteger, UInt256)> ValuesTuple => Values.Select(x => (x, (UInt256)x));

        public IEnumerable<int> ValuesInt => UnaryOps.RandomInt(3);

        public IEnumerable<UInt256> ValuesIntUint256 => ValuesInt.Select(x => (UInt256)x);

        public IEnumerable<(int, UInt256)> ValuesIntTuple => ValuesInt.Select(x => (x, (UInt256)x));
    }

    public class UnsignedIntTwoParamBenchmarkBase : UnsingedBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, UInt256) A;

        [ParamsSource(nameof(ValuesIntTuple))]
        public (int, UInt256) D;
    }

    public class UnsignedTwoParamBenchmarkBase : UnsingedBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, UInt256) A;

        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, UInt256) B;
    }

    public class UnsignedThreeParamBenchmarkBase : UnsignedTwoParamBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, UInt256) C;
    }

    public class SignedBenchmarkBase
    {
        public IEnumerable<BigInteger> Values => Enumerable.Concat(new[] { Numbers.Int256Max }, UnaryOps.RandomSigned(1));

        public IEnumerable<BigInteger> ValuesPositive => Values.Where(x => x.Sign >= 0);

        public IEnumerable<Int256> ValuesInt256 => Values.Select(x => (Int256)x);

        public IEnumerable<(BigInteger, Int256)> ValuesTuple => Values.Select(x => (x, (Int256)x));

        public IEnumerable<(BigInteger, Int256)> ValuesTuplePositive => ValuesPositive.Select(x => (x, (Int256)x));

        public IEnumerable<int> ValuesInt => UnaryOps.RandomInt(3);

        public IEnumerable<Int256> ValuesIntInt256 => ValuesInt.Select(x => (Int256)x);

        public IEnumerable<(int, Int256)> ValuesIntTuple => ValuesInt.Select(x => (x, (Int256)x));
    }

    public class SignedTwoParamBenchmarkBase : SignedBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, Int256) A;

        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, Int256) B;
    }

    public class SignedThreeParamBenchmarkBase : SignedTwoParamBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, Int256) C;
    }

    public class SignedIntTwoParamBenchmarkBase : SignedBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, Int256) A;

        [ParamsSource(nameof(ValuesIntTuple))]
        public (int, Int256) D;
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class AddUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Add_BigInteger()
        {
            return (A.Item1 + B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Add_UInt256()
        {
            UInt256.Add(A.Item2, B.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class AddSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Add_BigInteger()
        {
            return (A.Item1 + B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Add_Int256()
        {
            Int256.Add(A.Item2, B.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class SubtractUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Subtract_BigInteger()
        {
            return (A.Item1 - B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Subtract_UInt256()
        {
            UInt256.Subtract(A.Item2, B.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class SubtractSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Subtract_BigInteger()
        {
            return (A.Item1 - B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Subtract_Int256()
        {
            Int256.Subtract(A.Item2, B.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class AddModUnsinged : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger AddMod_BigInteger()
        {
            return ((A.Item1 + B.Item1) % C.Item1);
        }

        [Benchmark]
        public UInt256 AddMod_UInt256()
        {
            UInt256.AddMod(A.Item2, B.Item2, C.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class AddModSinged : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger AddMod_BigInteger()
        {
            return ((A.Item1 + B.Item1) % C.Item1);
        }

        [Benchmark]
        public Int256 AddMod_Int256()
        {
            Int256.AddMod(A.Item2, B.Item2, C.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class SubtractModUnsinged : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger SubtractMod_BigInteger()
        {
            return ((A.Item1 - B.Item1) % C.Item1);
        }

        [Benchmark]
        public UInt256 SubtractMod_UInt256()
        {
            UInt256.SubtractMod(A.Item2, B.Item2, C.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class SubtractModSigned : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger SubtractMod_BigInteger()
        {
            return ((A.Item1 - B.Item1) % C.Item1);
        }

        [Benchmark]
        public Int256 SubtractMod_Int256()
        {
            Int256.SubtractMod(A.Item2, B.Item2, C.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class MultiplyUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Multiply_BigInteger()
        {
            return (A.Item1 * B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 Multiply_UInt256()
        {
            UInt256.Multiply(A.Item2, B.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class MultiplySigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Multiply_BigInteger()
        {
            return (A.Item1 * B.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 Multiply_Int256()
        {
            Int256.Multiply(A.Item2, B.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class MultiplyModUnsigned : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger MultiplyMod_BigInteger()
        {
            return ((A.Item1 * B.Item1) % C.Item1);
        }

        [Benchmark]
        public UInt256 MultiplyMod_UInt256()
        {
            UInt256.MultiplyMod(A.Item2, B.Item2, C.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class MultiplyModSigned : SignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger MultiplyMod_BigInteger()
        {
            return ((A.Item1 * B.Item1) % C.Item1);
        }

        [Benchmark]
        public Int256 MultiplyMod_Int256()
        {
            Int256.MultiplyMod(A.Item2, B.Item2, C.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class DivideUnsigned : UnsignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Divide_BigInteger()
        {
            return (A.Item1 / B.Item1);
        }

        [Benchmark]
        public UInt256 Divide_UInt256()
        {
            UInt256.Divide(A.Item2, B.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class DivideSigned : SignedTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Divide_BigInteger()
        {
            return (A.Item1 / B.Item1);
        }

        [Benchmark]
        public Int256 Divide_Int256()
        {
            Int256.Divide(A.Item2, B.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class ExpUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Exp_BigInteger()
        {
            return BigInteger.ModPow(A.Item1, D.Item1, Numbers.TwoTo256);
        }

        [Benchmark]
        public UInt256 Exp_UInt256()
        {
            UInt256.Exp(A.Item2, D.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class ExpSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger Exp_BigInteger()
        {
            return BigInteger.ModPow(A.Item1, D.Item1, Numbers.TwoTo256);
        }

        [Benchmark]
        public Int256 Exp_Int256()
        {
            Int256.Exp(A.Item2, D.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class ExpModUnsigned : UnsignedThreeParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.ModPow(A.Item1, B.Item1, C.Item1);
        }

        [Benchmark]
        public UInt256 ExpMod_UInt256()
        {
            UInt256.ExpMod(A.Item2, B.Item2, C.Item2, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class ExpModSigned : SignedBenchmarkBase
    {
        [ParamsSource(nameof(ValuesTuple))]
        public (BigInteger, Int256) A;

        [ParamsSource(nameof(ValuesTuplePositive))]
        public (BigInteger, Int256) B;

        [ParamsSource(nameof(ValuesTuplePositive))]
        public (BigInteger, Int256) C;

        [Benchmark(Baseline = true)]
        public BigInteger ExpMod_BigInteger()
        {
            return BigInteger.ModPow(A.Item1, B.Item1, C.Item1);
        }

        [Benchmark]
        public Int256 ExpMod_Int256()
        {
            Int256.ExpMod(A.Item2, B.Item2, C.Item2, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class LeftShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger LeftShift_BigInteger()
        {
            return (A.Item1 << D.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 LeftShift_UInt256()
        {
            A.Item2.LeftShift(D.Item1, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class LeftShiftSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger LeftShift_BigInteger()
        {
            return (A.Item1 << D.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 LeftShift_Int256()
        {
            A.Item2.LeftShift(D.Item1, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class RightShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger RightShift_BigInteger()
        {
            return (A.Item1 >> D.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public UInt256 RightShift_UInt256()
        {
            A.Item2.RightShift(D.Item1, out UInt256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class RightShiftSigned : SignedIntTwoParamBenchmarkBase
    {
        [Benchmark(Baseline = true)]
        public BigInteger RightShift_BigInteger()
        {
            return (A.Item1 >> D.Item1) % Numbers.TwoTo256;
        }

        [Benchmark]
        public Int256 RightShift_Int256()
        {
            A.Item2.RightShift(D.Item1, out Int256 res);
            return res;
        }
    }

    [SimpleJob(RuntimeMoniker.NetCoreApp50)]
    [MemoryDiagnoser]
    public class IsZeroOne
    {
        public UInt256[] Values { get; } = {UInt256.Zero, UInt256.One, UInt256.MaxValue};

        [ParamsSource(nameof(Values))]
        public UInt256 A;

        [Benchmark]
        public bool IsZero()
        {
            return A.IsZero;
        }
        
        [Benchmark]
        public bool IsOne()
        {
            return A.IsOne;
        }
    }
}
