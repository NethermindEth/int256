using System.Collections.Generic;
using System.Numerics;
using System.Linq;

namespace Nethermind.Int256.Test
{
    public static class TernaryOps
    {
        public static IEnumerable<(BigInteger, BigInteger, BigInteger)> TestCases
        {
            get
            {
                foreach ((var case1, var case2) in BinaryOps.TestCases)
                {
                    foreach (var case3 in UnaryOps.TestCases)
                    {
                        yield return (case1, case2, case3);
                    }
                }
            }
        }

        public static IEnumerable<(BigInteger, BigInteger, BigInteger)> SignedTestCases
        {
            get
            {
                foreach ((var case1, var case2) in BinaryOps.SignedTestCases)
                {
                    foreach (var case3 in UnaryOps.SignedTestCases)
                    {
                        yield return (case1, case2, case3);
                    }
                }
            }
        }

        public static IEnumerable<(BigInteger, BigInteger, BigInteger)> SignedModTestCases => SignedTestCases.Where(v => v.Item3 >= 0);

        public static IEnumerable<(ulong, ulong, ulong)> ULongTestCases
        {
            get
            {
                foreach ((var case1, var case2) in BinaryOps.ULongTestCases)
                {
                    foreach (var case3 in UnaryOps.ULongTestCases)
                    {
                        yield return (case1, case2, case3);
                    }
                }
            }
        }
    }
}
