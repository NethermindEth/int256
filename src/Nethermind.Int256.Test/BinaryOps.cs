using System.Collections.Generic;
using System.Numerics;

namespace Nethermind.Int256.Test
{
    public static class BinaryOps
    {
        public static IEnumerable<(BigInteger, BigInteger)> TestCases
        {
            get
            {
                foreach (var case1 in UnaryOps.TestCases)
                {
                    foreach (var case2 in UnaryOps.TestCases)
                    {
                        yield return (case1, case2);
                    }
                }
            }
        }

        public static IEnumerable<(BigInteger, BigInteger)> SignedTestCases
        {
            get
            {
                foreach (var case1 in UnaryOps.SignedTestCases)
                {
                    foreach (var case2 in UnaryOps.SignedTestCases)
                    {
                        yield return (case1, case2);
                    }
                }
            }
        }

        public static IEnumerable<(ulong, ulong)> ULongTestCases
        {
            get
            {
                foreach (var case1 in UnaryOps.ULongTestCases)
                {
                    foreach (var case2 in UnaryOps.ULongTestCases)
                    {
                        yield return (case1, case2);
                    }
                }
            }
        }

        public static IEnumerable<(BigInteger, int)> ShiftTestCases
        {
            get
            {
                foreach (var n in UnaryOps.TestCases)
                {
                    foreach (var s in UnaryOps.ShiftTestCases)
                    {
                        yield return (n, s);
                    }
                }
            }
        }

        public static IEnumerable<(BigInteger, int)> SignedShiftTestCases
        {
            get
            {
                foreach (var n in UnaryOps.SignedTestCases)
                {
                    foreach (var s in UnaryOps.ShiftTestCases)
                    {
                        yield return (n, s);
                    }
                }
            }
        }
    }
}
