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
                for (int i = 0; i < UnaryOps.TestCases.Length; i++)
                {
                    for (int j = 0; j < UnaryOps.TestCases.Length; j++)
                    {
                        yield return (UnaryOps.TestCases[i], UnaryOps.TestCases[j]);
                    }    
                }
            }
        }
        
        public static IEnumerable<(ulong, ulong)> ULongTestCases
        {
            get
            {
                for (int i = 0; i < UnaryOps.ULongTestCases.Length; i++)
                {
                    for (int j = 0; j < UnaryOps.ULongTestCases.Length; j++)
                    {
                        yield return (UnaryOps.ULongTestCases[i], UnaryOps.ULongTestCases[j]);
                    }    
                }
            }
        }
    }
}