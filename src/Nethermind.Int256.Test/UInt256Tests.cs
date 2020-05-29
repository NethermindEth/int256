using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test
{
    public class UInt256Tests
    {
        [SetUp]
        public void Setup()
        {
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void Add((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A + test.B;
            resBigInt = BigInteger.ModPow(resBigInt, BigInteger.One, BigInteger.Pow(2, 256));
            
            UInt256 uint256a = (UInt256) test.A;
            UInt256 uint256b = (UInt256) test.B;
            UInt256.Add(uint256a, uint256b, out UInt256 res);
            BigInteger resUInt256 = (BigInteger)res;

            resUInt256.Should().Be(resBigInt);
        }
        
        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void Subtract((BigInteger A, BigInteger B) test)
        {
            if (test.A < test.B)
            {
                return;
            }

            BigInteger resBigInt = test.A - test.B;
            
            UInt256 uint256a = (UInt256) test.A;
            UInt256 uint256b = (UInt256) test.B;
            UInt256.Subtract(uint256a, uint256b, out UInt256 res);
            BigInteger resUInt256 = (BigInteger) res;

            resUInt256.Should().Be(resBigInt);
        }
        
        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void ToBigIntegerAndBack(BigInteger test)
        {
            UInt256 uint256 = (UInt256)test;
            BigInteger res = (BigInteger)uint256;
            res.Should().Be(test);
        }
        
        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void ToString(BigInteger test)
        {
            UInt256 uint256 = (UInt256)test;
            BigInteger res = (BigInteger)uint256;
            res.ToString().Should().Be(test.ToString());
        }
    }
}