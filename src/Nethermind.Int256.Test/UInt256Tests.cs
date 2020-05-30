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
            resBigInt = resBigInt % (BigInteger.One << 256);
            
            UInt256 uint256a = (UInt256) test.A;
            UInt256 uint256b = (UInt256) test.B;
            UInt256.Add(uint256a, uint256b, out UInt256 res);
            BigInteger resUInt256 = (BigInteger)res;

            resUInt256.Should().Be(resBigInt);
            
            BigInteger resUInt256Op = (BigInteger)(uint256a + uint256b);
            resUInt256Op.Should().Be(resBigInt);
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
        
        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void Multiply((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A * test.B % (BigInteger.One << 256);
            
            UInt256 uint256a = (UInt256) test.A;
            UInt256 uint256b = (UInt256) test.B;
            UInt256.Add(uint256a, uint256b, out UInt256 res);
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
            uint256.ToString().Should().Be(test.ToString());
        }
        
        [Test]
        public void Zero_is_min_value()
        {
            UInt256.Zero.Should().Be(UInt256.MinValue);
        }
        
        [Test]
        public void Zero_is_zero()
        {
            UInt256.Zero.Should().Be((UInt256)BigInteger.Zero);
        }
        
        [Test]
        public void Is_zero()
        {
            UInt256.Zero.IsZero.Should().BeTrue();
            UInt256.One.IsZero.Should().BeFalse();
        }
        
        [Test]
        public void One_is_one()
        {
            UInt256.One.Should().Be((UInt256)BigInteger.One);
        }
        
        [Test]
        public void Is_one()
        {
            UInt256.One.IsOne.Should().BeTrue();
            UInt256.Zero.IsOne.Should().BeFalse();
        }
        
        [Test]
        public void Max_value_is_correct()
        {
            UInt256.MaxValue.Should().Be((UInt256)TestNumbers.UInt256Max);
        }
    }
}