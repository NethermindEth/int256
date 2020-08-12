using System.Runtime.CompilerServices;
using System.Numerics;

namespace Nethermind.Int256
{
    public interface IInteger<T> where T : IInteger<T>
    {
        void Add(in T a, out T res);
        void AddMod(in T a, in T m, out T res);

        void Subtract(in T a, out T res);
        void SubtractMod(in T a, in T m, out T res);

        void Multiply(in T a, out T res);
        void MultiplyMod(in T a, in T m, out T res);

        void Divide(in T a, out T res);

        void Exp(in T e, out T res);
        void ExpMod(in T e, in T m, out T res);

        void LeftShift(int n, out T res);
        void RightShift(int n, out T res);

        void Convert(out BigInteger big);

        string ToString();

        T OneValue { get; }

        T ZeroValue { get; }

        bool IsZero { get; }

        bool IsOne { get; }

        T MaximalValue { get; }
    }
}
