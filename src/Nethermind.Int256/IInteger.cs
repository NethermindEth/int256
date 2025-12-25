// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Numerics;

namespace Nethermind.Int256
{
    /// <summary>
    /// Legacy interface for backward compatibility with existing code.
    /// New code should use the standard .NET numeric interfaces (IBinaryInteger, INumber, etc.)
    /// </summary>
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

        abstract static bool AddOverflow(in T a, in T b, out T res);
        abstract static void And(in T a, in T b, out T res);
        abstract static void Or(in T a, in T b, out T res);
        abstract static void Xor(in T a, in T b, out T res);
        abstract static void Not(in T a, out T res);

        void Convert(out BigInteger big);

        T OneValue { get; }

        T ZeroValue { get; }

        bool IsZero { get; }

        bool IsOne { get; }

        T MaximalValue { get; }
    }
}
