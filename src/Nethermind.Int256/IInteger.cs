// SPDX-FileCopyrightText: 2023 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

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
        void Exp(in T exp, out T res);
        void ExpMod(in T exp, in T m, out T res);
        void LeftShift(int n, out T res);
        void RightShift(int n, out T res);
        void Convert(out BigInteger big);
        T ZeroValue { get; }
        T OneValue { get; }
        T MaximalValue { get; }
        bool IsZero { get; }
        bool IsOne { get; }

        static abstract bool AddOverflow(in T a, in T b, out T res);
        static abstract void And(in T a, in T b, out T res);
        static abstract void Or(in T a, in T b, out T res);
        static abstract void Xor(in T a, in T b, out T res);
        static abstract void Not(in T a, out T res);
    }
}
