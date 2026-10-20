// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Reflection;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
    // Guests stub this getter by name and signature in their ILC substitutions (see README).
    [Test]
    public void HasByteReverse_keeps_the_substituted_signature()
    {
        MethodInfo? getter = typeof(UInt256).GetMethod("get_HasByteReverse",
            BindingFlags.Static | BindingFlags.NonPublic, Type.EmptyTypes);

        Assert.That(getter, Is.Not.Null);
        Assert.That(getter!.ReturnType, Is.EqualTo(typeof(bool)));
        Assert.That(getter.Invoke(null, null), Is.False);
    }
}
