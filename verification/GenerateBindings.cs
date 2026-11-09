#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include ProofBindings.cs

if (args is not ([] or ["--check"])) throw new ArgumentException("Usage: GenerateBindings.cs [--check]");
ProofBindings.Write(VerificationSupport.Root, VerificationSupport.Gates(VerificationSupport.Root), args.Length != 0);
Console.WriteLine("Checked primitive equality and comparison binding sources.");
