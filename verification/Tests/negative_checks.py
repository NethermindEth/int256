"""Isolated arithmetic, stale-output and fail-closed extraction regressions."""

from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import ROOT, VERIFY, run, sha
from support import (build_extract, build_fixture, copy_source, model_refutation,
                     native_witness, require_production_report, require_semantic_rejection)


def check_aliasing(lake):
    with tempfile.TemporaryDirectory(prefix="int256-aliasing-") as temporary:
        destination = Path(temporary)
        proof = copy_source(destination)
        assembly, _, _ = build_extract(destination, "WrongAliasing")
        native_witness(destination, assembly,
            'using System;\nusing Nethermind.Int256;\n'
            'UInt256 a = new(42, 1, 0, 0), b = new(1, 0, 0, 0);\n'
            'UInt256.Add(in a, in b, out a);\n'
            'Console.WriteLine($"Aliasing witness: limbs {a.u0},{a.u1},{a.u2},{a.u3}; expected 43,1,0,0");\n'
            'if (a.u0 != 1 || a.u1 != 1 || a.u2 != 0 || a.u3 != 0) Environment.Exit(1);\n')
        model_refutation(proof, lake, "if address = 0 then 42 else if address = 8 ∨ address = 32 then 1 else 0",
                         0, 32, 8, 16, 0, 1)
        output = run([lake, "build", "Audit"], proof, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/Entry.lean")
        print("PASS: early output write has a concrete aliasing counterexample and fails the proof")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Lean 4.34.1 / lake must be on PATH")
    baseline = require_production_report()
    run([lake, "build", "Audit"], VERIFY)
    check_aliasing(lake)
    with tempfile.TemporaryDirectory(prefix="int256-carry-") as temporary:
        destination = Path(temporary)
        proof = copy_source(destination)
        assembly, generated, _ = build_extract(destination, "WrongCarry")
        if sha(generated / "Extracted.lean") == sha(baseline):
            raise RuntimeError("Mutation did not change imported program")
        native_witness(destination, assembly,
            'using System;\nusing Nethermind.Int256;\n'
            'UInt256 a = new(ulong.MaxValue, 1, 0, 0), b = new(1, 1, 0, 0);\n'
            'UInt256.Add(a, b, out UInt256 r);\n'
            'Console.WriteLine($"Mutation witness: limbs {r.u0},{r.u1},{r.u2},{r.u3}; expected 0,3,0,0");\n'
            'if (r.u0 != 0 || r.u1 != 2 || r.u2 != 0 || r.u3 != 0) Environment.Exit(1);\n')
        model_refutation(proof, lake,
                         "if address < 8 then 255 else if address = 8 ∨ address = 32 ∨ address = 40 then 1 else 0",
                         0, 32, 64, 72, 2, 3)
        output = run([lake, "build", "Audit"], proof, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/Entry.lean")
        print("PASS: compilable wrong arithmetic changes extraction and fails the correctness proof")
        # Seed all three old success artifacts. The public command must consume
        # its new build/extraction, fail on the changed code, and remove the old report.
        for name in ("Extracted.lean", "artifact.json", "report.json"):
            shutil.copy2(VERIFY / "generated" / name, generated / name)
        output = run([sys.executable, str(proof / "verify.py"), "--fixture", "WrongCarry"], destination, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/Entry.lean")
        if "Verification failed:" not in output:
            raise RuntimeError("Stale regression did not reach fresh proof checking")
        if (generated / "report.json").exists():
            raise RuntimeError("Stale successful report survived failed verification")
        print("PASS: stale extraction and report cannot verify a changed assembly")
    with tempfile.TemporaryDirectory(prefix="int256-unsupported-") as temporary:
        destination = Path(temporary)
        copy_source(destination)
        assembly = build_fixture(destination, "Unsupported")
        output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                      str(assembly), str(destination / "verification/generated")], ROOT, succeeds=False)
        if "Unsupported instruction:" not in output or "mul" not in output:
            raise RuntimeError("Unsupported CIL failed for an unexpected reason")
        print("PASS: reachable unsupported mul rejected explicitly")
    run([lake, "build", "Tests.SummaryTransactions"], VERIFY)
    for name in ("ThrowingInitializer", "BeforeFieldInit"):
        with tempfile.TemporaryDirectory(prefix="int256-initialisation-") as temporary:
            destination = Path(temporary)
            proof = copy_source(destination)
            assembly = build_fixture(destination, name)
            if name == "ThrowingInitializer":
                native_witness(destination, assembly,
                    'using System;\nusing Nethermind.Int256;\n'
                    'UInt256 a = new(1, 1, 0, 0), b = new(2, 1, 0, 0);\n'
                    'try { UInt256.Add(in a, in b, out _); Environment.Exit(1); }\n'
                    'catch (TypeInitializationException e) when (e.InnerException is InvalidOperationException)\n'
                    '{ Console.WriteLine("PASS: real execution throws during helper type initialisation"); }\n')
            output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                          str(assembly), str(proof / "generated")], ROOT, succeeds=False)
            if "Unmodelled static initialisation: Nethermind.Int256.ArithmeticHelper" not in output:
                raise RuntimeError("Initialisation fixture rejected for an unexpected reason")
            if (proof / "generated/Extracted.lean").exists():
                raise RuntimeError("Unsafe initialisation produced an extracted program")
            print(f"PASS: {name} rejected before method-body extraction")
    fixture = VERIFY / "Tests/RegressionFixture"
    run(["dotnet", "build", str(fixture), "-c", "Release",
         "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], ROOT)
    with tempfile.TemporaryDirectory(prefix="int256-metadata-") as temporary:
        destination = Path(temporary)
        copy_source(destination)
        assembly = build_fixture(destination, "Baseline")
        for mode, diagnostic in (("unresolved", "MissingAddHelper"),
                                 ("recursion", "Recursive managed dependency"),
                                 ("layout", "Unsupported field"),
                                 ("cycle", "Malformed or cyclic control flow"),
                                 ("framework", "Unsupported assembly identity"),
                                 ("configuration", "Unsupported assembly identity")):
            mutated = destination / f"{mode}.dll"
            run(["dotnet", "run", "--project", str(fixture), "-c", "Release", "--no-build", "--",
                 mode, str(assembly), str(mutated)], ROOT)
            output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                          str(mutated), str(destination / mode)], ROOT, succeeds=False)
            if diagnostic not in output:
                raise RuntimeError(f"{mode} fixture failed for an unexpected reason")
            print(f"PASS: {mode} extraction fixture rejected explicitly")
    run([lake, "build", "Audit"], VERIFY)


if __name__ == "__main__":
    main()
