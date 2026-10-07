"""Production-shaped SIMD refactors and independently refuted semantic negatives.

Each run snapshots the repository once. Every positive case uses the complete public
verifier and identical handwritten proofs. Negative classifications require a prior
kernel proof refuting the unchanged full public contract for every successful fuel.
"""

import argparse
import json
from pathlib import Path
import shutil
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import simd_data, verifier_command, ROOT, PROFILES, run, sha
from common import SIMD_POSITIVES as POSITIVES, SIMD_NEGATIVES as NEGATIVES
from support import copy_source, model_refutation, require_semantic_rejection

FAMILIES = ("arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx512")


def report_path(proof, method, profile):
    return proof / "generated/profiles" / profile / method.lower() / "report.json"


def cil(artifact):
    return [[(i["opcode"], i["operand"]) for i in m["instructions"]]
            for m in artifact["methods"]]


def positive(destination, proof, case, method, profile):
    started = time.monotonic()
    output = run([*verifier_command(proof.parent), "--method", method,
                  "--profile", profile, "--simd-fixture", case], destination)
    report = json.loads(report_path(proof, method, profile).read_text(encoding="utf-8"))
    expected_source = "verification/Tests/Fixtures/SIMD/Cases.props"
    if (report["status"] != "verified" or report["source"]["kind"] != "fixture"
            or report["source"]["fixture"] != expected_source
            or report["source"].get("case") != case
            or report["executionProfile"]["Name"] != profile):
        raise RuntimeError("Fixture report does not identify the selected artifact/profile")
    if any(kind == "resource limit" for _, kind in report["summaryRejections"]):
        raise RuntimeError("A fixture summary exhausted proof resources")
    if case == "ReversedStore" and not any("storeLimbsIndex" in name
                                         for name, _ in report["summaryRejections"]):
        raise RuntimeError("Storage mismatch did not exercise transactional raw fallback")
    if case == "Renamed":
        signatures = [m["signature"] for m in report["artifact"]["methods"]]
        if any(any(f"::{old}(" in s for old in ("AddVector128", "SubtractVector128", "PrepareAdd", "FinishAdd", "SubtractImpl"))
               for s in signatures):
            raise RuntimeError("Renamed fixture retained an old vector helper name")
    print(f"PASS: {method}/{profile}/{case}, complete public proof, {time.monotonic()-started:.3f}s", flush=True)
    return report


def positive_applicable(case, method, profile):
    return simd_data("positive", case, method, profile)


def target_changed(case, method, profile, before, after):
    if case == "FeatureExpressions":
        def getters(artifact):
            live = {c["method"]: set(c["reachable"]) for c in artifact["coverage"]}
            return sum(op["opcode"] == "call" and "::get_IsSupported()" in str(op["operand"])
                       for body in artifact["methods"] for op in body["instructions"]
                       if op["Offset"] in live[body["signature"]])
        if getters(after) <= getters(before):
            raise RuntimeError("Feature rewrite did not change reachable feature expressions")
        return
    if case == "Renamed":
        if cil(before) == cil(after): raise RuntimeError("Renaming did not change a reachable call operand")
        return
    name = ("AddVector128" if method == "Add" else "SubtractVector128")
    if case == "ReversedStore": name = "StoreLimbs"
    if case == "EquivalentMask": name = "PrepareAdd" if method == "Add" else "SubtractImpl"
    if case == "ExtractedHelper" and profile not in FAMILIES[:2]:
        name = "FinishAdd" if method == "Add" else "SubtractImpl"
    def body(artifact):
        found = [m for m in artifact["methods"] if f"::{name}(" in m["signature"]]
        if len(found) != 1: raise RuntimeError(f"Missing/ambiguous targeted fixture method {name}")
        return [(i["opcode"],i["operand"]) for i in found[0]["instructions"]]
    if body(before) == body(after):
        raise RuntimeError(f"{case}: targeted reachable CIL {name} did not change")


def witness(case, method):
    return simd_data("witness", case, method)


def applicable(case, method, profile):
    return simd_data("negative", case, method, profile)


def negative(destination, proof, case, method, profile, lake, baseline):
    project = proof / "Tests/Fixtures/SIMD/Nethermind.Int256.csproj"
    run(["dotnet", "build", str(project), "-c", "Release", "--no-incremental",
         f"-p:FixtureCase={case}", f"-p:FixtureMethod={method}",
         "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], destination)
    assembly = project.parent / "bin/Release/net10.0/Nethermind.Int256.dll"
    generated = proof / "generated"
    run(["dotnet", "run", "--project", str(proof / "Extractor"), "-c", "Release", "--",
         str(assembly), str(generated), method, profile], destination)
    artifact = json.loads((generated/"artifact.json").read_text(encoding="utf-8"))
    if artifact["profile"]["Name"] != profile: raise RuntimeError("Wrong counterexample extraction profile")
    if case == "WrongTable":
        table = lambda a: [entry["bytes"] for entry in a["staticData"]]
        if table(artifact) == table(baseline["artifact"]): raise RuntimeError("Table bytes did not change")
    else:
        name = ("AddVector128" if method == "Add" else "SubtractVector128")
        if case in ("WrongAvxAlignment","WrongBlend","WrongTernary","WrongPredicate","EarlyReread"):
            name = "PrepareAdd" if method == "Add" else "SubtractImpl"
        if case == "WrongScale": name = "FinishAdd" if method == "Add" else "SubtractImpl"
        body = lambda a: [[(i["opcode"],i["operand"]) for i in m["instructions"]]
                          for m in a["methods"] if f"::{name}(" in m["signature"]]
        if not body(artifact) or body(artifact) == body(baseline["artifact"]):
            raise RuntimeError("Targeted negative fixture CIL did not change")
    for relative,digest in baseline["leanSourceSha256"].items():
        if sha(proof/relative) != digest: raise RuntimeError("Negative fixture changed handwritten proof sources")
    a, b, out, (address, actual) = witness(case, method)
    number = lambda words: sum(word << (64*i) for i, word in enumerate(words))
    expected_number = (number(a) + number(b) if method == "Add" else number(a)-number(b)) % 2**256
    expected = (expected_number >> (8*(address-out))) & 255
    if actual == expected: raise RuntimeError("Fixture witness does not distinguish the contract")
    initial = (f"if address < 32 then BitVec.ofNat 8 ((({a} : List Nat)[address / 8]!).toNat / 256^(address % 8)) "
               f"else if 64 ≤ address ∧ address < 96 then BitVec.ofNat 8 ((({b} : List Nat)[(address-64) / 8]!).toNat / 256^(address % 8)) else 0")
    # Nat has no toNat; retain a closed, ordinary kernel-reducible list/byte encoding.
    initial = initial.replace("!).toNat", "!)")
    configuration = proof / "lakefile.toml"
    original = configuration.read_text(encoding="utf-8").split('\n[[lean_lib]]\nname = "Refutation"')[0]
    configuration.write_text(original.rstrip()+'\n', encoding="utf-8")
    model_refutation(proof, lake, initial, 0, 64, out, address, actual, expected, method)
    target = "Audit" if method == "Add" else "SubtractAudit"
    output = run([lake, "build", target], proof, succeeds=False)
    require_semantic_rejection(output, f"UInt256/Methods/{method}/Entry.lean")
    output = run([*verifier_command(proof.parent), "--method", method, "--profile", profile,
                  "--simd-fixture", case], destination, succeeds=False)
    require_semantic_rejection(output, f"UInt256/Methods/{method}/Entry.lean")
    if report_path(proof, method, profile).exists():
        raise RuntimeError("A negative fixture retained stale successful evidence")
    print(f"PASS: {method}/{profile}/{case}, independently refuted full contract", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method", choices=("Add", "Subtract", "all"), default="all")
    parser.add_argument("--profile", choices=PROFILES[1:]+("all",), default="all")
    parser.add_argument("--case", choices=POSITIVES+NEGATIVES+("all",), default="all")
    parser.add_argument("--suite", choices=("positive", "negative", "all"), default="all")
    args = parser.parse_args()
    if args.case in NEGATIVES and args.suite == "positive": raise RuntimeError("Negative case requires the negative suite")
    if args.case in POSITIVES and args.suite == "negative": raise RuntimeError("Positive case requires the positive suite")
    lake = shutil.which("lake")
    if not lake: raise RuntimeError("Pinned Lean/lake must be on PATH")
    methods = ("Add", "Subtract") if args.method == "all" else (args.method,)
    profiles = PROFILES[1:] if args.profile == "all" else (args.profile,)
    if args.case in POSITIVES[1:] and not any(positive_applicable(args.case,m,p) for m in methods for p in profiles):
        raise RuntimeError("Selected positive rewrite is inapplicable to these profiles")
    if args.case in NEGATIVES and not any(applicable(args.case,m,p) for m in methods for p in profiles):
        raise RuntimeError("Selected negative witness is inapplicable to these profiles")
    with tempfile.TemporaryDirectory(prefix="int256-simd-regressions-") as temporary:
        destination = Path(temporary)
        run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(destination)], ROOT)
        proof = copy_source(destination)
        hashes = None
        negative_jobs = []
        for method in methods:
            for profile in profiles:
                if args.suite != "positive":
                    run([*verifier_command(proof.parent),"--method",method,"--profile",profile],destination)
                    production = json.loads(report_path(proof,method,profile).read_text(encoding="utf-8"))
                    if production["source"]["kind"] != "production": raise RuntimeError("Production baseline required")
                baseline = positive(destination, proof, "Baseline", method, profile)
                hashes = hashes or baseline["leanSourceSha256"]
                if baseline["leanSourceSha256"] != hashes: raise RuntimeError("Handwritten proofs changed")
                if args.suite != "negative":
                    for case in POSITIVES[1:]:
                        if args.case not in ("all", case) or not positive_applicable(case, method, profile): continue
                        report = positive(destination, proof, case, method, profile)
                        if report["leanSourceSha256"] != hashes: raise RuntimeError("Fixture used different handwritten proofs")
                        target_changed(case, method, profile, baseline["artifact"], report["artifact"])
                if args.suite != "positive":
                    for case in NEGATIVES:
                        if args.case not in ("all", case) or not applicable(case, method, profile): continue
                        negative_jobs.append((case, method, profile, baseline))
        for case, method, profile, baseline in negative_jobs:
            negative(destination, proof, case, method, profile, lake, baseline)


if __name__ == "__main__": main()
