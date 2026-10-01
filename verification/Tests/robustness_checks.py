"""Verify independent, versioned Add fixtures with the production proof sources."""

import json
from pathlib import Path
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import ROOT, run
from negative_checks import copy_source


FIXTURES = ("Baseline", "CarryOr", "Renamed", "FullyInlined", "StraightLine", "ExtractedHelper", "ExpandedHardware")


def instructions(artifact):
    return [[(i["opcode"], i["operand"]) for i in method["instructions"]] for method in artifact["methods"]]


def verify_fixture(name):
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix=f"int256-robust-{name}-") as temporary:
        destination = Path(temporary)
        run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(destination)], ROOT)
        proof = copy_source(destination)
        try:
            run([sys.executable, str(proof / "verify.py"), "--fixture", name], destination)
        except RuntimeError as error:
            raise RuntimeError(f"Fixture {name} failed; distinguish build/extraction/proof diagnostics above") from error
        report = json.loads((proof / "generated/report.json").read_text(encoding="utf-8"))
        if report["status"] != "verified" or report["source"]["kind"] != "fixture":
            raise RuntimeError(f"{name}: wrong verification source or status")
        return report, round(time.monotonic() - started, 3)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    proof_hashes = None
    baseline = None
    results = []
    for name in FIXTURES:
        report, seconds = verify_fixture(name)
        if baseline is None:
            baseline = report
            proof_hashes = report["leanSourceSha256"]
        else:
            if report["leanSourceSha256"] != proof_hashes:
                raise RuntimeError("Handwritten proof sources differ between fixtures")
            if instructions(report["artifact"]) == instructions(baseline["artifact"]):
                raise RuntimeError(f"{name}: instructions did not change")
        methods = report["artifact"]["methods"]
        if name in ("FullyInlined", "StraightLine") and len(methods) != 1:
            raise RuntimeError("Complete inlining fixture still has reachable managed helpers")
        if name == "FullyInlined":
            branches = sum(i["opcode"].startswith(("brtrue", "brfalse", "beq", "bne", "bge", "blt"))
                           for method in methods for i in method["instructions"])
            if branches < 8:
                raise RuntimeError("Fixture maintenance failure: complete inlining lost small-operand dispatch")
        if name == "ExtractedHelper" and not any("::AddPair(" in m["signature"] for m in methods):
            raise RuntimeError("New helper was not discovered")
        if name == "Renamed" and any(any(f"::{old}(" in m["signature"] for old in
                                      ("AddScalar", "AddScalarUInt64", "AddWithCarry", "StoreLimbs")) for m in methods):
            raise RuntimeError("Renaming fixture retains the old helper names")
        if name == "ExpandedHardware" and sum(len(c["excluded"]) for c in report["artifact"]["coverage"]) <= 512:
            raise RuntimeError("Excluded hardware expansion did not exceed the old budget")
        results.append({"fixture": name, "seconds": seconds,
                        "assemblySha256": report["artifact"]["sha256"],
                        "programSha256": report["generatedProgramSha256"], "managedMethods": len(methods)})
        print(f"PASS: {name}, identical proof sources, {seconds}s", flush=True)
    print(json.dumps({"proofSources": proof_hashes, "fixtures": results}, indent=2))


if __name__ == "__main__":
    main()
