"""Freshly verify both public methods and compose coverage of every valid feature profile."""

import argparse
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time

from common import PROFILES, ROOT, SEMANTICS_VERSION, VERIFY, expected_profile, generated_directory, run, sha, source_files
from verify import audit_names, build_artifact, check_proof_snapshot, main as verify_one, source_inputs, theorem_audits


METHODS = ("Add", "Subtract")
COVERAGE_THEOREMS = ("CIL.FeatureProfile.classification_total",
                     "UInt256Proof.checked_feature_classes",
                     "UInt256Proof.checked_representative_classes",
                     "UInt256Proof.add_complete_coverage",
                     "UInt256Proof.subtract_complete_coverage")


def checked_certificate(method, profile, inputs):
    directory = generated_directory(method, profile)
    path = directory / "report.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    manifest = json.loads((VERIFY / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))
    names = audit_names(method)
    artifact = json.loads((directory / "artifact.json").read_text(encoding="utf-8"))
    lean_hashes = {p.relative_to(VERIFY).as_posix(): sha(p) for p in source_files(VERIFY, {".lean"})}
    production_source = {"kind": "production", "project": "src/Nethermind.Int256/Nethermind.Int256.csproj",
                         "fixture": None}
    if report.get("status") != "verified" or report.get("source") != production_source:
        raise RuntimeError(f"Missing production certificate: {method}/{profile}")
    if report.get("sourceInputs") != inputs or report.get("leanSourceSha256") != lean_hashes:
        raise RuntimeError(f"Stale proof inputs: {method}/{profile}")
    if report.get("semanticsVersion") != SEMANTICS_VERSION:
        raise RuntimeError(f"Semantics version mismatch: {method}/{profile}")
    if report.get("artifact") != artifact or report.get("generatedProgramSha256") != sha(directory / "Extracted.lean"):
        raise RuntimeError(f"Stale extraction: {method}/{profile}")
    if report.get("executionProfile") != expected_profile(profile) or artifact.get("profile") != expected_profile(profile):
        raise RuntimeError(f"Profile mismatch: {method}/{profile}")
    if artifact["methods"][artifact["entryIndex"]]["signature"] != manifest["entry"]:
        raise RuntimeError(f"Public entry mismatch: {method}/{profile}")
    if report.get("auditedTheorems") != names or set(report.get("axiomAudits", {})) != set(names):
        raise RuntimeError(f"Missing family gate: {method}/{profile}")
    for name in names:
        axioms = report["axiomAudits"][name]
        if len(set(axioms)) != len(axioms) or set(axioms) - set(manifest["approvedAxioms"]):
            raise RuntimeError(f"Unapproved family axioms: {method}/{profile}")
    coverage = report.get("coverage", {})
    if coverage.get("kind") != "feature-family" or coverage.get("representative") != profile:
        raise RuntimeError(f"Missing family coverage: {method}/{profile}")
    return {"method": method, "representative": profile,
            "report": path.relative_to(ROOT).as_posix(), "reportSha256": sha(path),
            "assemblySha256": artifact["sha256"], "generatedProgramSha256": report["generatedProgramSha256"],
            "familyTheorem": names[1], "compositionCertificate": names[2],
            "representativeTheorem": names[3], "axiomAudits": report["axiomAudits"],
            "timings": report.get("timings")}


def check_composition(inputs):
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("Pinned Lean toolchain must be on PATH")
    lean = run([lake, "env", "lean", "--version"], VERIFY).strip()
    if not re.search(r"version 4\.34\.1\b", lean):
        raise RuntimeError(f"Unexpected composition Lean toolchain: {lean}")
    approved = [json.loads((VERIFY / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))["approvedAxioms"]
                for method in METHODS]
    if set(approved[0]) != set(approved[1]):
        raise RuntimeError("Method axiom approvals differ")
    with tempfile.TemporaryDirectory(prefix="int256-coverage-") as temporary:
        proof = Path(temporary)
        sources = list(source_files(VERIFY, {".lean"}))
        for source in sources:
            target = proof / source.relative_to(VERIFY)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        for name in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(VERIFY / name, proof / name)
        copied_paths = [p.relative_to(VERIFY) for p in sources] + [Path("lakefile.toml"), Path("lean-toolchain")]
        check_proof_snapshot(proof, copied_paths, inputs)
        output = run([lake, "build", "+UInt256.FeatureCoverage:olean"], proof)
        audits = theorem_audits(output, COVERAGE_THEOREMS, approved[0])
        check_proof_snapshot(proof, copied_paths, inputs)
    if inputs != source_inputs():
        raise RuntimeError("Inputs changed during coverage checking")
    return audits, lean


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-reports", action="store_true",
                        help="Compose existing production reports only after checking their complete freshness")
    args = parser.parse_args()
    destination = VERIFY / "generated/coverage.json"
    destination.unlink(missing_ok=True)
    started = time.perf_counter()
    inputs = source_inputs()
    build_timings = None
    if not args.check_reports:
        # One fresh production DLL binds every family. Each kernel proof still
        # gets its own source directory without any compiled Lean caches.
        with tempfile.TemporaryDirectory(prefix="int256-all-artifact-") as temporary:
            bundle = build_artifact(ROOT / "src/Nethermind.Int256/Nethermind.Int256.csproj",
                                    Path(temporary), "Add")
            build_timings = bundle["timings"]
            for method in METHODS:
                for profile in PROFILES:
                    verify_one(["--method", method, "--profile", profile], prepared=bundle)
    certificates = [checked_certificate(method, profile, inputs) for method in METHODS for profile in PROFILES]
    composition = check_composition(inputs)
    # Recheck generated files as well as reports after the kernel composition.
    current_certificates = [checked_certificate(method, profile, inputs)
                            for method in METHODS for profile in PROFILES]
    if inputs != source_inputs() or current_certificates != certificates:
        raise RuntimeError("Certificates changed during composition")
    audits, lean = composition
    report = {"status": "verified", "coverage": "all valid FeatureProfile configurations",
              "domain": "CIL.FeatureProfile.Valid", "sourceInputs": inputs,
              "semanticsVersion": SEMANTICS_VERSION,
              "compositionToolchain": lean,
              "composition": "Seven full family gates per method plus kernel-checked total classification and composition rule",
              "auditedTheorems": list(COVERAGE_THEOREMS), "axiomAudits": audits,
              "certificates": certificates, "sharedBuildTimings": build_timings,
              "totalSeconds": time.perf_counter() - started}
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(destination)
    print("Verified complete Add/Subtract coverage from 14 fresh family certificates")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Coverage verification failed: {error}", file=sys.stderr)
        sys.exit(1)
