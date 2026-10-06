"""Freshly verify selected public APIs and compose total valid-profile coverage."""

import argparse
import copy
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time

from common import PROFILES, ROOT, SEMANTICS_VERSION, VERIFY, expected_profile, generated_directory, run, sha, source_files
from verify import audit_names, build_artifact, check_proof_snapshot, main as verify_one, source_inputs, theorem_audits
from methods import LEGACY, api_entries, check_calling_convention, method_manifest, method_names, native_limitations
from gate_templates import audit_module
from safety_gate import safety_gate, selected_safety_module


METHODS = ("Add", "Subtract")
COVERAGE_THEOREMS = ("CIL.FeatureProfile.classification_total",
                     "UInt256Proof.checked_feature_classes",
                     "UInt256Proof.checked_representative_classes",
                     "UInt256Proof.add_complete_coverage",
                     "UInt256Proof.subtract_complete_coverage")
OPERATION_COVERAGE_THEOREMS = ("UInt256Proof.vector_storage_complete_coverage",
                               "UInt256Proof.classified_complete_coverage",
                               "UInt256Proof.vector_reduction_complete_coverage",
                               "UInt256Proof.relational_complete_coverage",
                               "CIL.FeatureProfile.multiply_classification_flags",
                               "UInt256Proof.multiply_complete_coverage")


def check_family_representatives(family):
    """Check the concrete premises of the audited total composition rule."""
    kind = family["kind"]
    if kind == "feature-class":
        # These seven profiles are defined directly by expected_profile.
        return
    if kind == "vector256-storage":
        required = [{"Vector256Accelerated": flag} for flag in (False, True)]
    elif kind == "vector-reduction":
        required = [{"Vector256Accelerated": False, "Sse41": flag} for flag in (False, True)]
        required.append({"Vector256Accelerated": True})
    elif kind == "relational-dispatch":
        required = [{"Avx512FVL": False, "Avx2": False, "Vector256Accelerated": flag}
                    for flag in (False, True)]
        required.extend([{"Avx512FVL": False, "Avx2": True}, {"Avx512FVL": True}])
    elif kind == "multiply-dispatch-storage":
        arithmetic = [(False, False, False, False), (False, False, False, True),
                      (False, False, True, True), (True, False, False, False),
                      (True, False, False, True), (True, False, True, True),
                      (False, True, False, False)]
        keys = ("Bmi2", "ArmBase64", "Avx512DQVL", "Avx2", "Vector256Accelerated")
        required = [dict(zip(keys, flags + (storage,)))
                    for flags in arithmetic for storage in (False, True)]
    else:
        raise RuntimeError(f"Unknown total feature family: {kind}")
    if len(family["representatives"]) != len(required):
        raise RuntimeError("Incomplete feature-family representative premises")
    for name, conditions in zip(family["representatives"], required):
        profile = expected_profile(name)
        if any(profile.get(key) is not value for key, value in conditions.items()):
            raise RuntimeError(f"Feature-family representative premise changed: {kind}/{name}")


def coverage_plan(methods, safety=False):
    """Require total audited coverage before building any selected method."""
    if not methods or len(set(methods)) != len(methods):
        raise RuntimeError("Coverage requires distinct selected methods")
    plan = []
    for method in methods:
        manifest = method_manifest(method)
        if method in LEGACY:
            representatives = list(PROFILES)
        elif manifest["verification"].get("allProfiles"):
            representatives = ["scalar"]
        elif family := manifest["verification"].get("familyCoverage"):
            check_family_representatives(family)
            representatives = family["representatives"]
        else:
            raise RuntimeError(f"Total feature coverage is not implemented yet: {method}")
        plan.extend((method, representative) for representative in representatives)
    if safety:
        for method, profile in plan:
            gate = safety_gate(method, profile)
            if gate.get("coverage", {}).get("kind") not in {"feature-family", "all-profiles"}:
                raise RuntimeError(f"Total safety feature coverage is not implemented yet: {method}/{profile}")
    return plan


def checked_certificate(method, profile, inputs, safety=False):
    directory = generated_directory(method, profile)
    if safety:
        directory /= "safety"
    path = directory / "report.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    manifest = (json.loads((VERIFY / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))
                if method in LEGACY else method_manifest(method))
    names = audit_names(method)
    safety_spec = safety_gate(method, profile) if safety else None
    if safety_spec:
        names += safety_spec["theorems"]
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
    if method not in LEGACY:
        check_calling_convention(artifact["methods"][artifact["entryIndex"]], manifest["callingConvention"])
        scope = copy.deepcopy(manifest)
        scope["environment"]["selectedProfile"] = profile
        if report.get("scope") != scope:
            raise RuntimeError(f"Selected contract scope mismatch: {method}/{profile}")
        gate_hash = hashlib.sha256(audit_module(api_entries()[method]).encode("utf-8")).hexdigest()
        if report.get("generatedGateSha256") != gate_hash or sha(directory / "SelectedGate.lean") != gate_hash:
            raise RuntimeError(f"Stale typed audit module: {method}/{profile}")
    if report.get("auditedTheorems") != names or set(report.get("axiomAudits", {})) != set(names):
        raise RuntimeError(f"Missing family gate: {method}/{profile}")
    for name in names:
        axioms = report["axiomAudits"][name]
        if len(set(axioms)) != len(axioms) or set(axioms) - set(manifest["approvedAxioms"]):
            raise RuntimeError(f"Unapproved family axioms: {method}/{profile}")
    combined = {}
    if safety_spec:
        if report.get("evidenceKind") != "arithmetic-and-memory-safety" or report.get("safety") != safety_spec:
            raise RuntimeError(f"Missing or mismatched combined safety evidence: {method}/{profile}")
        expected_coverage = {"aggregateChecked": False, "representative": profile, **safety_spec["coverage"]}
        if report.get("coverage") != expected_coverage or expected_coverage["kind"] not in {"feature-family", "all-profiles"}:
            raise RuntimeError(f"Missing safety family coverage: {method}/{profile}")
        safety_hash = (hashlib.sha256(selected_safety_module(method, profile).encode("utf-8")).hexdigest()
                       if safety_spec.get("generatedAudit") else None)
        if report.get("generatedSafetyGateSha256") != safety_hash or (safety_hash is not None and
                sha(directory / "SelectedSafetyGate.lean") != safety_hash):
            raise RuntimeError(f"Stale typed safety audit module: {method}/{profile}")
        combined = {"evidenceKind": report["evidenceKind"], "safety": safety_spec}
    coverage = report.get("arithmeticCoverage" if safety else "coverage", {})
    if method not in LEGACY:
        if coverage != {"kind": manifest["verification"]["profileCoverage"], "aggregateChecked": False,
                        "representative": profile,
                        "condition": ("Every valid profile; kernel-checked independence of actual program operations"
                                      if manifest["verification"].get("allProfiles") else
                                      "Valid profile agreeing on actual program feature queries and operation availability")}:
            raise RuntimeError(f"Missing conditional program coverage: {method}/{profile}")
        return {"method": method, "representative": profile,
                "report": path.relative_to(ROOT).as_posix(), "reportSha256": sha(path),
                "assemblySha256": artifact["sha256"],
                "generatedProgramSha256": report["generatedProgramSha256"],
                "contract": manifest["verification"]["contract"],
                "allProfilesTheorem": manifest["verification"].get("allProfilesTheorem"),
                "familyCoverage": copy.deepcopy(manifest["verification"].get("familyCoverage")),
                "auditedTheorems": names, "axiomAudits": report["axiomAudits"],
                "timings": report.get("timings"), **combined}
    if coverage.get("kind") != "feature-family" or coverage.get("representative") != profile:
        raise RuntimeError(f"Missing family coverage: {method}/{profile}")
    return {"method": method, "representative": profile,
            "report": path.relative_to(ROOT).as_posix(), "reportSha256": sha(path),
            "assemblySha256": artifact["sha256"], "generatedProgramSha256": report["generatedProgramSha256"],
            "familyTheorem": names[1], "compositionCertificate": names[2],
            "representativeTheorem": names[3], "axiomAudits": report["axiomAudits"],
            "timings": report.get("timings"), **combined}


def check_composition(inputs, operations=False):
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
        targets = ["+UInt256.FeatureCoverage:olean"]
        names = COVERAGE_THEOREMS
        if operations:
            targets.append("+UInt256.OperationCoverage:olean")
            targets.append("+UInt256.MultiplyCoverage:olean")
            names += OPERATION_COVERAGE_THEOREMS
        output = run([lake, "build", *targets], proof)
        audits = theorem_audits(output, names, approved[0])
        check_proof_snapshot(proof, copied_paths, inputs)
    if inputs != source_inputs():
        raise RuntimeError("Inputs changed during coverage checking")
    return audits, lean


def positive_jobs(value):
    jobs = int(value)
    if jobs < 1:
        raise argparse.ArgumentTypeError("jobs must be positive")
    return jobs


def verify_profiles(plan, bundle, jobs, safety=False):
    def check(selection):
        method, profile = selection
        verify_one(["--method", method, "--profile", profile] + (["--safety"] if safety else []), prepared=bundle)

    if jobs == 1:
        for selection in plan:
            check(selection)
        return
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = [pool.submit(check, selection) for selection in plan]
        try:
            for future in as_completed(pending):
                future.result()
        except BaseException:
            for future in pending:
                future.cancel()
            raise


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-reports", action="store_true",
                        help="Compose existing production reports only after checking their complete freshness")
    parser.add_argument("--print-plan", action="store_true",
                        help="Print the complete method/profile CI matrix without building or changing reports")
    parser.add_argument("--safety", action="store_true",
                        help="Require combined memory-safety and arithmetic certificates for every profile")
    parser.add_argument("--jobs", type=positive_jobs, default=1,
                        help="Maximum concurrent isolated profile proofs (default: 1)")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--expanded", action="store_true",
                           help="Require every selected API and baseline method; missing gates fail explicitly")
    selection.add_argument("--method", choices=method_names(),
                           help="Check total profile coverage of one exact method")
    args = parser.parse_args()
    if args.print_plan and args.check_reports:
        parser.error("--print-plan cannot compose reports")
    methods = tuple(method_names()) if args.expanded else (args.method,) if args.method else METHODS
    if args.print_plan:
        plan = coverage_plan(methods, args.safety)
        print(json.dumps({"include": [{"method": method, "profile": profile} for method, profile in plan]}))
        return
    destination = ((generated_directory(args.method) / "coverage.json") if args.method else
                   VERIFY / "generated/coverage.json")
    if args.safety:
        destination = destination.parent / "safety" / destination.name
    destination.unlink(missing_ok=True)
    plan = coverage_plan(methods, args.safety)
    operations = args.safety or any(method not in LEGACY for method in methods)
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
            verify_profiles(plan, bundle, args.jobs, args.safety)
    certificates = [checked_certificate(method, profile, inputs, args.safety) for method, profile in plan]
    composition = check_composition(inputs, operations)
    # Recheck generated files as well as reports after the kernel composition.
    current_certificates = [checked_certificate(method, profile, inputs, args.safety)
                            for method, profile in plan]
    if inputs != source_inputs() or current_certificates != certificates:
        raise RuntimeError("Certificates changed during composition")
    audits, lean = composition
    report = {"status": "verified",
              "evidenceKind": "arithmetic-and-memory-safety" if args.safety else "arithmetic", "coverage": "all valid FeatureProfile configurations",
              "nativeLimitations": native_limitations(methods),
              "methods": list(methods), "selectedApiCoverage": args.expanded,
              "domain": "CIL.FeatureProfile.Valid", "sourceInputs": inputs,
              "semanticsVersion": SEMANTICS_VERSION,
              "compositionToolchain": lean,
              "composition": "Audited universal or full family gates plus kernel-checked total classification and composition rules",
              "auditedTheorems": list(audits), "axiomAudits": audits,
              "certificates": certificates, "sharedBuildTimings": build_timings,
              "proofJobs": None if args.check_reports else args.jobs,
              "totalSeconds": time.perf_counter() - started}
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(destination)
    print(f"Verified total profile coverage for {len(methods)} methods from {len(certificates)} certificates")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Coverage verification failed: {error}", file=sys.stderr)
        sys.exit(1)
