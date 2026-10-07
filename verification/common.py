"""Shared process, hashing and source-selection utilities for verification."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import threading


ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "verification"
MANIFESTS = VERIFY / "manifests"
LEGACY = ("Add", "Subtract")
BUILD_DIRECTORIES = frozenset({"artifacts", "bin", "obj", "generated", ".lake", ".vs", "__pycache__"})
PROFILES = ("scalar", "arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx2-bmi1",
            "x64-avx512", "x64-avx512-bmi1")
MULTIPLY_PROFILES = ("scalar", "x64-vector256",
                     "x64-avx2", "x64-avx2-vector256",
                     "x64-avx512dqvl", "x64-avx512dqvl-vector256",
                     "x64-bmi2", "x64-bmi2-vector256",
                     "x64-avx2-bmi2", "x64-avx2-bmi2-vector256",
                     "x64-avx512dqvl-bmi2", "x64-avx512dqvl-bmi2-vector256",
                     "arm64-armbase", "arm64-armbase-vector256")
PROFILE_DIRECTORY = VERIFY / "manifests/profiles"
PROFILE_NAMES = PROFILES + tuple(sorted(path.stem for path in PROFILE_DIRECTORY.glob("*.json")))
SEMANTICS_VERSION = "cil-uint256-operations-1"


def expected_profile(name):
    """The representative for each constructor of Lean FeatureClass.all."""
    if name in PROFILE_NAMES and name not in PROFILES:
        profile = json.loads((PROFILE_DIRECTORY / f"{name}.json").read_text(encoding="utf-8"))
        expected_keys = {key[0].lower() + key[1:] for key in expected_profile("scalar")}
        if set(profile) != expected_keys or profile.get("name") != name:
            raise RuntimeError("Named profile has incomplete or inconsistent capability fields")
        return {key[0].upper() + key[1:]: value for key, value in profile.items()}
    if name not in PROFILES:
        raise RuntimeError(f"Unclassified representative: {name}")
    x64 = name.startswith("x64-")
    avx = name.startswith("x64-avx")
    vl = name.startswith("x64-avx512")
    return {"Name": name, "Architecture": "x64" if x64 else "arm64" if name == "arm64-advsimd" else "scalar",
            "NativeWidth": 64, "LittleEndian": True, "AdvSimd": name == "arm64-advsimd",
            "Sse2": x64, "Ssse3": x64, "Sse42": x64, "Avx": avx, "Avx2": avx,
            "Avx512F": vl, "Avx512FVL": vl, "Bmi1": name.endswith("-bmi1"),
            "Sse41": x64, "Avx512DQ": False, "Avx512DQVL": False,
            "Bmi2": False, "ArmBase64": name == "arm64-advsimd", "Vector256Accelerated": False}


def generated_directory(method="Add", profile="scalar"):
    if method not in method_names() or profile not in PROFILE_NAMES:
        raise ValueError("Unknown verification method or feature profile")
    if method not in LEGACY:
        return VERIFY / "generated/operations" / method / profile
    if profile == "scalar":
        return VERIFY / ("generated" if method == "Add" else "generated/subtract")
    return VERIFY / "generated/profiles" / profile / method.lower()


def run(command, cwd, *, succeeds=True):
    env = os.environ.copy()
    env.update(DOTNET_EnableHWIntrinsic="0", DOTNET_CLI_TELEMETRY_OPTOUT="1",
               DOTNET_SKIP_FIRST_TIME_EXPERIENCE="1", MSBuildEnableWorkloadResolver="false")
    result = subprocess.run(command, cwd=cwd, env=env, text=True, encoding="utf-8",
                            errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="")
    if succeeds != (result.returncode == 0):
        raise RuntimeError(f"Unexpected exit {result.returncode}: {command}")
    return result.stdout


def verifier_command(root=ROOT):
    """Invoke the C# public verifier in the selected regression workspace."""
    root = Path(root).resolve()
    return ["dotnet", "run", "--project", str(root / "verification/Runner/Verification.csproj"),
            "-c", "Release", "--", "--root", str(root), "verify"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(directory, suffixes):
    return (p for p in directory.rglob("*") if p.is_file() and p.suffix in suffixes
            and not BUILD_DIRECTORIES.intersection(p.relative_to(directory).parts))


_runner_lock = threading.Lock()
_runner_inputs = None
_runner_outputs = {}


def _runner_request(arguments, payload=None, *, cache=True, show_output=False):
    """Temporary bridge while proof orchestration moves to the C# runner."""
    global _runner_inputs
    root = Path(__file__).resolve().parent.parent
    project = root / "verification/Runner/Verification.csproj"
    binary = project.parent / "bin/Release/net10.0/Verification.dll"
    serialized = json.dumps(payload, sort_keys=True)
    key = (tuple(arguments), serialized)
    with _runner_lock:
        inputs = {str(p): sha(p) for p in source_files(project.parent, {".cs", ".csproj"})}
        inputs.update({str(p): sha(p) for p in root.iterdir()
                       if p.is_file() and (p.suffix in {".props", ".targets"} or p.name in {"global.json", "NuGet.Config"})})
        inputs.update({str(p): sha(p) for p in source_files(project.parent.parent / "manifests", {".json"})})
        registry = project.parent.parent / "Tests/Fixtures/SIMD/Cases.props"
        inputs[str(registry)] = sha(registry)
        if inputs != _runner_inputs or not binary.is_file():
            _runner_outputs.clear()
            result = subprocess.run(["dotnet", "build", str(project), "-c", "Release", "--nologo"],
                                    cwd=root, capture_output=True, text=True, encoding="utf-8")
            if result.returncode:
                raise RuntimeError("C# gate generator build failed:\n" + result.stdout + result.stderr)
            _runner_inputs = inputs
        if not cache or key not in _runner_outputs:
            result = subprocess.run(["dotnet", str(binary), *arguments], cwd=root,
                                    input=serialized, capture_output=True, text=True, encoding="utf-8")
            if show_output:
                print(result.stderr, end="", file=sys.stderr)
            if result.returncode:
                raise RuntimeError(result.stderr.strip() or "C# verification runner failed")
            if not cache:
                return result.stdout
            _runner_outputs[key] = result.stdout
        return _runner_outputs[key]


def source_inputs(root=ROOT):
    return json.loads(_runner_request(["--root", str(Path(root).resolve()), "inputs"], cache=False))


def copy_source(destination):
    return Path(json.loads(_runner_request(["copy-source", "--json"],
                {"destination": str(Path(destination).resolve())}, cache=False)))


def check_proof_snapshot(proof, relative_paths, inputs):
    return json.loads(_runner_request(["snapshot", "--json"],
        {"proof": str(Path(proof).resolve()), "paths": [str(path) for path in relative_paths], "inputs": inputs}, cache=False))


def build_artifact(project, work, method, fixture=None, simd_fixture=False, fixture_name=None):
    bundle = json.loads(_runner_request(["build-artifact", "--json"],
        {"project": str(Path(project).resolve()), "work": str(Path(work).resolve()), "method": method,
         "fixture": str(Path(fixture).resolve()) if fixture else None,
         "registeredFixture": simd_fixture, "fixtureName": fixture_name}, cache=False, show_output=True))
    for name in ("assembly", "extractor", "project"):
        bundle[name] = Path(bundle[name])
    return bundle


def build_fixture(destination, name, method="Add"):
    return Path(json.loads(_runner_request(["legacy-fixture", "--json"],
        {"destination": str(Path(destination).resolve()), "case": name, "method": method, "extract": False}, cache=False, show_output=True)))


def build_extract(destination, name, method="Add"):
    assembly, generated, output = json.loads(_runner_request(["legacy-fixture", "--json"],
        {"destination": str(Path(destination).resolve()), "case": name, "method": method, "extract": True}, cache=False, show_output=True))
    return Path(assembly), Path(generated), output


def require_production_report(method="Add"):
    return Path(json.loads(_runner_request(["production-report", "--json"], {"method": method}, cache=False)))


def model_refutation(proof, lake, initial, left, right, out, address, actual, expected, method="Add"):
    _runner_request(["model-refutation", "--json"],
        {"proof": str(Path(proof).resolve()), "lake": str(lake), "initial": initial, "method": method,
         "left": str(left), "right": str(right), "out": str(out), "address": str(address), "actual": str(actual), "expected": str(expected)},
        cache=False, show_output=True)
    print(f"PASS: kernel refutes the full contract at byte {address}: actual {actual}, expected {expected}")


def native_witness(destination, assembly, source):
    _runner_request(["native-witness", "--json"],
        {"destination": str(Path(destination).resolve()), "assembly": str(Path(assembly).resolve()), "source": source},
        cache=False, show_output=True)


def mutation_proof(work, project, case, method, profile, baseline, intended=None):
    result = json.loads(_runner_request(["mutation", "--json"],
        {"work": str(Path(work).resolve()), "project": str(Path(project).resolve()), "case": case,
         "method": method, "profile": profile, "baseline": baseline, "intended": intended}, cache=False, show_output=True))
    for name in ("assembly", "extractor", "project"):
        result["bundle"][name] = Path(result["bundle"][name])
    return result["bundle"], Path(result["proof"])


def audit_module(entry):
    return _runner_request(["gate", "--entry-json"], entry)


def bound_audit_names(entry):
    return json.loads(_runner_request(["bound-audits", "--entry-json"], entry))


def api_entries():
    document = json.loads((MANIFESTS / "api-coverage.json").read_text(encoding="utf-8"))
    return json.loads(_runner_request(["entries", "--json"], document))


def method_names():
    return LEGACY + tuple(api_entries())


def method_manifest(name):
    if name in LEGACY:
        return json.loads(_runner_request(["manifest", name]))
    entry = api_entries().get(name)
    if entry is None:
        raise ValueError(f"Unknown verification method: {name}")
    return json.loads(_runner_request(["manifest", "--json"], entry))


def native_limitations(methods):
    return json.loads(_runner_request(["native-limitations", "--json"], list(methods)))


def check_calling_convention(actual, expected):
    _runner_request(["calling-convention", "--json"], {"actual": actual, "expected": expected})


def resolve_fixture_groups(entries, groups):
    resolved = json.loads(_runner_request(["fixture-groups", "--json"], {"entries": entries, "groups": groups}))
    for entry, replacement in zip(entries, resolved):
        entry.clear()
        entry.update(replacement)


def representative_safety_gate(method, profile):
    return json.loads(_runner_request(["safety-representative", method, profile]))


def safety_gate(method, profile):
    return json.loads(_runner_request(["safety", method, profile]))


def selected_safety_module(method, profile):
    return _runner_request(["safety-module", method, profile])


def coverage_plan(methods, safety=False):
    plan = json.loads(_runner_request(["plan", "--json"], {"methods": list(methods), "safety": safety}))
    return [(job["method"], job["profile"]) for job in plan["include"]]


def theorem_audits(output, names, approved):
    return json.loads(_runner_request(["theorem-audits", "--json"],
                      {"output": output, "names": list(names), "approved": list(approved)}))


def rejection_check(kind, output, module="", diagnostic=""):
    _runner_request(["rejection", "--json"],
                    {"kind": kind, "output": output, "module": module, "diagnostic": diagnostic})


def fixture_check(kind, **payload):
    _runner_request(["fixture-check", "--json"], {"kind": kind, **payload})


def template_refutation(proof, lake, template, substitutions, module, theorem, approved, register=False):
    _runner_request(["refutation", "--json"],
        {"proof": str(Path(proof).resolve()), "lake": str(lake), "template": str(Path(template).resolve()),
         "substitutions": [[name, str(value)] for name, value in substitutions.items()],
         "module": module, "theorem": theorem, "approved": list(approved), "register": register}, cache=False, show_output=True)


def simd_data(kind, case, method, profile=""):
    return json.loads(_runner_request(["simd-data", "--json"],
                      {"kind": kind, "case": case, "method": method, "profile": profile}))


def __getattr__(name):
    # Temporary registry exports for Python regression scheduling during migration.
    if name in {"SIMD_CASES", "SIMD_POSITIVES", "SIMD_NEGATIVES"}:
        return tuple(json.loads(_runner_request(["simd-fixtures"]))[name])
    if name not in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY", "BITWISE_DESCRIPTORS",
                    "COMPARISON_GATES", "OPERATOR_DESCRIPTORS", "PRIMITIVE_COMPARISONS"}:
        raise AttributeError(name)
    value = json.loads(_runner_request(["safety-registry"]))[name]
    return frozenset(value) if name in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY"} else value
