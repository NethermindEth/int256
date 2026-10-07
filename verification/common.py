"""Shared process, hashing and source-selection utilities for verification."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(directory, suffixes):
    return (p for p in directory.rglob("*") if p.is_file() and p.suffix in suffixes
            and not BUILD_DIRECTORIES.intersection(p.relative_to(directory).parts))


_runner_lock = threading.Lock()
_runner_inputs = None
_runner_outputs = {}


def _runner_request(arguments, payload=None):
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
        if key not in _runner_outputs:
            result = subprocess.run(["dotnet", str(binary), *arguments], cwd=root,
                                    input=serialized, capture_output=True, text=True, encoding="utf-8")
            if result.returncode:
                raise RuntimeError(result.stderr.strip() or "C# verification runner failed")
            _runner_outputs[key] = result.stdout
        return _runner_outputs[key]


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


def __getattr__(name):
    # Temporary registry exports for Python regression scheduling during migration.
    if name in {"SIMD_CASES", "SIMD_POSITIVES", "SIMD_NEGATIVES"}:
        return tuple(json.loads(_runner_request(["simd-fixtures"]))[name])
    if name not in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY", "BITWISE_DESCRIPTORS",
                    "COMPARISON_GATES", "OPERATOR_DESCRIPTORS", "PRIMITIVE_COMPARISONS"}:
        raise AttributeError(name)
    value = json.loads(_runner_request(["safety-registry"]))[name]
    return frozenset(value) if name in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY"} else value
