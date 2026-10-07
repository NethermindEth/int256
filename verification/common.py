"""Shared process, hashing and source-selection utilities for verification."""

import hashlib
import json
from pathlib import Path
import subprocess
import threading


ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "verification"
MANIFESTS = VERIFY / "manifests"
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(directory, suffixes):
    return (p for p in directory.rglob("*") if p.is_file() and p.suffix in suffixes
            and not BUILD_DIRECTORIES.intersection(p.relative_to(directory).parts))


_runner_lock = threading.Lock()
_runner_inputs = None
_runner_outputs = {}


def _runner_request(arguments, payload=None, *, cache=True):
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


def api_entries():
    document = json.loads((MANIFESTS / "api-coverage.json").read_text(encoding="utf-8"))
    return json.loads(_runner_request(["entries", "--json"], document))


def coverage_plan(methods, safety=False):
    plan = json.loads(_runner_request(["plan", "--json"], {"methods": list(methods), "safety": safety}))
    return [(job["method"], job["profile"]) for job in plan["include"]]


def __getattr__(name):
    # Temporary registry exports for Python regression scheduling during migration.
    if name not in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY", "BITWISE_DESCRIPTORS",
                    "COMPARISON_GATES", "OPERATOR_DESCRIPTORS", "PRIMITIVE_COMPARISONS"}:
        raise AttributeError(name)
    value = json.loads(_runner_request(["safety-registry"]))[name]
    return frozenset(value) if name in {"MULTIPLY_SAFETY_METHODS", "BITWISE_UNARY"} else value
