"""Shared process, hashing and source-selection utilities for verification."""

import hashlib
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "verification"
BUILD_DIRECTORIES = frozenset({"artifacts", "bin", "obj", "generated", ".lake", "__pycache__"})
PROFILES = ("scalar", "arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx2-bmi1",
            "x64-avx512", "x64-avx512-bmi1")
SEMANTICS_VERSION = "cil-simd-2"


def expected_profile(name):
    """The representative for each constructor of Lean FeatureClass.all."""
    if name not in PROFILES:
        raise RuntimeError(f"Unclassified representative: {name}")
    x64 = name.startswith("x64-")
    avx = name.startswith("x64-avx")
    vl = name.startswith("x64-avx512")
    return {"Name": name, "Architecture": "x64" if x64 else "arm64" if name == "arm64-advsimd" else "scalar",
            "NativeWidth": 64, "LittleEndian": True, "AdvSimd": name == "arm64-advsimd",
            "Sse2": x64, "Ssse3": x64, "Sse42": x64, "Avx": avx, "Avx2": avx,
            "Avx512F": vl, "Avx512FVL": vl, "Bmi1": name.endswith("-bmi1")}


def generated_directory(method="Add", profile="scalar"):
    if method not in ("Add", "Subtract") or profile not in PROFILES:
        raise ValueError("Unknown verification method or feature profile")
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
