"""Shared process, hashing and source-selection utilities for verification."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
from methods import LEGACY, method_names

ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "verification"
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
