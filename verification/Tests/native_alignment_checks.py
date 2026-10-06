"""Supplementary native Add/Subtract alignment and overlap checks of an exact DLL.

This does not issue a proof certificate or establish a portable CLI guarantee.
Unsupported hardware profiles are recorded separately from passing samples.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, VERIFY, run, sha


PROFILES = {
    "scalar": (False, False, False, False),
    "x64-sse42": (True, False, False, False),
    "x64-avx2": (True, True, False, False),
    "x64-avx512": (True, True, True, False),
    "arm64-advsimd": (False, False, False, True),
}


def environment(profile):
    env = os.environ.copy()
    for prefix in ("DOTNET_", "COMPlus_"):
        env.update({prefix + name: value for name, value in {
            "TieredCompilation": "0",
            "EnableHWIntrinsic": "0" if profile == "scalar" else "1",
            # Disable AVX itself to exercise legacy SSE encodings/containment.
            "EnableAVX": "0" if profile == "x64-sse42" else "1",
            "EnableAVX2": "0" if profile == "x64-sse42" else "1",
            "EnableAVX512": "1" if profile == "x64-avx512" else "0",
        }.items()})
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assembly", required=True, type=Path)
    parser.add_argument("--profile", action="append", choices=PROFILES)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    assembly = args.assembly.resolve(strict=True)
    identity = sha(assembly)
    # Never leave an earlier successful receipt behind after a failed attempt.
    if args.output:
        if args.output.resolve() == assembly:
            parser.error("Output must not overwrite the tested assembly")
        args.output.unlink(missing_ok=True)
    records = []
    with tempfile.TemporaryDirectory(prefix="int256-native-alignment-") as temporary:
        artifacts = Path(temporary)
        run(["dotnet", "build", str(VERIFY / "Tests/NativeAlignmentWitness/NativeAlignmentWitness.csproj"),
             "-c", "Release", "--nologo", f"-p:VerifiedAssembly={assembly}",
             f"-p:ArtifactsPath={artifacts}", "-p:EnforceCodeStyleInBuild=true",
             "-p:GenerateDocumentationFile=true"], ROOT)
        driver = artifacts / "bin/NativeAlignmentWitness/release/NativeAlignmentWitness.dll"
        for profile in args.profile or PROFILES:
            result = subprocess.run(["dotnet", str(driver)], cwd=ROOT,
                                    env=environment(profile), text=True,
                                    encoding="utf-8", capture_output=True, check=True)
            record = json.loads(result.stdout)
            if (record.get("status") != "passed" or record.get("cases") != 41600 or
                    record.get("assemblySha256") != identity):
                raise RuntimeError(f"Invalid native witness result: {record}")
            flags = tuple(record.get(key) for key in ("sse42", "avx2", "avx512", "advSimd"))
            architecture = record.get("architecture")
            supported = architecture in ("X64", "Arm64") and flags == PROFILES[profile]
            if profile.startswith("x64-"):
                supported = supported and architecture == "X64"
            elif profile.startswith("arm64-"):
                supported = supported and architecture == "Arm64"
            record.update(profile=profile, status="passed" if supported else "unavailable")
            records.append(record)
            print(f"{record['status'].upper()}: {profile} ({architecture}, {record['runtime']})", flush=True)
    if sha(assembly) != identity:
        raise RuntimeError("Tested assembly changed during native checks")
    if not any(record["status"] == "passed" for record in records):
        raise RuntimeError("No requested native profile was available")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"kind": "native-samples", "samples": records}, indent=2) + "\n",
                               encoding="utf-8")


if __name__ == "__main__":
    main()
