"""Native samples of the versioned SIMD fixtures on available runtime profiles.

Actual runtime flags and complete initial/result byte maps are recorded. These
samples supplement the kernel proofs; unavailable profiles are explicitly skipped.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, VERIFY, PROFILES, run, sha
from simd_checks import NEGATIVES, applicable, witness


def environment(profile):
    env = os.environ.copy()
    for prefix in ("DOTNET_", "COMPlus_"):
        env[prefix + "EnableHWIntrinsic"] = "1"
        env[prefix + "EnableAVX2"] = "0" if profile == "x64-sse42" else "1"
        env[prefix + "EnableAVX512"] = "1" if "avx512" in profile else "0"
        env[prefix + "EnableBMI1"] = "1" if profile.endswith("bmi1") else "0"
    return env


def initial_bytes(a, b):
    memory = bytearray(192)
    memory[:32] = b"".join(word.to_bytes(8, "little") for word in a)
    memory[64:96] = b"".join(word.to_bytes(8, "little") for word in b)
    return memory.hex()


def positive_samples(method):
    maximum = 2**64 - 1
    vectors = [
        ("small-operand", [maximum]*4, [1, 0, 0, 0]),
        ("vector-fast", [11, 13, 17, 19], [2, 3, 5, 7]),
    ]
    if method == "Add":
        vectors += [
            ("cross-half", [2, maximum, 5, 7], [3, 1, 1, 2]),
            # Carry through limbs 1 and 2: ARM repairs its early high-half store;
            # SSE uses its scalar cascade fallback before storing.
            ("cascade", [maximum, maximum, maximum, 5], [1, 0, 0, 2]),
        ]
    else:
        vectors += [
            ("cross-half", [10, 0, 5, 7], [1, 1, 1, 2]),
            ("cascade", [0, 0, 0, 5], [1, 0, 0, 2]),
        ]
    # Exact aliases, partial overlaps with either input, and disjoint output.
    return [(name, a, b, output) for name, a, b in vectors
            for output in (0, 8, 64, 72, 128)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILES[1:], action="append")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    profiles = args.profile or list(PROFILES[1:])
    records = []
    with tempfile.TemporaryDirectory(prefix="int256-native-simd-") as temporary:
        work = Path(temporary)

        def build(project, artifacts, *properties):
            run(["dotnet", "build", str(project), "-c", "Release", "--nologo",
                 f"-p:ArtifactsPath={artifacts}", "-p:EnforceCodeStyleInBuild=true",
                 "-p:GenerateDocumentationFile=true", *properties], ROOT)

        build(VERIFY / "Tests/NativeSIMDWitness/NativeSIMDWitness.csproj", work / "driver")
        driver = work / "driver/bin/NativeSIMDWitness/release/NativeSIMDWitness.dll"
        assemblies = {}
        for profile in profiles:
            available = True
            for method in ("Add", "Subtract"):
                for case in ("Baseline", *[case for case in NEGATIVES if applicable(case, method, profile)]):
                    key = (case, method)
                    if key not in assemblies:
                        artifacts = work / case / method
                        build(VERIFY / "Tests/Fixtures/SIMD/Nethermind.Int256.csproj", artifacts,
                              f"-p:FixtureCase={case}", f"-p:FixtureMethod={method}")
                        assemblies[key] = artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"
                    assembly = assemblies[key]
                    if case == "Baseline":
                        samples = [(name, a, b, output, "positive")
                                   for name, a, b, output in positive_samples(method)]
                    else:
                        a, b, output, (address, actual) = witness(case, method)
                        samples = [(case, a, b, output, f"{address}:{actual}")]
                    for name, a, b, output, expected in samples:
                        result = subprocess.run(["dotnet", str(driver), str(assembly), method, profile,
                                                 initial_bytes(a, b), str(output), expected],
                                                cwd=ROOT, env=environment(profile), text=True,
                                                encoding="utf-8", capture_output=True, check=False)
                        if result.returncode not in (0, 77):
                            raise RuntimeError(f"Native {case}/{method}/{profile} failed:\n{result.stdout}\n{result.stderr}")
                        record = json.loads(result.stdout)
                        record.update(case=case, method=method, profile=profile,
                                      sample=name, assemblySha256=sha(assembly), witness=expected)
                        records.append(record)
                        if result.returncode == 77:
                            print(f"SKIP: {profile}; actual runtime flags do not match", flush=True)
                            available = False
                            break
                    if not available:
                        break
                    print(f"PASS: native {case}/{method}/{profile}", flush=True)
                if not available:
                    break
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"kind": "native-samples", "samples": records}, indent=2) + "\n", encoding="utf-8")
    print(f"Native samples: {sum(r['status'] == 'matched' for r in records)} matched, "
          f"{sum(r['status'] == 'unsupported' for r in records)} unavailable profiles", flush=True)


if __name__ == "__main__":
    main()
