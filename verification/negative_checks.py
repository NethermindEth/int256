"""Isolated arithmetic, stale-output and fail-closed extraction regressions."""

from pathlib import Path
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "verification"


def run(command, cwd, *, succeeds=True):
    env = os.environ.copy()
    env.update(DOTNET_EnableHWIntrinsic="0", DOTNET_CLI_TELEMETRY_OPTOUT="1",
               DOTNET_SKIP_FIRST_TIME_EXPERIENCE="1", MSBuildEnableWorkloadResolver="false")
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, end="")
    if succeeds != (result.returncode == 0):
        raise RuntimeError(f"Unexpected exit {result.returncode}: {command}")
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_source(destination):
    shutil.copytree(ROOT / "src", destination / "src",
                    ignore=shutil.ignore_patterns("artifacts", "bin", "obj", "TestResults"))
    for name in ("global.json", "README.md", ".editorconfig"):
        shutil.copy2(ROOT / name, destination / name)
    proof = destination / "verification"
    shutil.copytree(VERIFY, proof, ignore=shutil.ignore_patterns("generated", ".lake", "bin", "obj"))
    workflows = destination / ".github/workflows"
    workflows.mkdir(parents=True)
    shutil.copy2(ROOT / ".github/workflows/verify-uint256.yml", workflows / "verify-uint256.yml")
    return proof


def build_extract(destination):
    project = destination / "src/Nethermind.Int256/Nethermind.Int256.csproj"
    run(["dotnet", "build", str(project), "-c", "Release"], destination)
    assembly = destination / "src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll"
    output = destination / "verification/generated"
    result = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                  str(assembly), str(output)], ROOT)
    return assembly, output, result


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Lean 4.34.1 / lake must be on PATH")
    baseline = VERIFY / "generated/Extracted.lean"
    if not baseline.exists():
        raise RuntimeError("Extract and check the valid baseline before negative checks")
    run([lake, "build", "Audit"], VERIFY)
    with tempfile.TemporaryDirectory(prefix="int256-carry-") as temporary:
        destination = Path(temporary)
        proof = copy_source(destination)
        source = destination / "src/Nethermind.Int256/UInt256.cs"
        text = source.read_text(encoding="utf-8-sig")
        original = "carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);"
        if text.count(original) != 1:
            raise RuntimeError("Carry mutation anchor changed; review regression")
        source.write_text(text.replace(original,
            "carry = (t < x ? 0UL : 0UL) + (r < t ? 1UL : 0UL);"), encoding="utf-8")
        assembly, generated, _ = build_extract(destination)
        if digest(generated / "Extracted.lean") == digest(baseline):
            raise RuntimeError("Mutation did not change imported program")
        witness = destination / "Witness"
        witness.mkdir()
        (witness / "Witness.csproj").write_text(
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup><ItemGroup>'
            f'<Reference Include="Nethermind.Int256"><HintPath>{assembly.as_posix()}</HintPath>'
            '</Reference></ItemGroup></Project>', encoding="utf-8")
        (witness / "Program.cs").write_text(
            'using System;\nusing Nethermind.Int256;\n'
            'UInt256 a = new(ulong.MaxValue, 1, 0, 0), b = new(1, 1, 0, 0);\n'
            'UInt256.Add(a, b, out UInt256 r);\n'
            'Console.WriteLine($"Mutation witness: limbs {r.u0},{r.u1},{r.u2},{r.u3}; expected 0,3,0,0");\n'
            'if (r.u0 != 0 || r.u1 != 2 || r.u2 != 0 || r.u3 != 0) Environment.Exit(1);\n',
            encoding="utf-8")
        run(["dotnet", "run", "--project", str(witness), "-c", "Release"], destination)
        output = run([lake, "build", "Audit"], proof, succeeds=False)
        if "UInt256/Methods/Add/Helpers.lean" not in output.replace("\\", "/") or "error:" not in output:
            raise RuntimeError("Negative proof failed outside expected proof compilation")
        print("PASS: compilable wrong arithmetic changes extraction and fails the correctness proof")
        # Seed all three old success artifacts. The public command must consume
        # its new build/extraction, fail on the changed code, and remove the old report.
        for name in ("Extracted.lean", "artifact.json", "report.json"):
            shutil.copy2(VERIFY / "generated" / name, generated / name)
        output = run([sys.executable, str(proof / "verify.py")], destination, succeeds=False)
        if "UInt256/Methods/Add/Helpers.lean" not in output.replace("\\", "/") or "Verification failed:" not in output:
            raise RuntimeError("Stale regression did not reach fresh proof checking")
        if (generated / "report.json").exists():
            raise RuntimeError("Stale successful report survived failed verification")
        print("PASS: stale extraction and report cannot verify a changed assembly")
    with tempfile.TemporaryDirectory(prefix="int256-unsupported-") as temporary:
        destination = Path(temporary)
        copy_source(destination)
        source = destination / "src/Nethermind.Int256/UInt256.cs"
        text = source.read_text(encoding="utf-8-sig")
        original = "ulong t = x + y;"
        if text.count(original) != 1:
            raise RuntimeError("Unsupported mutation anchor changed; review regression")
        source.write_text(text.replace(original, "ulong t = x * y;"), encoding="utf-8")
        project = destination / "src/Nethermind.Int256/Nethermind.Int256.csproj"
        run(["dotnet", "build", str(project), "-c", "Release"], destination)
        assembly = destination / "src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll"
        output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                      str(assembly), str(destination / "verification/generated")], ROOT, succeeds=False)
        if "Unsupported instruction:" not in output or "mul" not in output:
            raise RuntimeError("Unsupported CIL failed for an unexpected reason")
        print("PASS: reachable unsupported mul rejected explicitly")
    fixture = VERIFY / "RegressionFixture"
    run(["dotnet", "build", str(fixture), "-c", "Release",
         "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], ROOT)
    run(["dotnet", "build", str(ROOT / "src/Nethermind.Int256/Nethermind.Int256.csproj"),
         "-c", "Release", "--no-incremental", "-p:EnableZkEvm=false"], ROOT)
    assembly = ROOT / "src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll"
    with tempfile.TemporaryDirectory(prefix="int256-metadata-") as temporary:
        destination = Path(temporary)
        for mode, diagnostic in (("unresolved", "MissingAddHelper"),
                                 ("layout", "Unsupported field"),
                                 ("cycle", "Malformed or cyclic control flow"),
                                 ("framework", "Unsupported assembly identity"),
                                 ("configuration", "Unsupported assembly identity")):
            mutated = destination / f"{mode}.dll"
            run(["dotnet", "run", "--project", str(fixture), "-c", "Release", "--no-build", "--",
                 mode, str(assembly), str(mutated)], ROOT)
            output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                          str(mutated), str(destination / mode)], ROOT, succeeds=False)
            if diagnostic not in output:
                raise RuntimeError(f"{mode} fixture failed for an unexpected reason")
            print(f"PASS: {mode} extraction fixture rejected explicitly")
    run([lake, "build", "Audit"], VERIFY)


if __name__ == "__main__":
    main()
