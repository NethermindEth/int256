"""Shared isolation, witnesses and rejection gates for verification regressions."""

import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import verifier_command, ROOT, VERIFY, generated_directory, run, sha, source_inputs
from common import copy_source, template_refutation, mutation_proof, native_witness, model_refutation
from common import rejection_check, fixture_check


def isolated_run(script, arguments, prefix):
    with tempfile.TemporaryDirectory(prefix=prefix) as temporary:
        destination = Path(temporary) / "source"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(destination)], ROOT)
        copy_source(destination)
        target = destination / Path(script).resolve().relative_to(ROOT)
        run([sys.executable, str(target), "--workspace", *arguments], destination)


def require_diagnostic_rejection(output, module, diagnostic):
    """Use only after an independent full-contract refutation has passed."""
    rejection_check("diagnostic", output, module, diagnostic)


def reject_resource_failure(output):
    rejection_check("resources", output)


def initial_bytes_expression(witness):
    initial = "0"
    for address, value in reversed(list(witness["initialBytes"].items())):
        initial = f"if address = {int(address)} then {int(value)} else {initial}"
    return initial


def require_changed_method(artifact, baseline, signature):
    """Require a compiled change in the intended reachable method."""
    fixture_check("changed-method", artifact=artifact, baseline=baseline, signature=signature)


def selected_fixture_baseline(method, profile, positive=None, *, safety=False):
    public = [*verifier_command(ROOT), "--method", method, "--profile", profile]
    directory = generated_directory(method, profile)
    if safety:
        public.append("--safety")
        directory /= "safety"
    report_path = directory / "report.json"

    def read_report():
        report = json.loads(report_path.read_text(encoding="utf-8"))
        if safety:
            fixture_check("safety-report", report=report, method=method, profile=profile)
        return report

    run(public, ROOT)
    production = read_report()
    fixture_check("production", production=production, inputs=source_inputs())
    run(public + ["--fixture", "Baseline"], ROOT)
    baseline = read_report()
    fixture_check("baseline", production=production, baseline=baseline, inputs=source_inputs())
    if positive:
        run(public + ["--fixture", positive], ROOT)
        alternative = read_report()
        fixture_check("alternative", baseline=baseline, alternative=alternative)
    return public, report_path, baseline


def build_fixture(destination, name, method="Add"):
    project = destination / "verification/Tests/Fixtures/Nethermind.Int256.csproj"
    source = project.parent / method / f"{name}.cs"
    if not source.is_file():
        raise RuntimeError(f"Fixture maintenance failure: missing {name}")
    run(["dotnet", "build", str(project), "-c", "Release",
         f"-p:FixtureSource={source}", f"-p:FixtureMethod={method}", "-p:EnforceCodeStyleInBuild=true",
         "-p:GenerateDocumentationFile=true"], destination)
    return project.parent / "bin/Release/net10.0/Nethermind.Int256.dll"


def build_extract(destination, name, method="Add"):
    assembly = build_fixture(destination, name, method)
    output = destination / "verification/generated"
    result = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                  str(assembly), str(output), method], ROOT)
    return assembly, output, result


def require_semantic_rejection(output, module):
    # A kernel-checked full-contract refutation must precede this diagnostic gate.
    rejection_check("semantic", output, module)


def require_production_report(method="Add"):
    generated = VERIFY / ("generated" if method == "Add" else "generated/subtract")
    baseline = generated / "Extracted.lean"
    report_path = generated / "report.json"
    if not baseline.is_file() or not report_path.is_file():
        raise RuntimeError(f"Freshly verify production {method} before negative checks")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if (report.get("status") != "verified" or report.get("source", {}).get("kind") != "production"
            or report["sourceInputs"] != source_inputs()
            or report["generatedProgramSha256"] != sha(baseline)
            or any(sha(VERIFY / name) != digest for name, digest in report["leanSourceSha256"].items())):
        raise RuntimeError(f"Fresh current {method} production report required")
    return baseline
