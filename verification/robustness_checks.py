"""Compile real Add variants and check them with the unchanged proof sources."""

import json
from pathlib import Path
import shutil
import sys
import tempfile
import time

from common import ROOT, VERIFY, run
from negative_checks import copy_source


def replace_once(text, original, replacement):
    if text.count(original) != 1:
        raise RuntimeError(f"Variant anchor is ambiguous or absent: {original}")
    return text.replace(original, replacement)


def alternative_carry(text):
    return replace_once(text,
        "carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);",
        "carry = (t < y ? 1UL : 0UL) + (r < t ? 1UL : 0UL);")


def reorder_intermediates(text):
    start = text.index("private static bool AddScalar(")
    end = text.index("private static bool AddVector128(", start)
    body = replace_once(text[start:end], "ulong carry = 0;",
        "ulong a1 = a.u1, b1 = b.u1, a2 = a.u2, b2 = b.u2, a3 = a.u3, b3 = b.u3;\n"
        "        ulong carry = 0;")
    for i in range(1, 4):
        body = replace_once(body, f"AddWithCarry(a.u{i}, b.u{i}, ref carry, out ulong r{i});",
                            f"AddWithCarry(a{i}, b{i}, ref carry, out ulong r{i});")
    return text[:start] + body + text[end:]


def inline_stores(text):
    start = text.index("private static bool AddScalarUInt64(")
    end = text.index("    /// <summary>", start)
    body = text[start:end]
    replacements = {
        "StoreLimbs(out res, low, a1, a2, a3);": ("low", "a1", "a2", "a3"),
        "StoreLimbs(out res, r0, a1, a2, a3);": ("r0", "a1", "a2", "a3"),
        "StoreLimbs(out res, r0, 0, a2, a3);": ("r0", "0", "a2", "a3"),
        "StoreLimbs(out res, r0, 0, 0, a3);": ("r0", "0", "0", "a3"),
        "StoreLimbs(out res, r0, 0, 0, 0);": ("r0", "0", "0", "0"),
    }
    for call, values in replacements.items():
        if call not in body:
            raise RuntimeError(f"Missing inline-store anchor: {call}")
        stores = "Unsafe.SkipInit(out res);\n" + "\n".join(
            f"        Unsafe.AsRef(in res.u{i}) = {value};" for i, value in enumerate(values))
        body = body.replace(call, stores)
    return text[:start] + body + text[end:]


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean/lake must be on PATH")
    baseline = None
    proof_hashes = None
    seen = set()
    results = []
    for name, transform, target in (("baseline", lambda text: text, None),
                                   ("alternative-carry", alternative_carry, "AddWithCarry"),
                                   ("reordered-intermediates", reorder_intermediates, "AddScalar"),
                                   ("inlined-stores", inline_stores, "AddScalarUInt64")):
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix=f"int256-robust-{name}-") as temporary:
            destination = Path(temporary)
            # Preserve repository provenance without creating commits. Source
            # files come from the current worktree, including uncommitted edits.
            run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT),
                 str(destination)], ROOT)
            proof = copy_source(destination)
            source = destination / "src/Nethermind.Int256/UInt256.cs"
            text = source.read_text(encoding="utf-8-sig")
            source.write_text(transform(text), encoding="utf-8")
            run([sys.executable, str(proof / "verify.py")], destination)
            report = json.loads((proof / "generated/report.json").read_text(encoding="utf-8"))
            if report["status"] != "verified":
                raise RuntimeError(f"{name}: fresh verifier did not certify the artifact")
            program_hash = report["generatedProgramSha256"]
            if program_hash in seen:
                raise RuntimeError(f"{name} did not produce distinct extracted CIL")
            seen.add(program_hash)
            if baseline is None:
                baseline = report
                proof_hashes = report["leanSourceSha256"]
            elif report["leanSourceSha256"] != proof_hashes:
                raise RuntimeError("Handwritten proof sources changed between variants")
            if target is not None:
                def method_instructions(artifact):
                    method = next(m for m in artifact["methods"] if f"::{target}(" in m["signature"])
                    return [(i["opcode"], i["operand"]) for i in method["instructions"]]
                if method_instructions(report["artifact"]) == method_instructions(baseline["artifact"]):
                    raise RuntimeError(f"{name}: intended method's instructions did not change")
            results.append({"variant": name, "assemblySha256": report["artifact"]["sha256"],
                            "programSha256": program_hash,
                            "seconds": round(time.monotonic() - started, 3)})
            print(f"PASS: {name} verifies with unchanged proof sources")
    print(json.dumps({"proofSources": proof_hashes, "variants": results}, indent=2))


if __name__ == "__main__":
    main()
