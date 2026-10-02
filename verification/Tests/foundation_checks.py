"""Kernel-check shared SIMD foundations and enforce their transitive axiom audits."""

import json
from pathlib import Path
import re
import shutil
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, VERIFY, run
from verify import source_inputs


TARGETS = ("VectorSemantics", "VectorMemory", "ProfileSemantics", "SIMDArithmetic")
REQUIRED = frozenset({
    "CIL.Vector.ternary_add", "CIL.Vector.ternary_subtract",
    "CIL.Vector.pack256_lanes", "CIL.Vector.avx2_blend_incoming",
    "CIL.Vector.arithmetic_sign_mask", "UInt256Proof.readBytes_writeBytes",
    "UInt256Proof.captured256_survives_store", "UInt256Proof.vector_store4",
    "UInt256Proof.ProfileChecks.fixed_query", "CIL.invoke_representative_eq",
    "CIL.invoke_same_family_eq", "UInt256Proof.SIMD.packed_cascade",
    "UInt256Proof.SIMD.read_lookup", "UInt256Proof.SIMD.ternary_carry_mask",
    "UInt256Proof.SIMD.ternary_borrow_mask",
    "UInt256Proof.SIMD.carry_generated_propagated",
    "UInt256Proof.SIMD.borrow_generated_propagated", "UInt256Proof.SIMD.cascade_flags",
    "UInt256Proof.SIMD.add_cascade_words", "UInt256Proof.SIMD.subtract_cascade_words",
    "UInt256Proof.SIMD.add_cascade_vector", "UInt256Proof.SIMD.subtract_cascade_vector",
    "UInt256Proof.add_contract_profiles", "UInt256Proof.subtract_contract_profiles",
})
AUDIT = re.compile(r"'([^']+)' depends on axioms: \[([^]\r\n]*)\]")


def check_audits(output, approved, required=REQUIRED):
    audits = {}
    for theorem, text in AUDIT.findall(output):
        if theorem in audits:
            raise RuntimeError(f"Duplicate axiom audit: {theorem}")
        axioms = [name.strip() for name in text.split(",") if name.strip()]
        if len(axioms) != len(set(axioms)):
            raise RuntimeError(f"Duplicate axiom in audit: {theorem}")
        if set(axioms) - set(approved):
            raise RuntimeError(f"Unapproved axioms for {theorem}: {axioms}")
        audits[theorem] = axioms
    missing = required - audits.keys()
    if missing:
        raise RuntimeError(f"Missing axiom audits: {sorted(missing)}")
    return audits


class AuditParserTests(unittest.TestCase):
    def test_accepts_approved_and_empty(self):
        self.assertEqual(check_audits("'a' depends on axioms: [propext]\n"
                                     "'b' depends on axioms: []", {"propext"}, {"a", "b"}),
                         {"a": ["propext"], "b": []})

    def test_rejects_missing(self):
        with self.assertRaisesRegex(RuntimeError, "Missing"):
            check_audits("", {"propext"}, {"a"})

    def test_rejects_duplicate(self):
        with self.assertRaisesRegex(RuntimeError, "Duplicate axiom audit"):
            check_audits("'a' depends on axioms: []\n'a' depends on axioms: []", set(), {"a"})

    def test_rejects_unapproved(self):
        with self.assertRaisesRegex(RuntimeError, "Unapproved"):
            check_audits("'a' depends on axioms: [invented.correctness]", {"propext"}, {"a"})

    def test_rejects_unapproved_extra_audit(self):
        with self.assertRaisesRegex(RuntimeError, "Unapproved"):
            check_audits("'a' depends on axioms: []\n'b' depends on axioms: [bad]", set(), {"a"})

    def test_rejects_duplicate_axiom(self):
        with self.assertRaisesRegex(RuntimeError, "Duplicate axiom in"):
            check_audits("'a' depends on axioms: [propext, propext]", {"propext"}, {"a"})


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(AuditParserTests)
    if not unittest.TextTestRunner().run(suite).wasSuccessful():
        raise RuntimeError("Axiom audit parser checks failed")
    manifests = [json.loads((VERIFY / f"manifests/{method}.json").read_text(encoding="utf-8"))
                 for method in ("add", "subtract")]
    approved = set(manifests[0]["approvedAxioms"])
    if approved != set(manifests[1]["approvedAxioms"]):
        raise RuntimeError("Foundation axiom approvals differ between method manifests")
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("Pinned Lean toolchain must be available on PATH")
    inputs = source_inputs()
    output = run([lake, "-d", str(VERIFY), "build",
                  *(f"+Tests.{target}:olean" for target in TARGETS)], ROOT)
    audits = check_audits(output, approved)
    if inputs != source_inputs():
        raise RuntimeError("Inputs changed during foundation checking")
    print(f"Checked four foundation modules and {len(audits)} transitive axiom audits")


if __name__ == "__main__":
    main()
