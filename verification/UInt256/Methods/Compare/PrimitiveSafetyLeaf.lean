import Extracted
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

def leafIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .field _ => true | _ => false

def leafBody : CIL.Method := Extracted.program[leafIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def leafSigned : Bool := leafBody.code.any fun op => match op with | .blt _ => true | _ => false

def leafScalarFirst : Bool :=
  let field := leafBody.code.findIdx fun op => match op with | .field _ => true | _ => false
  match leafBody.code[field - 1]? with | some (.arg 1) => true | _ => false

def leafResult (memory : Memory) (input : Reference) (word : BitVec 64) : BitVec 32 :=
  if leafSigned && decide (word.toInt < 0) then if leafScalarFirst then 1 else 0
  else if inputLimb memory input 1 = 0 ∧ inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 then
    if (if leafScalarFirst then word.toNat < (inputLimb memory input 0).toNat
        else (inputLimb memory input 0).toNat < word.toNat) then 1 else 0
  else if leafScalarFirst then 1 else 0

macro "primitive_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, CIL.truth, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, cil_code, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

/-- Follow the current extracted branch ordering and field reads; no helper
    arithmetic contract is assumed. -/
theorem leaf_run (memory : Memory) (input : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program memory [input] []) :
    run Extracted.program 22 leafIndex 0
      (scalarOperatorArguments leafScalarFirst input (.i64 word)) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (leafResult memory input word))]) := by
  have formed := call.input_formed (reference := input) (by simp)
  have constant (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := by rfl
  have fields := fun index rest => call.input_field_instruction (reference := input) (by simp) index rest
  have first : leafScalarFirst = leafScalarFirst := rfl
  conv at first => rhs; cbv
  have signed : leafSigned = leafSigned := rfl
  conv at signed => rhs; cbv
  conv in leafIndex => cbv
  simp only [first]
  first
    | (have unsigned : leafSigned = false := by decide
       by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
       · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
         · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
           · primitive_steps 13 with formed, constant, fields, h1, h2, h3
             simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           · primitive_steps 9 with formed, constant, fields, h1, h2, h3
             simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         · primitive_steps 6 with formed, constant, fields, h3, h2
           simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h3, h2, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       · primitive_steps 3 with formed, constant, fields, h3
         simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
    | (have signedLeaf : leafSigned = true := by decide
       by_cases negative : word.toInt < 0
       · primitive_steps 4 with formed, constant, negative
         simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       · primitive_steps 4 with formed, constant, negative
         first
           | (have forward : leafScalarFirst = false := by decide
              by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
              · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
                · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
                  · primitive_steps 13 with formed, constant, fields, h1, h2, h3
                    simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
                  · primitive_steps 9 with formed, constant, fields, h1, h2, h3
                    simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
                · primitive_steps 6 with formed, constant, fields, h3, h2
                  simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h3, h2, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
              · primitive_steps 3 with formed, constant, fields, h3
                simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
           | (have backward : leafScalarFirst = true := by decide
              by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
              · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
                · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
                  · primitive_steps 13 with formed, constant, fields, h1, h2, h3
                    simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
                  · primitive_steps 9 with formed, constant, fields, h1, h2, h3
                    simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
                · primitive_steps 6 with formed, constant, fields, h1, h2
                  simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, h2, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
              · primitive_steps 3 with formed, constant, fields, h1
                simp (config := { implicitDefEqProofs := false }) [run, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, leafResult, first, signed, h1, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

#print axioms leaf_run
end UInt256Proof.Compare.PrimitiveSafety
