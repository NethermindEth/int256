import CIL.ProfileEquivalence
import CIL.ExecutionLemmas

namespace CIL.AggregateTests

private def empty : Memory := fun _ => none

example : step (.local 0) false 0 [] 0 []
    (write empty (.local 0 0) .unmodeled) = none := by rfl

example : step (.arg 0) false 0 [.unmodeled] 0 [] empty = none := by rfl

example : step (.call 1 1) false 0 [] 0 [.unmodeled] empty = none := by rfl

example : step .ret true 0 [] 0 [.unmodeled] empty = none := by rfl

example : step .convU8 false 0 [] 0 [.i32 (BitVec.ofInt 32 (-1))] empty =
    some (.next 1 [.i64 (BitVec.ofNat 64 (2^32 - 1))] empty) := by rfl

example : step (.bge 9) false 0 [] 0 [.i32 0, .i32 (BitVec.ofInt 32 (-1))] empty =
    some (.next 1 [] empty) := by rfl

private def readArgument : Method :=
  { code := [.aggregateArg 0, .ret], locals := [], aggregateArgs := [0], returnsValue := true }

example (m : Memory) (bits : BitVec 256) :
    (invoke [readArgument] 2 0 [.v256 bits] m).map Prod.snd = some [.v256 bits] := by
  simp [invoke, run, step, readArgument, initFrame, initLocals, Value.initialized]

example (m : Memory) (bits : BitVec 256) (address : Nat) :
    initFrame m 0 readArgument [.v256 bits] (.byte address) = m (.byte address) := by
  simp [initFrame, initLocals, readArgument, writeAggregate]

private def uninitializedLocal : Method :=
  { code := [.aggregateLocal 0, .ret], locals := [.unmodeled],
    aggregateLocals := [0], returnsValue := true }

-- Reusing a child frame cannot expose bytes left by an earlier invocation.
example (m : Memory) (bits : BitVec 256) :
    invoke [uninitializedLocal] 2 0 [] (writeAggregate m 0 0 0 bits) = none := by
  simp [invoke, run, step, uninitializedLocal, initFrame, initLocals]

private def constructor : Method :=
  { code := [.arg 0, .const64 7, .setField 0,
      .arg 0, .const64 11, .setField 1,
      .arg 0, .const64 13, .setField 2,
      .arg 0, .const64 17, .setField 3, .ret],
    locals := [], returnsValue := false }

private def constructValue : Method :=
  { code := [.newValue 1 0, .ret], locals := [], returnsValue := true }

-- The result comes from the four executed field stores, including the high limb.
example : (invoke [constructValue, constructor] 16 0 [] empty).map Prod.snd =
    some [.v256 (Vector.pack256 7 11 13 17)] := by decide

private def partialConstructor : Method :=
  { code := [.arg 0, .const64 7, .setField 0, .ret], locals := [], returnsValue := false }

-- newobj zeroes the value before executing its constructor, independently of local initialization.
example : (invoke [constructValue, partialConstructor] 8 0 [] empty).map Prod.snd =
    some [.v256 (Vector.pack256 7 0 0 0)] := by decide

-- Reusing the allocation cannot expose the previous home's bytes to a partial constructor.
example : (invoke [constructValue, partialConstructor] 8 0 []
    (fun _ => some (.i8 255))).map Prod.snd =
    some [.v256 (Vector.pack256 7 0 0 0)] := by decide

example (p : FeatureProfile) (h : p.LegacyValid) : p.extendLegacy.Valid :=
  p.extendLegacy_valid h

end CIL.AggregateTests
