import UInt256.Methods.Add.Correctness

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

-- Supplementary concrete check of the extracted entry, aliasing and carry ripple.
def rippleBytes : Bytes := fun address =>
  if address < 32 then 255 else if address = 32 then 1 else 0

example :
    (invoke Extracted.program 512 0 [.object 0, .object 32, .object 0]
      (byteMemory rippleBytes)).map (fun (m, _) => m (.byte 31)) =
        some (some (.i8 0)) := by decide

end UInt256Proof
