/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import DY.Trace.Monad
public import Mathlib.Tactic.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Refinement.EncodeWithCovered
import VCVio.EvalDist.ProbabilityNotation
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Clamping, byte-array round-trip, and session protobuf helpers

Idempotence of RFC 7748 scalar clamping (`clamp_clamp`), `ByteArray` round-trip for literal
bytes (`ofByteArray_toByteArray`), and auxiliary protobuf encoding definitions (`pbFields`,
`PbOk`, `sessionBytes`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY.Libsignal.Refinement DY.TrWire

section Gamma

open DY DY.Comparse DY.DiffieHellman DY.SymEnc DY.KdfExtract DY.Concat DY.Literal DY.Trunc
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)

theorem clampByte_idem (i : Nat) (b : BitVec 8) : clampByte i (clampByte i b) = clampByte i b := by
  unfold clampByte
  split
  · rw [BitVec.and_assoc, BitVec.and_self]
  · split
    · have h : ∀ x : BitVec 8,
          (((x &&& 0x7F#8) ||| 0x40#8) &&& 0x7F#8) ||| 0x40#8 = (x &&& 0x7F#8) ||| 0x40#8 := by
        decide
      exact h b
    · rfl

theorem clamp_clamp (k : HwBytes) : clamp (clamp k) = clamp k := by
  unfold clamp
  split
  · rename_i h
    simp only [List.length_mapIdx, h, ite_true]
    rw [List.mapIdx_mapIdx]
    congr 1
    funext i b
    exact clampByte_idem i b
  · rfl

/-- Literal bytes round-trip through `ByteArray`. -/
theorem ofByteArray_toByteArray (bs : HwBytes) :
    ofByteArray ⟨(bs.map UInt8.ofBitVec : List UInt8).toArray⟩ = bs := by
  simp [ofByteArray, Function.comp_def]

end Gamma

section Runs

open DY DY.Comparse

end Runs

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Rust

section RecordBytes

def pbFields (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap (fun p => encodeField p.1 0 0 p.2)

def PbOk (p : Nat × PbValue) : Prop :=
  match p.2 with
  | .varint _ => True
  | .bytes _ => True
  | .unknown _ _ => False

def sessionBytes (s : SessionRec) : HwBytes :=
  u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
  bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
  u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
  s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
  ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
  u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
  bytesField 15 s.pqRatchetState

end RecordBytes

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.TripleRatchet.Refinement
export DY.Libsignal.Composed.Refinement (
  clampByte clamp x25519UCoord leBytes variantBytes ofByteArray litOf
  trItemEncode honestTrItems trFields trWireBytes spqrKeyBytes
  Ghost ConcretizedTerm gamma' gamma
  clampByte_idem  clamp_clamp ofByteArray_toByteArray
    pbFields PbOk
   sessionBytes
)
end DY.Libsignal.TripleRatchet.Refinement

namespace DY.Libsignal.Refinement
export DY.Libsignal.Composed.Refinement (
  clampByte_idem  clamp_clamp ofByteArray_toByteArray
)
end DY.Libsignal.Refinement
