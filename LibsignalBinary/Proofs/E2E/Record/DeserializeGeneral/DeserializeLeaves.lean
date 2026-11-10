/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopEntryG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserReprG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ProstSSGAtMove
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ProstSSGRepr

/-!
# Segment and Representation Leaf Theorems for General `SessionRecord::deserialize`

Exports the loop-entry, loop-iteration, loop-exit, 344-byte `SessionStructure` relocation, and
representation conversion theorems composed in `Root.lean`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)

/-- Entry segment (`+0x000 → +0x254`, `k = 0`) of `SessionRecord::deserialize`: initializes
`previous_sessions`, reads outer `RecordStructure` key `0x0a` and 1–3 byte length varint, writes
`SessionStructure::default()` (`prostSSGAt A0 … SSG.empty`), and enters the field loop. -/
theorem deserLoopEntryG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeGenSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepG C ctl x R s0 s0 (DeserLoopG C ctl x R s0 0) abs := by
  exact Leaf.DeserLoopEntryG.deserLoopEntryG_ok C ctl hC x R s0 hpc hrun hpre hal

/-- Single field-loop iteration (`+0x254 → +0x254`, `k → k + 1`): reads the 1-byte field key,
checks tag and wire type, and invokes `SessionStructure::merge_field`. -/
theorem deserLoopIterG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hMF : MergeFieldGenOk C ctl (fun _ => True) abs) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScope x.r) (hk : k < (recFields x.r).length)
    (hs : DeserLoopG C ctl x R s0 k s) :
    DeserStepG C ctl x R s0 s (DeserLoopG C ctl x R s0 (k + 1)) abs := by
  exact Leaf.DeserLoopIterG.deserLoopIterG_ok C ctl hMF x R s0 k s hr hk hs

/-- Loop exit (`+0x254 → ret`) when `remaining = 0`: relocates the 344-byte `SessionStructure` into
the `sret` slot (`prostSSGAt_move`) as `current_session = Some` and runs the epilogue to
`deserOutRawG`. -/
theorem deserLoopExitG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopG C ctl x R s0 (recFields x.r).length s) :
    DeserStepG C ctl x R s0 s (DeserRetG x R s0) abs := by
  exact Leaf.DeserLoopExitG.deserLoopExitG_ok C ctl x R s0 s hr hs

/-- Relocates `prostSSGAt A src v` across a 344-byte `memcpy` to `dst`, establishing that word `0`
(`lik` capacity) avoids the `None` niche. -/
theorem prostSSGAt_move (A : RustAlloc) (a : BitVec 64) (v : SSG) :
    prostSSGAt A a v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGAt A b v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  exact Leaf.ProstSSGAtMove.prostSSGAt_move A a v

/-- Converts `prostSSGAt A ss (ssgOf s)` for an in-scope session `s` into `sessionStateReprAt` with
a canonical ghost (`CanonSession`). -/
theorem prostSSG_repr (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (ss : BitVec 64) :
    prostSSGAt A0 ss (ssgOf s) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G s⌝ ∗ sessionStateReprAt A0 ss G s := by
  exact Leaf.ProstSSGRepr.prostSSG_repr_impl r hr s hs ss

/-- Converts the raw `deserOutRecordG` layout at `out` into `sessionRecordAt` holding `r` with
`CanonRecord`. -/
theorem deserReprG_ok (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r) (out : BitVec 64) :
    deserOutRecordG out r ⊢
      ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r := by
  exact Leaf.DeserReprG.deserReprG_ok r hr out (prostSSG_repr r hr)

end CryptoVerification.E2E.Record.DeserializeGeneral
