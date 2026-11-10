/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs -- shake: keep

/-!
# Heap Predicates for `SessionRecord` with Previous Sessions

While `sessionRecordAt` fixes `previous_sessions = []`, the over-accept path of `decrypt_prekey`
archives the displaced session via `archive_current_state_inner`, producing a `SessionRecord` with
non-empty `previous_sessions`. This module defines the separation-logic predicates (`prevVecAt`,
`Prev1`, `sessionRecordPrevAt`, and `sessionBucketEntryPrevAt`) shared across the over-path proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.E2E.InMem.HashbrownBin

/-! ## `previous_sessions : Vec<Vec<u8>>` -/

/-- Element predicate for `previous_sessions`: an owned `Vec<u8>` at `a` holding `bs`. -/
abbrev prevElem (A : RustAlloc) : List (BitVec 8) → BitVec 64 → SepProp :=
  fun bs a => vecU8 A a bs

/-- Three-word `{cap, ptr, len}` header of `previous_sessions` at `r`. -/
abbrev HdrP (r cap ptr len : BitVec 64) : SepProp :=
  vecHeader r cap ptr len

/-- `previous_sessions` (`Vec<Vec<u8>>`) at `r` with capacity `cap`, buffer `ptr`, and elements `ps`. -/
abbrev prevVecAt (A : RustAlloc) (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (prevElem A) r cap ptr ps

/-- Backing buffer of `previous_sessions` after `insert(0, enc)` into an empty vector (`grow_one`
allocates capacity 4 = 96 bytes, with `enc` in slot 0 and 72 spare bytes), kept opaque to framing. -/
def Prev1 (A : RustAlloc) (q : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  vecBuf A 24 8 (prevElem A) 4#64 q [enc]

theorem hdrP_prev1_eq (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    HdrP r 4#64 q 1#64 ∗ Prev1 A q enc = prevVecAt A r 4#64 q [enc] :=
  rfl

theorem prevVecAt_eq (A : RustAlloc) (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) :
    prevVecAt A r cap ptr ps =
      HdrP r cap ptr (BitVec.ofNat 64 ps.length) ∗ vecBuf A 24 8 (prevElem A) cap ptr ps :=
  rfl

theorem hdrP_eq (r cap ptr len : BitVec 64) :
    HdrP r cap ptr len = (r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ len) :=
  rfl

/-- Rewrites `HdrP (c + 0xe0#64)` into the three coroutine-frame cells at `+0xe0`, `+0xe8`, and
`+0xf0`. -/
theorem hdrP_coro_eq (c cap ptr len : BitVec 64) :
    HdrP (c + 0xe0#64) cap ptr len =
      ((c + 0xe0#64) ↦₆₄ cap) ∗ ((c + 0xe8#64) ↦₆₄ ptr) ∗ ((c + 0xf0#64) ↦₆₄ len) := by
  have h8 : c + 0xe0#64 + 8#64 = c + 0xe8#64 := by rw [BitVec.add_assoc]; rfl
  have h16 : c + 0xe0#64 + 16#64 = c + 0xf0#64 := by rw [BitVec.add_assoc]; rfl
  rw [hdrP_eq, h8, h16]

theorem vecBuf_prev_one_eq (A : RustAlloc) (cap q : BitVec 64) (enc : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    vecBuf A 24 8 (prevElem A) cap q [enc] =
      ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  have hc : ¬ (cap = 0) := hcap
  unfold vecBuf
  simp only [hc, ↓reduceIte, arrayAt, List.length_singleton, Nat.one_mul, sepConj_emp]
  rfl

theorem prev1_eq (A : RustAlloc) (q : BitVec 64) (enc : List (BitVec 8)) :
    Prev1 A q enc =
      ⌜1 ≤ 4 ∧ 4 * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q 96 8 ∗ vecU8 A q enc ∗ memRegion (q + 24#64) 72) := by
  unfold Prev1
  rw [vecBuf_prev_one_eq A 4#64 q enc (by decide)]
  rfl

theorem prevVecAt_one_eq (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] =
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_eq, vecBuf_prev_one_eq A cap q enc hcap]
  rfl

/-! ## `SessionRecord` with Previous Sessions -/

/-- The `current_session` field of a `SessionRecord` (`r + 0x18`, 344 bytes): niche word
`noneCap` plus 336 slack bytes when `None`, or `sessionStateReprAt` when `Some`. -/
def recCurAt (A : RustAlloc) (r : BitVec 64) (cur : Option SessionGhost)
    (rec : SessionRecord (List (BitVec 8))) : SepProp :=
  match cur, rec.currentSession with
  | none, none => ((r + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (r + 0x20#64) 336
  | some G, some s => sessionStateReprAt A (r + 0x18#64) G s
  | _, _ => ⌜False⌝

theorem recCurAt_some (A : RustAlloc) (r : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    recCurAt A r (some G) ⟨some s⟩ = sessionStateReprAt A (r + 0x18#64) G s :=
  rfl

/-- A 368-byte `SessionRecord` at `r` whose `previous_sessions` holds `ps`: `prevVecAt` at
offset 0 paired with `recCurAt` at `+0x18`. -/
def sessionRecordPrevAt (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (ps : List (List (BitVec 8))) (rec : SessionRecord (List (BitVec 8))) : SepProp :=
  prevVecAt A r g.prevCap g.prevPtr ps ∗ recCurAt A r g.cur rec

theorem sessionRecordPrevAt_eq (A : RustAlloc) (r cap ptr : BitVec 64) (cur : Option SessionGhost)
    (ps : List (List (BitVec 8))) (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordPrevAt A r ⟨cap, ptr, cur⟩ ps rec = prevVecAt A r cap ptr ps ∗ recCurAt A r cur rec :=
  rfl

theorem sessionRecordPrevAt_one_some_eq (A : RustAlloc) (r cap q : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    sessionRecordPrevAt A r ⟨cap, q, some G⟩ [enc] ⟨some s⟩ =
      (HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24))) ∗
      sessionStateReprAt A (r + 0x18#64) G s := by
  rw [sessionRecordPrevAt_eq, prevVecAt_one_eq A r cap q enc hcap, recCurAt_some]

/-! ## Session-Store Bucket with Previous Sessions -/

/-- A `RawTable<(ProtocolAddress, SessionRecord)>` bucket at `a` holding a canonical current
session `ss` (ghost `G`) and previous sessions `ps`. -/
def sessionBucketEntryPrevAt (A : RustAlloc) (g : AddrGhost) (G : SessionGhost)
    (ss : Session (List (BitVec 8))) (cap ptr : BitVec 64) (ps : List (List (BitVec 8)))
    (a : BitVec 64) : SepProp :=
  ⌜CanonSession G ss⌝ ∗
    protocolAddressAt A g a ∗
    sessionRecordPrevAt A (a + asm64% CryptoVerification.E2E.InMem.HashbrownBin.sessionBucketValueOff) ⟨cap, ptr, some G⟩ ps ⟨some ss⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
