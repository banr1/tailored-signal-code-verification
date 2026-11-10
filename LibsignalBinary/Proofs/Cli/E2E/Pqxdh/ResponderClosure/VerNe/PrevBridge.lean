/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove

/-!
# Archived Session Predicates and `previous_sessions` Bridges

Defines canonical archived-session predicates (`OverPrevEncOKAt`, `OverPrevEncOK`), separation-logic
entailments turning a decoded `prostSSGQAt` into a `SessionStructure` drop precondition
(`prevDec_dropPreA`), and `Vec<Vec<u8>>` layout helpers (`prevVecAt`, `hdrP_coro_344_entails_368`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf prostSSGQ_reprA prostSSGQ_repr)

/-! ## Archived previous-session predicates -/

/-- The archived bytes `enc` are the encoding of `sess` in `DeserializeScopeP_Q NonEmptyV1Q`,
with `session_version = 4` and no pending pre-keys. -/
def OverPrevEncOKAt (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))) : Prop :=
  enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

/-- The archived previous session `enc` is the encoding of a canonical v4 session with no pending pre-keys. -/
def OverPrevEncOK (enc : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

theorem overPrevEncOK_iff_exists_at (enc : List (BitVec 8)) :
    OverPrevEncOK enc ↔ ∃ sess, OverPrevEncOKAt enc sess :=
  Iff.rfl

/-! ## Decoded `SSGQ` to `sessionStateAt` drop precondition bridges -/

/-- The decoded previous session `prostSSGQAt A ss (ssgqOf sess)` entails `sessionStateReprAt A` with a canonical ghost. -/
theorem prevDec_sessionAtA (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateReprAt A ss G sess :=
  prostSSGQ_reprA A ⟨some sess⟩ hQ sess rfl ss

theorem prevDec_sessionAt (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateReprAt A0 ss G sess :=
  prevDec_sessionAtA A0 sess hQ ss

/-- Refines `prostSSGQAt A ss (ssgqOf sess)` to `sessionStateAt A ss G sess.state` with a canonical ghost `G`. -/
theorem prevDec_sessionStateAt_canonA (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateAt A ss G sess.state := by
  refine Entails.trans (prevDec_sessionAtA A sess hQ ss) ?_
  refine Entails.sepExists_elim fun G => Entails.sepExists_right G ?_
  refine sepConj_mono_right ?_
  dsimp only [sessionStateReprAt]
  exact Entails.pure_left fun _ => Entails.refl _

theorem prevDec_sessionStateAt_canon (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ⌜CanonSession G sess⌝ ∗ sessionStateAt A0 ss G sess.state :=
  prevDec_sessionStateAt_canonA A0 sess hQ ss

/-- With `sess.state.sessionVersion = 4#32`, the decoded previous session gives the `SessionStructure`
drop precondition at `ss` plus `st.sessionVersion = 4#32` for arbitrary `A : RustAlloc`. -/
theorem prevDec_dropPreA (A : RustAlloc) (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (hv : sess.state.sessionVersion = 4#32)
    (ss : BitVec 64) :
    prostSSGQAt A ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ∃∗ st : SessionState (List (BitVec 8)),
        ⌜st.sessionVersion = 4#32⌝ ∗ sessionStateAt A ss G st := by
  refine Entails.trans (prevDec_sessionStateAt_canonA A sess hQ ss) ?_
  refine Entails.sepExists_elim fun G => Entails.sepExists_right G ?_
  refine Entails.sepExists_right sess.state ?_
  refine Entails.pure_left fun _ => Entails.pure_right hv (Entails.refl _)

theorem prevDec_dropPre (sess : Session (List (BitVec 8)))
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩) (hv : sess.state.sessionVersion = 4#32)
    (ss : BitVec 64) :
    prostSSGQAt A0 ss (ssgqOf sess) ⊢
      ∃∗ G : SessionGhost, ∃∗ st : SessionState (List (BitVec 8)),
        ⌜st.sessionVersion = 4#32⌝ ∗ sessionStateAt A0 ss G st :=
  prevDec_dropPreA A0 sess hQ hv ss

/-! ## `previous_sessions` `Vec<Vec<u8>>` layout helpers -/

/-- One element of `previous_sessions`: an owned `Vec<u8>` header at `a` whose buffer holds `bs`. -/
abbrev prevElem (A : RustAlloc) : List (BitVec 8) → BitVec 64 → SepProp :=
  fun bs a => vecU8 A a bs

/-- The 24-byte header `{cap, ptr, len}` of `previous_sessions` at `r`. -/
abbrev HdrP (r cap ptr len : BitVec 64) : SepProp :=
  vecHeader r cap ptr len

/-- `previous_sessions` at `r` with capacity `cap`, buffer `ptr`, and encoded sessions `ps`. -/
abbrev prevVecAt (A : RustAlloc) (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (prevElem A) r cap ptr ps

theorem prevVecAt_eq (A : RustAlloc) (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) :
    prevVecAt A r cap ptr ps =
      HdrP r cap ptr (BitVec.ofNat 64 ps.length) ∗ vecBuf A 24 8 (prevElem A) cap ptr ps :=
  rfl

theorem hdrP_eq (r cap ptr len : BitVec 64) :
    HdrP r cap ptr len = (r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ len) :=
  rfl

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

theorem prevVecAt_one_eq (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] =
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_eq, vecBuf_prev_one_eq A cap q enc hcap]
  rfl

/-- Collapse the 24-byte `HdrP (c + 0xe0)` header and the 344-byte dropped `current_session`
at `c + 0xf8` into `memRegion (c + 0xe0) 368`. -/
theorem hdrP_coro_344_entails_368 (c cap ptr len : BitVec 64) :
    HdrP (c + 0xe0#64) cap ptr len ∗ memRegion (c + 0xf8#64) 344 ⊢
      memRegion (c + 0xe0#64) 368 := by
  rw [hdrP_coro_eq]
  have h368 := ProofLib.memRegion_split' (b := c + 0xe0#64) (n := 24) (k := 344)
    (b' := c + 0xf8#64) rfl (by bv_omega) (by decide)
  have h24 := ProofLib.memRegion_split' (b := c + 0xe0#64) (n := 8) (k := 16)
    (b' := c + 0xe8#64) rfl (by bv_omega) (by decide)
  have h16 := ProofLib.memRegion_split' (b := c + 0xe8#64) (n := 8) (k := 8)
    (b' := c + 0xf0#64) rfl (by bv_omega) (by decide)
  rw [h368, h24, h16]
  refine sepConj_mono ?_ (Entails.refl _)
  exact sepConj_mono (pointsTo64_entails_memRegion (c + 0xe0#64) cap)
    (sepConj_mono (pointsTo64_entails_memRegion (c + 0xe8#64) ptr)
      (pointsTo64_entails_memRegion (c + 0xf0#64) len))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
