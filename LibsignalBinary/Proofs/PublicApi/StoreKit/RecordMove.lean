/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# `SessionRecord` Inline-Byte Decomposition and 312-Byte Move Lemmas

Decomposes `sessionRecordAt A p g r` (`368` B = `24`-B `previous_sessions` header + `344`-B
`current_session`, or `56`-B leading header words + `312`-B `memcpy` tail) into inline bytes at `p`
and address-independent `recordHeap A g r`, providing word-repack and niche-bound (`< 2 ^ 63`)
lemmas for `load_session` and `store_session`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. `current_session` (344 Bytes at `p + 0x18`) Inline-Byte & Heap Decomposition -/

/-- Pure W0 invariant on `SessionGhost` and `Session` carried by `sessionStateReprAt`. -/
def SessionAtPure (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

/-- Word 0 (`+0x18` of the record) of `current_session`: `noneCap` (`-1`) when `g.cur = none`,
or `G.localIk.cap` when `g.cur = some G`. -/
def recordCurCap (g : RecordGhost) : BitVec 64 :=
  match g.cur with
  | none => noneCap
  | some G => G.localIk.cap

/-- Spatial predicate for the 344-byte `current_session` field at `ss = p + 0x18`. -/
def curSessionAt (A : RustAlloc) (ss : BitVec 64) (gcur : Option SessionGhost)
    (rcur : Option (Session (List (BitVec 8)))) : SepProp :=
  match gcur, rcur with
  | none, none => (ss ↦₆₄ noneCap) ∗ memRegion (ss + 8#64) 336
  | some G, some s => sessionStateReprAt A ss G s
  | _, _ => ⌜False⌝

/-- Position-independent pure predicate on the 344 inline bytes `bs` of `curSessionAt A ss gcur rcur`. -/
def CurSessionInline : Option SessionGhost → Option (Session (List (BitVec 8))) → List (BitVec 8) → Prop
  | none, none, bs =>
    ∃ pad : List (BitVec 8), pad.length = 336 ∧ bs = unpack64 noneCap ++ pad
  | some G, some s, bs =>
    SessionInline G s.state bs
  | _, _, _ => False

/-- Position-independent detached heap of `curSessionAt A ss gcur rcur`. Does not mention `ss`. -/
def curSessionHeap (A : RustAlloc) :
    Option SessionGhost → Option (Session (List (BitVec 8))) → SepProp
  | none, none => emp
  | some G, some s => ⌜SessionAtPure G s⌝ ∗ sessionHeap A G s.state
  | _, _ => ⌜False⌝

theorem CurSessionInline.length_eq {gcur : Option SessionGhost}
    {rcur : Option (Session (List (BitVec 8)))} {bs : List (BitVec 8)}
    (h : CurSessionInline gcur rcur bs) : bs.length = 344 := by
  cases gcur with
  | none =>
    cases rcur with
    | none =>
      rcases h with ⟨pad, hpad, rfl⟩
      simp [hpad]
    | some _ => exact False.elim h
  | some G =>
    cases rcur with
    | none => exact False.elim h
    | some s => exact SessionInline.length_eq h

/-- `curSessionAt A ss gcur rcur` decomposes into 344 inline bytes `ss ↦ₛ bs` and
address-independent `curSessionHeap A gcur rcur`. -/
theorem curSessionAt_eq_inline_sep_heap (A : RustAlloc) (ss : BitVec 64)
    (gcur : Option SessionGhost) (rcur : Option (Session (List (BitVec 8)))) :
    curSessionAt A ss gcur rcur =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 344 ∧ CurSessionInline gcur rcur bs⌝ ∗
          (ss ↦ₛ bs) ∗ curSessionHeap A gcur rcur := by
  cases gcur with
  | none =>
    cases rcur with
    | none =>
      dsimp only [curSessionAt, curSessionHeap]
      rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (ss + 8#64) 336 (by decide),
          sepExists_sepConj_right]
      apply RawByteMove.sepProp_eq_of_entails
      · apply Entails.sepExists_elim; intro pad
        rw [sepConj_pure_left_comm]
        apply Entails.pure_left; intro hpad
        have h8 : ss + 8#64 = ss + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
        rw [h8, ← pointsToBytes_append]
        have hinl : CurSessionInline none none (unpack64 noneCap ++ pad) := ⟨pad, hpad, rfl⟩
        refine Entails.sepExists_right (unpack64 noneCap ++ pad) ?_
        rw [sepConj_emp]
        exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
      · apply Entails.sepExists_elim; intro bs
        rw [sepConj_emp]
        apply Entails.pure_left; rintro ⟨_, pad, hpad, rfl⟩
        rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
        refine Entails.sepExists_right pad ?_
        apply sepConj_mono_right
        exact Entails.pure_right hpad (Entails.refl _)
    | some s =>
      dsimp only [curSessionAt, curSessionHeap, CurSessionInline]
      apply RawByteMove.sepProp_eq_of_entails
      · apply Entails.pure_left_only; intro h; exact False.elim h
      · apply Entails.sepExists_elim; intro bs
        apply Entails.pure_left; rintro ⟨_, h⟩; exact False.elim h
  | some G =>
    cases rcur with
    | none =>
      dsimp only [curSessionAt, curSessionHeap, CurSessionInline]
      apply RawByteMove.sepProp_eq_of_entails
      · apply Entails.pure_left_only; intro h; exact False.elim h
      · apply Entails.sepExists_elim; intro bs
        apply Entails.pure_left; rintro ⟨_, h⟩; exact False.elim h
    | some s =>
      dsimp only [curSessionAt, curSessionHeap, CurSessionInline, sessionStateReprAt, SessionAtPure]
      rw [sessionStateAt_eq_inline_sep_heap A ss G s.state, sepExists_sepConj_right]
      apply RawByteMove.sepExists_congr; intro bs
      ac_rfl

/-- Reassemble `curSessionAt A dst gcur rcur` from `(dst ↦ₛ bs) ∗ curSessionHeap A gcur rcur`. -/
theorem curSessionAt_of_bytes (A : RustAlloc) (dst : BitVec 64)
    (gcur : Option SessionGhost) (rcur : Option (Session (List (BitVec 8))))
    {bs : List (BitVec 8)} (h : CurSessionInline gcur rcur bs) :
    ((dst ↦ₛ bs) ∗ curSessionHeap A gcur rcur) ⊢ curSessionAt A dst gcur rcur := by
  rw [curSessionAt_eq_inline_sep_heap A dst gcur rcur]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

/-! ## 2. `sessionRecordAt` (368 Bytes = 24 B Header + 344 B `current_session`) Decomposition & Moves -/

/-- Position-independent pure predicate on the 368 inline bytes `bs` of `sessionRecordAt A p g r`:
the 24-byte `previous_sessions` `Vec` header `{g.prevCap, g.prevPtr, 0}` followed by 344 bytes
satisfying `CurSessionInline g.cur r.currentSession`. -/
def RecordInline (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (bs : List (BitVec 8)) : Prop :=
  ∃ curBs : List (BitVec 8),
    curBs.length = 344 ∧
    CurSessionInline g.cur r.currentSession curBs ∧
    bs = vecHeaderBytes g.prevCap g.prevPtr 0#64 ++ curBs

/-- Position-independent detached heap of `sessionRecordAt A p g r`. Does not mention `p`. -/
def recordHeap (A : RustAlloc) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    SepProp :=
  vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗
    curSessionHeap A g.cur r.currentSession

theorem RecordInline.length_eq {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {bs : List (BitVec 8)} (h : RecordInline g r bs) : bs.length = 368 := by
  rcases h with ⟨curBs, hlen, _, rfl⟩
  simp [vecHeaderBytes, hlen]

/-- `sessionRecordAt` written in terms of `curSessionAt` at `p + 0x18`. -/
theorem sessionRecordAt_eq_vecAt_sep_curSessionAt (A : RustAlloc) (p : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A p g r =
      vecAt A 24 8 (fun (_ : Unit) _ => emp) p g.prevCap g.prevPtr [] ∗
        curSessionAt A (p + 0x18#64) g.cur r.currentSession := by
  unfold sessionRecordAt curSessionAt
  have h20 : p + 0x18#64 + 8#64 = p + 0x20#64 := by bv_arith
  rw [h20]
  cases g.cur <;> cases r.currentSession <;> rfl

/-- `sessionRecordAt` 368-byte inline + heap decomposition:
`sessionRecordAt A p g r = ∃∗ bs, ⌜bs.length = 368 ∧ RecordInline g r bs⌝ ∗ (p ↦ₛ bs) ∗ recordHeap A g r`. -/
theorem sessionRecordAt_eq_inline_sep_heap (A : RustAlloc) (p : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A p g r =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 368 ∧ RecordInline g r bs⌝ ∗ (p ↦ₛ bs) ∗ recordHeap A g r := by
  rw [sessionRecordAt_eq_vecAt_sep_curSessionAt,
      vecAt_eq_bytes_sep_buf A 24 8 (fun (_ : Unit) _ => emp) p g.prevCap g.prevPtr [],
      curSessionAt_eq_inline_sep_heap A (p + 0x18#64) g.cur r.currentSession,
      sepConj_assoc]
  change ((p ↦ₛ vecHeaderBytes g.prevCap g.prevPtr 0#64) ∗
    vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗ _) = _
  apply RawByteMove.sepProp_eq_of_entails
  · simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro curBs
    have hpull :
        ((p ↦ₛ vecHeaderBytes g.prevCap g.prevPtr 0#64) ∗
          vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗
          (⌜curBs.length = 344 ∧ CurSessionInline g.cur r.currentSession curBs⌝ ∗
            ((p + 0x18#64) ↦ₛ curBs) ∗ curSessionHeap A g.cur r.currentSession)) =
        (⌜curBs.length = 344 ∧ CurSessionInline g.cur r.currentSession curBs⌝ ∗
          ((p ↦ₛ vecHeaderBytes g.prevCap g.prevPtr 0#64) ∗ ((p + 0x18#64) ↦ₛ curBs)) ∗
          recordHeap A g r) := by
      unfold recordHeap
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro ⟨hcur_len, hcur_inl⟩
    have h18 : p + 0x18#64 = p + BitVec.ofNat 64 (vecHeaderBytes g.prevCap g.prevPtr 0#64).length := by
      simp [vecHeaderBytes]
    rw [h18, ← pointsToBytes_append]
    set bs := vecHeaderBytes g.prevCap g.prevPtr 0#64 ++ curBs
    have hinl : RecordInline g r bs := ⟨curBs, hcur_len, hcur_inl, rfl⟩
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, curBs, hcur_len, hcur_inl, rfl⟩
    rw [pointsToBytes_append, vecHeaderBytes_length]
    have h18 : p + BitVec.ofNat 64 24 = p + 0x18#64 := rfl
    rw [h18]
    have hpull :
        (((p ↦ₛ vecHeaderBytes g.prevCap g.prevPtr 0#64) ∗ ((p + 0x18#64) ↦ₛ curBs)) ∗
          recordHeap A g r) =
        ((p ↦ₛ vecHeaderBytes g.prevCap g.prevPtr 0#64) ∗
          vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗
          (((p + 0x18#64) ↦ₛ curBs) ∗ curSessionHeap A g.cur r.currentSession)) := by
      unfold recordHeap
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    apply sepConj_mono_right
    refine Entails.sepExists_right curBs ?_
    exact Entails.pure_right ⟨hcur_len, hcur_inl⟩ (Entails.refl _)

/-- Entailment direction of `sessionRecordAt_eq_inline_sep_heap`. -/
theorem sessionRecordAt_entails_inline_sep_heap (A : RustAlloc) (p : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A p g r ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 368 ∧ RecordInline g r bs⌝ ∗ (p ↦ₛ bs) ∗ recordHeap A g r :=
  Entails.of_eq (sessionRecordAt_eq_inline_sep_heap A p g r)

/-- Reassemble `sessionRecordAt A dst g r` from `(dst ↦ₛ bs) ∗ recordHeap A g r`
given `RecordInline g r bs`. -/
theorem sessionRecordAt_of_bytes (A : RustAlloc) (dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : RecordInline g r bs) :
    ((dst ↦ₛ bs) ∗ recordHeap A g r) ⊢ sessionRecordAt A dst g r := by
  rw [sessionRecordAt_eq_inline_sep_heap A dst g r]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

/-- Forgetting the 368 inline bytes of `sessionRecordAt` yields
`memRegion p 368 ∗ recordHeap A g r`. -/
theorem sessionRecordAt_entails_memRegion_sep_heap (A : RustAlloc) (p : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A p g r ⊢ memRegion p 368 ∗ recordHeap A g r := by
  rw [sessionRecordAt_eq_inline_sep_heap A p g r]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  apply sepConj_mono_left
  have h := pointsToBytes_entails_memRegion p bs
  rwa [hlen] at h

/-- Move `sessionRecordAt` from `src` to `dst` given `RecordInline g r bs`, leaving `src ↦ₛ bs`. -/
theorem sessionRecordAt_move_bytes (A : RustAlloc) (src dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : RecordInline g r bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ recordHeap A g r) ⊢
      sessionRecordAt A dst g r ∗ (src ↦ₛ bs) := by
  have hpull :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ recordHeap A g r) =
      (((dst ↦ₛ bs) ∗ recordHeap A g r) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_left (sessionRecordAt_of_bytes A dst g r h)

/-- Move `sessionRecordAt` from `src` to `dst` after copying `bs`, collapsing `src ↦ₛ bs` to
`memRegion src 368`. -/
theorem sessionRecordAt_move_to_memRegion (A : RustAlloc) (src dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : RecordInline g r bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ recordHeap A g r) ⊢
      sessionRecordAt A dst g r ∗ memRegion src 368 := by
  refine Entails.trans (sessionRecordAt_move_bytes A src dst g r h) ?_
  apply sepConj_mono_right
  have hregion := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hregion

/-- Two-hop move of `sessionRecordAt` (`src → mid → dst`): reassembles `sessionRecordAt A dst g r`
and collapses both `mid` and `src` to 368-byte `memRegion`s. -/
theorem sessionRecordAt_move_bytes_twice (A : RustAlloc) (src mid dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : RecordInline g r bs) :
    ((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ recordHeap A g r) ⊢
      sessionRecordAt A dst g r ∗ memRegion mid 368 ∗ memRegion src 368 := by
  have hpull :
      ((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ recordHeap A g r) =
      (((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ recordHeap A g r) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  refine Entails.trans (sepConj_mono (sessionRecordAt_move_to_memRegion A mid dst g r h) ?_)
    (Entails.of_eq (sepConj_assoc _ _ _))
  have hsrc := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hsrc

/-! ## 3. Splitting `sessionRecordAt` into 56-B Header Words (`24 + 8 + 24`) + 312-B `memcpy` Tail -/

/-- Any `curBs` satisfying `CurSessionInline g.cur r.currentSession curBs` splits into
`unpack64 (recordCurCap g)` (8 B), three 64-bit words `w4, w5, w6` (24 B), and a 312-byte tail `tail`. -/
theorem CurSessionInline.exists_split_8_24_312 {g : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} {curBs : List (BitVec 8)}
    (h : CurSessionInline g.cur r.currentSession curBs) :
    ∃ (w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)),
      tail.length = 312 ∧
      curBs = unpack64 (recordCurCap g) ++ unpack64 w4 ++ unpack64 w5 ++ unpack64 w6 ++ tail := by
  have hlen : curBs.length = 344 := h.length_eq
  have htake8 : curBs.take 8 = unpack64 (recordCurCap g) := by
    cases hcurG : g.cur with
    | none =>
      cases hcurR : r.currentSession with
      | none =>
        rw [hcurG, hcurR] at h
        rcases h with ⟨pad, _, rfl⟩
        unfold recordCurCap
        rw [hcurG]
        exact List.take_left' (unpack64_length noneCap)
      | some _ =>
        rw [hcurG, hcurR] at h
        exact False.elim h
    | some G =>
      cases hcurR : r.currentSession with
      | none =>
        rw [hcurG, hcurR] at h
        exact False.elim h
      | some s =>
        rw [hcurG, hcurR] at h
        rcases h with ⟨_, scBs, pendBs, kybBs, _, _, _, _, _, _, rfl⟩
        unfold recordCurCap
        rw [hcurG]
        dsimp only [sessionPrefixBytes, vecGhostHeaderBytes, vecHeaderBytes]
        simp only [List.append_assoc]
        exact List.take_left' (unpack64_length G.localIk.cap)
  have hw4 : ((curBs.drop 8).take 8).length = 8 := by simp [hlen]
  have hw5 : ((curBs.drop 16).take 8).length = 8 := by simp [hlen]
  have hw6 : ((curBs.drop 24).take 8).length = 8 := by simp [hlen]
  have htail : (curBs.drop 32).length = 312 := by simp [hlen]
  obtain ⟨w4, hw4_eq⟩ := exists_unpack64_of_length_8 hw4
  obtain ⟨w5, hw5_eq⟩ := exists_unpack64_of_length_8 hw5
  obtain ⟨w6, hw6_eq⟩ := exists_unpack64_of_length_8 hw6
  refine ⟨w4, w5, w6, curBs.drop 32, htail, ?_⟩
  rw [← htake8, ← hw4_eq, ← hw5_eq, ← hw6_eq]
  simp only [List.append_assoc]
  have s3 : (curBs.drop 24).take 8 ++ curBs.drop 32 = curBs.drop 24 := by
    have := List.take_append_drop 8 (curBs.drop 24)
    rwa [List.drop_drop] at this
  have s2 : (curBs.drop 16).take 8 ++ curBs.drop 24 = curBs.drop 16 := by
    have := List.take_append_drop 8 (curBs.drop 16)
    rwa [List.drop_drop] at this
  have s1 : (curBs.drop 8).take 8 ++ curBs.drop 16 = curBs.drop 8 := by
    have := List.take_append_drop 8 (curBs.drop 8)
    rwa [List.drop_drop] at this
  rw [s3, s2, s1, List.take_append_drop]

/-- The 56-byte leading header of a `SessionRecord` at `p` as 7 64-bit words (`+0x00..+0x38`). -/
def recordWords56At (p w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : SepProp :=
  (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
    ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
    ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6)

/-- Byte list of 7 64-bit words (56 bytes). -/
def bytes56Of7W (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) : List (BitVec 8) :=
  unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++
    unpack64 w4 ++ unpack64 w5 ++ unpack64 w6

@[scoped simp]
theorem bytes56Of7W_length (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (bytes56Of7W w0 w1 w2 w3 w4 w5 w6).length = 56 := by
  simp [bytes56Of7W]

theorem recordWords56At_eq_pointsToBytes (p w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    recordWords56At p w0 w1 w2 w3 w4 w5 w6 =
      (p ↦ₛ bytes56Of7W w0 w1 w2 w3 w4 w5 w6) := by
  unfold recordWords56At bytes56Of7W
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes]
  have h08 : p + BitVec.ofNat 64 8 = p + 8#64 := rfl
  have h10 : p + 8#64 + BitVec.ofNat 64 8 = p + 0x10#64 := by bv_arith
  have h18 : p + 0x10#64 + BitVec.ofNat 64 8 = p + 0x18#64 := by bv_arith
  have h20 : p + 0x18#64 + BitVec.ofNat 64 8 = p + 0x20#64 := by bv_arith
  have h28 : p + 0x20#64 + BitVec.ofNat 64 8 = p + 0x28#64 := by bv_arith
  have h30 : p + 0x28#64 + BitVec.ofNat 64 8 = p + 0x30#64 := by bv_arith
  rw [h08, h10, h18, h20, h28, h30]

theorem recordWords56At_entails_memRegion (p w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    recordWords56At p w0 w1 w2 w3 w4 w5 w6 ⊢ memRegion p 56 := by
  rw [recordWords56At_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion p (bytes56Of7W w0 w1 w2 w3 w4 w5 w6)
  rwa [bytes56Of7W_length] at h

/-- Pure inline relation for the `56 + 312` decomposition of `sessionRecordAt`:
words `w4, w5, w6` at `+0x20..+0x38` and 312-byte `tail` at `+0x38..+0x170`. -/
def RecordTailInline (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) : Prop :=
  tail.length = 312 ∧
    CurSessionInline g.cur r.currentSession
      (unpack64 (recordCurCap g) ++ unpack64 w4 ++ unpack64 w5 ++ unpack64 w6 ++ tail)

theorem RecordTailInline.toRecordInline {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (h : RecordTailInline g r w4 w5 w6 tail) :
    RecordInline g r (bytes56Of7W g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ++ tail) := by
  rcases h with ⟨_, hcur⟩
  refine ⟨unpack64 (recordCurCap g) ++ unpack64 w4 ++ unpack64 w5 ++ unpack64 w6 ++ tail,
    hcur.length_eq, hcur, ?_⟩
  simp [bytes56Of7W, vecHeaderBytes, List.append_assoc]

/-- `sessionRecordAt` 56-B words + 312-B tail decomposition:
Exposes the 7 leading 64-bit words (`g.prevCap`, `g.prevPtr`, `0#64`, `recordCurCap g`, `w4`, `w5`, `w6`),
the 312-byte slice `(p + 0x38#64) ↦ₛ tail` (copied by `memcpy`), and `recordHeap A g r`. -/
theorem sessionRecordAt_eq_words56_sep_tail (A : RustAlloc) (p : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A p g r =
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜RecordTailInline g r w4 w5 w6 tail⌝ ∗
          recordWords56At p g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
          ((p + 0x38#64) ↦ₛ tail) ∗ recordHeap A g r := by
  rw [sessionRecordAt_eq_inline_sep_heap A p g r]
  apply RawByteMove.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, curBs, _, hcur, rfl⟩
    obtain ⟨w4, w5, w6, tail, htail, hcur_eq⟩ := hcur.exists_split_8_24_312
    have hbs : vecHeaderBytes g.prevCap g.prevPtr 0#64 ++ curBs =
        bytes56Of7W g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ++ tail := by
      rw [hcur_eq]
      simp [vecHeaderBytes, bytes56Of7W, List.append_assoc]
    rw [hbs, pointsToBytes_append, bytes56Of7W_length, ← recordWords56At_eq_pointsToBytes]
    have h38 : p + BitVec.ofNat 64 56 = p + 0x38#64 := rfl
    rw [h38]
    rw [hcur_eq] at hcur
    refine Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)))
    rw [← sepConj_assoc (recordWords56At _ _ _ _ _ _ _ _)]
    exact Entails.pure_right ⟨htail, hcur⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail_inl
    have hinl := htail_inl.toRecordInline
    have h38 : p + 0x38#64 =
        p + BitVec.ofNat 64 (bytes56Of7W g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6).length := by
      simp [bytes56Of7W]
    rw [recordWords56At_eq_pointsToBytes, ← sepConj_assoc (p ↦ₛ _), h38, ← pointsToBytes_append]
    refine Entails.sepExists_right
      (bytes56Of7W g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ++ tail) ?_
    exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)

/-- Reassemble `sessionRecordAt A dst g r` from `recordWords56At dst`, `(dst + 0x38#64) ↦ₛ tail`,
and `recordHeap A g r`. -/
theorem sessionRecordAt_of_words56_sep_tail (A : RustAlloc) (dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (h : RecordTailInline g r w4 w5 w6 tail) :
    (recordWords56At dst g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
      ((dst + 0x38#64) ↦ₛ tail) ∗ recordHeap A g r) ⊢
      sessionRecordAt A dst g r := by
  rw [sessionRecordAt_eq_words56_sep_tail A dst g r]
  refine Entails.sepExists_right w4 (Entails.sepExists_right w5
    (Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)))
  exact Entails.pure_right h (Entails.refl _)

/-- Move `sessionRecordAt` from `src` to `dst` via the 7 leading words and a two-hop 312-B `memcpy`
(`src + 0x38 → mid → dst + 0x38`, as in `loadSessionPoll_okS`), collapsing `src` to `memRegion src 368`
and `mid` to `memRegion mid 312`. -/
theorem sessionRecordAt_move_words56_twice (A : RustAlloc) (src mid dst : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (h : RecordTailInline g r w4 w5 w6 tail) :
    (recordWords56At dst g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
      ((dst + 0x38#64) ↦ₛ tail) ∗
      recordWords56At src g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
      ((src + 0x38#64) ↦ₛ tail) ∗
      (mid ↦ₛ tail) ∗ recordHeap A g r) ⊢
      sessionRecordAt A dst g r ∗ memRegion src 368 ∗ memRegion mid 312 := by
  have hpull :
      (recordWords56At dst g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((dst + 0x38#64) ↦ₛ tail) ∗
        recordWords56At src g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((src + 0x38#64) ↦ₛ tail) ∗
        (mid ↦ₛ tail) ∗ recordHeap A g r) =
      ((recordWords56At dst g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
          ((dst + 0x38#64) ↦ₛ tail) ∗ recordHeap A g r) ∗
        (recordWords56At src g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
          ((src + 0x38#64) ↦ₛ tail)) ∗
        (mid ↦ₛ tail)) := by
    ac_rfl
  rw [hpull]
  refine sepConj_mono (sessionRecordAt_of_words56_sep_tail A dst g r h) ?_
  refine sepConj_mono ?_ ?_
  · rw [memRegion_split src 56 312 (by decide)]
    have h38 : src + BitVec.ofNat 64 56 = src + 0x38#64 := rfl
    rw [h38]
    refine sepConj_mono (recordWords56At_entails_memRegion _ _ _ _ _ _ _ _) ?_
    have hsrc_tail := pointsToBytes_entails_memRegion (src + 0x38#64) tail
    rwa [h.1] at hsrc_tail
  · have hmid := pointsToBytes_entails_memRegion mid tail
    rwa [h.1] at hmid

/-! ## 4. Unaligned Repack of Words `2..6` (`+0x10..+0x38`) for MessageDecrypt `segDispatch` and MessageEncrypt `segLoad` -/

/-- Repack 5 consecutive 64-bit words at `p + 0x10 .. p + 0x38` into:
`↦₃₂` at `+0x10`, two `↦₁₂₈` quadwords at `+0x14` and `+0x24`, and `↦₃₂` at `+0x34`
(matching `session_message_decrypt_signal_with_stores+0x0dc..+0x1a4` in `segDispatch_ok`). -/
theorem words5_repack_w32_2q128_w32 (p w2 w3 w4 w5 w6 : BitVec 64) :
    ((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
        ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6) =
      ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((p + 0x14#64) ↦₁₂₈
          ((w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32) ++
            (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32))) ∗
        ((p + 0x24#64) ↦₁₂₈
          ((w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32) ++
            (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32))) ∗
        ((p + 0x34#64) ↦₃₂ w6.extractLsb' 32 32) := by
  rw [← pointsTo64_pair (p + 0x14#64), ← pointsTo64_pair (p + 0x24#64),
      ← pointsTo32_pair (p + 0x14#64), ← pointsTo32_pair (p + 0x14#64 + 8#64),
      ← pointsTo32_pair (p + 0x24#64), ← pointsTo32_pair (p + 0x24#64 + 8#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Repack 3 consecutive 64-bit words at `p + 0x20 .. p + 0x38` into one `↦₁₂₈` quadword at `+0x20`
and one `↦₆₄` word at `+0x30` (matching `session_message_encrypt_with_stores+0x104..+0x1b4` in MessageEncrypt `segLoad_ok`). -/
theorem words3_repack_q128_w64 (p w4 w5 w6 : BitVec 64) :
    ((p + 0x20#64) ↦₆₄ w4) ∗ ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6) =
      ((p + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗ ((p + 0x30#64) ↦₆₄ w6) := by
  have h28 : p + 0x20#64 + 8#64 = p + 0x28#64 := by bv_arith
  rw [← sepConj_assoc, ← h28, pointsTo64_pair]

/-! ## 5. Capacity Niche Bounds (`prevCap` and `recordCurCap`) -/

/-- From `vecBuf A stride align elem cap ptr xs`, `cap.toNat < 2 ^ 63`, so `cap`
cannot equal any negative niche word (`-1`, `-2`, `-3`). -/
theorem vecBuf_cap_lt_two_pow_63 {α : Type} {A : RustAlloc} {stride align : Nat}
    {elem : α → BitVec 64 → SepProp} {cap ptr : BitVec 64} {xs : List α}
    (hstride : 0 < stride) :
    vecBuf A stride align elem cap ptr xs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecBuf A stride align elem cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hcap_lt : cap.toNat < 2 ^ 63 := by
    have hmul : cap.toNat * 1 ≤ cap.toNat * stride := Nat.mul_le_mul_left _ hstride
    omega
  exact Entails.pure_right hcap_lt (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

theorem ne_neg_tags_of_lt_two_pow_63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap ≠ 0xFFFFFFFFFFFFFFFF#64 ∧ cap ≠ 0xFFFFFFFFFFFFFFFE#64 ∧ cap ≠ 0xFFFFFFFFFFFFFFFD#64 := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro heq; subst heq; revert h; decide)

/-- `recordHeap A g r` entails that `g.prevCap.toNat < 2 ^ 63` (hence `g.prevCap` is never
`-1` (`Ok(None)`), `-2` (`Err`), or `-3` (`Pending`)). -/
theorem recordHeap_prevCap_lt_two_pow_63 (A : RustAlloc) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8))) :
    recordHeap A g r ⊢ ⌜g.prevCap.toNat < 2 ^ 63⌝ ∗ recordHeap A g r := by
  unfold recordHeap
  rw [← sepConj_assoc]
  exact sepConj_mono_left (vecBuf_cap_lt_two_pow_63 (by decide))

/-- When `g.cur = some G` and `r.currentSession = some s`, `recordHeap A g r` entails that
`recordCurCap g = G.localIk.cap` satisfies `(recordCurCap g).toNat < 2 ^ 63` (hence
`recordCurCap g ≠ noneCap`). -/
theorem recordHeap_curCap_lt_two_pow_63_of_some (A : RustAlloc) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8))) (G : SessionGhost) (s : Session (List (BitVec 8)))
    (hg : g.cur = some G) (hr : r.currentSession = some s) :
    recordHeap A g r ⊢ ⌜(recordCurCap g).toNat < 2 ^ 63⌝ ∗ recordHeap A g r := by
  unfold recordHeap curSessionHeap recordCurCap
  rw [hg, hr]
  dsimp only
  unfold sessionHeap
  have hpull :
      (vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗
        ⌜SessionAtPure G s⌝ ∗
        (⌜SessionPure G s.state⌝ ∗
          vecGhostHeap A G.localIk ∗
          vecGhostHeap A G.remoteIk ∗
          vecU8Buf A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ∗
          vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
            (G.chains.zip s.state.receiverChains) ∗
          vecGhostHeap A G.alice ∗
          vecU8Buf A G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
          optSenderChainHeap A G.sender s.state.senderChain ∗
          optTailVecHeap A G.pending ∗
          optTailVecHeap A G.kyber)) =
      (vecGhostHeap A G.localIk ∗
        (vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr [] ∗
          ⌜SessionAtPure G s⌝ ∗
          ⌜SessionPure G s.state⌝ ∗
          vecGhostHeap A G.remoteIk ∗
          vecU8Buf A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ∗
          vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
            (G.chains.zip s.state.receiverChains) ∗
          vecGhostHeap A G.alice ∗
          vecU8Buf A G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
          optSenderChainHeap A G.sender s.state.senderChain ∗
          optTailVecHeap A G.pending ∗
          optTailVecHeap A G.kyber)) := by
    ac_rfl
  rw [hpull]
  have hlocal :
      vecGhostHeap A G.localIk ⊢ ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ vecGhostHeap A G.localIk := by
    unfold vecGhostHeap vecU8Buf
    apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
    exact Entails.pure_right hlt (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hlocal) ?_
  rw [sepConj_assoc, ← hpull]
  exact Entails.refl _

/-! ## 6. Relocatable `[LibsignalPlacement]` Proofs -/

/-- Placed `loadPollPlacedOutAtS` coincides with `loadPollOutAtS` at any base `b` on `.ok`. -/
theorem loadPollPlacedOutAtS_ok_eq [LibsignalPlacement]
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b out : BitVec 64) (o : Option (SessionRecord (List (BitVec 8)))) :
    loadPollPlacedOutAtS Scope A out (.ok o) = loadPollOutAtS Scope A b out (.ok o) := by
  cases o <;> rfl

/-- Placed `storePollPlacedOutAt` coincides with `storePollOutAt` at any base `b` on `.ok`. -/
theorem storePollPlacedOutAt_ok_eq [LibsignalPlacement] (b out : BitVec 64) (u : Unit) :
    storePollPlacedOutAt out (.ok u) = storePollOutAt b out (.ok u) := by
  cases u; rfl

/-- Placed `trustPollPlacedOutAt` coincides with `trustPollOutAt` at any base `b` on `.ok`. -/
theorem trustPollPlacedOutAt_ok_eq [LibsignalPlacement] (b out : BitVec 64) (t : Bool) :
    trustPollPlacedOutAt out (.ok t) = trustPollOutAt b out (.ok t) := rfl

/-- Placed `savePollPlacedOutAt` coincides with `savePollOutAt` at any base `b` on `.ok`. -/
theorem savePollPlacedOutAt_ok_eq [LibsignalPlacement] (b out : BitVec 64) (c : IdentityChange) :
    savePollPlacedOutAt out (.ok c) = savePollOutAt b out (.ok c) := rfl

/-- Placed `loadPollPlacedOutAtS` `.ok (some r)` decomposes into `recordWords56At`, 312-B tail bytes,
and `recordHeap` with the `prevCap < 2^63` niche bound exposed. -/
theorem loadPollPlacedOutAtS_some_words56 [LibsignalPlacement]
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (out : BitVec 64)
    (r : SessionRecord (List (BitVec 8))) :
    loadPollPlacedOutAtS Scope A out (.ok (some r)) ⊢
      ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜g.prevCap.toNat < 2 ^ 63 ∧ RecordTailInline g r w4 w5 w6 tail⌝ ∗
        recordWords56At out g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        (out + 0x38#64) ↦ₛ tail ∗
        recordHeap A g r := by
  dsimp only [loadPollPlacedOutAtS]
  apply sepConj_mono_right
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [sessionRecordAt_eq_words56_sep_tail A out g r]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro tail
  refine Entails.sepExists_right w4 ?_
  refine Entails.sepExists_right w5 ?_
  refine Entails.sepExists_right w6 ?_
  refine Entails.sepExists_right tail ?_
  apply Entails.pure_left; intro htail
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (recordHeap_prevCap_lt_two_pow_63 A g r))) ?_
  have hcomm :
      recordWords56At out g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((out + 0x38#64) ↦ₛ tail ∗ (⌜g.prevCap.toNat < 2 ^ 63⌝ ∗ recordHeap A g r)) =
      ⌜g.prevCap.toNat < 2 ^ 63⌝ ∗
        (recordWords56At out g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
          (out + 0x38#64) ↦ₛ tail ∗ recordHeap A g r) := by ac_rfl
  rw [hcomm]
  apply Entails.pure_left; intro hlt
  exact Entails.pure_right ⟨hlt, htail⟩ (Entails.refl _)

end CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
