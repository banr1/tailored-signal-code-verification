/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Callee stack budget inside `SessionRecord::serialize` below its 800-byte frame. -/
abbrev serializeSubStack : Nat :=
  64 + sessionCloneStack + vecVecCloneStack + sessionLenStack + allocHookStack +
    Prost.encodeVarintStack + encodeRawStack + doReserveStack +
    FromRecordCallees.dropSessionStructureLocal1Stack

theorem serializeStack_eq : serializeStack = serializeSubStack + 800 := by
  decide

theorem stackAt_serializeSub_split (fp : BitVec 64) (S : Nat) (hS : S ≤ serializeSubStack) :
    stackAt fp serializeSubStack =
      memRegion (fp - BitVec.ofNat 64 serializeSubStack) (serializeSubStack - S) ∗
      stackAt fp S := by
  have hval : serializeSubStack < 2 ^ 32 := by decide
  have h := stackAt_split_bottom fp S (serializeSubStack - S) (by omega)
  have hsum : S + (serializeSubStack - S) = serializeSubStack := Nat.add_sub_of_le hS
  rwa [hsum] at h

/-- Weakens a `subroutine_ok` contract by threading an `s0`-dependent frame `F x s0`. -/
theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {entry : BitVec 64}
    {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem allocPanic_frame_entails {α : Type} (x : α) (s0 sf : State) (F : SepProp) :
    allocPanic x s0 sf ∗ F ⊢ allocPanic x s0 sf := by
  unfold allocPanic
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem memRegion_out32 (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ out3 : BitVec 64, ∃∗ out12 : BitVec 128, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₁₂₈ out12) ∗ ((out + 24#64) ↦₆₄ out3)) := by
  rw [memRegion_split out 8 24 (by decide),
    memRegion_split (out + 8#64) 16 8 (by decide),
    ProofLib.memRegion_eight out,
    memRegion_16_eq_exists_pointsTo128 (out + 8#64),
    ProofLib.memRegion_eight (out + 8#64 + 16#64)]
  have h24 : out + 8#64 + 16#64 = out + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [h24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem pointsTo64_pair_sub (sp : BitVec 64) (a : Nat) (lo hi : BitVec 64)
    (ha : 8 < a := by decide) (hbound : a < 2 ^ 64 := by decide) :
    ((sp - BitVec.ofNat 64 a) ↦₆₄ lo) ∗ ((sp - BitVec.ofNat 64 (a - 8)) ↦₆₄ hi) =
      ((sp - BitVec.ofNat 64 a) ↦₁₂₈ (hi ++ lo)) := by
  have h := pointsTo64_pair (sp - BitVec.ofNat 64 a) lo hi
  rwa [bv_sub_add_lit sp a 8 ha hbound] at h

theorem pointsTo64_pair_out (out lo hi : BitVec 64) :
    ((out + 8#64) ↦₁₂₈ (hi ++ lo)) =
      ((out + 8#64) ↦₆₄ lo) ∗ ((out + 16#64) ↦₆₄ hi) := by
  have h := (pointsTo64_pair (out + 8#64) lo hi).symm
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by rw [BitVec.add_assoc]; rfl
  rwa [h16] at h

theorem vecHeader_zero_entails_memRegion24 (a p : BitVec 64) :
    vecHeader a 0#64 p 0#64 ⊢ memRegion a 24 := by
  unfold vecHeader
  rw [memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16]
  exact sepConj_mono (Entails.sepExists_intro 0#64)
    (sepConj_mono (Entails.sepExists_intro p) (Entails.sepExists_intro 0#64))

/-! ## Stack frame split for `serializeStack` -/

theorem stackAt_serialize_base (sp : BitVec 64) :
    stackAt sp serializeStack =
      stackAt (sp - 800#64) serializeSubStack ∗
      memRegion (sp - 800#64) 368 ∗
      memRegion (sp - 432#64) 336 ∗
      cells (sp - 96#64) 12 := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp (serializeSubStack + 704) 12 (by decide)
  change stackAt sp serializeStack =
    stackAt (sp - 96#64) (serializeSubStack + 704) ∗ cells (sp - 96#64) 12 at h1
  have h2 : stackAt (sp - 96#64) (serializeSubStack + 704) =
      memRegion (sp - 800#64) 704 ∗ stackAt (sp - 800#64) serializeSubStack := by
    simp only [stackAt]
    have hsplit := memRegion_split (sp - 96#64 - BitVec.ofNat 64 (serializeSubStack + 704))
      serializeSubStack 704 (by decide)
    have e1 : sp - 96#64 - BitVec.ofNat 64 (serializeSubStack + 704) =
        sp - 800#64 - BitVec.ofNat 64 serializeSubStack := by
      rw [BitVec.sub_sub, BitVec.ofNat_add, ← BitVec.add_assoc,
        show (96#64 + BitVec.ofNat 64 serializeSubStack + 704#64 : BitVec 64) =
          800#64 + BitVec.ofNat 64 serializeSubStack by bv_omega,
        ← BitVec.sub_sub]
    have e2 : sp - 800#64 - BitVec.ofNat 64 serializeSubStack + BitVec.ofNat 64 serializeSubStack =
        sp - 800#64 := BitVec.sub_add_cancel _ _
    rw [e1, e2] at hsplit
    rw [e1, hsplit, sepConj_comm]
  have h3 := memRegion_split (sp - 800#64) 368 336 (by decide)
  have e3 : sp - 800#64 + BitVec.ofNat 64 368 = sp - 432#64 := bv_sub_add_lit sp 800 368
  rw [show 368 + 336 = 704 by rfl, e3] at h3
  rw [h1, h2, h3]
  ac_rfl

theorem memRegion_368_split (sp : BitVec 64) :
    memRegion (sp - 800#64) 368 =
      memRegion (sp - 800#64) 24 ∗
      (∃∗ w : BitVec 64, (sp - 776#64) ↦₆₄ w) ∗
      memRegion (sp - 768#64) 336 := by
  rw [memRegion_split (sp - 800#64) 24 344 (by decide),
    memRegion_split (sp - 800#64 + BitVec.ofNat 64 24) 8 336 (by decide),
    ProofLib.memRegion_eight (sp - 800#64 + BitVec.ofNat 64 24)]
  have e1 : sp - 800#64 + BitVec.ofNat 64 24 = sp - 776#64 := bv_sub_add_lit sp 800 24
  have e2 : sp - 776#64 + BitVec.ofNat 64 8 = sp - 768#64 := bv_sub_add_lit sp 776 8
  rw [e1, e2]

theorem memRegion_368_for_clone (sp : BitVec 64) :
    memRegion (sp - 800#64) 368 =
      memRegion (sp - 800#64) 344 ∗ memRegion (sp - 456#64) 24 := by
  have h := memRegion_split (sp - 800#64) 344 24 (by decide)
  have e : sp - 800#64 + BitVec.ofNat 64 344 = sp - 456#64 := bv_sub_add_lit sp 800 344
  rwa [e] at h

theorem repack_frame_368 (sp w0 : BitVec 64) {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    ((sp - 800#64) ↦₆₄ w0) ∗ ((sp - 792#64) ↦ₛ bs336) ∗ memRegion (sp - 456#64) 24 ⊢
      memRegion (sp - 800#64) 24 ∗
      (∃∗ w : BitVec 64, (sp - 776#64) ↦₆₄ w) ∗
      memRegion (sp - 768#64) 336 := by
  rw [← memRegion_368_split sp, memRegion_368_for_clone sp,
    memRegion_split (sp - 800#64) 8 336 (by decide)]
  have e : sp - 800#64 + BitVec.ofNat 64 8 = sp - 792#64 := bv_sub_add_lit sp 800 8
  rw [e, sepConj_assoc]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono ?_ (Entails.refl _))
  have hb := pointsToBytes_entails_memRegion (sp - 792#64) bs336
  rwa [h336] at hb

theorem memRegion_336_split24 (sp : BitVec 64) :
    memRegion (sp - 432#64) 336 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2)) ∗
      memRegion (sp - 408#64) 312 := by
  rw [memRegion_split (sp - 432#64) 24 312 (by decide),
    memRegion_24_eq_exists_vecHeader (sp - 432#64)]
  unfold vecHeader
  have e1 : sp - 432#64 + 8#64 = sp - 424#64 := bv_sub_add_lit sp 432 8
  have e2 : sp - 432#64 + 16#64 = sp - 416#64 := bv_sub_add_lit sp 432 16
  have e3 : sp - 432#64 + BitVec.ofNat 64 24 = sp - 408#64 := bv_sub_add_lit sp 432 24
  rw [e1, e2, e3]

theorem repack_336_from_q01_w2 (sp : BitVec 64) (q01 : BitVec 128) (w2 : BitVec 64) :
    (((sp - 432#64) ↦₁₂₈ q01) ∗ ((sp - 416#64) ↦₆₄ w2) ∗ memRegion (sp - 408#64) 312) ⊢
      memRegion (sp - 432#64) 336 := by
  rw [memRegion_split (sp - 432#64) 16 320 (by decide),
    memRegion_split (sp - 432#64 + BitVec.ofNat 64 16) 8 312 (by decide),
    memRegion_16_eq_exists_pointsTo128 (sp - 432#64)]
  have e1 : sp - 432#64 + BitVec.ofNat 64 16 = sp - 416#64 := bv_sub_add_lit sp 432 16
  have e2 : sp - 416#64 + BitVec.ofNat 64 8 = sp - 408#64 := bv_sub_add_lit sp 416 8
  rw [e1, e2]
  exact sepConj_mono (Entails.sepExists_intro q01)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))

theorem repack_stack_some (sp : BitVec 64) (q01 : BitVec 128) (w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStack ∗
      vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₁₂₈ q01) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStack := by
  rw [stackAt_serialize_base sp, memRegion_split (sp - 800#64) 24 344 (by decide)]
  have e1 : sp - 800#64 + BitVec.ofNat 64 24 = sp - 776#64 := bv_sub_add_lit sp 800 24
  rw [e1]
  have hpull :
      (stackAt (sp - 800#64) serializeSubStack ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStack ∗
        (vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗ memRegion (sp - 776#64) 344) ∗
        (((sp - 432#64) ↦₁₂₈ q01) ∗ ((sp - 416#64) ↦₆₄ w2) ∗ memRegion (sp - 408#64) 312) ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right
    (sepConj_mono (sepConj_mono_left (vecHeader_entails_memRegion _ _ _ _))
      (sepConj_mono_left (repack_336_from_q01_w2 sp q01 w2)))

theorem repack_stack_none (sp w0 : BitVec 64) (q01 : BitVec 128) (w2 : BitVec 64)
    {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    (stackAt (sp - 800#64) serializeSubStack ∗
      vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
      ((sp - 776#64) ↦₆₄ w0) ∗
      ((sp - 768#64) ↦ₛ bs336) ∗
      ((sp - 432#64) ↦₁₂₈ q01) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStack := by
  refine Entails.trans ?_ (repack_stack_some sp q01 w2)
  have h344 : (((sp - 776#64) ↦₆₄ w0) ∗ ((sp - 768#64) ↦ₛ bs336)) ⊢ memRegion (sp - 776#64) 344 := by
    rw [memRegion_split (sp - 776#64) 8 336 (by decide)]
    have e : sp - 776#64 + BitVec.ofNat 64 8 = sp - 768#64 := bv_sub_add_lit sp 776 8
    rw [e]
    refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
    have hb := pointsToBytes_entails_memRegion (sp - 768#64) bs336
    rwa [h336] at hb
  have hpull :
      (stackAt (sp - 800#64) serializeSubStack ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        ((sp - 776#64) ↦₆₄ w0) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStack ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        (((sp - 776#64) ↦₆₄ w0) ∗ ((sp - 768#64) ↦ₛ bs336)) ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h344))

theorem sessionInline_exists_tail {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {bs : List (BitVec 8)} (h : SessionInline G st bs) :
    ∃ bs336 : List (BitVec 8),
      bs336.length = 336 ∧ bs = unpack64 G.localIk.cap ++ bs336 := by
  have hlen := h.length_eq
  rcases h with ⟨_, scBs, pendBs, kybBs, _, _, _, _, _, _, hbs⟩
  have hpref : ∃ ptail : List (BitVec 8),
      sessionPrefixBytes G st = unpack64 G.localIk.cap ++ ptail := by
    unfold sessionPrefixBytes vecGhostHeaderBytes vecHeaderBytes
    simp only [List.append_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨ptail, hptail⟩ := hpref
  rw [hptail] at hbs
  simp only [List.append_assoc] at hbs
  refine ⟨_, ?_, hbs⟩
  rw [hbs, List.length_append, unpack64_length] at hlen
  omega

def sessionAtHeap (A : RustAlloc) (G : SessionGhost)
    (s : LibsignalSessionApi.Session (List (BitVec 8))) : SepProp :=
  ⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
    sessionHeap A G s.state

theorem vecGhostHeap_cap_lt (A : RustAlloc) (g : VecGhost) :
    vecGhostHeap A g ⊢ ⌜g.cap.toNat < 2 ^ 63⌝ ∗ vecGhostHeap A g := by
  unfold vecGhostHeap RustHeap.vecU8Buf
  apply Entails.pure_left; intro hcap
  exact Entails.pure_right hcap.2.1 (Entails.pure_right hcap (Entails.refl _))

theorem sessionHeap_localIk_cap_lt (A : RustAlloc) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionHeap A G st ⊢ ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ sessionHeap A G st := by
  unfold sessionHeap
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (vecGhostHeap_cap_lt A G.localIk))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem sessionAt_unpack_head_tail (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  unfold sessionStateReprAt
  rw [sessionStateAt_eq_inline_sep_heap A ss G s.state]
  apply Entails.pure_left; intro hw0
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨_, hinl⟩
  obtain ⟨bs336, hlen336, rfl⟩ := sessionInline_exists_tail hinl
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
  have h8 : ss + BitVec.ofNat 64 8 = ss + 8#64 := rfl
  rw [h8]
  refine Entails.trans (sepConj_mono_right (sessionHeap_localIk_cap_lt A G s.state)) ?_
  have hpull :
      (((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336)) ∗
        (⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ sessionHeap A G s.state)) =
      (⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionHeap A G s.state) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hcap
  refine Entails.sepExists_right bs336 ?_
  apply Entails.pure_right ⟨hlen336, hcap, hinl⟩
  unfold sessionAtHeap
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact Entails.pure_right hw0 (Entails.refl _)

theorem sessionAt_pack_head_tail (A : RustAlloc) (dst : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8)))
    {bs336 : List (BitVec 8)}
    (h : SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)) :
    ((dst ↦₆₄ G.localIk.cap) ∗ ((dst + 8#64) ↦ₛ bs336) ∗ sessionAtHeap A G s) ⊢
      sessionStateReprAt A dst G s := by
  unfold sessionStateReprAt sessionAtHeap
  have hpull :
      ((dst ↦₆₄ G.localIk.cap) ∗ ((dst + 8#64) ↦ₛ bs336) ∗
        (⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
          G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
          (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
         sessionHeap A G s.state)) =
      (⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
          G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
          (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
        ((dst ↦₆₄ G.localIk.cap) ∗ ((dst + 8#64) ↦ₛ bs336) ∗ sessionHeap A G s.state)) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  have h8 : dst + 8#64 = dst + BitVec.ofNat 64 (unpack64 G.localIk.cap).length := rfl
  rw [pointsTo64_eq_pointsToBytes, h8, ← sepConj_assoc, ← pointsToBytes_append]
  exact sessionStateAt_of_bytes A dst G s.state h

/-! ## Callee specifications lifted to `serializeSubStack` -/

def vecVecCloneSubSpec : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp serializeSubStack

theorem vecVecClone_sub_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVV : OkAt b C ctl abs vecVecCloneName vecVecCloneEmptySpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      vecVecCloneSubSpec := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr vecVecCloneName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_vecVecClone,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - vecVecCloneStack))
    hVV
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def sessionCloneSubSpec (A : RustAlloc) : Spec SessionCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      sessionStateReprAt A x.src x.G x.s ∗ memRegion x.dst 344 ∗ A.pool ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s) ∗
      A.pool ∗ stackAt s0.sp serializeSubStack
  onPanic := allocPanic

theorem sessionClone_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hClone : OkAt b C ctl abs sessionCloneName (sessionCloneSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (sessionCloneSubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_sessionClone,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - sessionCloneStack))
    hClone
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def sessionLenSubSpec (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧ sf.trace = s0.trace⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp serializeSubStack

theorem sessionLen_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hLen : OkAt b C ctl abs sessionLenName (sessionLenSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (sessionLenSubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr sessionLenName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_sessionLen,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - sessionLenStack))
    hLen
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def encodeVarintSubSpec (A : RustAlloc) : Spec Prost.EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧ x.bs.length + 10 < 2 ^ 62⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt s0.sp serializeSubStack
  onPanic := allocPanic

theorem encodeVarint_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (encodeVarintSubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr Prost.encodeVarintName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_encodeVarint,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - Prost.encodeVarintStack))
    hEV
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpec, Prost.encodeVarintSpec,
      stackAt_serializeSub_split s0.sp Prost.encodeVarintStack (by decide)]
    refine Entails.trans (sepConj_mono_left (Entails.pure_mono
      (ψ := s0.readReg64 .x0 = x.val ∧ s0.readReg64 .x1 = x.v ∧
        (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62))
      fun ⟨h0, h1, h2⟩ => ⟨h0, h1, Or.inr h2⟩)) ?_
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeVarintSubSpec, Prost.encodeVarintSpec,
      stackAt_serializeSub_split s0.sp Prost.encodeVarintStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def encodeRawSubSpec (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool ∗ stackAt s0.sp serializeSubStack
  onPanic := allocPanic

theorem encodeRaw_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hRaw : OkAt b C ctl abs encodeRawName (encodeRawSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (encodeRawSubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_encodeRaw,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - encodeRawStack))
    hRaw
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def dropLocal1SubSpec (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp serializeSubStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp serializeSubStack

theorem dropLocal1_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDrop : FromRecordCallees.DropSessionStructureLocal1Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      (dropLocal1SubSpec A) := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal1Name =
      (tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_dropLocal1,
      libsignalSessionCode_fnOff_serialize, BitVec.add_assoc]
    rfl
  rw [← hrel]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - FromRecordCallees.dropSessionStructureLocal1Stack))
    hDrop
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpec, FromRecordCallees.dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp FromRecordCallees.dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [dropLocal1SubSpec, FromRecordCallees.dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp FromRecordCallees.dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def rustAllocSubSpec (A : RustAlloc) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp serializeSubStack
  post := fun (size, align) s0 sf =>
    let p := sf.readReg64 .x0
    (if p = 0 then
       ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
       ⌜p.toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live p size align ∗ memRegion p size) ∗
      A.pool ∗ stackAt s0.sp serializeSubStack

theorem alloc_sub_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (rustAllocSubSpec A) := by
  have halloc := alloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := serializeName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) hA (by
      simp only [libsignalSessionCode_fnOff_serialize, arm64_norm])
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - allocHookStack))
    halloc
    (fun ⟨size, align⟩ s0 => ?_)
    (fun ⟨size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [rustAllocSubSpec, rustAllocSpec,
      stackAt_serializeSub_split s0.sp allocHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [rustAllocSubSpec, rustAllocSpec,
      stackAt_serializeSub_split s0.sp allocHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8At_init_byte (A : RustAlloc) (v cap ptr : BitVec 64) (b0 : BitVec 8)
    (hcap_pos : 1 ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (cap.toNat - 1)) ⊢
      vecU8At A v cap ptr [b0] := by
  unfold vecU8At vecHeader
  split_ifs with h0
  · subst h0; simp at hcap_pos
  · simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton]
    have hpull :
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (cap.toNat - 1)) =
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (cap.toNat - 1))) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    exact Entails.pure_right ⟨hcap_pos, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecU8At_unpack_for_out (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ((v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
  unfold vecU8At RustHeap.vecU8Buf vecHeader
  rw [← pointsTo64_pair v cap ptr]
  ac_rfl

theorem vecU8_from_out_stores (A : RustAlloc) (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (((out + 8#64) ↦₁₂₈ (ptr ++ cap)) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs) ⊢
      vecU8 A (out + 8#64) bs := by
  unfold vecU8 vecU8At RustHeap.vecU8Buf vecHeader
  rw [pointsTo64_pair_out out cap ptr]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : out + 8#64 + 16#64 = out + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16, h24]
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_nil_from_out_stores (A : RustAlloc) (out : BitVec 64) :
    (((out + 8#64) ↦₁₂₈ (1#64 ++ 0#64)) ∗ ((out + 24#64) ↦₆₄ 0#64)) ⊢
      vecU8 A (out + 8#64) [] := by
  unfold vecU8 vecU8At vecHeader
  rw [pointsTo64_pair_out out 0#64 1#64]
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_zero, ↓reduceIte,
    sepConj_emp]
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : out + 8#64 + 16#64 = out + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16, h24, sepConj_assoc, @sepConj_comm _ ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ 1#64 ≠ 0#64⌝]
  apply Entails.pure_right ?_ (Entails.refl _)
  exact ⟨by decide, by decide, by decide⟩

theorem encodeKey_one_lengthDelimited :
    encodeKey 1 .lengthDelimited = [0x0a#8] := rfl

theorem lenField_one_eq (bs : List (BitVec 8)) :
    lenField 1 bs = [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := rfl

theorem lenField_one_length (bs : List (BitVec 8)) :
    (lenField 1 bs).length = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  simp only [lenField_one_eq, List.length_append, List.length_singleton]

theorem lenField_one_bv_eq (bs : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (lenField 1 bs).length := by
  rw [lenField_one_length, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem lenField_one_bounds {bs : List (BitVec 8)} (h : (lenField 1 bs).length < 2 ^ 32) :
    bs.length < 2 ^ 32 ∧
    1 ≤ (lenField 1 bs).length ∧
    (lenField 1 bs).length < 2 ^ 63 ∧
    LayoutOk (lenField 1 bs).length 1 ∧
    ([0x0a#8] : List (BitVec 8)).length + 10 < 2 ^ 62 ∧
    ([0x0a#8] : List (BitVec 8)).length +
      (encodeVarint (BitVec.ofNat 64 bs.length)).length ≤ (lenField 1 bs).length ∧
    ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length < 2 ^ 32 := by
  have hlen := lenField_one_length bs
  have h1 : bs.length < 2 ^ 32 := by omega
  have h2 : 1 ≤ (lenField 1 bs).length := by omega
  have h3 : (lenField 1 bs).length < 2 ^ 63 := by omega
  have h4 : LayoutOk (lenField 1 bs).length 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
  have h5 : ([0x0a#8] : List (BitVec 8)).length + 10 < 2 ^ 62 := by decide
  have h6 : ([0x0a#8] : List (BitVec 8)).length +
      (encodeVarint (BitVec.ofNat 64 bs.length)).length ≤ (lenField 1 bs).length := by
    simp only [List.length_singleton]; omega
  have h7 : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length < 2 ^ 32 := by
    simp only [List.length_append, List.length_singleton]; omega
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem serialize_varintLen_eq (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3)) + 73#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  SessionLenAux.sessHwVarintLen_eq_encodeVarint_length v

theorem serialize_varintLen_bvShift_eq (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  SessionLenAux.sessHwVarintLen_bvShift_eq_encodeVarint_length v

theorem sessionAt_entails_sessionStateAt (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s ⊢ sessionStateAt A ss G s.state := by
  unfold sessionStateReprAt
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem cells_12_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  exact (ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)).symm.trans
    (ProofLib.stackAt_eq_stackFrameAt sp 96 (by decide))

private theorem pull_exists_12 (P : SepProp)
    (B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
         BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
         BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp) :
    P ∗ (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
         ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
         ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
         B c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       P ∗ B c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) := by
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]; refine ProofLib.sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]

theorem cells_12_pack (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) :
    (((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
     ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
     ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
     ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
     ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
     ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) ⊢
      cells (sp - 96#64) 12 := by
  rw [cells_12_eq sp]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right c2 (Entails.sepExists_right c3
      (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.sepExists_right c7
          (Entails.sepExists_right c8 (Entails.sepExists_right c9
            (Entails.sepExists_right c10 (Entails.sepExists_right c11 (Entails.refl _))))))))))))

theorem stackAt_serialize_none_pre (sp : BitVec 64) :
    stackAt sp serializeStack =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ bs336 : List (BitVec 8),
       ∃∗ w_none : BitVec 64,
        ⌜bs336.length = 336⌝ ∗
        stackAt (sp - 800#64) serializeSubStack ∗
        memRegion (sp - 800#64) 24 ∗
        ((sp - 776#64) ↦₆₄ w_none) ∗
        memRegion (sp - 768#64) 336 ∗
        ((sp - 432#64) ↦ₛ bs336) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [stackAt_serialize_base sp, cells_12_eq sp]
  repeat rw [pull_exists_12]
  refine ProofLib.sepExists_congr fun c0 => ProofLib.sepExists_congr fun c1 =>
    ProofLib.sepExists_congr fun c2 => ProofLib.sepExists_congr fun c3 =>
    ProofLib.sepExists_congr fun c4 => ProofLib.sepExists_congr fun c5 =>
    ProofLib.sepExists_congr fun c6 => ProofLib.sepExists_congr fun c7 =>
    ProofLib.sepExists_congr fun c8 => ProofLib.sepExists_congr fun c9 =>
    ProofLib.sepExists_congr fun c10 => ProofLib.sepExists_congr fun c11 => ?_
  rw [memRegion_368_split sp, memRegion_eq_exists_bytes (sp - 432#64) 336 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun bs336 => ProofLib.sepExists_congr fun w_none => ?_
  ac_rfl

theorem stackAt_serialize_some_pre (sp : BitVec 64) :
    stackAt sp serializeStack =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        stackAt (sp - 800#64) serializeSubStack ∗
        memRegion (sp - 800#64) 344 ∗
        memRegion (sp - 456#64) 24 ∗
        memRegion (sp - 432#64) 336 ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [stackAt_serialize_base sp, memRegion_368_for_clone sp, cells_12_eq sp]
  repeat rw [pull_exists_12]
  refine ProofLib.sepExists_congr fun c0 => ProofLib.sepExists_congr fun c1 =>
    ProofLib.sepExists_congr fun c2 => ProofLib.sepExists_congr fun c3 =>
    ProofLib.sepExists_congr fun c4 => ProofLib.sepExists_congr fun c5 =>
    ProofLib.sepExists_congr fun c6 => ProofLib.sepExists_congr fun c7 =>
    ProofLib.sepExists_congr fun c8 => ProofLib.sepExists_congr fun c9 =>
    ProofLib.sepExists_congr fun c10 => ProofLib.sepExists_congr fun c11 => ?_
  ac_rfl

theorem bytes336_to_q01_w2 (sp : BitVec 64) {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    ((sp - 432#64) ↦ₛ bs336) ⊢
      ∃∗ w2 : BitVec 64, ∃∗ q01 : BitVec 128,
        ((sp - 432#64) ↦₁₂₈ q01) ∗ ((sp - 416#64) ↦₆₄ w2) ∗ memRegion (sp - 408#64) 312 := by
  have hb := pointsToBytes_entails_memRegion (sp - 432#64) bs336
  rw [h336, memRegion_split (sp - 432#64) 16 320 (by decide),
    memRegion_split (sp - 432#64 + BitVec.ofNat 64 16) 8 312 (by decide),
    memRegion_16_eq_exists_pointsTo128 (sp - 432#64),
    ProofLib.memRegion_eight (sp - 432#64 + BitVec.ofNat 64 16)] at hb
  have e1 : sp - 432#64 + BitVec.ofNat 64 16 = sp - 416#64 := bv_sub_add_lit sp 432 16
  have e2 : sp - 416#64 + BitVec.ofNat 64 8 = sp - 408#64 := bv_sub_add_lit sp 416 8
  rw [e1, e2] at hb
  simpa only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] using hb

theorem bytes336_to_w012 (sp : BitVec 64) {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    ((sp - 432#64) ↦ₛ bs336) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 := by
  have hb := pointsToBytes_entails_memRegion (sp - 432#64) bs336
  rw [h336, memRegion_336_split24 sp] at hb
  simpa only [sepExists_sepConj_left, sepConj_assoc] using hb

/-! ## Relocatable `[LibsignalPlacement]` lifted callee specifications (block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Lifts a `SepWP` basic block into `SepWPp` while preserving `LibsignalCodeLoaded`. -/
theorem sepWPp_of_sepWP_lscl_ser {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

theorem subroutine_ok_withLsCodeLoaded_frame_weaken {α : Type} {prog : Program}
    {pl : MultiPlacement} {entry : BitVec 64} {spec spec' : Spec α}
    (F : α → State → SepProp)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_frame_weaken F h (fun x s0 => ?_) hpost hpan hexit hoom
  dsimp only [withLsCodeLoaded]
  exact Entails.trans (sepConj_mono_left (hpre x s0)) (Entails.of_eq (by ac_rfl))

/-- Strengthens `withLsCodeLoaded pl spec` to `withLsCl pl spec` so calls preserve `LibsignalCodeLoaded` in postconditions. -/
theorem subroutine_ok_withLsCl_of_withLsCodeLoaded {α : Type} {prog : Program}
    {pl : MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCl pl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨sf, hsteps, hout, -⟩ := subroutine_ok.no_fault_before_outcome h x R s0 hpc hrun hpre hsp hL
  have hclf : LibsignalCodeLoaded pl sf.mem := hcl0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

theorem vecVecClone_caller_sub_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hVV : subroutine_ok (lsProg_52 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec)) :
    subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - vecVecCloneStack))
      hVV
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [vecVecCloneSubSpec, vecVecCloneEmptySpec,
      stackAt_serializeSub_split s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem vecVecClone_placed_sub_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hVV : subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec) :
    subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec) :=
  vecVecClone_caller_sub_ok
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H)
      (subroutine_ok_withLsCodeLoaded_of_plain hVV))

theorem sessionClone_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hClone : subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_80).base (withLsCl lsmpl (sessionCloneSubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - sessionCloneStack))
      hClone
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
      (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionCloneSubSpec, sessionCloneSpec,
      stackAt_serializeSub_split s0.sp sessionCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem sessionClone_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hClone : subroutine_ok (lsProg_80 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_80).base (withLsCl lsmpl (sessionCloneSubSpec A)) :=
  sessionClone_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hClone)

theorem sessionLen_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hLen : subroutine_ok (lsProg_52 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - sessionLenStack))
      hLen
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionLenSubSpec, sessionLenSpec,
      stackAt_serializeSub_split s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem sessionLen_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hLen : subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpec A)) :=
  sessionLen_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hLen)

theorem encodeVarint_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_10).base (withLsCl lsmpl (encodeVarintSubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - Prost.encodeVarintStack))
      hEV
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
      (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpec, Prost.encodeVarintSpec,
      stackAt_serializeSub_split s0.sp Prost.encodeVarintStack (by decide)]
    refine Entails.trans (sepConj_mono_left (Entails.pure_mono
      (ψ := s0.readReg64 .x0 = x.val ∧ s0.readReg64 .x1 = x.v ∧
        (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62))
      fun ⟨h0, h1, h2⟩ => ⟨h0, h1, Or.inr h2⟩)) ?_
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeVarintSubSpec, Prost.encodeVarintSpec,
      stackAt_serializeSub_split s0.sp Prost.encodeVarintStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem encodeVarint_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_10).base (withLsCl lsmpl (encodeVarintSubSpec A)) :=
  encodeVarint_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hEV)

theorem encodeRaw_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hRaw : subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_14).base (withLsCl lsmpl (encodeRawSubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - encodeRawStack))
      hRaw
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
      (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeRawSubSpec, encodeRawSpec,
      stackAt_serializeSub_split s0.sp encodeRawStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem encodeRaw_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hRaw : subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_14).base (withLsCl lsmpl (encodeRawSubSpec A)) :=
  encodeRaw_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hRaw)

theorem dropLocal1_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDrop : subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_6).base (withLsCl lsmpl (dropLocal1SubSpec A)) := by
  refine subroutine_ok_withLsCl_of_withLsCodeLoaded <|
    subroutine_ok_withLsCodeLoaded_frame_weaken
      (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
        (serializeSubStack - FromRecordCallees.dropSessionStructureLocal1Stack))
      hDrop
      (fun x s0 => ?_)
      (fun x s0 sf => ?_)
      (fun _ _ _ => Entails.pure_left False.elim)
      (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpec, FromRecordCallees.dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp FromRecordCallees.dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [dropLocal1SubSpec, FromRecordCallees.dropSessionStructureLocal1Spec,
      stackAt_serializeSub_split s0.sp FromRecordCallees.dropSessionStructureLocal1Stack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem dropLocal1_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDrop : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_6).base (withLsCl lsmpl (dropLocal1SubSpec A)) :=
  dropLocal1_caller_sub_ok (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hDrop)

theorem alloc_caller_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSpec A)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSubSpec A) := by
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStack)
      (serializeSubStack - allocHookStack))
    halloc
    (fun ⟨size, align⟩ s0 => ?_)
    (fun ⟨size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [rustAllocSubSpec, rustAllocSpec,
      stackAt_serializeSub_split s0.sp allocHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [rustAllocSubSpec, rustAllocSpec,
      stackAt_serializeSub_split s0.sp allocHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem alloc_placed_sub_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSubSpec A) :=
  alloc_caller_sub_ok (ls_hook_ok_of_mem halloc)

theorem panic_at_handle_error_52_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    (lsProg_52 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
  rw [ls_externAt?_of_mem, hpanic]

end Placed

end CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
