/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxW
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `[LibsignalPlacement]` Helpers and `pendingId` Leaf for Tag 9P (Block `15`)

Defines the relocatable `lsProg_15 H` specifications, rodata/call helpers, and
`mergeField9PW_id_placed_ok` (`GenFieldX.pendingId`) leaf for `SessionStructure::merge_field` on
tag 9 (`pending_pre_key`) at `mergeFieldStackX = 32768` with slice length `< 2 ^ 62`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

theorem L1_MF9PAuxWPlaced : True := trivial

/-! ## Relocatable `[LibsignalPlacement]` specifications and combinators -/

def mergeField9PPendingRawSpecW (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧
      (x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32) ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      pendingAt9P A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ pendingAt9P A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

abbrev mergeField9PPendingPlacedSpecW [LibsignalPlacement] (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeField9PPendingRawSpecW P)

def MergeField9PPendingPlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldX → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeField9PPendingPlacedSpecW P)

def mergeField9PRawSpecW (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostSSGXNoPqAt_x9pW A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGXNoPqAt_x9pW A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

abbrev mergeField9PPlacedSpecW [LibsignalPlacement] (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeField9PRawSpecW P)

def MergeField9PPlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldX → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeField9PPlacedSpecW P)

theorem mergeField9PPendingPlacedSpecW_pre_iff [LibsignalPlacement] {P : GenFieldX → Prop}
    {x : MergeFieldXGhost} {s : State} {R : SepProp} :
    (s.mem ⊨ (mergeField9PPendingPlacedSpecW P).pre x s ∗ R) ↔
      P x.fld ∧ (s.mem ⊨ (mergeField9PPendingPlacedSpecW (fun _ => True)).pre x s ∗ R) := by
  simp only [mergeField9PPendingRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeField9PPendingPlacedOkW_of_imp [LibsignalPlacement]
    {H : LibsignalHooks} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingPlacedOkW H P) (hQP : ∀ fl, Q fl → P fl) :
    MergeField9PPendingPlacedOkW H Q := by
  unfold MergeField9PPendingPlacedOkW
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hq, hpre⟩ := mergeField9PPendingPlacedSpecW_pre_iff.mp hpre
  exact hP.mono_outcome x R s0 hpc hrun
    (mergeField9PPendingPlacedSpecW_pre_iff.mpr ⟨hQP _ hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9PPendingPlacedOkW_or [LibsignalPlacement]
    {H : LibsignalHooks} {P Q : GenFieldX → Prop}
    (hP : MergeField9PPendingPlacedOkW H P) (hQ : MergeField9PPendingPlacedOkW H Q) :
    MergeField9PPendingPlacedOkW H (fun fl => P fl ∨ Q fl) := by
  unfold MergeField9PPendingPlacedOkW
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hpq, hpre⟩ := mergeField9PPendingPlacedSpecW_pre_iff.mp hpre
  rcases hpq with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun
      (mergeField9PPendingPlacedSpecW_pre_iff.mpr ⟨hp, hpre⟩) hal fun _ hout => hout
  · exact hQ.mono_outcome x R s0 hpc hrun
      (mergeField9PPendingPlacedSpecW_pre_iff.mpr ⟨hq, hpre⟩) hal fun _ hout => hout

theorem mergeField9PPlacedOkW_of_pending [LibsignalPlacement] {H : LibsignalHooks}
    {P : GenFieldX → Prop}
    (hP9 : ∀ fl, P fl → (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk))
    (hP : MergeField9PPendingPlacedOkW H P) :
    MergeField9PPlacedOkW H P := by
  unfold MergeField9PPlacedOkW
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  simp only [mergeField9PRawSpecW, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW,
    sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  obtain ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr, hlen⟩, hm⟩ := hpre_raw
  have hfl := hP9 x.fld hp
  have hfr' : x.v.base.pending = none ∧ x.v.ext.pid = none ∧ x.v.ext.spkId = 0#32 := by
    rcases hfl with ⟨i, k, hfl'⟩ | ⟨o, k, spk, hfl'⟩
    · rw [hfl'] at hfr; obtain ⟨hp0, he0⟩ := hfr; rw [he0]; exact ⟨hp0, rfl, rfl⟩
    · rw [hfl'] at hfr; obtain ⟨hp0, he0⟩ := hfr; rw [he0]; exact ⟨hp0, rfl, rfl⟩
  have hpre' : s0.mem ⊨ (mergeField9PPendingPlacedSpecW P).pre x s0 ∗
      (prostSSRestNoPq_x9p A0 x.ss x.v ∗ R) := by
    dsimp only [mergeField9PPendingPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl0, ?_⟩
    simp only [mergeField9PPendingRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨h0, h1, h2, h3, h4, hp, hok, hfr', hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  refine hP.mono_outcome x (prostSSRestNoPq_x9p A0 x.ss x.v ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [mergeField9PPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    simp only [mergeField9PRawSpecW, prostSSGXNoPqAt_eq_pending_sep_rest_x9pW,
      prostSSRestNoPq_x9p_apply_pending A0 x.ss x.v hfl]
    dsimp only [mergeField9PPendingPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    simp only [mergeField9PPendingRawSpecW] at hpost
    convert hpost using 1; ac_rfl
  · right; left
    refine ⟨hpan, ?_⟩
    dsimp only [mergeField9PPlacedSpecW, mergeField9PPendingPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeField9PRawSpecW, mergeField9PPendingRawSpecW] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

/-! ## Rodata, call-frame, and callee helpers on `lsProg_15 H` -/

theorem sepWP_intro_rodata_tag9_placed_x9pW [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 8#64) ↦₈ᵣ 181#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢; intro R hm
  have hR := h R; rw [sepConj_assoc] at hR
  exact hR (lsro8_intro hcrl.2 (by lsro_addr) (by decide +kernel) hm)

theorem sepWP_drop_left_x9pW {prog : Program} {target_pc : BitVec 64}
    {s : State} {Drop P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) : SepWP prog target_pc s (Drop ∗ P) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc] at hm; exact h R (Satisfies.of_sep_right hm)

theorem call_frame_lscro_x9p {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ hm
      exact not_satisfies_false_sepConj hm) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hTF : s.mem ⊨ (T ∗ F) ∗ R' := Satisfies.mono (sepConj_mono_left hP) hm
  have hpre_in : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj]
    rw [sepConj_assoc] at hTF
    exact ⟨hφ, hTF⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_in hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanst, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoomst, hpost⟩
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanst, _, hpost, hpanic sm hpanst⟩)⟩
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    exact (hexit sm code (F ∗ R') hex hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    exact (hoom sm (F ∗ R') hoomst hpost).elim

theorem callee_subs_placed_x9pW [LibsignalPlacement] {H : LibsignalHooks}
    (hC : DeserializeCalleesPlacedW H) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.int32MergeSpecW A0)) ∧
    subroutine_ok (lsProg_15 H) (lsmpl.base 7)
      (Prost.X.bytesMergePlacedSpecW A0) :=
  ⟨ls_call_ro_of_cl (callerProg := lsProg_15 H) hC.2.1,
   ls_call_ro_of_block (callerProg := lsProg_15 H) hC.2.2.1⟩

/-! ## `GenFieldX.pendingId` leaf (`mergeField9PW_id_placed_ok`) -/

private theorem final_post_entails_id_placed_x9pW (ss cap' ptr' : BitVec 64) (v : SSGX)
    (hspk0 : v.ext.spkId = 0#32)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
      (pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((ss + 276#64) ↦₃₂ i ∗
        (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
        pendingPtr2 ptr i ↦₈ 18#8 ∗
        ((ss + 272#64) ↦₃₂ 1#32 ∗
          (ss + 280#64) ↦₆₄ 0#64 ∗
          (ss + 288#64) ↦₃₂ 0#32 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗
          (ptr + 1#64) ↦₈ 8#8 ∗
          (sp0 - 80#64) ↦₆₄ r29 ∗
          (sp0 - 72#64) ↦₆₄ r30 ∗
          (sp0 - 64#64) ↦₆₄ r25 ∗
          (sp0 - 56#64) ↦₆₄ w118 ∗
          (sp0 - 48#64) ↦₆₄ r24 ∗
          (sp0 - 40#64) ↦₆₄ r23 ∗
          (sp0 - 32#64) ↦₆₄ r22 ∗
          (sp0 - 24#64) ↦₆₄ r21 ∗
          (sp0 - 16#64) ↦₆₄ r20 ∗
          (sp0 - 8#64) ↦₆₄ r19 ∗
          memRegion (sp0 - 240#64) 160))) ⊢
    pendingAt9P A0 ss (v.apply (.pendingId i k)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingId i k).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_id_x9p slot ptr i hk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 0x124#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (pendingPtr2 ptr i + 1#64 + 34#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 1#64 + 34#64) ↦ₛ tail)) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗
      (sp0 - 72#64) ↦₆₄ r30 ∗
      (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗
      (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗
      (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono (pendingAt9P_post_fold_id A0 ss cap' ptr' v hspk0 i k)
    (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
      r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)

set_option maxHeartbeats 800000 in
theorem mergeField9PW_id_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField9PPendingPlacedOkW H (fun fl => ∃ i k, fl = .pendingId i k) := by
  unfold MergeField9PPendingPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeField9PPendingRawSpecW]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen⟩ => ?_
  obtain ⟨i, k, rfl⟩ := hfld
  have hk : k.length = 33 := hOk
  obtain ⟨hp, _hpid, hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  rw [List.length_append, pendingId_payload_length_x9p i hk] at hlen
  rw [State.spAligned] at hsp_align
  obtain ⟨hcallI, hcallB⟩ := callee_subs_placed_x9pW hC
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length)
    (a' := 35 + (encodeVarint (i.setWidth 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl35_s1, hl35_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 35) (a' := 34) (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 35) (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9P_fresh_unfold A0 ss v hp,
        sliceCursorAt_unfold_id_x9p slot ptr i hk tail,
        stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  have hlsb := pid_disc_lsb_x9p v24
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl0
  apply sepWP_intro_rodata_tag9_placed_x9pW hcrl0
  wp_steps
  apply sepWP_drop_left_x9pW
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcrl2
  have hlen_i1 : 35 + (encodeVarint (i.setWidth 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length + (18#8 :: 33#8 :: k ++ tail).length := by
    simp only [List.length_cons, List.length_append, hk]; omega
  refine call_frame_lscro_x9p
    (x := ⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k ++ tail)⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      ((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      (ss + 272#64) ↦₃₂ 1#32 ∗
      (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗
      memRegion (ss + 292#64) 4 ∗
      ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗
      (ptr + 1#64) ↦₈ 8#8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 56#64) ↦₆₄ w118 ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
      memRegion (s0.sp - 240#64) 160)
    hcallI hcrl2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_append, List.length_cons, hk]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pW (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
          (i.setWidth 64) (18#8 :: 33#8 :: k ++ tail) _)
      rw [split_272_x9p ss, hlen_i1]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hcrl3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_int32_gen_x9pW (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
      (i.setWidth 64) i (setWidth32_setWidth64_x9p i) (18#8 :: 33#8 :: k ++ tail) _
      _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.pure_elim fun htr_i => SepWPp.pure_elim fun hx0_i => ?_
  have hlen_i2 : (18#8 :: 33#8 :: k ++ tail).length = 35 + tail.length := by
    simp only [List.cons_append, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hlen_i2, show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
      pendingPtr2 ptr i from rfl]
    simp only [List.cons_append, pointsToBytes_cons, sepConj_assoc]
  have hx19_i : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_i : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_i : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_i : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_i : sf.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_i : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_i : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_i : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_i : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_i : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_i : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl3
  iterate 35 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hcrl4
  refine call_frame_lscro_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      (ss + 276#64) ↦₃₂ i ∗
      (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
      pendingPtr2 ptr i ↦₈ 18#8 ∗
      ((ss + 272#64) ↦₃₂ 1#32 ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ∗
        (ptr + 1#64) ↦₈ 8#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hcrl4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by rw [List.length_cons, List.length_append, hk]; omega)
    (by
      simp only [← List.cons_append]
      rw [← pre_to_bytesMerge_gen_x9pW ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk tail,
        List.cons_append, pointsToBytes_cons]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_i]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _
  simp only [wp_norm, arm64_norm] at hpcf2
  rw [post_of_bytesMerge_gen_x9pW ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk tail _
    _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_i] using htr_sf
  have hx0_sf' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_i] using hcsf2.2.2.1
  have hx24_sf : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_i] using hcsf2.2.2.2.2.2.1
  have hx26_sf : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_i] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_sf : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_i] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_i] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_i
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_id_placed_x9pW ss cap' ptr' v hspk0 bufRef slot ptr i hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  refine ⟨fun hmf => close_x9p (by simp only [wp_norm, arm64_norm, htr_sf'])
      (by simp only [wp_norm, arm64_norm]) hmf,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf, hx27_sf,
      hx28_sf]; exact hvregs_sf⟩

end Symbolic.Swarm.TRREF.B3DeserQ
