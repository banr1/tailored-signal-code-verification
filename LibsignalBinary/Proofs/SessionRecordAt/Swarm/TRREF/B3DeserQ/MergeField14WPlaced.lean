/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `[LibsignalPlacement]` `merge_field` on Tag 14 (Block `15`)

Verifies `mergeField14KyberW_placed_ok` (over `kyberAt14`) and `mergeField14W_placed_ok`
(over `prostSSGXNoPqAt_x14`) on `lsProg_15 H` (Block `15`) at `mergeFieldStackX = 32768` with
slice length `< 2 ^ 62`.
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
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq

theorem L1_MergeField14WPlaced : True := trivial

def mergeField14KyberRawSpecW (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      kyberAt14 A0 x.ss x.v.ext.kyber ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      kyberAt14 A0 x.ss (x.v.apply x.fld).ext.kyber ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

abbrev mergeField14KyberPlacedSpecW [LibsignalPlacement] (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeField14KyberRawSpecW P)

def MergeField14KyberPlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldX → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeField14KyberPlacedSpecW P)

def mergeField14RawSpecW (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostSSGXNoPqAt_x14 A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGXNoPqAt_x14 A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

abbrev mergeField14PlacedSpecW [LibsignalPlacement] (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeField14RawSpecW P)

def MergeField14PlacedOkW [LibsignalPlacement] (H : LibsignalHooks)
    (P : GenFieldX → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeField14PlacedSpecW P)

theorem mergeField14PlacedOkW_of_kyber [LibsignalPlacement] {H : LibsignalHooks}
    {P : GenFieldX → Prop}
    (hP14 : ∀ fl, P fl → fl.tag = 14)
    (hP : MergeField14KyberPlacedOkW H P) :
    MergeField14PlacedOkW H P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  simp only [mergeField14RawSpecW, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
    sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  obtain ⟨h0, hm⟩ := hpre_raw
  obtain ⟨i, ct, hfl⟩ := (genFieldX_tag_eq_14_iff x.fld).mp (hP14 x.fld h0.2.2.2.2.2.1)
  have hpre' : s0.mem ⊨ (mergeField14KyberPlacedSpecW P).pre x s0 ∗
      (restX14NoPq A0 x.ss x.v ∗ R) := by
    dsimp only [mergeField14KyberPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl0, ?_⟩
    simp only [mergeField14KyberRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨h0, ?_⟩
    convert hm using 1; ac_rfl
  refine hP.mono_outcome x (restX14NoPq A0 x.ss x.v ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · left; refine ⟨hret, hcc, ?_⟩
    dsimp only [mergeField14PlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    simp only [mergeField14RawSpecW, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
      hfl, restX14NoPq_apply_kyber]
    dsimp only [mergeField14KyberPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    simp only [mergeField14KyberRawSpecW, hfl] at hpost
    convert hpost using 1; ac_rfl
  · right; left; refine ⟨hpan, ?_⟩
    dsimp only [mergeField14PlacedSpecW, mergeField14KyberPlacedSpecW,
      LibsignalTripleRatchet.withLsCodeRoLoaded, mergeField14RawSpecW, mergeField14KyberRawSpecW] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

private theorem sepWP_intro_rodata_tag14_placed_mf14W [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 13#64) ↦₈ᵣ 0x4c#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢; intro R hm
  have hR := h R; rw [sepConj_assoc] at hR
  exact hR (lsro8_intro hcrl.2 (by lsro_addr) (by decide +kernel) hm)

private theorem sepWP_drop_left_mf14W {prog : Program} {target_pc : BitVec 64}
    {s : State} {Drop P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) : SepWP prog target_pc s (Drop ∗ P) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc] at hm; exact h R (Satisfies.of_sep_right hm)

private theorem call_alloc_lscro_mf14W {α β : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  have hpre_in : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]; exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_in hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanst, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanst, _, hpost, fun hm' => ?_⟩)⟩
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm'
    rw [hpan] at hm'; dsimp only [allocPanic]; rw [sepConj_assoc] at hm'
    have h2 : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact hm'
    exact allowPanic_frame (fun h => by simpa only [allocFailedIn, htr] using h) h2
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost; rw [hexit] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost; rw [hoom] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

private theorem call_alloc_entails_lscro_mf14W {α β : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  exact call_alloc_lscro_mf14W hcall hcrl hpc hrun hsp hlr hspec hφ rfl hexit hpan htr hnext
    (hoom := hoom) R' (Satisfies.mono (sepConj_mono_left hP) hm) hL

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` minimal-footprint `merge_field` leaf (block `15`,
`lsProg_15 H`), tag 14 (`pending_kyber_pre_key`) over `kyberAt14` at `mergeFieldStackX` (`32768`)
and slice-length bound `< 2 ^ 62`. -/
theorem mergeField14KyberW_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField14KyberPlacedOkW H (fun fl => fl.tag = 14) := by
  unfold MergeField14KyberPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeField14KyberRawSpecW]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen⟩ => ?_
  obtain ⟨i, ct, rfl⟩ := (genFieldX_tag_eq_14_iff fld).mp htag
  have hct : ct.length = 1569 := hOk
  have hk : v.ext.kyber = none := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 14#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  rw [State.spAligned] at hsp_align
  have hcallD : subroutine_ok (lsProg_15 H) (lsmpl.base 76)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)) :=
    ls_call_ro_of_cl (callerProg := lsProg_15 H) hC.1
  have hcallI : subroutine_ok (lsProg_15 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.int32MergeSpecW A0)) :=
    ls_call_ro_of_cl (callerProg := lsProg_15 H) hC.2.1
  have hcallB : subroutine_ok (lsProg_15 H) (lsmpl.base 7) (Prost.X.bytesMergePlacedSpecW A0) :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hC.2.2.1
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr
      2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  by_cases hi : i = 0#32
  · subst hi
    rw [kyber_payload_tail_length hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1574 + tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1574 + tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1574 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [kyberAt14_none_unfold A0 ss v hk,
          sliceCursorAt_kyber_unfold_mf14 slot ptr hct tail,
          bytes_kyber_split_mf14,
          stackAt_mergeField_unfold_mf14W s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 76) hcrl0
    apply sepWP_intro_rodata_tag14_placed_mf14W hcrl0
    wp_steps
    apply sepWP_drop_left_mf14W
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hcrl2
    refine call_alloc_lscro_mf14W (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.decodeVarintSliceStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1574 + tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hcrl2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.X.decodeVarintSliceSpecW, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_split_mf14, show A0.pool = emp from rfl, emp_sepConj]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, innerBytes_length hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hcrl3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_mf14W hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2 : BitVec.ult (BitVec.ofNat 64 (1574 + tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2 : BitVec.ofNat 64 (1574 + tail.length) - 2#64 =
        BitVec.ofNat 64 (1572 + tail.length) := len_sub_mf14W (by omega) (by omega)
    have hc_ult1572 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length)) 1572#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub1572 : BitVec.ofNat 64 (1572 + tail.length) - 1572#64 =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14W (a := 1572) (b := 1572) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule1572 : BitVec.ule 1572#64 (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl3
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 47 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hcrl4
    refine call_alloc_lscro_mf14W (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A0 (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (innerBytes ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hcrl4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
      (by simp only [innerBytes_length hct]; omega)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_fold_mf14 slot ptr hct tail,
          show A0.pool = emp from rfl, emp_sepConj,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          decode_to_bytesMerge_stack_mf14W]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
    rw [post_of_bytesMerge_mf14W ss bufRef slot ptr s0.sp hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sf
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_kyber_mf14W ss cap' ptr' v bufRef slot ptr hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14W ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf2,
        hx27_sf2, hx28_sf2]; exact hvregs_sf2⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]
  · -- Case `hi : i ≠ 0#32`
    have hm_bounds := encodeVarint_length_bounds_mf14 (i.setWidth 64)
    rw [kyber_ne_payload_tail_length hi hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1575 +
      (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [kyberAt14_none_unfold A0 ss v hk,
          sliceCursorAt_kyber_ne_unfold_mf14 slot ptr hi hct tail,
          bytes_kyber_ne_split_mf14,
          stackAt_mergeField_unfold_mf14W s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 76) hcrl0
    apply sepWP_intro_rodata_tag14_placed_mf14W hcrl0
    wp_steps
    apply sepWP_drop_left_mf14W
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hcrl2
    refine call_alloc_lscro_mf14W (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.decodeVarintSliceStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
          tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hcrl2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.X.decodeVarintSliceSpecW, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_ne_split_mf14, show A0.pool = emp from rfl, emp_sepConj]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, kyberIdBytes_length i hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hcrl3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_ne_mf14W i hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2' : BitVec.ult (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2' : BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 2#64 =
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14W (a := 1575 + (encodeVarint (i.setWidth 64)).length) (b :=
        2) (n := tail.length) (by omega) (by omega)
      have heq : 1575 + (encodeVarint (i.setWidth 64)).length - 2 + tail.length =
          1573 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    have hc_ult_body : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub_body : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) -
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length) =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length)
        (b := 1573 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule_body : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2' : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n' : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2' : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n' : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n' : (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) ==
        BitVec.ofNat 64 tail.length) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1' : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 1#64 =
        BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length) (b :=
        1) (n := tail.length) (by omega) (by omega)
      have heq : 1573 + (encodeVarint (i.setWidth 64)).length - 1 + tail.length =
          1572 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl3
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 45 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hcrl4
    refine call_alloc_entails_lscro_mf14W (s0 := s0) (R := R)
      (x := (⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ :
        Prost.Int32MergeGhost))
      (T := memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallI hcrl4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
      (by rw [kyberIdBytes_length i hct]; omega)
      (by
        refine Entails.trans ?_ (pre_to_int32Merge_ne_mf14W ss bufRef slot ptr s0.sp i hct tail _)
        exact Entails.of_eq (by ac_rfl))
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sfI hpcfI hrunfI hspfI hcsfI hcrl5
    simp only [wp_norm, arm64_norm] at hpcfI
    have hsp_sfI : sfI.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspfI
    rw [post_of_int32Merge_ne_mf14W ss bufRef slot ptr s0.sp i hct tail _ sfI
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.pure_elim fun htr_sfI => SepWPp.pure_elim fun hx0_sfI => ?_
    have htr_sfI' : sfI.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sfI
    have hx0_sfI' : sfI.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sfI
    have hx19_sfI : sfI.readReg64 (Reg.gpr 19#5) = 98#64 := by
      simpa only [wp_norm, arm64_norm] using hcsfI.1
    have hx20_sfI : sfI.readReg64 (Reg.gpr 20#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.1
    have hx21_sfI : sfI.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.1
    have hx22_sfI : sfI.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.2.1
    have hx26_sfI : sfI.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsfI.2.2.2.2.2.2.2.1
    have hx27_sfI : sfI.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsfI.2.2.2.2.2.2.2.2.1
    have hx28_sfI : sfI.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsfI.2.2.2.2.2.2.2.2.2.1
    have hvregs_sfI : calleeSavedVRegs sfI = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sfI = calleeSavedVRegs sf := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsfI.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sf
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
    apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl5
    iterate 33 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunfI])
    intro hcrl6
    refine call_alloc_lscro_mf14W (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A0 (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) ∗ A0.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hcrl6
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunfI])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sfI] using hsp_align)
      rfl
      (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sfI]; rfl)
      (by simp only [innerBytes_length hct]; omega)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_ne_fold_mf14 slot ptr i hct tail,
          show A0.pool = emp from rfl, emp_sepConj,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          int32Merge_to_bytesMerge_stack_mf14W]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sfI'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sfI] using hspf2
    rw [post_of_bytesMerge_ne_mf14W ss bufRef slot ptr s0.sp i hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sfI])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sfI'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sfI] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sfI] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sfI] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sfI := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sfI
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm, hx21_sfI] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm, hx22_sfI] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_ne_kyber_mf14W ss cap' ptr' v bufRef slot ptr hi hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14W ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf2,
        hx27_sf2, hx28_sf2]; exact hvregs_sf2⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]

/-- Relocatable `[LibsignalPlacement]` PQXDH-scope `merge_field` leaf (block `15`, `lsProg_15 H`),
tag 14 (`pending_kyber_pre_key`) over `prostSSGXNoPqAt_x14`, derived from `mergeField14KyberW_placed_ok`. -/
theorem mergeField14W_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField14PlacedOkW H (fun fl => fl.tag = 14) :=
  mergeField14PlacedOkW_of_kyber (fun _ h => h) (mergeField14KyberW_placed_ok H hC)

end Symbolic.Swarm.TRREF.B3DeserQ
