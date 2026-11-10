/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
public meta import ProofLib
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import all LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem stagedRes_storeErr_placed_intro (A : RustAlloc)
    (strPtr vt x28 w20 w21 src w5 o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64)
    (hw1 : resWord1 w20 w21 = strPtr.extractLsb' 0 32)
    (ho2 : o2 = (10#64 : BitVec 64).extractLsb' 0 32 ++ strPtr.extractLsb' 32 32)
    (ho3 : o3 = (1#64 : BitVec 64).extractLsb' 0 32 ++ (10#64 : BitVec 64).extractLsb' 32 32)
    (ho4 : o4 = vt.extractLsb' 0 32 ++ (1#64 : BitVec 64).extractLsb' 32 32)
    (ho5 : o5 = w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
    (ho6 : o6 = w5.extractLsb' 32 32) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      (strPtr ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  let w2 := 10#64
  let w3 := 1#64
  rw [words36At_eq_pointsToBytes]
  unfold StagedRes
  refine Entails.sepExists_right (bytes36 o2 o3 o4 o5 o6) ?_
  refine Entails.sepExists_right (strPtr ↦ᵣ storeHookStr) ?_
  refine Entails.pure_right ⟨bytes36_length o2 o3 o4 o5 o6, fun r => ?_⟩ (Entails.refl _)
  rw [hx28, hw1, ← words36At_eq_pointsToBytes]
  have hrep := (out_repack r strPtr w2 w3 vt w5).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep ⊢
  have hgrp :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₃₂ strPtr.extractLsb' 0 32) ∗
        (((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₃₂ strPtr.extractLsb' 0 32) ∗
          ((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        (strPtr ↦ᵣ storeHookStr)) := by ac_rfl
  rw [hgrp, ho2, ho3, ho4, ho5, ho6, hrep]
  unfold apiDecResultAt apiErrAt strRefAt
  have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by decide +kernel
  have htag : (0x800000000000001A#64 : BitVec 64) = speWord speApplicationCallback := rfl
  rw [htag, hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hstr :
      (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ (strPtr ↦ᵣ storeHookStr)) ⊢
      (∃∗ p : BitVec 64, ((r + 8#64) ↦₆₄ p) ∗ ((r + 16#64) ↦₆₄ 10#64) ∗ (p ↦ᵣ storeHookStr)) :=
    Entails.sepExists_right strPtr (Entails.refl _)
  have hd : ((r + 24#64) ↦₆₄ w3) ⊢ (∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 24#64) ↦₆₄ d)) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 32#64) ↦₆₄ vt) ⊢ (∃∗ vt' : BitVec 64, ((r + 32#64) ↦₆₄ vt')) :=
    Entails.sepExists_right vt (Entails.refl _)
  have hw5 : ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 40#64) 8 :=
    pointsTo64_entails_memRegion (r + 40#64) w5
  have hpull :
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗
          ((r + 32#64) ↦₆₄ vt) ∗ ((r + 40#64) ↦₆₄ w5)) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
        ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ vt) ∗ ((r + 40#64) ↦₆₄ w5)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hw5)))

def pollOutPlacedRel {α : Type} (strPtr vt o2 o3 o4 o5 : BitVec 64) (o1 : BitVec 32) :
    Except Unit α → Prop
  | .ok _ => True
  | .error () =>
    o1 = strPtr.extractLsb' 0 32 ∧
    o2 = 10#32 ++ strPtr.extractLsb' 32 32 ∧
    o3 = 0x100000000#64 ∧
    o4 = vt.extractLsb' 0 32 ++ 0#32 ∧
    o5.extractLsb' 0 32 = vt.extractLsb' 32 32

@[simp] theorem pollOutPlacedRel_ok {α : Type} (strPtr vt o2 o3 o4 o5 : BitVec 64)
    (o1 : BitVec 32) (c : α) :
    pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 (.ok c) = True := rfl

@[simp] theorem pollOutPlacedRel_err {α : Type} (strPtr vt w5 : BitVec 64) :
    pollOutPlacedRel (α := α) strPtr vt
      (10#32 ++ strPtr.extractLsb' 32 32)
      4294967296#64
      (vt.extractLsb' 0 32 ++ 0#32)
      (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (strPtr.extractLsb' 0 32)
      (.error ()) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact BitVec.extractLsb'_append_eq_right

theorem stagedRes_storeErr_of_pollOutPlacedRel {α : Type} (A : RustAlloc)
    (strPtr vt x28 w20 w21 src o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := α) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      (strPtr ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  rcases hrel with ⟨ho1, ho2, ho3, ho4, ho5⟩
  refine stagedRes_storeErr_placed_intro A strPtr vt x28 w20 w21 src (o6 ++ o5.extractLsb' 32 32)
    o2 o3 o4 o5 o6 hx28 (by rw [hw1, ho1]) ho2 ho3 ho4 ?_ ?_
  · rw [BitVec.extractLsb'_append_eq_right, ← ho5, bitvec64_eta32]
  · exact BitVec.extractLsb'_append_eq_left.symm

def withLsRoClBox {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  StoreKit.withLsRoCl pl spec

theorem box_lscro {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec)) :
    subroutine_ok prog entry (withLsRoClBox pl spec) := h

theorem subroutine_ok_withStepsPost_lscro {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec)) :
    subroutine_ok prog entry (withLsRoClBox pl (withStepsPost prog spec)) := by
  show subroutine_ok prog entry (StoreKit.withLsRoCl pl (withStepsPost prog spec))
  refine subroutine_ok_mono (subroutine_ok_withStepsPost h)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  dsimp only [StoreKit.withLsRoCl, withStepsPost, Arm64.ReachesOutcome.withStepsPost] at hq ⊢
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq

theorem shim_463 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {off : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok (lsProg_463 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl spec)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) off
      (withLsRoClBox lsmpl (withStepsPost ((blkPC_463).rebase (blkPl_463).base H) spec)) := by
  rw [BitVec.zero_add] at h
  exact subroutine_ok_withStepsPost_lscro h

theorem box_lscro_463 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {off : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok (lsProg_463 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl spec)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) off (withLsRoClBox lsmpl spec) := by
  rw [BitVec.zero_add] at h
  exact h

theorem futDrop_463 [LibsignalPlacement] {H : LibsignalHooks} {off : BitVec 64}
    (h : subroutine_ok (lsProg_463 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl futDropSpec)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) off
      (StoreKit.withLsCodeRoLoaded lsmpl futDropSpec) := by
  rw [BitVec.zero_add] at h
  exact StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl h

theorem lscro_pre_intro {α : Type} {pl : Obj.MultiPlacement} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s0.mem)
    (h : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRoClBox pl spec).pre x s0 ∗ R := by
  dsimp only [withLsRoClBox, StoreKit.withLsRoCl]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcrl, h⟩

theorem sepWPp_call_panic_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsRoClBox lsmpl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun
      (lscro_pre_intro hcrl (hpre R' hm)) hsp_align hL
  dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hout
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl_sm, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm hcrl_sm).elim hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq⟩⟩
    · exact (not_satisfies_false_sepConj _hoom).elim
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · rw [hoom_eq] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim

theorem sepWPp_call_panic_p_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsRoClBox lsmpl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun
      (lscro_pre_intro hcrl (hpre R' hm)) hsp_align hL
  dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hout
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl_sm, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      (hnext sm hpcm hrunm hspm hcsm hcrl_sm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · rw [hoom_eq] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim

open Lean Elab Tactic Meta in
meta def clearLscroInvHyps (g : MVarId) : MetaM MVarId := g.withContext do
  let lastStr : Name → String := fun
    | .str _ s => s
    | _ => ""
  let mut fvs : Array FVarId := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let mentions := (ty.find? fun t => t.isConst &&
      (["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded"].contains
        (lastStr t.constName!))).isSome
    if mentions || ty.isAppOf ``Arm64.subroutine_ok then
      fvs := fvs.push decl.fvarId
  g.tryClearMany fvs

open Lean Elab Tactic in
elab "cli_messageDecrypt_call_panic_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId := mkIdent `hcrl_poll
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "cli_messageDecrypt_call_panic_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "cli_messageDecrypt_call_panic_p_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId ← freshIdent `hcrl_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "cli_messageDecrypt_call_panic_p_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

theorem wsMetaPlaced_of_steps [LibsignalPlacement] {prog : Program} {x : DecryptGhost} {s0 s sf : State}
    (hm : wsMetaPlaced x s0 s) (hst : Steps prog s sf)
    (hrun : sf.status = .Running) (hsp : sf.sp = s.sp)
    (hx29 : sf.readReg64 .x29 = s.readReg64 .x29)
    (hx27 : sf.readReg64 .x27 = s.readReg64 .x27)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s) :
    wsMetaPlaced x s0 sf := by
  obtain ⟨_, hsp0, hal0, hal, hx29_0, hx27_0, hcrl, hvregs_0⟩ := hm
  refine ⟨hrun, hsp.trans hsp0, hal0, ?_, hx29.trans hx29_0, hx27.trans hx27_0,
    hcrl.of_keepsFrozen hst.keepsFrozen, hvregs.trans hvregs_0⟩
  unfold State.spAligned at hal ⊢
  rwa [hsp]

theorem panic_outcome_of_allocFailedInVPlaced [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold withStoresDecPlacedSpecV StoreKit.withLsCodeRoLoaded
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl (allocFailedIn_trans htr0 haf)⟩ (Entails.refl _)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
