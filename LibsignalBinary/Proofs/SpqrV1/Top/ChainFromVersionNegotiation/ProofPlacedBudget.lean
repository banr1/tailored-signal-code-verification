/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Verification of `spqr::chain_from_version_negotiation` (Block `328`)

Proves `RustCliAllocBudget` `ChainFromVersionNegotiationPlacedOkX` for Block `328` (18 instructions)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (ChainNewEnv chainNewSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromVersionNegotiationEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlacedBudget
  (ChainFromVersionNegotiationPlacedOkX)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (HkdfFn chainFromVersionNegotiation)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainNewGhost chainEpochAlign chainEpochSize chainNewVal)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (LsCallInv SepWP.seq_lsCallInv withLsCallInv)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (ChainFromVersionNegotiationCall chainFromVersionNegotiationStackX chainResultAt
   optChainParamsPBAt versionNegotiationPBAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
  (chainNew_post_entails_chainRepr direction_fromI32_or fold_chainErrorAt
   header_bytesAt_rest_entails_vecU8At memRegion_88_err_split
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre ult_one_toI32
   vecU8At_entails_header_bytesAt_rest)
open CryptoVerification.SpqrV1.Top.Placed
  (blkPC_328 blkPl_328)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32

private theorem align_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem sepWP_rw_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

private theorem calleeSavedPreserved_trans {s0 s1 sf : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 sf) :
    CalleeSavedPreserved s0 sf := by
  unfold CalleeSavedPreserved at h01 h12 ⊢
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩
  rcases h12 with ⟨k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, kv⟩
  exact ⟨k19.trans h19, k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28,
    k29.trans h29, kv.trans hv⟩

/-- Framed `BL` / tail-`B` call rule for `SepWP` with a `withLsCallInv pl` callee contract
    whose `onPanic`, `onExit`, and `onOom` are `⌜False⌝`. -/
theorem call_frame_lsCallInv {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry callee_ret_pc caller_ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCallInv pl spec))
    (x : α) {s : State} {φ : Prop} {P T F : SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = callee_ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = callee_ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog caller_ret_pc sf (spec.post x s sf ∗ F) post) :
    SepWP prog caller_ret_pc s P post := by
  refine SepWP.call_subroutine_frame (x := x) (F := F) hcall hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCallInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hF, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hpost
    dsimp only [withLsCallInv] at hpost
    rw [hpan_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sf _ hpost
    dsimp only [withLsCallInv] at hpost
    rw [hexit_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · exact hnext
  · intro R' sf _ hpost
    dsimp only [withLsCallInv] at hpost
    rw [hoom_eq] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

private theorem sepWP_chainFromVN_finish [LibsignalPlacement]
    {hkdf : HkdfFn} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {call : ChainFromVersionNegotiationCall} {st : M.σ} {evs : List AllocEvent}
    (hevs : ChainFromVersionNegotiationEnv call.v evs)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf M A lim)).post
          (call, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hwp : SepWP ((blkPC_328).rebase (blkPl_328).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        VmPreserved s sf ∧
        (P_f ⊢
          chainResultAt A.repAlloc call.out (chainFromVersionNegotiation hkdf call.v) ∗
          versionNegotiationPBAt A.repAlloc call.pin call.vPtr call.v ∗
          A.pool lim (M.stepEvents evs st) s ∗
          stackAt s0.sp chainFromVersionNegotiationStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    SepWP ((blkPC_328).rebase (blkPl_328).base H) (s0.readReg64 .lr) s P post := by
  subst hpost
  refine SepWP.mono hwp ?_
  intro sf P_f _ _ ⟨hvm, hent, hspf, hcsf, htrf⟩
  refine ⟨fun hmR => ?_, hspf, hcsf⟩
  have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
  rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs st) hvm] at hm1
  dsimp only [withLsCallInv, chainFromVersionNegotiationSpecX]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, hevs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1⟩

set_option maxHeartbeats 800000 in
/-- Relocatable `spqr::chain_from_version_negotiation` (Block `328`, 18 instructions) meets
`withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf M A lim)`. -/
theorem chainFromVersionNegotiation_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_new : subroutine_ok ((blkPC_328).rebase (blkPl_328).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf M A lim))) :
    subroutine_ok ((blkPC_328).rebase (blkPl_328).base H)
      (blkPl_328).base
      (withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf M A lim)) := by
  apply subroutine_ok_of_sepWP_init
  intro ⟨⟨out, vPtr, pin, v⟩, st⟩ R s0 hpc hrun hpre0 hsp0
  dsimp only [withLsCallInv, chainFromVersionNegotiationSpecX, Reg.x8, Reg.x0] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hinv0, hpre0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hx0, hfits⟩, hpre0⟩
  refine ⟨_, hpre0, ?_⟩
  subst hx8 hx0
  rcases direction_fromI32_or v.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : v.chainParams with
    | none =>
      have hres : chainFromVersionNegotiation hkdf v = .error .chainNotAvailable := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      have hevs : ChainFromVersionNegotiationEnv v [] := by
        simp [ChainFromVersionNegotiationEnv, hdir_opt, hcp]
      refine sepWP_rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro bs7
      apply SepWP.exists_elim; intro b0
      apply SepWP.exists_elim; intro w0
      refine SepWP.focus_pure (by sep_focus) fun hbs7 => ?_
      apply sepWP_chainFromVN_finish
        (call := ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pin, v⟩) hevs rfl
      rw [hres]
      conv =>
        arg 5
        ext sf P_f
        simp only [chainResultAt, versionNegotiationPBAt, optChainParamsPBAt, hcp]
      by_vm_steps (
        simp only [versionNegotiationPBAt, optChainParamsPBAt, hcp]
        wp_steps
        refine SepWP.fold
          (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .chainNotAvailable 15#8 rfl hbs7 w1 w2)
          (by sep_focus) ?_
        refine align_pre (by sep_ac_rfl) ?_
        wp_done
      )
    | some cp =>
      have hres : chainFromVersionNegotiation hkdf v =
          .ok (chainNewVal hkdf v.authKey dir cp) := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      have henv_eq : ChainFromVersionNegotiationEnv v = ChainNewEnv := by
        funext evs
        simp [ChainFromVersionNegotiationEnv, ChainNewEnv,
          LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents,
          LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.chainNewEvents,
          chainEpochSize, chainEpochAlign, hdir_opt, hcp]
      have hfits_new : FitsEnv M lim st ChainNewEnv := henv_eq ▸ hfits
      conv =>
        arg 4
        simp only [versionNegotiationPBAt, optChainParamsPBAt, hcp]
      refine SepWP.fold (vecU8At_entails_header_bytesAt_rest A.repAlloc
        (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
      refine SepWP.focus_pure (by sep_focus) fun hlen64 => ?_
      refine SepWP.seq_lsCallInv (mid := lsmpl.base 363) hinv0 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      apply (call_frame_lsCallInv h_new
        ((⟨s0.readReg64 (.gpr 8#5), false, pin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost), st)
        hinv1 (callee_ret_pc := s0.readReg64 .lr))
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rfl
      · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
          by wp_norm_lhs, by wp_norm_lhs, hlen64, hfits_new⟩
      · rw [show (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
            (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
            (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
            (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
            (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
            (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
            (subsPState32 dir.toI32 1#32)).setPC (lsmpl.base 363)).sp = s0.sp by wp_norm_lhs]
        have hpool_eq : A.pool lim st s0 = A.pool lim st
            (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
              (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
              (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
              (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
              (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
              (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
              (subsPState32 dir.toI32 1#32)).setPC (lsmpl.base 363)) := by
          simp only [wp_norm, arm64_norm]
        rw [hpool_eq]
        sep_focus
      · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
        dsimp only [chainNewSpecX]
        rw [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro evs
        refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
        rcases hpure with ⟨htr_sf, _hacp, hevs_new⟩
        have hevs : ChainFromVersionNegotiationEnv v evs := henv_eq.symm ▸ hevs_new
        have hsp_sf' : sf.sp = s0.sp := hsp_sf.trans (by wp_norm_lhs)
        have htr_sf' : sf.trace = s0.trace := htr_sf.trans (by wp_norm_lhs)
        have hcs0 : CalleeSavedPreserved s0 sf :=
          calleeSavedPreserved_trans
            (by unfold CalleeSavedPreserved; simp only [Reg.fp, wp_norm, arm64_norm, and_self])
            hcs_sf
        apply sepWP_chainFromVN_finish
          (call := ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pin, v⟩) hevs rfl
        refine SepWP.fold (chainNew_post_entails_chainRepr A.repAlloc (s0.readReg64 (.gpr 8#5))
          (chainNewVal hkdf v.authKey dir cp))
          (by sep_focus) ?_
        refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A.repAlloc
          (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
        refine SepWP.done hpc_sf hrun_sf ⟨VmPreserved.refl sf, ?_, hsp_sf', hcs0, htr_sf'⟩
        rw [hres, show (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
            (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
            (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
            (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
            (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
            (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
            (subsPState32 dir.toI32 1#32)).setPC (lsmpl.base 363)).sp = s0.sp by wp_norm_lhs]
        simp only [versionNegotiationPBAt, optChainParamsPBAt, chainResultAt, hcp]
        exact Entails.of_eq (by sep_ac_rfl)
  · have hres : chainFromVersionNegotiation hkdf v = .error .stateDecode := by
      simp [chainFromVersionNegotiation, hdir_opt]; rfl
    have hevs : ChainFromVersionNegotiationEnv v [] := by
      simp [ChainFromVersionNegotiationEnv, hdir_opt]
    refine sepWP_rw_pre (by
      simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rfl) ?_
    apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro bs7
    apply SepWP.exists_elim; intro b0
    apply SepWP.exists_elim; intro w0
    refine SepWP.focus_pure (by sep_focus) fun hbs7 => ?_
    apply sepWP_chainFromVN_finish
      (call := ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pin, v⟩) hevs rfl
    rw [hres]
    conv =>
      arg 5
      ext sf P_f
      dsimp only [chainResultAt, versionNegotiationPBAt]
    by_vm_steps (
      dsimp only [versionNegotiationPBAt]
      wp_steps
      refine SepWP.fold
        (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .stateDecode 0#8 rfl hbs7 w1 w2)
        (by sep_focus) ?_
      refine align_pre (by sep_ac_rfl) ?_
      wp_done
    )

theorem chainFromVersionNegotiation_placed_ok_x [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_new : subroutine_ok ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf M A lim))) :
    ChainFromVersionNegotiationPlacedOkX hkdf M A lim ext :=
  chainFromVersionNegotiation_placed_ok_of_contracts_x h_new

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
