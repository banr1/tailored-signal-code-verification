/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsPlaced -- shake: keep

/-!
# Relocatable Verification of `spqr::chain_from_version_negotiation` (Block `328`)

Proves `ChainFromVersionNegotiationPlacedOkX` for Block `328` (18 instructions) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.Placed
open ChainFromVNNorm

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32

/-- Framed tail-call (`Operation.B`) rule for `SepWPp` with a `withLsCallInv pl` callee contract. -/
theorem SepWPp.tail_call_frame_lsCallInv {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCallInv pl spec))
    (x : α) {s : State} {φ : Prop} {P T F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog ret_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog ret_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp hcall (x := x) (F := F) hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [withLsCallInv]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hF, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sf code R' _ hex => by
      dsimp only [withLsCallInv] at hex
      rw [hexit_eq] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm => SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm))
    (fun sf R' _ hoom => by
      dsimp only [withLsCallInv] at hoom
      rw [hoom_eq] at hoom
      exact (not_satisfies_false_sepConj hoom).elim)

set_option maxHeartbeats 800000 in
/-- Relocatable `spqr::chain_from_version_negotiation` (Block `328`, 18 instructions) meets
`withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf A)`. -/
theorem chainFromVersionNegotiation_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_new : subroutine_ok ((blkPC_328).rebase (blkPl_328).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf A))) :
    subroutine_ok ((blkPC_328).rebase (blkPl_328).base H)
      (blkPl_328).base
      (withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf A)) := by
  wpp_init x s0
  replace h_new : subroutine_ok ((blkPC_328).rebase (blkPl_328).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf A)) := h_new
  rcases x with ⟨out, vPtr, pin, v⟩
  dsimp only [versionNegotiationPBAt] at *
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_2 h
  rcases direction_fromI32_or v.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : v.chainParams with
    | none =>
      have hres : chainFromVersionNegotiation hkdf v = .error .chainNotAvailable := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro bs7
      apply SepWPp.exists_elim; intro b0
      apply SepWPp.exists_elim; intro w0
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hres]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .chainNotAvailable 15#8 rfl hbs7 w1 w2)
        (by sep_focus) ?_
      wp_done
    | some cp =>
      have hres : chainFromVersionNegotiation hkdf v =
          .ok (chainNewVal hkdf v.authKey dir cp) := by
        simp [chainFromVersionNegotiation, hdir_opt, hcp]; rfl
      dsimp only [optChainParamsPBAt]
      refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
        (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
      refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 363) hinv0 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      apply (SepWPp.tail_call_frame_lsCallInv h_new
        (⟨s0.readReg64 (.gpr 8#5), false, pin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
        hinv1)
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · rfl
      · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64⟩
      · rw [show (((((((((s0.writeReg64 (.gpr 3#5) (BitVec.zeroExtend 64 dir.toI32)).writeReg64
            (.gpr 9#5) 1#64).writeReg64 (.gpr 1#5) pin.ptr).writeReg64
            (.gpr 2#5) (BitVec.ofNat 64 v.authKey.length)).writeReg64
            (.gpr 4#5) (BitVec.zeroExtend 64 cp.maxJump)).writeReg64
            (.gpr 5#5) (BitVec.zeroExtend 64 cp.maxOooKeys)).writeReg64
            (.gpr 0#5) (s0.readReg64 (.gpr 8#5))).setPState
            (subsPState32 dir.toI32 1#32)).setPC (lsmpl.base 363)).sp = s0.sp by wp_norm_lhs]
        sep_focus
      · intro sf
        exact ChainFromVNNorm.onPanic_entails_of_trace_eq (by wp_norm_lhs)
      · intro _ _; rfl
      · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
        dsimp only [chainNewSpecX]
        refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
        rw [hres]
        dsimp only [chainResultAt]
        refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 8#5)) _)
          (by sep_focus) ?_
        refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
          (s0.readReg64 (.gpr 0#5)) pin.cap pin.ptr v.authKey) (by sep_focus) ?_
        wp_done
  · have hres : chainFromVersionNegotiation hkdf v = .error .stateDecode := by
      simp [chainFromVersionNegotiation, hdir_opt]; rfl
    refine SepWPp.rw_pre (by
      simp only [memRegion_88_err_split (s0.readReg64 (.gpr 8#5)),
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rfl) ?_
    apply SepWPp.exists_elim; intro w2
    apply SepWPp.exists_elim; intro w1
    apply SepWPp.exists_elim; intro bs7
    apply SepWPp.exists_elim; intro b0
    apply SepWPp.exists_elim; intro w0
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [hres]
    dsimp only [chainResultAt]
    refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 8#5)) .stateDecode 0#8 rfl hbs7 w1 w2)
      (by sep_focus) ?_
    wp_done

end CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
