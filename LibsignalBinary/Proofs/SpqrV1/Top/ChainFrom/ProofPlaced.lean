/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlaced
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsPlaced -- shake: keep

/-!
# Relocatable Verification of `spqr::chain_from` (Block `323`)

Proves `ChainFromPlacedOkX` for `spqr::chain_from` (Block `323`, 76 instructions) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.ChainFrom

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.Placed
open ChainFromNorm

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  ult_one_toI32
  extractLsb_lo_append64 extractLsb_hi_append64

theorem sp_of_lsCallInv {pl : Obj.MultiPlacement} {s : State} (_ : LsCallInv pl s.mem)
    {sp' : BitVec 64} (h : s.sp = sp') : s.sp = sp' := h

/-- Framed `BL` call rule for `SepWPp` with a `withLsCallInv pl` callee contract and a `SepWP`
return continuation. -/
theorem SepWPp.call_frame_lsCallInv_ret {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry callee_ret_pc caller_ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCallInv pl spec))
    (x : α) {s : State} {φ : Prop} {P T F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = callee_ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = callee_ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog caller_ret_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog caller_ret_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine ProofLib.SepWPp.call_wpp hcall hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [withLsCallInv]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hF, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sf code _ _ hpost => by
      dsimp only [withLsCallInv] at hpost
      rw [hexit_eq] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sf hpcm hrunm hspm hcsm => SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm))
    (fun sf _ _ hpost => by
      dsimp only [withLsCallInv] at hpost
      rw [hoom_eq] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

local macro "wp_elim_exists" : tactic =>
  `(tactic| repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _)))

set_option maxHeartbeats 1600000 in
/-- Relocatable `spqr::chain_from` (Block `323`, 76 instructions) meets
`withLsCallInv lsmpl (chainFromSpecX hkdf A)`. -/
theorem chainFrom_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_from_pb : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX A)))
    (h_new : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf A))) :
    subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (blkPl_323).base
      (withLsCallInv lsmpl (chainFromSpecX hkdf A)) := by
  wpp_init x s0
  replace h_from_pb : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX A)) := h_from_pb
  replace h_new : subroutine_ok ((blkPC_323).rebase (blkPl_323).base H)
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX hkdf A)) := h_new
  rcases x with ⟨out, pbPtr, vnOptPtr, gPb, vnPin, pb, vn⟩
  have hinv0 : LsCallInv lsmpl s0.mem := h_1
  subst h_3 h_2 h
  refine SepWPp.rw_pre (by
    simp only [stackAt_chainFrom_split s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    rfl) ?_
  wp_elim_exists
  cases pb with
  | some chainPb =>
    have hcf_eq : chainFrom hkdf (some chainPb) vn = Chain.fromPb chainPb := rfl
    dsimp only [optChainPBAt]
    refine SepWPp.fold (chainPBAt_expose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun hcap_ne => ?_
    have hz_cap : (gPb.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 364) hinv0 ?_
    wp_steps
    refine SepWP.fold (chainPBAt_unexpose_cap A gPb (s0.readReg64 (.gpr 1#5)) chainPb)
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    apply (SepWPp.call_frame_lsCallInv_ret h_from_pb
      (⟨s0.sp - 120#64, s0.readReg64 (.gpr 1#5), gPb, chainPb⟩ : ChainFromPbCall)
      hinv1 (callee_ret_pc := (blkPl_323).base + 44#64))
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rfl
    · refine ⟨by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [sp_of_lsCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      sep_focus
    · intro sf
      exact ChainFromVNNorm.onPanic_entails_of_trace_eq (by wp_norm_lhs)
    · intro _ _; rfl
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [chainFromPbSpecX]
      have hsp_sf' : sf.sp = s0.sp - 144#64 := hsp_sf.trans (by wp_norm_lhs)
      have hx19_sf : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 0#5) :=
        hcs_sf.1.trans (by wp_norm_lhs)
      rw [sp_of_lsCallInv hinv1 (sp' := s0.sp - 144#64) (by wp_norm_lhs)]
      refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
      rw [hcf_eq]
      cases hres : Chain.fromPb chainPb with
      | ok ch =>
        dsimp only [chainResultAt]
        refine SepWP.fold (chainRepr_entails_words11 A (s0.sp - 120#64) ch)
          (by sep_focus) ?_
        refine SepWP.rw_pre (by
          simp only [sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro G
        apply SepWP.exists_elim; intro pad
        refine SepWP.focus_pure (by sep_focus) fun hcap_ch_ne => ?_
        have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ch_ne
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words11 (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        wp_steps
        refine SepWP.fold (words11_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) G ch pad)
          (by sep_focus) ?_
        refine SepWP.fold (words11_to_memRegion_88 (s0.sp - 120#64)
          G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
          G.nextRoot.cap G.nextRoot.ptr (BitVec.ofNat 64 ch.nextRoot.length)
          ch.currentEpoch ch.sendEpoch (ch.params.maxOooKeys ++ ch.params.maxJump)
          (pad ++ ch.dir.toI32)) (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
      | error err =>
        dsimp only [chainResultAt]
        refine SepWP.rw_pre (by
          simp only [chainErrorAt_unpack_words4 (s0.sp - 120#64) err,
            sepExists_sepConj_left, sepConj_assoc]
          rfl) ?_
        apply SepWP.exists_elim; intro q0_err
        apply SepWP.exists_elim; intro w3_err
        refine SepWP.rw_pre (by
          simp only [memRegion_88_words4_rest (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        wp_elim_exists
        refine SepWP.focus_pure (by sep_focus) fun htag_q0 => ?_
        refine SepWP.rw_pre (by simp only [noneCap]; rfl) ?_
        wp_steps
        refine SepWP.fold (chainErrorAt_pack_words4 (s0.readReg64 (.gpr 0#5)) err q0_err w3_err htag_q0)
          (by sep_focus) ?_
        refine SepWP.fold (words4_rest_to_memRegion_88 (s0.sp - 120#64)
          18446744073709551615#64 (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done
  | none =>
    dsimp only [optChainPBAt, noneCap]
    cases vn with
    | none =>
      have hcf_eq : chainFrom hkdf none none = .error .chainNotAvailable := rfl
      dsimp only [optVersionNegotiationRefAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn0 => ?_
      refine SepWPp.rw_pre (by
        simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        rfl) ?_
      apply SepWPp.exists_elim; intro w2_out
      apply SepWPp.exists_elim; intro w1_out
      apply SepWPp.exists_elim; intro bs7_out
      apply SepWPp.exists_elim; intro b0_out
      apply SepWPp.exists_elim; intro w0_out
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [hcf_eq]
      dsimp only [chainResultAt]
      refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
        (by sep_focus) ?_
      refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
      wp_done
    | some v =>
      dsimp only [optVersionNegotiationRefAt, versionNegotiationPBAt]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun hvn_ne => ?_
      rcases direction_fromI32_or v.direction with
        ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
      · cases hcp : v.chainParams with
        | none =>
          have hcf_eq : chainFrom hkdf none (some v) = .error .chainNotAvailable := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.rw_pre (by
            simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            rfl) ?_
          apply SepWPp.exists_elim; intro w2_out
          apply SepWPp.exists_elim; intro w1_out
          apply SepWPp.exists_elim; intro bs7_out
          apply SepWPp.exists_elim; intro b0_out
          apply SepWPp.exists_elim; intro w0_out
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
          apply SepWPp.of_sepWP_ret
          wp_steps
          rw [hcf_eq]
          dsimp only [chainResultAt]
          refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .chainNotAvailable 15#8 rfl hbs7 w1_out w2_out)
            (by sep_focus) ?_
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          wp_done
        | some cp =>
          have hcf_eq : chainFrom hkdf none (some v) =
              .ok (chainNewVal hkdf v.authKey dir cp) := by
            simp [chainFrom, chainFromVersionNegotiation, hdir_opt, hcp]; rfl
          dsimp only [optChainParamsPBAt]
          refine SepWPp.fold (vecU8At_entails_header_bytesAt_rest A
            (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
          refine SepWPp.pure_left_focus _ (by sep_focus) fun hlen64 => ?_
          refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 363) hinv0 ?_
          wp_steps
          refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.rw_pre (by
            simp only [stackAt_chainFrom_split_chainNew s0.sp, sepConj_assoc]
            rfl) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv1
          apply (SepWPp.tail_call_frame_lsCallInv h_new
            (⟨s0.readReg64 (.gpr 0#5), false, vnPin.ptr, v.authKey, dir, cp⟩ : ChainNewGhost)
            hinv1)
          · wp_focus_close wp_norm_goal
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · wp_focus_close wp_norm_lhs
          · rfl
          · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hlen64⟩
          · rw [sp_of_lsCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            sep_focus
          · intro sf
            exact ChainFromVNNorm.onPanic_entails_of_trace_eq (by wp_norm_lhs)
          · intro _ _; rfl
          · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
            dsimp only [chainNewSpecX]
            rw [sp_of_lsCallInv hinv1 (sp' := s0.sp) (by wp_norm_lhs)]
            refine SepWP.focus_pure (by sep_focus) fun htr_sf => ?_
            rw [hcf_eq]
            dsimp only [chainResultAt]
            refine SepWP.fold (chainNew_post_entails_chainRepr A (s0.readReg64 (.gpr 0#5)) _)
              (by sep_focus) ?_
            refine SepWP.fold (header_bytesAt_rest_entails_vecU8At A
              (s0.readReg64 (.gpr 2#5)) vnPin.cap vnPin.ptr v.authKey) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_chainFrom_split_chainNew s0.sp).symm)
              (by sep_focus) ?_
            wp_done
      · have hcf_eq : chainFrom hkdf none (some v) = .error .stateDecode := by
          simp [chainFrom, chainFromVersionNegotiation, hdir_opt]; rfl
        refine SepWPp.rw_pre (by
          simp only [memRegion_88_err_split (s0.readReg64 (.gpr 0#5)),
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          rfl) ?_
        apply SepWPp.exists_elim; intro w2_out
        apply SepWPp.exists_elim; intro w1_out
        apply SepWPp.exists_elim; intro bs7_out
        apply SepWPp.exists_elim; intro b0_out
        apply SepWPp.exists_elim; intro w0_out
        refine SepWPp.pure_left_focus _ (by sep_focus) fun hbs7 => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [hcf_eq]
        dsimp only [chainResultAt]
        refine SepWP.fold (fold_chainErrorAt (s0.readReg64 (.gpr 0#5)) .stateDecode 0#8 rfl hbs7 w1_out w2_out)
          (by sep_focus) ?_
        refine SepWP.fold (word_rest72_to_memRegion_80 (s0.readReg64 (.gpr 1#5)) 18446744073709551615#64)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_chainFrom_join s0.sp _ _ _ _ _ _) (by sep_focus) ?_
        wp_done

end CryptoVerification.SpqrV1.Top.ChainFrom
