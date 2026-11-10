/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAdvanceBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Proof of `<spqr::chain::Chain>::recv_key` (Block `366`)

Proves `recvKey_from_64_placed`, `chainRecvKey_placed_ok_of_contracts`, and
`chainRecvKey_placed_ok` (`ChainRecvKeyPlacedOkX M A lim hkdf H`, Block `366`) against
`chainRecvKeySpecX M A lim hkdf`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsmpl lsρ blkPC_366 blkPl_366
)
open CryptoVerification.LibsignalSpqrV1 (Chain HkdfFn)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainRecvKeyGhost RecvPrevFits SepWPp.mono_pre
  back_add_not_no_borrow back_ge64_props back_lt64_props ced_key_of_eq ced_key_of_gt_jump
  ced_key_of_lt chainAt chainAt_entails_chainRepr chainEpochAt_unpack_recv
  chainOuterRecvAt chainRepr_pack_recv chainRestSendKeyAt_params_eq cmp32_eq_props
  cmp32_gt_props cmp32_lt_props ge64_props jump_cmp_props lt64_props
  maxJumpOrDefault_csel_eq memRegion_32_ok_split nextKeyInternalPanicSpecX
  nextKeyInternalStackX recvKeyFrameRestAt recvKeyFrameRestAt_def recvKeyOkAt_empty_intro
  recvKeyPostAt recvKey_of_epochIdx_err recvKey_of_epochIdx_ok recvKey_zero_zero
  stackAt_chainRecvKeyX_split vecDequePhysIdx vecU8At_pack_prev
  zeroExtend64_truncate32_beq_zero
)
open CryptoVerification.SpqrV1.ChainProofs.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (SepWPp.pure_left_focus)
open CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts (
  add_not_eq_ofNat_sub chainAt_unpack_sendKey chainRepr_pack_sendKey epochIdx_of_back_ge
  epochIdx_of_gt epochIdx_of_lt physIdx_madd_eq vecDequeRingBuf_get_physIdx
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWPp.of_sepWP_lsCallInv withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (allocCallPreserved_trans)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget (withAllocCallPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAdvanceBudget (recvKey_advance_from_360_placed)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget (
  RecvKeyPlacedStateInv recvKeyPanic recvKeyPost recvKey_epilogue_placed
  recvKey_err_epochOutOfRange_from_228_placed recvKey_err_keyAlreadyRequested_from_880_placed
  recvKey_err_keyJump_from_204_placed
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoopBudget (recvKey_get_from_276_placed)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (
  ChainRecvKeyEnv ChainRecvKeyPlacedOkX chainRecvKeyEvents chainRecvKeySpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack withStack)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

local macro "sep_elim_10 "
    c0:ident c1:ident c2:ident c3:ident c4:ident
    c5:ident c6:ident c7:ident c8:ident c9:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $c0:ident; apply SepWPp.exists_elim; intro $c1:ident
    apply SepWPp.exists_elim; intro $c2:ident; apply SepWPp.exists_elim; intro $c3:ident
    apply SepWPp.exists_elim; intro $c4:ident; apply SepWPp.exists_elim; intro $c5:ident
    apply SepWPp.exists_elim; intro $c6:ident; apply SepWPp.exists_elim; intro $c7:ident
    apply SepWPp.exists_elim; intro $c8:ident; apply SepWPp.exists_elim; intro $c9:ident))

private theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem SepWPp.post_of_entails {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp} {R : SepProp} {Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ Q sf))
      Qp) :
    SepWPp prog ret s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hrun, P', hm', hsp, hcs, hent⟩ | hpan
  · exact Or.inl ⟨hret, hrun, P', hm', ⟨fun hmR => Satisfies.mono (sepConj_mono_left hent) hmR, hsp, hcs⟩⟩
  · exact Or.inr hpan

/-! ## Budget-Threaded `<spqr::chain::Chain>::recv_key` (`blkPC_366`) -/

set_option maxHeartbeats 1200000 in
theorem recvKey_from_64_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))))
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (st0 : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hfits : RecvPrevFits x.self)
    (hfits_env : FitsEnv M lim st0 (ChainRecvKeyEnv hkdf x))
    (hne_zero : ¬ (x.epoch = 0#64 ∧ x.index = 0#32))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 64#64)
    (hx1 : s.readReg64 (.gpr 1#5) = x.selfPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainAt A.repAlloc x.selfPtr x.G x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st0 s)
      (recvKeyPost M A lim hkdf x st0 s0)
      (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro prog
  have hnot_zero : (x.epoch == 0#64 && x.index == 0#32) = false := by
    by_cases he : x.epoch = 0#64
    · have hi : x.index ≠ 0#32 := fun hi => hne_zero ⟨he, hi⟩
      simp [he, beq_false_of_ne hi]
    · simp [beq_false_of_ne he]
  have h_err228 := @recvKey_err_epochOutOfRange_from_228_placed _ M A lim hkdf H x st0 s0 c3 R
  have h_err880 := @recvKey_err_keyAlreadyRequested_from_880_placed _ M A lim hkdf H x st0 s0 c3 R
  have h_err204 := @recvKey_err_keyJump_from_204_placed _ M A lim hkdf H x st0 s0 c3 R
  have h_get276 := @recvKey_get_from_276_placed _ hkdf M A lim H hshim halloc hassert_ext hadd_ext x st0 s0 c3 R
  have h_adv360 := @recvKey_advance_from_360_placed _ M A lim hkdf H hnextKey hnextKeyPanic hshim halloc hdoRes
    hslice_ext hpanic_ext hadd_ext x st0 s0 c3 R
  clear hnextKey hnextKeyPanic hshim halloc hdoRes hassert_ext hadd_ext hslice_ext hpanic_ext
  dsimp only [prog]; clear prog
  refine SepWPp.fold (chainAt_unpack_sendKey A.repAlloc x.selfPtr x.G x.self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx2; wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp htrace
  by_cases hgt_curr : x.epoch > x.self.currentEpoch
  · have ⟨hult_curr, hule_curr⟩ := lt64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    have hev_err : chainRecvKeyEvents hkdf x = [] := by
      unfold chainRecvKeyEvents
      rw [hnot_zero, epochIdx_of_gt x.self x.epoch hgt_curr]; rfl
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 228#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 228#64)
    refine SepWP.fold (chainRepr_pack_sendKey A.repAlloc x.selfPtr x.G x.self
      x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
      recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero (epochIdx_of_gt x.self x.epoch hgt_curr)
    refine SepWPp.mono_pre _ ?_
      (h_err228 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    rw [hev_err, AllocCostModel.stepEvents_nil]
    sep_frame
  · have ⟨hult_curr, hule_curr⟩ := ge64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    by_cases hback_ge : (x.self.currentEpoch - x.epoch).toNat ≥ x.self.links.length
    · have ⟨hult_back, hule_back⟩ := back_ge64_props hback_ge (by omega : x.self.links.length < 2 ^ 63)
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      have hev_err : chainRecvKeyEvents hkdf x = [] := by
        unfold chainRecvKeyEvents
        rw [hnot_zero, epochIdx_of_back_ge x.self x.epoch hgt_curr hback_ge]; rfl
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 228#64) hF ?_
      wp_steps_sync_pool ((blkPl_366).base + 228#64)
      refine SepWP.fold (chainRepr_pack_sendKey A.repAlloc x.selfPtr x.G x.self
        x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
         allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
      have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
        recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero
          (epochIdx_of_back_ge x.self x.epoch hgt_curr hback_ge)
      refine SepWPp.mono_pre _ ?_
        (h_err228 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      rw [hev_err, AllocCostModel.stepEvents_nil]
      sep_frame
    · have hback_lt : (x.self.currentEpoch - x.epoch).toNat < x.self.links.length := by omega
      have hlen_lt63 : x.self.links.length < 2 ^ 63 := by omega
      have ⟨hult_back, hule_back⟩ := back_lt64_props hback_lt hlen_lt63
      have ⟨hult_nb, hule_nb⟩ := back_add_not_no_borrow hback_lt hlen_lt63
      let epochIndex := x.self.links.length - 1 - (x.self.currentEpoch - x.epoch).toNat
      have hi_ep : epochIndex < x.self.links.length := by dsimp [epochIndex]; omega
      have hidx_eq : x.self.epochIdx x.epoch = .ok epochIndex :=
        epochIdx_of_lt x.self x.epoch hgt_curr hback_lt
      have hadd_not :
          BitVec.ofNat 64 x.self.links.length + ~~~(x.self.currentEpoch - x.epoch) =
            BitVec.ofNat 64 epochIndex :=
        add_not_eq_ofNat_sub hback_lt
      have hzip_le : (x.G.epochs.zip x.self.links).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
      have hzip_i : epochIndex < (x.G.epochs.zip x.self.links).length := by simp [hlen_eq, hi_ep]
      refine SepWPp.fold
        (vecDequeRingBuf_get_physIdx A.repAlloc x.G.linksCap x.G.linksPtr x.G.linksHead
          (x.G.epochs.zip x.self.links) hzip_le hzip_i) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hhead, _, _⟩
      have hzip_geti : (x.G.epochs.zip x.self.links)[epochIndex] =
          (x.G.epochs[epochIndex]'(by omega), x.self.links[epochIndex]'hi_ep) := by
        simp [List.getElem_zip]
      rw [hzip_geti]
      let gce := x.G.epochs[epochIndex]'(by omega)
      let link := x.self.links[epochIndex]'hi_ep
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      refine SepWPp.fold (chainEpochAt_unpack_recv A.repAlloc gce epPtr link) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hn_le, hn_cap, hn_ptr, hp_le, hp_cap, hp_ptr⟩
      refine SepWPp.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A.repAlloc x.selfPtr x.G x.self)) (by sep_focus) ?_
      have hmadd := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi_ep hlen_le) hcap_lt
      have hres_ep : Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (recv', out) ← link.recv.key hkdf x.index x.self.params
          let links' := x.self.links.set epochIndex { link with recv := recv' }
          return ({ x.self with links := links' }, out)) :=
        recvKey_of_epochIdx_ok hkdf x.self x.epoch x.index epochIndex link hne_zero hidx_eq
          (List.getElem?_eq_getElem hi_ep)
      have hult_ei : (BitVec.ofNat 64 epochIndex).ult (BitVec.ofNat 64 x.self.links.length) = true :=
        hadd_not ▸ hult_nb
      have hule_ei : (BitVec.ofNat 64 x.self.links.length).ule (BitVec.ofNat 64 epochIndex) = false :=
        hadd_not ▸ hule_nb
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      wp_norm_hyp hult_nb; wp_norm_hyp hule_nb
      wp_norm_hyp hadd_not; wp_norm_hyp hult_ei; wp_norm_hyp hule_ei; wp_norm_hyp hmadd
      by_cases heq_ctr : x.index = link.recv.ctr
      · have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_eq_props heq_ctr
        wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
        wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
        have hev_err : chainRecvKeyEvents hkdf x = [] := by
          unfold chainRecvKeyEvents
          rw [hnot_zero, hidx_eq]
          dsimp only [link] at heq_ctr
          simp only [Bool.false_eq_true, ↓reduceIte, hi_ep, ↓reduceDIte, heq_ctr,
            BitVec.lt_irrefl, beq_self_eq_true]
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 880#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 880#64)
        refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A.repAlloc x.selfPtr x.G x.self).symm) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
          link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
          link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
        have hpack := chainRepr_pack_recv A.repAlloc x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
          hhead hcap_lt hptr hlen_le hlen_eq
        dsimp only [s_idx, epPtr, link] at hpack ⊢
        have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
            x.self.links := List.set_getElem_self hi_ep
        rw [hset_self] at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hres_already : Chain.recvKey hkdf x.self x.epoch x.index =
            .error (.err (.keyAlreadyRequested x.index)) := by
          rw [hres_ep, ced_key_of_eq hkdf link.recv x.index x.self.params heq_ctr]
          rfl
        refine SepWPp.mono_pre _ ?_
          (h_err880 hres_already _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        rw [hev_err, AllocCostModel.stepEvents_nil]
        sep_frame
      · by_cases hlt_ctr : x.index < link.recv.ctr
        · have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_lt_props hlt_ctr
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 276#64) hF ?_
          wp_steps_sync_pool ((blkPl_366).base + 276#64)
          refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A.repAlloc x.selfPtr x.G x.self).symm) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
            link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
            link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF'
          have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
            ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
             by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
             allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
          have hres_get : Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
            rw [hres_ep, ced_key_of_lt hkdf link.recv x.index x.self.params hlt_ctr]
            dsimp only [link]
            cases (x.self.links[epochIndex]'hi_ep).recv.prev.get x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params <;> rfl
          refine SepWPp.mono_pre _ ?_
            (h_get276 epochIndex hi_ep gce hnot_zero hidx_eq hlt_ctr hfits_env hhead hcap_lt hptr hlen_le hlen_eq hres_get
              _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
          unfold chainOuterRecvAt
          dsimp only [s_idx, epPtr, link, gce]
          sep_frame
        · have hgt_ctr : link.recv.ctr < x.index := by
            apply BitVec.lt_def.mpr
            have h1 : ¬ (x.index.toNat < link.recv.ctr.toNat) := fun h => hlt_ctr (BitVec.lt_def.mpr h)
            have h2 : x.index.toNat ≠ link.recv.ctr.toNat := fun h => heq_ctr (BitVec.eq_of_toNat_eq h)
            omega
          have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_gt_props hgt_ctr
          have ⟨hmaxJ1, hmaxJ2⟩ := maxJumpOrDefault_csel_eq x.self.params
          have ⟨hult_jmp, hule_jmp⟩ := jump_cmp_props x.index link.recv.ctr x.self.params
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          wp_norm_hyp hmaxJ1; wp_norm_hyp hmaxJ2
          wp_norm_hyp hult_jmp; wp_norm_hyp hule_jmp
          by_cases hjump : x.index - link.recv.ctr > x.self.params.maxJumpOrDefault
          · have hjump_t : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = true :=
              decide_eq_true hjump
            wp_norm_hyp hjump_t
            have hev_err : chainRecvKeyEvents hkdf x = [] := by
              unfold chainRecvKeyEvents
              rw [hnot_zero, hidx_eq]
              dsimp only [link] at heq_ctr hlt_ctr hjump
              simp only [Bool.false_eq_true, ↓reduceIte, hi_ep, ↓reduceDIte,
                hlt_ctr, beq_false_of_ne heq_ctr, hjump]
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 204#64) hF ?_
            wp_steps_sync_pool ((blkPl_366).base + 204#64)
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A.repAlloc x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
              link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A.repAlloc (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
              link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
            have hpack := chainRepr_pack_recv A.repAlloc x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
              hhead hcap_lt hptr hlen_le hlen_eq
            dsimp only [s_idx, epPtr, link] at hpack ⊢
            have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
                x.self.links := List.set_getElem_self hi_ep
            rw [hset_self] at hpack
            refine SepWP.fold hpack (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
               allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
            have hres_jmp : Chain.recvKey hkdf x.self x.epoch x.index =
                .error (.err (.keyJump link.recv.ctr x.index)) := by
              rw [hres_ep, ced_key_of_gt_jump hkdf link.recv x.index x.self.params hgt_ctr hjump]
              rfl
            refine SepWPp.mono_pre _ ?_
              (h_err204 link.recv.ctr hres_jmp _ hinv' (by wp_norm_goal)
                (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            rw [hev_err, AllocCostModel.stepEvents_nil]
            sep_frame
          · have hjump_f : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = false :=
              decide_eq_false hjump
            wp_norm_hyp hjump_f
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 360#64) hF ?_
            wp_steps_sync_pool ((blkPl_366).base + 360#64)
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A.repAlloc x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal,
               allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
            have hp_fit0 : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 61 :=
              hfits _ (List.getElem_mem hi_ep)
            refine SepWPp.mono_pre _ ?_
              (h_adv360 epochIndex hi_ep gce hnot_zero hidx_eq hfits_env hhead hcap_lt hptr hlen_le hlen_eq rfl
                hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hp_fit0 hgt_ctr hjump hres_ep
                _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
                (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            unfold chainOuterRecvAt
            dsimp only [s_idx, epPtr, link, gce]
            sep_frame

set_option maxHeartbeats 1200000 in
theorem chainRecvKey_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))))
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    ChainRecvKeyPlacedOkX M A lim hkdf H := by
  unfold ChainRecvKeyPlacedOkX
  wpp_init x_st s0
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x_st with ⟨⟨out, selfPtr, epoch, index, G, self⟩, st0⟩
  dsimp only [withLsCallInv, chainRecvKeySpecX] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹LibsignalRoLoaded lsmpl s0.mem›, ‹LibsignalCodeLoaded lsmpl s0.mem›⟩
  have hfits_env : FitsEnv M lim st0
      (ChainRecvKeyEnv hkdf ⟨out, selfPtr, epoch, index, G, self⟩) := ‹_›
  subst out selfPtr epoch index
  let x0 : ChainRecvKeyGhost :=
    ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), s0.readReg64 (.gpr 2#5),
     (s0.readReg64 (.gpr 3#5)).setWidth 32, G, self⟩
  have h_epi := @recvKey_epilogue_placed _ M A lim hkdf H x0 st0 s0
  have h_from64 := @recvKey_from_64_placed _ M A lim hkdf H hnextKey hnextKeyPanic hshim halloc hdoRes
    hassert_ext hadd_ext hslice_ext hpanic_ext x0 st0 s0
  dsimp only [x0] at h_epi h_from64
  clear hnextKey hnextKeyPanic hshim halloc hdoRes hassert_ext hadd_ext hslice_ext hpanic_ext
  refine SepWPp.rw_pre (by rw [stackAt_chainRecvKeyX_split s0.sp]) ?_
  sep_elim_10 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  by_cases hep0 : s0.readReg64 (.gpr 2#5) = 0#64
  · have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = true := by simp [hep0]
    wp_norm_hyp hep_beq
    by_cases hidx0 : (s0.readReg64 (.gpr 3#5)).setWidth 32 = 0#32
    · have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = true := by simp [hidx0]
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = true := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      have hev00 : chainRecvKeyEvents hkdf x0 = [] := by
        unfold chainRecvKeyEvents
        simp [x0, hep0, hidx0]
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      rw [memRegion_32_ok_split (s0.readReg64 (.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro w0
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w3
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hinv0 ?_
      wp_steps_sync_pool ((blkPl_366).base + 248#64)
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      refine SepWP.fold (recvKeyOkAt_empty_intro A.repAlloc (s0.readReg64 (.gpr 0#5))) (by sep_focus) ?_
      refine SepWP.fold (chainAt_entails_chainRepr A.repAlloc (s0.readReg64 (.gpr 1#5)) G self) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal,
         by unfold AllocCallPreserved; wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_ (h_epi c3 _ hinv' (by wp_norm_goal))
      dsimp only [x0] at hev00
      rw [hev00, AllocCostModel.stepEvents_nil, hep0, hidx0, recvKey_zero_zero hkdf self]
      dsimp only [recvKeyPostAt]
      sep_frame
    · have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = false := beq_false_of_ne hidx0
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = false := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 64#64) hinv0 ?_
      wp_steps_sync_pool ((blkPl_366).base + 64#64)
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal,
         by unfold AllocCallPreserved; wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_
        (h_from64 c3 ‹RecvPrevFits self› hfits_env (fun ⟨_, hi⟩ => hidx0 hi)
          _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  · have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = false := beq_false_of_ne hep0
    wp_norm_hyp hep_beq
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 64#64) hinv0 ?_
    wp_steps_sync_pool ((blkPl_366).base + 64#64)
    refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal,
       by unfold AllocCallPreserved; wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_from64 c3 ‹RecvPrevFits self› hfits_env (fun ⟨he, _⟩ => hep0 he)
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

abbrev chainRecvKey_placed_ok := @chainRecvKey_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyBudget
