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
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
public meta import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Proof of `<spqr::chain::Chain>::add_epoch` (Block `368`)

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract
`ChainAddEpochPlacedOkX hkdf M A lim H` for `<spqr::chain::Chain>::add_epoch` (Block `368`)
against `chainAddEpochSpecX hkdf M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_368 blkPl_368 withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (Chain EpochSecret HkdfFn chainAddEpochInfo)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainAddEpochGhost ChainGhost HkdfToSliceGhost RegsAt348 SepWP.bind_cell64
  SepWP.unfold_vecDeque_bind SepWPp.exists_left SepWPp.reassoc_panic SepWPp.rw_pre
  VecDequeGrowGhost VecPin addEpochMidFramePlaced addEpochMidFramePlaced_def
  add_neg_eq_zero_false_of_ne bytesAt_false bytesAt_true calleeSavedStackAt
  calleeSavedStackAt_def cedStackBothAt cedStackBothAt_def chainAddEpochStackX
  chainAddEpochVal chainAt chainEpochAlign chainEpochAt chainEpochSize
  chainEpochDirectionAt_madd_recv_intro chainEpochDirectionAt_madd_send_intro
  chainRepr chain_addEpoch_eq_ok cmn_one_false_of_ne epochSecretAt hkdfToSliceSpec
  hkdfToSliceSpqrSpec isOk_addEpoch_false_of_epoch_ne isOk_addEpoch_false_of_ovf
  len_lt_newCapChainEpoch newCapChainEpoch ofNat_len_add_one ofNat_len_ne_cap
  physIdx_madd_eq sub_eq_zero_false_of_ne vecDequeAt_fold_addEpoch vecDequePhysIdx
  vecDequeRingBuf vecDequeRingBuf_split_madd_links vecU8Rest_eq_zero
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochFacts (
  cedCells_reframe_addEpoch cells12_192_entails_memRegion_96 cells4_entails_memRegion_32
  chainAddEpochInfo_length chainAt_unpack_addEpoch chainRepr_addEpoch_intro chainUntouchedAt
  cmp_dir_toI32 cmp_dir_toI32_bne csel_cedSrcAddEpoch_dir csel_cedSrcAddEpoch_dir_bne
  csel_cedSrcAddEpoch_switch csel_cedSrcAddEpoch_switch_bne epochSecretAt_unpack
  hokm_sp_reframe_addEpoch rejoin_stack_chainAddEpochX rodata_chainAddEpochInfo_placed
  stackAt_chainAddEpochX_split stackAt_chainAddEpochX_top_split vecU8Rest
  vecU8Rest_nonzero_entails
)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (
  SepWPp.pure_left_focus cedCells_eq_pointsToBytes exists_unpack64_of_length_96_split
  memRegion_32_cells4
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWP.pure_left_focus SepWP.seq_lsCallInv SepWPp.call_allowPanic_lsCallInv_mid
  SepWPp.of_sepWP_lsCallInv subroutine_ok_withLsCallInv_of_plain
  subroutine_ok_withLsCallInv_of_withLsCodeLoaded subroutine_ok_withLsCallInv_rodata1_keep
  withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (
  ChainAddEpochEnv ChainAddEpochPlacedOkX chainAddEpochEvents chainAddEpochSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  VecDequeGrowEnv vecDequeGrowEvents vecDequeGrowSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans subroutine_ok_allocNoOomWithStack_of_budget
  subroutine_ok_post_entails withAllocVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack rustDeallocSpecWithStack withStack
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false chainAddEpochInfo_length chainEpochSize
  cmp_dir_toI32 cmp_dir_toI32_bne
  csel_cedSrcAddEpoch_dir csel_cedSrcAddEpoch_dir_bne
  csel_cedSrcAddEpoch_switch csel_cedSrcAddEpoch_switch_bne
  RegsAt348
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

private theorem allowPanic_addEpochBudget_err {hkdf : HkdfFn} {self : Chain}
    {epochSecret : EpochSecret} {s0 sf : State} {P R : SepProp}
    (herr : (Chain.addEpoch hkdf self epochSecret).isOk = false)
    (htr : (Rust.panicked sf).trace = s0.trace)
    (hm : (Rust.panicked sf).mem ⊨ P ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜(Chain.addEpoch hkdf self epochSecret).isOk = false ∧
          (Rust.panicked sf).trace = s0.trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨herr, htr⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

private theorem SepWP.join_lsCallInv_acp {prog : Program} {pl : Obj.MultiPlacement}
    {join_pc target_pc : BitVec 64} {s : State} {P : SepProp} {P_join : State → SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hreach : SepWP prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        AllocCallPreserved s sm ∧ (Pm ⊢ P_join sm)))
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf.mem →
      SepWPp prog target_pc sf (⌜AllocCallPreserved s sf⌝ ∗ P_join sf) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  rcases hreach.elim hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hcsm, hacpm, hent⟩ | ⟨hoom, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ (⌜AllocCallPreserved s sm⌝ ∗ P_join sm) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hacpm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

private theorem SepWPp.join_at_348_lsCallInv_acp {prog : Program} {pl : Obj.MultiPlacement}
    {join_pc target_pc cap1 : BitVec 64} {s : State} {P : SepProp} {P_join : State → SepProp}
    {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (hreach : SepWPp prog join_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ RegsAt348 s sm ∧
        sm.readReg64 (.gpr 9#5) = cap1 ∧
        AllocCallPreserved s sm ∧ (Pm ⊢ P_join sm))
      panic_post)
    (hnext : ∀ sf : State, sf.pc = join_pc → sf.status = .Running →
      sf.sp = s.sp → RegsAt348 s sf → sf.readReg64 (.gpr 9#5) = cap1 → LsCallInv pl sf.mem →
      SepWPp prog target_pc sf (⌜AllocCallPreserved s sf⌝ ∗ P_join sf) post panic_post) :
    SepWPp prog target_pc s P post panic_post := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hspm, hregm, hcapm, hacpm, hent⟩ | hpan⟩ :=
    hreach R hm hL
  · have hmm' : sm.mem ⊨ (⌜AllocCallPreserved s sm⌝ ∗ P_join sm) ∗ R := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hacpm, Satisfies.mono (sepConj_mono_left hent) hmm⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hregm hcapm (hF.of_steps hsteps) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

private def chainAddEpochPostConcrete [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (ChainAddEpochGhost × M.σ) → State → State → SepProp :=
  fun x_st s0 sf =>
    (lsρ "spqr:.rodata..Lanon.175" ↦ᵣ chainAddEpochInfo) ∗
      (chainAddEpochSpecX hkdf M A lim).post x_st s0 sf

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::chain::Chain>::add_epoch` (Block `368`) meets
`withLsCallInv lsmpl (chainAddEpochSpecX hkdf M A lim)` under `[LibsignalPlacement]`. -/
theorem chainAddEpoch_placed_ok_of_contracts_x [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379) (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec hkdf))))
    (hgrow : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353) (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)))
    (hshim : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack))
    (hpan_ovf : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") =
        some Rust.panicked)
    (hpan_core : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H) (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX hkdf M A lim)) := by
  have halloc_nooom := subroutine_ok_allocNoOomWithStack_of_budget halloc
  refine subroutine_ok_withLsCallInv_rodata1_keep rodata_chainAddEpochInfo_placed ?_
  refine subroutine_ok_post_entails
    (chainAddEpochPostConcrete hkdf M A lim)
    (fun _ _ _ => Entails.refl _)
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨x, st⟩
  rcases x with ⟨selfPtr, esPtr, G, esPin, self, epochSecret⟩
  dsimp only [chainAddEpochSpecX] at *
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹_›, ‹_›⟩
  have hheadroom :
      self.links.length < G.linksCap.toNat ∨
        max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 := ‹_›
  have hfits_env :
      FitsEnv M lim st
        (ChainAddEpochEnv hkdf ⟨selfPtr, esPtr, G, esPin, self, epochSecret⟩) := ‹_›
  have hx0 : s0.readReg64 (.gpr 0#5) = selfPtr := ‹_›
  have hx1 : s0.readReg64 (.gpr 1#5) = esPtr := ‹_›
  subst hx0 hx1
  refine SepWPp.rw_pre (by rw [stackAt_chainAddEpochX_split s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 40#64) hinv0 ?_
  refine SepWP.fold (chainAt_unpack_addEpoch A.repAlloc (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hnr_le, hnr_lt, hnr_ptr⟩
  refine SepWP.fold (epochSecretAt_unpack A.repAlloc (s0.readReg64 (.gpr 1#5)) esPin epochSecret) (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_lt, hes_ptr⟩
  have hnr_len_lt : self.nextRoot.length < 2 ^ 63 := Nat.lt_of_le_of_lt hnr_le hnr_lt
  have hes_len_lt : epochSecret.secret.length < 2 ^ 63 := Nat.lt_of_le_of_lt hes_le hes_lt
  refine SepWP.bind_cell64 (s0.sp - 72#64) (by sep_focus) fun v15 => ?_
  wp_steps_sync_pool ((blkPl_368).base + 40#64)
  refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv0'
  by_cases hovf : self.currentEpoch = 0xffffffffffffffff#64
  · have herr := isOk_addEpoch_false_of_ovf hkdf self epochSecret hovf
    have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = true := by simp [hovf]
    wp_norm_hyp hovf_beq
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
    wp_steps_sync_pool (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_ovf) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_addEpochBudget_err herr (by simp only [Rust.panicked, arm64_norm]) hm
  · have hovf_beq : (self.currentEpoch == 0xffffffffffffffff#64) = false := by simp [hovf]
    have hovf_cmn := cmn_one_false_of_ne hovf
    wp_norm_hyp hovf_beq
    wp_norm_hyp hovf_cmn
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 60#64) hinv0' ?_
    wp_steps_sync_pool ((blkPl_368).base + 60#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv0''
    by_cases hep : epochSecret.epoch = self.currentEpoch + 1#64
    · have hok_eq := chain_addEpoch_eq_ok hkdf hovf hep
      have hfits_all :
          FitsEvents M lim st
            (chainAddEpochEvents ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, esPin, self, epochSecret⟩) := by
        refine hfits_env _ ?_
        dsimp only [ChainAddEpochEnv]
        rw [hok_eq]
      let evs_nr : List AllocEvent :=
        if G.nextRoot.cap = 0#64 then [] else rustDeallocEvents G.nextRoot.cap.toNat 1
      let evs_grow : List AllocEvent :=
        if self.links.length = G.linksCap.toNat then vecDequeGrowEvents G.linksCap else []
      let evs_es : List AllocEvent :=
        if esPin.cap = 0#64 then [] else rustDeallocEvents esPin.cap.toNat 1
      let st1 := M.stepEvents (rustAllocEvents 32 1) st
      let st2 := M.stepEvents evs_nr st1
      let st3 := M.stepEvents (rustAllocEvents 72 1) st2
      let st4 := M.stepEvents (rustAllocEvents 32 1) st3
      let st5 := M.stepEvents (rustAllocEvents 72 1) st4
      let st6 := M.stepEvents (rustAllocEvents 32 1) st5
      let st7 := M.stepEvents evs_grow st6
      let st8 := M.stepEvents evs_es st7
      have hfits_split := hfits_all
      simp only [chainAddEpochEvents, List.append_assoc, fitsEvents_append] at hfits_split
      rcases hfits_split with
        ⟨hfits_a1, hfits_nr, hfits_a2, hfits_a3, hfits_a4, hfits_a5, hfits_grow, hfits_es⟩
      have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = false := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = true := by simp [hep]
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 164#64) hinv0'' ?_
      apply SepWP.seq_lsCallInv (mid := lsmpl.base 379) hinv0''
      wp_steps_sync_pool (lsmpl.base 379)
      refine SepWP.fold (cells12_192_entails_memRegion_96 s0.sp 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      have ⟨hF1, hsym1⟩ := hinv1
      wp_call hhkdf
        (⟨false, G.nextRoot.ptr, self.nextRoot,
          false, esPin.ptr, epochSecret.secret,
          true, lsρ "spqr:.rodata..Lanon.175", chainAddEpochInfo,
          s0.sp - 192#64, 96⟩ : HkdfToSliceGhost)
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      have hstack_sf : stackAt (s0.sp - 192#64) extHookStack = stackAt sf.sp extHookStack := by
        rw [‹sf.sp = s0.sp - 192#64›]
      refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
      wp_call hshim ()
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [‹sf_1.sp = sf.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      wp_call halloc_nooom (32, 1, st)
      have hoom1_64 : sf_2.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
      obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        hokm_all, hokm_root, hokm_a2b, hokm_b2a⟩ :=
        exists_unpack64_of_length_96_split
          ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
      refine SepWP.fold (Entails.of_eq (hokm_sp_reframe_addEpoch s0.sp hokm_all self.dir)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_2.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
      sep_elim_exists
      wp_steps_sync_pool ((blkPl_368).base + 164#64)
      refine SepWP.fold (Entails.of_eq (hokm_root (sf_2.readReg64 (.gpr 0#5))).symm) (by sep_focus) ?_
      have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
        rw [‹sf_2.sp = sf_1.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
      have hacp_0 : AllocCallPreserved s0 sf := by
        have h := ‹AllocCallPreserved _ sf›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
      have hacp_1 : AllocCallPreserved sf sf_1 := by
        have h := ‹AllocCallPreserved _ sf_1›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
      have hacp_2 : AllocCallPreserved sf_1 sf_2 := by
        have h := ‹AllocCallPreserved _ sf_2›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
      have hacp_02 : AllocCallPreserved s0 sf_2 :=
        allocCallPreserved_trans (allocCallPreserved_trans hacp_0 hacp_1) hacp_2
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      refine SepWP.join_lsCallInv_acp (join_pc := (blkPl_368).base + 180#64)
        (P_join := fun sm =>
          ((lsρ "spqr:.rodata..Lanon.175") ↦ᵣ chainAddEpochInfo) ∗
          ((s0.sp - 192#64) ↦₆₄ w0) ∗ ((s0.sp - 184#64) ↦₆₄ w1) ∗
          ((s0.sp - 176#64) ↦₆₄ w2) ∗ ((s0.sp - 168#64) ↦₆₄ w3) ∗
          cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
          calleeSavedStackAt s0 v15 ∗
          (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗
          ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
          ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ G.linksHead) ∗
          ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
          vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
            G.linksCap G.linksPtr G.linksHead (G.epochs.zip self.links) ∗
          ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ G.nextRoot.cap) ∗
          ((s0.readReg64 (.gpr 0#5) + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
          ((s0.readReg64 (.gpr 0#5) + 48#64) ↦₆₄ BitVec.ofNat 64 self.nextRoot.length) ∗
          ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) ∗
          ((s0.readReg64 (.gpr 0#5) + 80#64) ↦₃₂ self.dir.toI32) ∗
          chainUntouchedAt (s0.readReg64 (.gpr 0#5)) self ∗
          (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
          ((s0.readReg64 (.gpr 1#5) + 8#64) ↦₆₄ esPin.ptr) ∗
          ((s0.readReg64 (.gpr 1#5) + 16#64) ↦₆₄ BitVec.ofNat 64 epochSecret.secret.length) ∗
          ((s0.readReg64 (.gpr 1#5) + 24#64) ↦₆₄ epochSecret.epoch) ∗
          (esPin.ptr ↦ₛ epochSecret.secret) ∗
          vecU8Rest A.repAlloc esPin.cap esPin.ptr epochSecret.secret.length ∗
          A.live (sf_2.readReg64 (.gpr 0#5)) 32 1 ∗
          (sf_2.readReg64 (.gpr 0#5) ↦ₛ (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96).take 32) ∗
          A.pool lim st2 sm ∗ stackAt sf_2.sp extHookStack)
        hinv4 ?_ ?_
      · by_cases hnr_cap : G.nextRoot.cap = 0#64
        · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = true := by simp [hnr_cap]
          wp_norm_hyp hnr_cap_beq
          refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc G.nextRoot.ptr hnr_cap hnr_le)) (by sep_focus) ?_
          wp_steps_sync_pool ((blkPl_368).base + 180#64)
          have hst2_eq : st2 = st1 := by
            simp only [st2, evs_nr, hnr_cap, ite_true, AllocCostModel.stepEvents_nil]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by wp_norm_goal,
            by unfold AllocCallPreserved; wp_norm_goal, ?_⟩
          rw [hst2_eq]
          simp only [wp_norm, arm64_norm]
          sep_frame
        · have hnr_cap_beq : (G.nextRoot.cap == 0#64) = false := beq_false_of_ne hnr_cap
          wp_norm_hyp hnr_cap_beq
          refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc G.nextRoot.ptr hnr_cap hnr_le hnr_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hnr_layout
          have ⟨hnr_pos, _, hnr_isize⟩ := hnr_layout
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          wp_call hdealloc (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1, st1)
          have hst2_eq : st2 = M.stepEvents (rustDeallocEvents G.nextRoot.cap.toNat 1) st1 := by
            simp only [st2, evs_nr, hnr_cap, ite_false]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal,
            by have h := ‹AllocCallPreserved _ _›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h, ?_⟩
          rw [← hst2_eq]
          simp only [wp_norm, arm64_norm]
          sep_frame
      · intro sf_nr hpc_nr hrun_nr hsp_nr hcs_nr hinv_nr
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        intro hacp_nr_raw
        have hacp_nr : AllocCallPreserved sf_2 sf_nr := by
          unfold AllocCallPreserved at hacp_nr_raw ⊢; simpa only [wp_norm, arm64_norm] using hacp_nr_raw
        have hacp_0_nr : AllocCallPreserved s0 sf_nr := allocCallPreserved_trans hacp_02 hacp_nr
        wp_split_join hsp_nr hcs_nr
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 344#64) hinv_nr ?_
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
        (conv => arg 4; simp only [← RustCliAllocBudget.repAlloc_live])
        refine SepWP.fold (Entails.of_eq (addEpochMidFramePlaced_def hkdf A.repAlloc s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret)) (by sep_focus) ?_
        have hstack_nr : stackAt sf_2.sp extHookStack = stackAt sf_nr.sp extHookStack := by
          rw [‹sf_nr.sp = sf_2.sp›]
        refine SepWP.fold (Entails.of_eq hstack_nr) (by sep_focus) ?_
        wp_call hshim ()
        refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        have hstack_sf3 : stackAt sf_nr.sp extHookStack = stackAt sf_3.sp extHookStack := by
          rw [‹sf_3.sp = sf_nr.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
        wp_call halloc_nooom (72, 1, st2)
        have hoom2_64 : sf_4.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
        have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by
          rw [‹sf_4.sp = sf_3.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
        wp_call hshim ()
        refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
          rw [‹sf_5.sp = sf_4.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
        wp_call halloc_nooom (32, 1, st3)
        have hoom3_64 : sf_6.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        sep_elim_exists
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
        refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir (sf_6.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
        have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
          rw [‹sf_6.sp = sf_5.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
        wp_call hshim ()
        refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        have hstack_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by
          rw [‹sf_7.sp = sf_6.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
        wp_call halloc_nooom (72, 1, st4)
        have hoom4_64 : sf_8.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
        have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
          rw [‹sf_8.sp = sf_7.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
        wp_call hshim ()
        refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
        wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        have hstack_sf9 : stackAt sf_8.sp extHookStack = stackAt sf_9.sp extHookStack := by
          rw [‹sf_9.sp = sf_8.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
        wp_call halloc_nooom (32, 1, st5)
        have hoom5_64 : sf_10.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        sep_elim_exists
        wp_steps_sync_pool ((blkPl_368).base + 344#64)
        refine SepWP.fold (Entails.of_eq (cedCells_eq_pointsToBytes hokm_a2b hokm_b2a self.dir.switch (sf_10.readReg64 (.gpr 0#5)))) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir)) (by sep_focus) ?_
        have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
          rw [‹sf_10.sp = sf_9.sp›]
        refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
        have hacp_3 : AllocCallPreserved sf_nr sf_3 := by
          have h := ‹AllocCallPreserved _ sf_3›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_4 : AllocCallPreserved sf_3 sf_4 := by
          have h := ‹AllocCallPreserved _ sf_4›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_5 : AllocCallPreserved sf_4 sf_5 := by
          have h := ‹AllocCallPreserved _ sf_5›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_6 : AllocCallPreserved sf_5 sf_6 := by
          have h := ‹AllocCallPreserved _ sf_6›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_7 : AllocCallPreserved sf_6 sf_7 := by
          have h := ‹AllocCallPreserved _ sf_7›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_8 : AllocCallPreserved sf_7 sf_8 := by
          have h := ‹AllocCallPreserved _ sf_8›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_9 : AllocCallPreserved sf_8 sf_9 := by
          have h := ‹AllocCallPreserved _ sf_9›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_10 : AllocCallPreserved sf_9 sf_10 := by
          have h := ‹AllocCallPreserved _ sf_10›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
        have hacp_0_10 : AllocCallPreserved s0 sf_10 :=
          allocCallPreserved_trans hacp_0_nr
            (allocCallPreserved_trans
              (allocCallPreserved_trans
                (allocCallPreserved_trans hacp_3 hacp_4)
                (allocCallPreserved_trans hacp_5 hacp_6))
              (allocCallPreserved_trans
                (allocCallPreserved_trans hacp_7 hacp_8)
                (allocCallPreserved_trans hacp_9 hacp_10)))
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv13
        let cap1 : BitVec 64 :=
          if self.links.length = G.linksCap.toNat then newCapChainEpoch G.linksCap else G.linksCap
        have hlen_lt_cap1 : self.links.length < cap1.toNat := by
          dsimp only [cap1]
          split_ifs with heq
          · exact len_lt_newCapChainEpoch heq (Or.resolve_left hheadroom (by omega))
          · omega
        refine SepWPp.join_at_348_lsCallInv_acp (join_pc := (blkPl_368).base + 348#64) (cap1 := cap1)
          (P_join := fun sm =>
            ∃∗ ptr1 : BitVec 64, ∃∗ head1 : BitVec 64,
              addEpochMidFramePlaced hkdf A.repAlloc s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret ∗
              cedStackBothAt s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir ∗
              (s0.readReg64 (.gpr 0#5) ↦₆₄ cap1) ∗
              ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ ptr1) ∗
              ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ head1) ∗
              ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
              vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
                cap1 ptr1 head1 (G.epochs.zip self.links) ∗
              (s0.readReg64 (.gpr 1#5) ↦₆₄ esPin.cap) ∗
              A.live (sf_4.readReg64 (.gpr 0#5)) 72 1 ∗
              memRegion (sf_4.readReg64 (.gpr 0#5)) 72 ∗
              A.live (sf_6.readReg64 (.gpr 0#5)) 32 1 ∗
              (sf_6.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir).next) ∗
              A.live (sf_8.readReg64 (.gpr 0#5)) 72 1 ∗
              memRegion (sf_8.readReg64 (.gpr 0#5)) 72 ∗
              A.live (sf_10.readReg64 (.gpr 0#5)) 32 1 ∗
              (sf_10.readReg64 (.gpr 0#5) ↦ₛ (Chain.cedForDirection (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) self.dir.switch).next) ∗
              A.pool lim st7 sm ∗ stackAt sf_10.sp extHookStack)
          hinv13 ?_ ?_
        · by_cases heq_cap : self.links.length = G.linksCap.toNat
          · have hcap1_eq : cap1 = newCapChainEpoch G.linksCap := by simp [cap1, heq_cap]
            have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = true := by
              rw [heq_cap]; simp
            wp_norm_hyp hcmp_eq
            have hgrow_ok : max (2 * G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 :=
              Or.resolve_left hheadroom (by omega)
            have hzip_eq : (G.epochs.zip self.links).length = G.linksCap.toNat := by
              simp [hlen_eq, heq_cap]
            let x_grow : VecDequeGrowGhost :=
              ⟨s0.readReg64 (.gpr 0#5), G.linksCap, G.linksPtr, G.linksHead, G.epochs.zip self.links⟩
            have hfits_grow_env : FitsEnv M lim st6 (VecDequeGrowEnv x_grow) := by
              intro evs hevs
              rw [hevs]
              simpa only [VecDequeGrowEnv, x_grow, evs_grow, heq_cap, ite_true] using hfits_grow
            refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 353) hinv13 ?_
            refine SepWP.fold (vecDequeAt_fold_addEpoch A.repAlloc (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr G.linksHead G self hlen_eq) (by sep_focus) ?_
            wp_steps_sync_pool (lsmpl.base 353)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hinv14
            change subroutine_ok _ _ (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) at hgrow
            apply (SepWPp.call_allowPanic_lsCallInv_mid hgrow (x := (x_grow, st6)) hinv14)
            · wp_norm_goal
            · wp_norm_lhs
            · wp_norm_goal
            · wp_norm_lhs
            · intro R' hmR'
              rw [← sepConj_assoc]
              dsimp only [vecDequeGrowSpec, x_grow, st6]
              refine Satisfies.mono (sepConj_mono_left ?_) hmR'
              simp only [wp_norm, arm64_norm]
              refine Entails.pure_right ⟨hzip_eq, hgrow_ok, hfits_grow_env⟩ ?_
              sep_frame
            · intro _; dsimp only [vecDequeGrowSpec]; exact Entails.pure_left False.elim
            · dsimp only [vecDequeGrowSpec]; exact ⟨fun _ _ => rfl, fun _ => rfl⟩
            intro sf_grow hpc_grow hrun_grow hsp_grow hcs_grow _hF_grow
            dsimp only [vecDequeGrowSpec, x_grow]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWPp.exists_elim; intro evs_g
            apply SepWPp.exists_elim; intro ptr_g
            apply SepWPp.exists_elim; intro head_g
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            rintro ⟨htrace_grow, hacp_grow, hevs_g⟩
            have hevs_g_eq : evs_g = evs_grow := by
              rw [hevs_g]
              simp only [VecDequeGrowEnv, x_grow, evs_grow, heq_cap, ite_true]
            subst hevs_g_eq
            refine SepWPp.pure_left_focus _ (by sep_focus) ?_
            intro _hhead_imp
            wp_split_join hsp_grow hcs_grow
            wp_norm_hyp hpc_grow
            wp_norm_hyp htrace_grow
            apply SepWPp.of_sepWP_ret
            refine SepWP.unfold_vecDeque_bind A.repAlloc (s0.readReg64 (.gpr 0#5)) (newCapChainEpoch G.linksCap) G self hlen_eq (by sep_focus) ?_
            intro ptr1 head1
            wp_steps_sync_pool ((blkPl_368).base + 348#64)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal,
              by unfold AllocCallPreserved at hacp_grow ⊢; simpa only [wp_norm, arm64_norm] using hacp_grow, ?_⟩
            rw [hcap1_eq]
            dsimp only [st7]
            simp only [wp_norm, arm64_norm]
            refine Entails.sepExists_right ptr1 (Entails.sepExists_right head1 ?_)
            sep_frame
          · have hcap1_eq : cap1 = G.linksCap := by simp [cap1, heq_cap]
            have hcmp_ne : BitVec.ofNat 64 self.links.length ≠ G.linksCap :=
              ofNat_len_ne_cap (by omega)
            have hcmp_eq : (BitVec.ofNat 64 self.links.length == G.linksCap) = false :=
              beq_false_of_ne hcmp_ne
            have hcmp_sub := sub_eq_zero_false_of_ne hcmp_ne
            have hcmp_add := add_neg_eq_zero_false_of_ne hcmp_ne
            wp_norm_hyp hcmp_eq
            wp_norm_hyp hcmp_sub
            wp_norm_hyp hcmp_add
            apply SepWPp.of_sepWP_ret
            wp_steps_sync_pool ((blkPl_368).base + 348#64)
            have hst7_eq : st7 = st6 := by
              simp only [st7, evs_grow, heq_cap, ite_false, AllocCostModel.stepEvents_nil]
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨by wp_norm_goal, by wp_norm_goal, by rw [hcap1_eq]; wp_norm_goal,
              by unfold AllocCallPreserved; wp_norm_goal, ?_⟩
            rw [hcap1_eq, hst7_eq]
            dsimp only [st6]
            simp only [wp_norm, arm64_norm]
            refine Entails.sepExists_right G.linksPtr (Entails.sepExists_right G.linksHead ?_)
            sep_frame
        · intro sf_348 hpc_348 hrun_348 hsp_348 hreg_348 hcap_348 hinv_348
          refine SepWPp.pure_left_focus _ (by sep_focus) ?_
          intro hacp_348_raw
          have hacp_348 : AllocCallPreserved sf_10 sf_348 := by
            unfold AllocCallPreserved at hacp_348_raw ⊢; simpa only [wp_norm, arm64_norm] using hacp_348_raw
          have hacp_0_348 : AllocCallPreserved s0 sf_348 :=
            allocCallPreserved_trans hacp_0_10 hacp_348
          have htr_348 : sf_348.trace = s0.trace := hacp_0_348.2.1
          apply SepWPp.exists_elim; intro ptr1
          apply SepWPp.exists_elim; intro head1
          wp_split_join hsp_348 hreg_348
          wp_norm_hyp hcap_348
          wp_norm_hyp htr_348
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_368).base + 428#64) hinv_348 ?_
          refine SepWP.fold (vecDequeRingBuf_split_madd_links A.repAlloc cap1 ptr1 head1 G self hlen_eq hlen_lt_cap1) (by sep_focus) ?_
          sep_elim_exists
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          rintro ⟨hhead1, hcap1_lt, hptr1⟩
          wp_steps_sync_pool ((blkPl_368).base + 428#64)
          have hmadd_eq := physIdx_madd_eq (ptr := ptr1) hhead1 hlen_lt_cap1 hcap1_lt
          let slotPtr := ptr1 + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat cap1.toNat self.links.length * 112)
          (conv => arg 4; simp only [← RustCliAllocBudget.repAlloc_live])
          refine SepWP.fold (chainEpochDirectionAt_madd_send_intro A.repAlloc _ slotPtr
            (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5)) hmadd_eq
            ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
            self.dir hoom3_64 hoom2_64) (by sep_focus) ?_
          refine SepWP.fold (chainEpochDirectionAt_madd_recv_intro A.repAlloc _ slotPtr
            (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) hmadd_eq
            ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
            self.dir.switch hoom5_64 hoom4_64) (by sep_focus) ?_
          have hlen_add1 := ofNat_len_add_one hlen_lt_cap1 hcap1_lt
          have hlen_cell :
              ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ (BitVec.ofNat 64 self.links.length + 1#64)) =
              ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 (self.links.length + 1)) := by
            rw [hlen_add1]
          refine SepWP.fold (Entails.of_eq hlen_cell) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (addEpochMidFramePlaced_def hkdf A.repAlloc s0 v15 w0 w1 w2 w3 (sf_2.readReg64 (.gpr 0#5)) esPin self epochSecret).symm) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (calleeSavedStackAt_def s0 v15).symm) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (cedStackBothAt_def s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
          have hep_cell :
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ (self.currentEpoch + 1#64)) =
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ epochSecret.epoch) := by
            rw [hep]
          refine SepWP.fold (Entails.of_eq hep_cell) (by sep_focus) ?_
          have hchain_intro := chainRepr_addEpoch_intro A.repAlloc hkdf
            (s0.readReg64 (.gpr 0#5)) cap1 ptr1 head1
            (sf_2.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_4.readReg64 (.gpr 0#5))
            (sf_10.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5))
            G self epochSecret hlen_eq hlen_lt_cap1 hhead1 hcap1_lt hptr1 hoom1_64
            ‹List.length (hkdf self.nextRoot epochSecret.secret chainAddEpochInfo 96) = 96›
          dsimp only [] at hchain_intro
          refine SepWP.fold hchain_intro (by sep_focus) ?_
          refine SepWP.fold (cells4_entails_memRegion_32 (s0.readReg64 (.gpr 1#5))
            esPin.cap esPin.ptr (BitVec.ofNat 64 epochSecret.secret.length) epochSecret.epoch)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (cedCells_reframe_addEpoch s0.sp w4 w5 w6 w7 w8 w9 w10 w11 self.dir).symm) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hinv15
          have hst8_final :
              st8 = M.stepEvents
                (chainAddEpochEvents ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, esPin, self, epochSecret⟩)
                st := by
            simp only [st8, st7, st6, st5, st4, st3, st2, st1, evs_es, evs_grow, evs_nr,
              ← AllocCostModel.stepEvents_append, chainAddEpochEvents, List.append_assoc]
          by_cases hes_cap : esPin.cap = 0#64
          · have hes_cap_beq : (esPin.cap == 0#64) = true := by simp [hes_cap]
            wp_norm_hyp hes_cap_beq
            apply SepWPp.of_sepWP_ret
            refine SepWP.fold (Entails.of_eq (vecU8Rest_eq_zero A.repAlloc esPin.ptr hes_cap hes_le)) (by sep_focus) ?_
            wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
            have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
              rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
            refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
            refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
              w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
              (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
              (s0.readReg64 (.gpr 27#5)) v15
              (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
              (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
              (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
              (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
              (by sep_focus) ?_
            have hst7_8 : st7 = st8 := by
              simp only [st8, evs_es, hes_cap, ite_true, AllocCostModel.stepEvents_nil]
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨?_, by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal⟩
            intro hmR
            dsimp only [chainAddEpochPostConcrete, chainAddEpochSpecX]
            rw [hok_eq]
            dsimp only
            refine Satisfies.mono (sepConj_mono_left ?_) hmR
            rw [hst7_8, hst8_final]
            rw [sepConj_left_comm (lsρ "spqr:.rodata..Lanon.175" ↦ᵣ chainAddEpochInfo)]
            refine Entails.pure_right
              ⟨by wp_norm_goal, by unfold AllocCallPreserved at hacp_0_348 ⊢; simpa only [wp_norm, arm64_norm] using hacp_0_348⟩ ?_
            exact Entails.of_eq (by sep_ac_rfl)
          · have hes_cap_beq : (esPin.cap == 0#64) = false := beq_false_of_ne hes_cap
            wp_norm_hyp hes_cap_beq
            apply SepWPp.of_sepWP_ret
            refine SepWP.fold (vecU8Rest_nonzero_entails A.repAlloc esPin.ptr hes_cap hes_le hes_lt) (by sep_focus) ?_
            refine SepWP.pure_left_focus _ (by sep_focus) ?_
            intro hes_layout
            have ⟨hes_pos, _, hes_isize⟩ := hes_layout
            wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
            have hstack_348 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 192#64) extHookStack := by
              rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sf_8.sp›, ‹sf_8.sp = sf_7.sp›,
                ‹sf_7.sp = sf_6.sp›, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›,
                ‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_nr.sp›, ‹sf_nr.sp = sf_2.sp›,
                ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 192#64›]
            refine SepWP.fold (Entails.of_eq hstack_348) (by sep_focus) ?_
            refine SepWP.fold (rejoin_stack_chainAddEpochX s0.sp
              w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
              (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
              (s0.readReg64 (.gpr 27#5)) v15
              (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5))
              (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
              (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5))
              (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp)) (by sep_focus) ?_
            wp_call hdealloc (esPin.ptr, esPin.cap.toNat, 1, st7)
            refine SepWP.fold (Entails.of_eq (stackAt_chainAddEpochX_top_split s0.sp).symm) (by sep_focus) ?_
            have hacp_es : AllocCallPreserved sf_348 sf_11 := by
              have h := ‹AllocCallPreserved _ sf_11›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
            have hacp_0_11 : AllocCallPreserved s0 sf_11 :=
              allocCallPreserved_trans hacp_0_348 hacp_es
            have htr_11 : sf_11.trace = s0.trace := hacp_0_11.2.1
            wp_norm_hyp htr_11
            have hst8_dealloc :
                M.stepEvents (rustDeallocEvents esPin.cap.toNat 1) st7 = st8 := by
              simp only [st8, evs_es, hes_cap, ite_false]
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            refine ⟨?_, by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal⟩
            intro hmR
            dsimp only [chainAddEpochPostConcrete, chainAddEpochSpecX]
            rw [hok_eq]
            dsimp only
            refine Satisfies.mono (sepConj_mono_left ?_) hmR
            rw [hst8_dealloc, hst8_final]
            rw [sepConj_left_comm (lsρ "spqr:.rodata..Lanon.175" ↦ᵣ chainAddEpochInfo)]
            refine Entails.pure_right
              ⟨by wp_norm_goal, by unfold AllocCallPreserved at hacp_0_11 ⊢; simpa only [wp_norm, arm64_norm] using hacp_0_11⟩ ?_
            exact Entails.of_eq (by sep_ac_rfl)
    · have herr := isOk_addEpoch_false_of_epoch_ne hkdf self epochSecret hovf hep
      have hep_bne : (epochSecret.epoch != self.currentEpoch + 1#64) = true := by simp [hep]
      have hep_beq : (epochSecret.epoch == self.currentEpoch + 1#64) = false := beq_false_of_ne hep
      have hep_sub := sub_eq_zero_false_of_ne hep
      have hep_add := add_neg_eq_zero_false_of_ne hep
      wp_norm_hyp hep_bne
      wp_norm_hyp hep_beq
      wp_norm_hyp hep_sub
      wp_norm_hyp hep_add
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic")
      wp_steps_sync_pool (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic")
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_core) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_addEpochBudget_err herr (by simp only [Rust.panicked, arm64_norm]) hm

/-- Relocatable `<spqr::chain::Chain>::add_epoch` (Block `368`) meets
`ChainAddEpochPlacedOkX hkdf M A lim H`, lifting plain/codeLoaded callee specs to `withLsCallInv`. -/
theorem chainAddEpoch_placed_ok [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379) (withAllocVmPreserved (hkdfToSliceSpqrSpec hkdf)))
    (hgrow : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353) (withLsCodeLoaded lsmpl (vecDequeGrowSpec M A lim)))
    (hshim : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack))
    (hpan_ovf : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") =
        some Rust.panicked)
    (hpan_core : ((blkPC_368).rebase (blkPl_368).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    ChainAddEpochPlacedOkX hkdf M A lim H :=
  chainAddEpoch_placed_ok_of_contracts_x
    (subroutine_ok_withLsCallInv_of_plain hhkdf)
    (subroutine_ok_withLsCallInv_of_withLsCodeLoaded hgrow)
    hshim halloc hdealloc hpan_ovf hpan_core

end LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochBudget
