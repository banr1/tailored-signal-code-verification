/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `spqr::send::<signal_session_ratchet::Coins>` Encoded Length & Allocation (Block `427`)

Threads `RustCliAllocBudget` and `VmPreserved` through `PqRatchetState` encoded-length
computation and output `Vec::with_capacity` allocation (`+4288..+4996`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427 blkPl_427_ρ ls_resolve_rel_427_blk_484 ls_resolve_rel_427_blk_485)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym
   spqr_externAt?_of_mem spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv VRegsAt bv_optChain_some_eq bv_optInner_some_eq
   calleeSavedPreserved_writeLr_setPC chainPBEncodedLen_lt_of_state
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainCap optChainPBFieldEncodedLen optChainPBPinnedAt_eq optChainRest
   optChainRest_cap_bounds optPqRatchetInnerCap optPqRatchetInnerPBFieldEncodedLen
   optPqRatchetInnerPBPinnedAt optPqRatchetInnerPBPinnedAt_cap_bounds
   optPqRatchetInnerPBPinnedAt_eq optVersionNegCap optVersionNegRest
   optVersionNegRest_cap_bounds optVersionNegotiationPBFieldEncodedLen
   optVersionNegotiationPBPinnedAt_eq pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   subroutine_ok_withStepInv v1StatePBEncodedLen_lt_of_state vecU8At_empty_of_alloc
   versionNegotiationRest vn_authKey_len_lt_of_state withStepInv)
open CryptoVerification.SpqrV1.ProtoRepr
  (ChainEncodedLenPinnedGhost PinnedEncLenGhost VersionNegotiationPBGhost
   chainPBEncodedLen optChainPBPinnedAt optVersionNegotiationPBPinnedAt
   v1StateEncodedLenStack v1StateJumpTableBytes varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendCalleeStack stackAt_spqrSendCallee_split_enc)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.IfaceLemmas (subroutine_ok_frame_oom')
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget
  (step_vn_len_authKey_3191c_vregs_placed
   step_vn_len_chainParams_319a0_vregs_placed
   step_vn_len_combine_31ad4_vregs_placed
   step_vn_len_dir_31940_vregs_placed
   step_vn_len_minVer_31974_vregs_placed
   step_vn_len_none_31968_vregs_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWPp_call_cs_noPanic sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget
  (spqrSendRustAllocNoOomStackSpec spqrSendRustAllocStackSpec spqrSendShimStackSpec
   subroutine_ok_spqrSendRustAllocNoOomStackSpec subroutine_ok_spqrSendRustAllocStackSpec
   subroutine_ok_spqrSendShimStackSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)

variable [LibsignalPlacement]

private theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Budget-Threaded Callee Contract Helpers for `spqr::send` (Block `427`) -/

/-- `VmPreserved`-equipped no-op shim contract at `s.sp` with `spqrSendCalleeStack`, matching
`AllocContractsPlaced.shim` (`sessionShimBudgetSpec`) so `A.pool` transports across the call. -/
def spqrSendShimVmStackSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp spqrSendCalleeStack
  post := fun _ s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ stackAt s0.sp spqrSendCalleeStack

theorem spqrSend_handle_alloc_error_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem spqrSend_shim_ok_enc_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimVmStackSpec) := by
  have hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      sessionShimBudgetSpec :=
    spqr_hook_ok_of_mem hA.shim
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_frame_oom' (fun _ s => stackAt s.sp spqrSendCalleeStack) hshim ?_ ?_
  · intro _ s
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, spqrSendShimVmStackSpec]
    rw [emp_sepConj]
    exact Entails.refl _
  · intro _ s sf
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, spqrSendShimVmStackSpec]
    rw [sepConj_assoc]
    refine Entails.pure_left fun hvm => Entails.pure_left fun htr => ?_
    exact Entails.pure_right ⟨hvm, htr⟩ (Entails.refl _)

theorem subroutine_ok_spqrSendShimVm_of_shimStack {prog : Program} {entry : BitVec 64}
    {s0 : State}
    (h : subroutine_ok prog entry (withStepInv s0 spqrSendShimStackSpec)) :
    subroutine_ok prog entry (withStepInv s0 spqrSendShimVmStackSpec) := by
  refine subroutine_ok_mono h (fun _ _ _ hpre => hpre) fun _ _ _ _ hpost => ?_
  dsimp only [withStepInv, spqrSendShimStackSpec, spqrSendShimVmStackSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.2.2, hpost.1.1⟩, hpost.2⟩

theorem spqrSend_shim_ok_enc_placed_of_vm {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimStackSpec) :=
  subroutine_ok_withStepInv s0 (subroutine_ok_spqrSendShimStackSpec (spqr_hook_ok_of_mem hshim))

theorem spqrSend_rustAlloc_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocStackSpec M A lim)) :=
  subroutine_ok_withStepInv s0
    (subroutine_ok_spqrSendRustAllocStackSpec (spqr_hook_ok_of_mem hA.alloc))

theorem spqrSend_rustAllocNoOom_ok_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    (s0 : State) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocNoOomStackSpec M A lim)) :=
  subroutine_ok_withStepInv s0
    (subroutine_ok_spqrSendRustAllocNoOomStackSpec (spqr_hook_ok_of_mem hA.alloc))

/-! ## 2. Combined `Option<VersionNegotiation>::encoded_len` (`+4288/+4364 -> +4768`) -/

/-- `spqrSendPlacedEntry + 4288#64 -> spqrSendPlacedEntry + 4768#64` (with `VmPreserved` and `VRegsAt`):
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn))` from
`versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn`. -/
theorem step_vn_len_some_3191c_vregs_placed {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        VmPreserved s s' ∧ VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn ∗ F)) := by
  refine SepWP.seq
    (step_vn_len_authKey_3191c_vregs_placed (ext := ext) A s g vn F hpc hrun hsp_align hlen) ?_
  intro s1 P1 hpc1 _ ⟨hvm1, hv1, hrun1, hsp1, htr1, hx8_1, hx19_1, hx21_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp1, hP1⟩
  rw [← hsp1] at hP1
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq (step_vn_len_dir_31940_vregs_placed (ext := ext) A s1 g vn F hpc1 hrun1
    (by rw [hsp1]; exact hsp_align)) ?_
  intro s2 P2 hpc2 _ ⟨hvm2, hv2, hrun2, hsp2, htr2, hx8_2, hx9_2, hx19_2, hx21_2, hx22_2,
    hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp2, hP2⟩
  rw [← hsp2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq (step_vn_len_minVer_31974_vregs_placed (ext := ext) A s2 g vn F hpc2 hrun2
    (by rw [hsp2, hsp1]; exact hsp_align)) ?_
  intro s3 P3 hpc3 _ ⟨hvm3, hv3, hrun3, hsp3, htr3, hx8_3, hx9_3, hx10_3, hx19_3, hx21_3,
    hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp3, hP3⟩
  rw [← hsp3] at hP3
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.seq (step_vn_len_chainParams_319a0_vregs_placed (ext := ext) A s3 g vn F hpc3 hrun3
    (by rw [hsp3, hsp2, hsp1]; exact hsp_align)) ?_
  intro s4 P4 hpc4 _ ⟨hvm4, hv4, hrun4, hsp4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4,
    hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp4, hP4⟩
  have hsp3_eq : s3.sp = s.sp := hsp3.trans (hsp2.trans hsp1)
  rw [hsp3_eq] at hP4
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono
    (step_vn_len_combine_31ad4_vregs_placed (ext := ext) s4 vn
      (versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn ∗ F)
      hpc4 hrun4 (hx8_4.trans (hx8_3.trans (hx8_2.trans hx8_1)))
      (hx9_4.trans (hx9_3.trans hx9_2)) (hx10_4.trans hx10_3) hx11_4) ?_
  intro s5 P5 _ _ ⟨hvm5, hv5, hrun5, hsp5, htr5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp5, hP5⟩
  exact ⟨(((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5,
    ⟨hv5.eq.trans (hv4.eq.trans (hv3.eq.trans (hv2.eq.trans hv1.eq)))⟩,
    hrun5, hsp5.trans (hsp4.trans hsp3_eq),
    htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))),
    hx20_5,
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1))),
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1))),
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1))),
    hx24_5.trans (hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_1))),
    hx25_5.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_5.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1))),
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_1))),
    hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1))),
    hP5⟩

/-- `spqrSendPlacedEntry + 4288#64 -> spqrSendPlacedEntry + 4768#64`:
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn))` from
`versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn`. -/
theorem step_vn_len_some_3191c_placed {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' =>
        VmPreserved s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A.repAlloc g (s.sp + 4704#64) vn ∗ F)) :=
  SepWP.mono (step_vn_len_some_3191c_vregs_placed (ext := ext) A s g vn F hpc hrun hsp_align hlen)
    (fun _ _ _ _ ⟨hvm, _, h⟩ => ⟨hvm, h⟩)

/-- Unified `Option<VersionNegotiation>::encoded_len` (`+4288/+4364 -> +4768`, with `VmPreserved`
and `VRegsAt`):
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)`. -/
theorem step_vn_len_unified_vregs_placed {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (s : State) (g : PqRatchetStatePBGhost) (st : PqRatchetState) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)
      (fun s' P' =>
        VmPreserved s s' ∧ VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 =
          BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64)
          st.versionNegotiation ∗ F)) := by
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    exact step_vn_len_none_31968_vregs_placed (ext := ext) s
      (optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64) none ∗ F) hpc hrun
  | some vn =>
    rw [hvn] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have hlen_vn := vn_authKey_len_lt_of_state hvn hlen
    have hpre_eq :
        optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64) (some vn) ∗ F =
        versionNegotiationRest A.repAlloc g.vn (s.sp + 4704#64) vn ∗
          (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) := by
      rw [optVersionNegotiationPBPinnedAt_eq A.repAlloc g.vn (s.sp + 4704#64) (some vn)]
      dsimp only [optVersionNegRest]
      sep_ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    refine SepWP.mono (step_vn_len_some_3191c_vregs_placed (ext := ext) A s g.vn vn
      (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) hpc hrun hsp_align hlen_vn) ?_
    intro s' P' _ _ ⟨hvm', hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24',
      hx25', hx26', hx27', hx28', hfp', hP'⟩
    refine ⟨hvm', hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26',
      hx27', hx28', hfp', ?_⟩
    exact Entails.trans hP' (Entails.of_eq hpre_eq.symm)

/-- Unified `Option<VersionNegotiation>::encoded_len` (`+4288/+4364 -> +4768`):
Computes `x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)`. -/
theorem step_vn_len_unified_placed {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M)
    (s : State) (g : PqRatchetStatePBGhost) (st : PqRatchetState) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)
      (fun s' P' =>
        VmPreserved s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 =
          BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64)
          st.versionNegotiation ∗ F)) :=
  SepWP.mono (step_vn_len_unified_vregs_placed (ext := ext) A s g st F hpc hrun hsp_align hlen)
    (fun _ _ _ _ ⟨hvm, _, h⟩ => ⟨hvm, h⟩)

/-! ## 3. `Option<Chain>::encoded_len` (`+4768 -> +4844`) -/

/-- `spqrSendPlacedEntry + 4768#64 -> spqrSendPlacedEntry + 4844#64`:
Stores `x22` (`msg_cap`) to `[sp + 0x18]` (`sp + 24#64`), computes `Option<Chain>::encoded_len`
(calling `Chain::encoded_len [local#3]` at `lsmpl.base 485` when `st.chain = some ch`), sets
`x22 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation + optChainPBFieldEncodedLen st.chain)`,
and exposes `VmPreserved s1 s2` alongside `StepInv s0 s2`. -/
theorem step_send_chain_len_31afc_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (sp msg_cap v_sp18 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s1.pc = spqrSendPlacedEntry + 4768#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = sp) (htr : s1.trace = s0.trace)
    (hx20 : s1.readReg64 .x20 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = msg_cap)
    (hx24 : s1.readReg64 .x24 = sp + 4704#64)
    (hx25 : s1.readReg64 .x25 = optChainCap g.chain st.chain)
    (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((sp + 24#64) ↦₆₄ v_sp18) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s2 : State,
      s2.pc = spqrSendPlacedEntry + 4844#64 → s2.status = .Running → s2.sp = sp →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = s1.readReg64 .x19 →
      s2.readReg64 .x21 = s1.readReg64 .x21 →
      s2.readReg64 .x22 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain) →
      s2.readReg64 .x23 = s1.readReg64 .x23 →
      s2.readReg64 .x24 = sp + 4704#64 →
      s2.readReg64 .x25 = optChainCap g.chain st.chain →
      s2.readReg64 .x26 = s1.readReg64 .x26 →
      s2.readReg64 .x27 = s1.readReg64 .x27 →
      s2.readReg64 .x28 = s1.readReg64 .x28 →
      s2.readReg64 .fp = s1.readReg64 .fp →
      StepInv s0 s2 → VmPreserved s1 s2 →
      SepWPp (spqrSendPlacedProg ext) ret s2
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((sp + 24#64) ↦₆₄ msg_cap) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
     (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optChainPBPinnedAt_eq] at hm
      have hm' : s1.mem ⊨ optChainRest A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
          (optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
           (((sp + 4704#64) + 48#64) ↦₆₄ optChainCap g.chain st.chain) ∗
           optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 128#64) st.inner ∗
           ((sp + 24#64) ↦₆₄ v_sp18) ∗
           stackAt sp spqrSendCalleeStack ∗ F ∗ R') := by
        convert hm using 1; sep_ac_rfl
      exact optChainRest_cap_bounds hm')
    fun ⟨hch_eq, hch_ne⟩ => ?_
  cases hch : st.chain with
  | none =>
    rw [hch] at hch_eq hch_ne
    simp only [Option.isSome_none, Bool.not_false] at hch_eq hch_ne
    have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq (a := 0)
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen none)
      (by dsimp [optChainPBFieldEncodedLen])
      (by unfold pqRatchetStatePBEncodedLen at hlen; dsimp [optChainPBFieldEncodedLen]; omega)
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4844#64)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [hch]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv1.trans hinv.1) hinv.2)
  | some ch =>
    rw [hch] at hch_eq hch_ne
    simp only [Option.isSome_some, Bool.not_true] at hch_eq hch_ne
    have ⟨hfit, hopt_lt, hvar_lt⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hls := cmp_ls_false_of_lt hvar_lt hopt_lt
    have hult_ch : (BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 (chainPBEncodedLen ch)))).ult
        (BitVec.ofNat 64 (optChainPBFieldEncodedLen (some ch))) = true := by
      rw [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hopt_lt]
      exact hvar_lt
    have hopt_ch := bv_optChain_some_eq ch
    have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq
      (a := optChainPBFieldEncodedLen (some ch))
      (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)
      (c := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen (some ch))
      rfl
      (by unfold pqRatchetStatePBEncodedLen at hlen; rw [hch] at hlen; omega)
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 485)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr
        (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_485, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv_bl
      refine sepWPp_call_cs_noPanic (x := ChainEncodedLenPinnedGhost.mk ((sp + 4704#64) + 0x30#64) g.chain ch)
        (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
          optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 0x80#64) st.inner ∗
          ((sp + 24#64) ↦₆₄ msg_cap) ∗
          memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - 0x60) ∗ F)
        hChainLen
        (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_485])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
        (ret_pc := (blkPl_427).base + 4788#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
      · intro R' hm
        rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
          stackAt_spqrSendCallee_split_enc sp 0x60 (by decide)] at hm
        simp only [arm64_norm] at hm
        simp only [withStepInv, chainEncodedLenPinnedSpec, withVmPreserved,
          CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec, arm64_norm, hsp,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hinv1.trans hinv_bl.1, hfit⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
      · intro sf code R' _ hm; exact allowPanic_not_exited hm
      · intro sf R' _ hm
        simp only [withStepInv, chainEncodedLenPinnedSpec, withVmPreserved,
          CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec,
          sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro sf R' _ hm; exact allowPanic_not_exited hm
      · intro sm hpcm hrunm hspm hcsm hinv_call
        simp only [arm64_norm, hsp] at hspm
        dsimp only [withStepInv, chainEncodedLenPinnedSpec, withVmPreserved,
          CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec]
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun hvm_call => ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
        simp only [arm64_norm, htr] at htrm
        rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
        simp only [arm64_norm, hx20, hx22, hx24, hx25]
          at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4844#64)
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by rw [hch]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (((hinv1.trans hinv_bl.1).trans hinv_call).trans hinv_post.1)
              ((hinv_bl.2.trans hvm_call).trans hinv_post.2))
          rw [pqRatchetStatePBPinnedAt, hch, optChainPBPinnedAt,
            stackAt_spqrSendCallee_split_enc sp 0x60 (by decide)]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_chain_len_31afc_pool_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (sp msg_cap v_sp18 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s1.pc = spqrSendPlacedEntry + 4768#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = sp) (htr : s1.trace = s0.trace)
    (hx20 : s1.readReg64 .x20 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = msg_cap)
    (hx24 : s1.readReg64 .x24 = sp + 4704#64)
    (hx25 : s1.readReg64 .x25 = optChainCap g.chain st.chain)
    (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      A.pool lim st0 s1 ∗
      ((sp + 24#64) ↦₆₄ v_sp18) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s2 : State,
      s2.pc = spqrSendPlacedEntry + 4844#64 → s2.status = .Running → s2.sp = sp →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = s1.readReg64 .x19 →
      s2.readReg64 .x21 = s1.readReg64 .x21 →
      s2.readReg64 .x22 =
        BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain) →
      s2.readReg64 .x23 = s1.readReg64 .x23 →
      s2.readReg64 .x24 = sp + 4704#64 →
      s2.readReg64 .x25 = optChainCap g.chain st.chain →
      s2.readReg64 .x26 = s1.readReg64 .x26 →
      s2.readReg64 .x27 = s1.readReg64 .x27 →
      s2.readReg64 .x28 = s1.readReg64 .x28 →
      s2.readReg64 .fp = s1.readReg64 .fp →
      StepInv s0 s2 →
      SepWPp (spqrSendPlacedProg ext) ret s2
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          A.pool lim st0 s2 ∗
          ((sp + 24#64) ↦₆₄ msg_cap) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P Q Qp oom := by
  refine step_send_chain_len_31afc_placed A.repAlloc ext hChainLen sp msg_cap v_sp18 g st hlen halign
    (F := A.pool lim st0 s1 ∗ F)
    hpc hrun hsp htr hx20 hx22 hx24 hx25 hinv1 (by rw [hP]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 h19 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv2 hvm2
  have hpool : A.pool lim st0 s1 = A.pool lim st0 s2 := (A.pool_of_vmPreserved hvm2).symm
  refine SepWPp.weaken_pre
    (by rw [hpool]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext s2 hpc2 hrun2 hsp2 htr2 h19 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv2)

/-! ## 4. `Option<pq_ratchet_state::Inner>::encoded_len` (`+4844 -> +4920`) -/

/-- `spqrSendPlacedEntry + 4844#64 -> spqrSendPlacedEntry + 4920#64`:
Computes `Option<pq_ratchet_state::Inner>::encoded_len` (calling `v1::State::encoded_len [local#3]`
at `lsmpl.base 484` when `st.inner = some (.v1 v1s)`), sets
`x20 = optPqRatchetInnerCap g.inner st.inner` and
`x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)`, and exposes `VmPreserved s2 s3`
alongside `StepInv s0 s3`. -/
theorem step_send_inner_len_31b48_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    {s0 s2 : State} {v1JtAddr : BitVec 64}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A v1JtAddr)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64)
    (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp →
      s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 →
      s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 →
      s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 →
      s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp →
      StepInv s0 s3 → VmPreserved s2 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := (sp + 4704#64) + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
        (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt sp spqrSendCalleeStack ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4920#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv
        refine SepWPp.weaken_pre ?_
          (hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv2.trans hinv.1) hinv.2)
        rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
        exact Entails.of_eq (by sep_ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 484)
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr
            (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_484, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv_bl
          refine sepWPp_call_cs_noPanic
            (x := PinnedEncLenGhost.mk ((sp + 4704#64) + 0x80#64) g.inner v1s)
            (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
              optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
              memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
                (spqrSendCalleeStack - v1StateEncodedLenStack) ∗ F)
            hV1StateLen
            (by simp only [arm64_norm, blkPl_427_ρ, ls_resolve_rel_427_blk_484])
            (by simp only [arm64_norm, *])
            (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
            (ret_pc := (blkPl_427).base + 4872#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
          · intro R' hm
            rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner ((sp + 4704#64) + 0x80#64) (some (.v1 v1s)),
              optPqRatchetInnerPBPinnedAt,
              stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)] at hm
            simp only [arm64_norm] at hm
            simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
              CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp, hx24,
              sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hinv2.trans hinv_bl.1, hfit⟩, ?_⟩
            exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
          · intro sf code R' _ hm; exact allowPanic_not_exited hm
          · intro sf R' _ hm
            simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
              CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec,
              sepConj_assoc, satisfies_pure_sepConj] at hm
            exact hm.1.elim
          · intro sf R' _ hm; exact allowPanic_not_exited hm
          · intro sm hpcm hrunm hspm hcsm hinv_call
            simp only [arm64_norm, hsp] at hspm
            dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
              CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec]
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun hvm_call => ?_
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
            simp only [arm64_norm, htr] at htrm
            rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
            simp only [arm64_norm, hx22, hx24]
              at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4920#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv_post
              refine SepWPp.weaken_pre ?_
                (hnext _
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *])
                  (((hinv2.trans hinv_bl.1).trans hinv_call).trans hinv_post.1)
                  ((hinv_bl.2.trans hvm_call).trans hinv_post.2))
              rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
                stackAt_spqrSendCallee_split_enc sp v1StateEncodedLenStack (by decide)]
              simp only [arm64_norm, hsp]
              exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_inner_len_31b48_pool_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s2 : State} {v1JtAddr : BitVec 64}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc v1JtAddr)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64)
    (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
      A.pool lim st0 s2 ∗
      stackAt sp spqrSendCalleeStack) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp →
      s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 →
      s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 →
      s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 →
      s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp →
      StepInv s0 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          (v1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
          A.pool lim st0 s3 ∗
          stackAt sp spqrSendCalleeStack) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q Qp oom := by
  refine step_send_inner_len_31b48_placed A.repAlloc ext hV1StateLen sp g st hlen halign
    (F := A.pool lim st0 s2 ∗ F)
    hpc hrun hsp htr hx22 hx24 hinv2 (by rw [hP]; sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv3 hvm3
  have hpool : A.pool lim st0 s2 = A.pool lim st0 s3 := (A.pool_of_vmPreserved hvm3).symm
  refine SepWPp.weaken_pre
    (by rw [hpool]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext s3 hpc3 hrun3 hsp3 htr3 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv3)

/-! ## 5. `Vec::with_capacity` Allocation (`+4920 -> +4996 / +5604`) -/

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

/-- `spqrSendPlacedEntry + 4920#64 -> spqrSendPlacedEntry + 4996#64` or `spqrSendPlacedEntry + 5604#64`:
Under `FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1)`, allocates the output
buffer of capacity `pqRatchetStatePBEncodedLen st` via `__rust_alloc` without panic or OOM,
initializes `vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr []`,
advances `A.pool lim st0 s` to `A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm`,
stores `optChainCap g.chain st.chain` at `[sp + 16#64]`, and branches to `spqrSendPlacedEntry + 4996#64`
if `st.versionNegotiation.isSome`, or `spqrSendPlacedEntry + 5604#64` otherwise. -/
theorem step_send_alloc_31b94_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimVmStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocNoOomStackSpec M A lim)))
    (sp v_sp10 v_590 v_598 v_5a0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      A.pool lim st0 s ∗
      stackAt sp spqrSendCalleeStack ∗
      ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗
      ((sp + 1432#64) ↦₆₄ v_598) ∗
      ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
               else spqrSendPlacedEntry + 5604#64) →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = ptr →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have hbit63 := getLsbD_63_ofNat_eq_false hlen
  have helem63 := getElem_63_ofNat_eq_false hlen
  have hcbz_f := ofNat_beq_zero_false_of_pos hpos hlen
  refine sepWPp_extract_pure
    ((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
     (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optVersionNegotiationPBPinnedAt_eq] at hm
      have hm' : s.mem ⊨ optVersionNegRest A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
          (((sp + 4704#64) ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
           optChainPBPinnedAt A.repAlloc g.chain ((sp + 4704#64) + 48#64) st.chain ∗
           optPqRatchetInnerPBPinnedAt A.repAlloc g.inner ((sp + 4704#64) + 128#64) st.inner ∗
           A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
           ((sp + 16#64) ↦₆₄ v_sp10) ∗
           ((sp + 1424#64) ↦₆₄ v_590) ∗
           ((sp + 1432#64) ↦₆₄ v_598) ∗
           ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F ∗ R') := by
        convert hm using 1; sep_ac_rfl
      exact optVersionNegRest_cap_bounds hm')
    fun ⟨hvn_eq, hvn_ne⟩ => ?_
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsρ spqrRustNoAllocShimSym)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr
      (by simp only [arm64_norm, blkPl_427_ρ, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine sepWPp_call_cs_noPanic (x := ())
      (F := pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗ A.pool lim st0 s ∗
        ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗
        ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
      hshim (by simp only [arm64_norm, blkPl_427_ρ]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_427).base + 4952#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, spqrSendShimVmStackSpec, arm64_norm, hsp, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hinv0.trans hinv1.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    · intro sf code R' _ hm
      simp only [withStepInv, spqrSendShimVmStackSpec, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sf R' _ hm
      simp only [withStepInv, spqrSendShimVmStackSpec, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro sf R' _ hm
      simp only [withStepInv, spqrSendShimVmStackSpec, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro s1 hpcs1 hruns1 hsps1 hcss1 hinv_s1
      simp only [arm64_norm, hsp] at hsps1
      rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
      simp only [arm64_norm, hx24, hx25, hx26]
        at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
      dsimp only [withStepInv, spqrSendShimVmStackSpec]
      simp only [arm64_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hvm_s1, htrs1⟩ => ?_
      have htrs1' : s1.trace = s0.trace := htrs1.trans htr
      rw [← A.pool_of_vmPreserved (hinv1.2.trans hvm_s1)]
      apply sepWPp_of_sepWP_cs_vm (mid := lsρ spqrRustAllocSym)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr
          (by simp only [arm64_norm, blkPl_427_ρ, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        rw [← A.pool_of_vmPreserved hinv2.2]
        have htoNat_len :
            (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)).toNat =
              pqRatchetStatePBEncodedLen st := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine sepWPp_call_cs_noPanic (x := (pqRatchetStatePBEncodedLen st, st0))
          (F := pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
            ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
            ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗
            ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
          halloc (by simp only [arm64_norm, blkPl_427_ρ]) (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsps1, beq_iff_eq]; exact halign)
          (ret_pc := (blkPl_427).base + 4968#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
        · intro R' hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, spqrSendRustAllocNoOomStackSpec, arm64_norm, hsps1, htoNat_len,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨(hinv0.trans hinv1.1).trans (hinv_s1.trans hinv2.1), hpos, hlen, hfits, ?_⟩, ?_⟩
          · simp only [wp_norm, arm64_norm, blkPl_427]
            apply lsRetAddr624_blockPlacement_base_add <;> decide
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
        · intro sf code R' _ hm
          simp only [withStepInv, spqrSendRustAllocNoOomStackSpec, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sf R' _ hm
          simp only [withStepInv, spqrSendRustAllocNoOomStackSpec, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro sf R' _ hm
          simp only [withStepInv, spqrSendRustAllocNoOomStackSpec, satisfies_pure_sepConj] at hm
          exact hm.1.elim
        · intro s2 hpcs2 hruns2 hsps2 hcss2 hinv_s2
          simp only [arm64_norm, hsps1] at hsps2
          rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
          simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_26, hs1_27, hs1_28, hs1_fp]
            at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
          have hinv_s2' : StepInv s0 s2 :=
            ((hinv0.trans hinv1.1).trans (hinv_s1.trans hinv2.1)).trans hinv_s2
          dsimp only [withStepInv, spqrSendRustAllocNoOomStackSpec]
          simp only [arm64_norm, hsps1, sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨htrs2, _, hoom⟩ => ?_
          have hoom_f : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
          have htrs2' : s2.trace = s0.trace := htrs2.trans htrs1'
          cases hvn_case : st.versionNegotiation with
          | none =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 5604#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv3
              refine SepWPp.weaken_pre ?_
                (hnext _ (s2.readReg64 .x0)
                  (by rw [hvn_case]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3.1))
              rw [← A.pool_of_vmPreserved hinv3.2,
                ← vecU8At_empty_of_alloc A.repAlloc (sp + 1424#64) (s2.readReg64 .x0)
                  (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
              have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
              have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
              rw [h1432, h1440]
              dsimp only [RustCliAllocBudget.repAlloc, Reg.x0]
              exact Entails.of_eq (by sep_ac_rfl)
          | some vn =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_some, Bool.not_true] at hvn_eq hvn_ne
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4996#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv3
              refine SepWPp.weaken_pre ?_
                (hnext _ (s2.readReg64 .x0)
                  (by rw [hvn_case]; simp only [↓reduceIte, arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3.1))
              rw [← A.pool_of_vmPreserved hinv3.2,
                ← vecU8At_empty_of_alloc A.repAlloc (sp + 1424#64) (s2.readReg64 .x0)
                  (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
              have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
              have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
              rw [h1432, h1440]
              dsimp only [RustCliAllocBudget.repAlloc, Reg.x0]
              exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_alloc_31b94_of_contracts_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State}
    (sp v_sp10 v_590 v_598 v_5a0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      A.pool lim st0 s ∗
      stackAt sp spqrSendCalleeStack ∗
      ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗
      ((sp + 1432#64) ↦₆₄ v_598) ∗
      ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
               else spqrSendPlacedEntry + 5604#64) →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = ptr →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_alloc_31b94_placed A lim st0 ext
    (spqrSend_shim_ok_enc_placed hA s0)
    (spqrSend_rustAllocNoOom_ok_placed hA s0)
    sp v_sp10 v_590 v_598 v_5a0 g st hpos hlen hfits halign
    hpc hrun hsp htr hx24 hx25 hx26 hinv0 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget
