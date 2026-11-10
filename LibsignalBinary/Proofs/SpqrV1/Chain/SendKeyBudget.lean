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
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKey
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Proof of `<spqr::chain::Chain>::send_key` (Block `367`)

Proves the `RustCliAllocBudget`-threaded `[LibsignalPlacement]` contract
`ChainSendKeyPlacedOkX hkdf M A lim H` for `<spqr::chain::Chain>::send_key` (Block `367`) against
`chainSendKeySpecX hkdf M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded lsmpl lsρ blkPC_367 blkPl_367)
open CryptoVerification.LibsignalSpqrV1 (Bytes Chain ChainEpoch ChainEpochDirection HkdfFn)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost ChainGhost ChainSendKeyGhost NextKeyInternalGhost
  bytesAt_false bytesAt_true chainAt chainEpochAlign chainEpochAt chainEpochAt_unpack_send_next
  chainEpochDirectionAt chainEpochSize chainRepr clearFrontPre iterHead iterL2 nextKeyInternalPanicSpecX
  nextKeyInternalStackX nextKeyNext nextKeyOut nextKeyOutAt sendKeyPostAt vecDequePhysIdx
  vecDequeRingBuf zip_set_snd
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (
  SepWPp.pure_left_focus memRegion_32_cells4
)
open CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts (
  add_not_eq_ofNat_sub chainAt_unpack_sendKey chainEpochDirectionAt_pack_nextKey
  chainRepr_pack_sendKey epochIdx_of_back_ge epochIdx_of_gt epochIdx_of_lt
  memRegion_40_err_split memRegion_40_ok_split physIdx_madd_eq
  pointsTo32_cells4_entails_memRegion_36 rejoin_stack_chainSendKeyX sendKeyErrAt_epochOutOfRange_intro
  sendKeyErrAt_sendKeyEpochDecreased_intro sendKeyOkAt_intro sendKeyTail sendKeyTail_eq_ok
  sendKeyTail_isPanic_of_bad sendKey_eq_tail_of_eq sendKey_eq_tail_of_ne_pos
  sendKey_eq_tail_of_ne_zero sendKey_of_epochIdx_err sendKey_of_lt stackAt_chainSendKeyX_split
  stackAt_nextKeyInternalX_top_split vecDequeRingBuf_get_physIdx vecDequeRingBuf_set_physIdx
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv
  SepWPp.call_allowPanic_lsCallInv_mid SepWPp.call_allowPanic_lsCallInv_ret
  SepWPp.of_sepWP_lsCallInv withLsCallInv
)
open CryptoVerification.SpqrV1.ChainProofs.SendKeyTailHelpers (
  SepWPp.post_of_entails
  back_ge_props back_lt_props calleeSavedSendKeyAt calleeSavedSendKeyAt_def ge_props
  k_plus_2_ge_2_props lt_props ne_branch_props nextKeyNext_length_of_nextKeyOut_length
  nextKeyOutAt_dup_len ofNat_lt_props sendKeyScratchAt sendKeyScratchAt_def sp_sub_208_aligned
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  NextKeyInternalEnv nextKeyInternalEvents nextKeyInternalSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans subroutine_ok_allocNoOomWithStack_of_budget
)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (
  ChainSendKeyAllocEnv ChainSendKeyPlacedOkX chainEpochPopEvents chainSendKeyEvents
  chainSendKeyPopEvents chainSendKeySpecX
)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPopBudget (
  popLoopPre sendKey_from_344_placed sendKey_pop_loop_placed
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

local macro "sep_elim_19 "
    c0:ident c1:ident c2:ident c3:ident c4:ident c5:ident
    c6:ident c7:ident c8:ident c9:ident c10:ident c11:ident
    l0:ident l1:ident l2:ident q0:ident q1:ident q2:ident q3:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $c0:ident; apply SepWPp.exists_elim; intro $c1:ident
    apply SepWPp.exists_elim; intro $c2:ident; apply SepWPp.exists_elim; intro $c3:ident
    apply SepWPp.exists_elim; intro $c4:ident; apply SepWPp.exists_elim; intro $c5:ident
    apply SepWPp.exists_elim; intro $c6:ident; apply SepWPp.exists_elim; intro $c7:ident
    apply SepWPp.exists_elim; intro $c8:ident; apply SepWPp.exists_elim; intro $c9:ident
    apply SepWPp.exists_elim; intro $c10:ident; apply SepWPp.exists_elim; intro $c11:ident
    apply SepWPp.exists_elim; intro $l0:ident; apply SepWPp.exists_elim; intro $l1:ident
    apply SepWPp.exists_elim; intro $l2:ident; apply SepWPp.exists_elim; intro $q0:ident
    apply SepWPp.exists_elim; intro $q1:ident; apply SepWPp.exists_elim; intro $q2:ident
    apply SepWPp.exists_elim; intro $q3:ident))

local macro "sep_elim_err4 " w0:ident b0:ident w2:ident w3:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $w0:ident; apply SepWPp.exists_elim; intro $b0:ident
    apply SepWPp.exists_elim; intro $w2:ident; apply SepWPp.exists_elim; intro $w3:ident))

private theorem onPanic_budget_of_trace_eq {s0 s sf : State} {P : Prop} {F : SepProp}
    (hP : P) (hs : s.trace = s0.trace) :
    (⌜sf.trace = s.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜P ∧ sf.trace = s0.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  exact Entails.pure_left fun htr => Entails.pure_right ⟨hP, htr.trans hs⟩ (entails_anyHeap _)

private theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

/-- State-indexed `SepWPp` sequence combinator preserving `LsCallInv`. -/
theorem SepWPp.seq_entails_lsCallInv_state {prog : Program} {pl : Obj.MultiPlacement}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {φ : State → Prop} {post panic_post : State → SepProp → Prop}
    (hF : LsCallInv pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid sm)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LsCallInv pl sm.mem → φ sm →
      SepWPp prog target sm (P_mid sm) post panic_post) :
    SepWPp prog target s P post panic_post := by
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ P_mid sm ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps2, hout⟩ :=
      h2 sm hpcm hrunm (hF.of_steps hsteps1) hφ R hmm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

/-- Frame a `SepWP` step whose post-resource depends on the post-state `sm` (e.g. `A.pool lim st sm`). -/
theorem SepWP.conseq_entails_state {prog : Program} {target : BitVec 64} {s : State}
    {P1 P : SepProp} {P2 P_mid : State → SepProp} {φ : State → Prop} {F : SepProp}
    (h : SepWP prog target s P1 (fun sm Pm => φ sm ∧ (Pm ⊢ P2 sm)))
    (hpre : P ⊢ P1 ∗ F)
    (hpost : ∀ sm, φ sm → (P2 sm ∗ F ⊢ P_mid sm)) :
    SepWP prog target s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid sm)) := by
  unfold SepWP
  intro R hm hL
  have hm1 : s.mem ⊨ P1 ∗ (F ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  rcases h.elim hm1 hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · refine ⟨sm, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, by rwa [sepConj_assoc], hφ, ?_⟩⟩
    exact Entails.trans (sepConj_mono_left hent) (hpost sm hφ)
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

/-- Frame a `VmPreserved` `SepWP` step against a `State → SepProp` frame (such as `A.pool lim st`). -/
theorem SepWP.conseq_entails_vm {prog : Program} {target : BitVec 64} {s : State}
    {P1 P2 P : SepProp} {P_mid F : State → SepProp} {φ : State → Prop}
    (h : SepWP prog target s P1 (fun sm Pm => VmPreserved s sm ∧ φ sm ∧ (Pm ⊢ P2)))
    (hpre : P ⊢ P1 ∗ F s)
    (hF_vm : ∀ sm, VmPreserved s sm → (F s ⊢ F sm))
    (hpost : ∀ sm, P2 ∗ F sm ⊢ P_mid sm) :
    SepWP prog target s P (fun sm Pm => φ sm ∧ (Pm ⊢ P_mid sm)) := by
  unfold SepWP
  intro R hm hL
  have hm1 : s.mem ⊨ P1 ∗ (F s ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  rcases h.elim hm1 hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, hφ, hent⟩ | ⟨_, hfalse⟩⟩
  · refine ⟨sm, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F s, by rwa [sepConj_assoc], hφ, ?_⟩⟩
    exact Entails.trans (sepConj_mono hent (hF_vm sm hvm)) (hpost sm)
  · rw [satisfies_pure_sepConj] at hfalse; exact False.elim hfalse.1

def from436Pre0 (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st_cur : M.σ) (s0 s : State) (x : ChainSendKeyGhost)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  chainRepr A.repAlloc x.selfPtr self' ∗
  nextKeyOutAt (s0.sp - 132#64) ctr' outKey ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool lim st_cur s

def from380Pre0 (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st_cur : M.σ) (s0 s : State) (x : ChainSendKeyGhost)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) : SepProp :=
  memRegion x.out 40 ∗
  (x.selfPtr ↦₆₄ x.G.linksCap) ∗ ((x.selfPtr + 8#64) ↦₆₄ x.G.linksPtr) ∗
  ((x.selfPtr + 16#64) ↦₆₄ head1) ∗ ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links2.length) ∗
  vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
    x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) ∗
  ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ sendEpoch1) ∗
  CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts.chainRestSendKeyAt A.repAlloc x.selfPtr x.G x.self ∗
  stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
  sendKeyScratchAt s0.sp l0 l1 l2 ∗
  ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
  ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
  memRegion (s0.sp - 132#64) 36 ∗
  calleeSavedSendKeyAt s0 ∗
  A.pool lim st_cur s

theorem from380Pre_intro (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st_cur : M.σ) (s0 s : State) (G : ChainGhost) (self : Chain)
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) :
    memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
    (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
    ((s0.readReg64 (.gpr 0#5) + 16#64) ↦₆₄ head1) ∗ ((s0.readReg64 (.gpr 0#5) + 24#64) ↦₆₄ BitVec.ofNat 64 links2.length) ∗
    vecDequeRingBuf A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
      G.linksCap G.linksPtr head1 (epochs2.zip links2) ∗
    ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗ ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ sendEpoch1) ∗
    CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts.chainRestSendKeyAt A.repAlloc (s0.readReg64 (.gpr 0#5)) G self ∗
    stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
    sendKeyScratchAt s0.sp l0 l1 l2 ∗
    ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
    ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗
    memRegion (s0.sp - 132#64) 36 ∗ calleeSavedSendKeyAt s0 ∗ A.pool lim st_cur s ⊢
    from380Pre0 M A lim st_cur s0 s
      ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
      sendEpoch1 head1 epochs2 links2 l0 l1 l2 q0 q1 q2 q3 := by
  unfold from380Pre0; sep_frame

set_option maxHeartbeats 800000 in
theorem sendKey_from_436_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost) (st0 st_alloc : M.σ)
    (self' : Chain) (ctr' : BitVec 32) (outKey : Bytes) (hout_len : outKey.length = 32)
    (hsend_ok : Chain.sendKey hkdf x.self x.epoch = .ok (self', (ctr', outKey)))
    (hfits_alloc : FitsEvents M lim st_alloc (rustAllocEvents 32 1))
    (hev_eq : M.stepEvents (rustAllocEvents 32 1) st_alloc = M.stepEvents (chainSendKeyEvents x) st0)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State)
    (hpc : s.pc = (blkPl_367).base + 436#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (_htr : s.trace = s0.trace) (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from436Pre0 M A lim st_alloc s0 s x self' ctr' outKey l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecX hkdf M A lim).post (x, st0) s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf M A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halloc_nooom := subroutine_ok_allocNoOomWithStack_of_budget halloc
  unfold from436Pre0 nextKeyOutAt
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  have hsp_align : s.spAligned = true := sp_sub_208_aligned hsp0_align hsp
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hsp0_align; wp_norm_hyp hsp; wp_norm_hyp hsp_align; wp_norm_hyp hx19
  wp_norm_hyp hx29; wp_norm_hyp hv
  obtain ⟨k0, k1, k2, k3, _, hout_pack⟩ := exists_unpack64_of_length_32 hout_len
  have hout_unpack := hout_pack (s0.sp - 128#64)
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
  refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
  have hstack_s0 : stackAt (s0.sp - 208#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  wp_call halloc_nooom (32, 1, st_alloc)
  let p_key := sf_1.readReg64 (Reg.gpr 0#5)
  have hoom_64 : p_key ≠ 0#64 := ‹_›
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 p_key)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_40_ok_split x.out)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0)) (by sep_focus) ?_
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := by rw [hsp_sf_1, hsp_sf, hsp]
  wp_norm_hyp hsp_sf1; sep_elim_exists
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
  (conv => arg 4; simp only [← RustCliAllocBudget.repAlloc_live])
  refine SepWP.fold (sendKeyOkAt_intro A.repAlloc x.out ctr' p_key outKey hout_len hoom_64) (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 208#64) extHookStack := by rw [hsp_sf, hsp]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp l0 l1 l2)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp l0 l1 l2 k0 k1 k2 k3
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
    (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
    (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
    (by sep_focus) ?_
  have hacp_shim : AllocCallPreserved s sf := by
    have h := ‹AllocCallPreserved _ sf›
    unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_alloc : AllocCallPreserved sf sf_1 := by
    have h := ‹AllocCallPreserved _ sf_1›
    unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_0_1 : AllocCallPreserved s0 sf_1 :=
    allocCallPreserved_trans hacp (allocCallPreserved_trans hacp_shim hacp_alloc)
  have htr_1 : sf_1.trace = s0.trace := hacp_0_1.2.1
  wp_norm_hyp htr_1
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
  rw [hev_eq]
  refine Entails.sepExists_right (chainSendKeyEvents x) ?_
  rw [hsend_ok]; dsimp only [sendKeyPostAt]
  refine Entails.pure_right
    ⟨by simp [ChainSendKeyAllocEnv, hsend_ok], by wp_norm_goal,
     by unfold AllocCallPreserved at hacp_0_1 ⊢; simpa only [wp_norm, arm64_norm] using hacp_0_1⟩ ?_
  sep_frame

set_option maxHeartbeats 800000 in
theorem sendKey_from_380_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost) (st0 : M.σ)
    (hfits_env : FitsEnv M lim st0 (ChainSendKeyAllocEnv hkdf x))
    (sendEpoch1 head1 : BitVec 64) (epochs2 : List ChainEpochGhost) (links2 : List ChainEpoch)
    (i : Nat) (hi : i < links2.length) (hlen_le : links2.length ≤ x.G.linksCap.toNat)
    (hlen_eq : epochs2.length = links2.length)
    (hres_eq : Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self sendEpoch1 links2 i hi)
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State) (hF : LsCallInv lsmpl s.mem)
    (hpc : s.pc = (blkPl_367).base + 380#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (_hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links2.length) (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from380Pre0 M A lim (M.stepEvents (chainSendKeyPopEvents x) st0) s0 s x sendEpoch1 head1
        epochs2 links2 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecX hkdf M A lim).post (x, st0) s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf M A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have h_from436 := @sendKey_from_436_placed _ hkdf M A lim H hshim halloc s0 hsp0_align x st0
  clear hshim halloc; unfold from380Pre0
  let st_pop := M.stepEvents (chainSendKeyPopEvents x) st0
  have hzip_le : (epochs2.zip links2).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
  have hzip_i : i < (epochs2.zip links2).length := by simp [hlen_eq, hi]
  refine SepWPp.fold (vecDequeRingBuf_get_physIdx A.repAlloc x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2) hzip_le hzip_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hhead, hcap_lt, hptr⟩
  have hzip_geti : (epochs2.zip links2)[i] = (epochs2[i]'(by omega), links2[i]'hi) := by simp [List.getElem_zip]
  rw [hzip_geti]
  let gce_i := epochs2[i]'(by omega); let ce_i := links2[i]'hi
  let slot_i := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx head1.toNat x.G.linksCap.toNat i * 112)
  refine SepWPp.fold (chainEpochAt_unpack_send_next A.repAlloc gce_i ce_i slot_i) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hle_i, hcap_i, hptr_i⟩
  have ⟨hule_i, hult_i⟩ := ofNat_lt_props hi (by omega : links2.length < 2 ^ 63)
  have hmaddi := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi hlen_le) hcap_lt
  wp_norm_hyp hsp0_align; wp_norm_hyp hsp; wp_norm_hyp _hsp_align; wp_norm_hyp hx19
  wp_norm_hyp hx20; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hx29
  wp_norm_hyp htr; wp_norm_hyp hv; wp_norm_hyp hule_i; wp_norm_hyp hult_i; wp_norm_hyp hmaddi
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 362) hF ?_
  wp_steps_sync_pool (lsmpl.base 362)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  by_cases hbad : ce_i.send.next.length ≠ 32 ∨ ce_i.send.ctr = 0xffffffff#32
  · have hpan_tail : (sendKeyTail hkdf x.self sendEpoch1 links2 i hi).isPanic = true :=
      sendKeyTail_isPanic_of_bad hkdf x.self sendEpoch1 links2 i hi hbad
    have hpan_eq : (Chain.sendKey hkdf x.self x.epoch).isPanic = true := by rw [hres_eq]; exact hpan_tail
    have hlen_lt64 : ce_i.send.next.length < 2 ^ 64 := by omega
    let x_nkp : NextKeyInternalGhost :=
      ⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩
    change subroutine_ok _ _ (withLsCallInv lsmpl nextKeyInternalPanicSpecX) at hnextKeyPanic
    apply (SepWPp.call_allowPanic_lsCallInv_ret hnextKeyPanic (x := x_nkp) hinv1)
    · wp_norm_goal
    · wp_norm_lhs
    · wp_norm_goal
    · wp_norm_lhs
    · intro R' hmR'
      rw [← sepConj_assoc]
      dsimp only [nextKeyInternalPanicSpecX, x_nkp]
      refine Satisfies.mono (sepConj_mono_left ?_) hmR'
      rw [sepConj_assoc]
      refine Entails.pure_right ⟨by wp_norm_goal, by dsimp [slot_i]; wp_norm_goal, hlen_lt64, hbad⟩ ?_
      simp only [wp_norm, arm64_norm, hsp]
      sep_frame
    · intro _
      dsimp only [nextKeyInternalPanicSpecX, chainSendKeySpecX]
      apply onPanic_budget_of_trace_eq hpan_eq
      simp only [wp_norm, arm64_norm, htr]
    · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
    · intro _ _ _ _ _ _
      dsimp only [nextKeyInternalPanicSpecX]
      exact CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts.SepWP.pure_left_focus _
        (by sep_focus) False.elim
  · have hlen32 : ce_i.send.next.length = 32 := by omega
    have hctr_ne : ce_i.send.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 ce_i.send.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    let send' : ChainEpochDirection :=
      { ce_i.send with next := nextKeyNext hkdf ce_i.send.next ce_i.send.ctr, ctr := ce_i.send.ctr + 1#32 }
    let links' := links2.set i { ce_i with send := send' }
    have htail_ok := sendKeyTail_eq_ok hkdf x.self sendEpoch1 links2 i hi hlen32 hctr_ne
    dsimp only at htail_ok
    have hsend_ok : Chain.sendKey hkdf x.self x.epoch =
        .ok ({ x.self with sendEpoch := sendEpoch1, links := links' },
             (ce_i.send.ctr + 1#32, nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) :=
      hres_eq.trans htail_ok
    have hfits_all : FitsEvents M lim st0 (chainSendKeyEvents x) :=
      hfits_env (chainSendKeyEvents x) (by simp [ChainSendKeyAllocEnv, hsend_ok])
    have hfits_after_pop : FitsEvents M lim st_pop (nextKeyInternalEvents ++ rustAllocEvents 32 1) := by
      have h : chainSendKeyEvents x = chainSendKeyPopEvents x ++ (nextKeyInternalEvents ++ rustAllocEvents 32 1) := by
        simp [chainSendKeyEvents, List.append_assoc]
      rw [h, fitsEvents_append] at hfits_all
      exact hfits_all.2
    rw [fitsEvents_append] at hfits_after_pop
    rcases hfits_after_pop with ⟨hfits_nk, hfits_alloc⟩
    have hfits_nk_env : FitsEnv M lim st_pop NextKeyInternalEnv := by
      intro evs hevs; rw [hevs]; exact hfits_nk
    let x_nk : NextKeyInternalGhost :=
      ⟨s0.sp - 132#64, gce_i.send.next.ptr, ce_i.send.next, slot_i + 48#64, ce_i.send.ctr⟩
    change subroutine_ok _ _ (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)) at hnextKey
    apply (SepWPp.call_allowPanic_lsCallInv_mid hnextKey (x := (x_nk, st_pop)) hinv1)
    · wp_norm_goal
    · wp_norm_lhs
    · wp_norm_goal
    · wp_norm_lhs
    · intro R' hmR'
      rw [← sepConj_assoc]
      dsimp only [nextKeyInternalSpecX, x_nk]
      refine Satisfies.mono (sepConj_mono_left ?_) hmR'
      rw [sepConj_assoc]
      refine Entails.pure_right
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by dsimp [slot_i]; wp_norm_goal, hlen32, hctr_ne, hfits_nk_env⟩ ?_
      simp only [wp_norm, arm64_norm, hsp]
      sep_frame
    · intro _; dsimp only [nextKeyInternalSpecX]; exact Entails.pure_left False.elim
    · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
    intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF_sf
    dsimp only [nextKeyInternalSpecX, x_nk]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro evs_nk
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr_sf, hacp_sf, hevs_nk⟩
    have hevs_nk_eq : evs_nk = nextKeyInternalEvents := hevs_nk
    subst hevs_nk_eq
    have hacp_s_sf : AllocCallPreserved s sf := by
      unfold AllocCallPreserved at hacp_sf ⊢; simpa only [wp_norm, arm64_norm] using hacp_sf
    have hacp_0_sf : AllocCallPreserved s0 sf := allocCallPreserved_trans hacp hacp_s_sf
    have hsp_sf' : sf.sp = s.sp := by simpa only [wp_norm, arm64_norm] using hsp_sf
    have hcs_sf' := hcs_sf
    unfold CalleeSavedPreserved at hcs_sf'
    simp only [wp_norm, arm64_norm] at hcs_sf'
    rcases hcs_sf' with ⟨hx19_sf, _, _, _, _, _, _, _, _, _, hx29_sf, hv_sf⟩
    (conv => arg 4; simp only [wp_norm, arm64_norm, hsp])
    refine SepWPp.fold (nextKeyOutAt_dup_len (s0.sp - 132#64) (ce_i.send.ctr + 1#32)
      (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_; intro hout_len
    have hnext'_len : (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr).length = 32 :=
      nextKeyNext_length_of_nextKeyOut_length hout_len
    have hced := chainEpochDirectionAt_pack_nextKey A.repAlloc slot_i gce_i.send ce_i.send
      (nextKeyNext hkdf ce_i.send.next ce_i.send.ctr) (ce_i.send.ctr + 1#32) hlen32 hnext'_len hle_i hcap_i hptr_i
    have hce : chainEpochDirectionAt A.repAlloc slot_i gce_i.send send' ∗
        chainEpochDirectionAt A.repAlloc (slot_i + 56#64) gce_i.recv ce_i.recv ⊢
        chainEpochAt A.repAlloc (gce_i, { ce_i with send := send' }) slot_i := Entails.refl _
    have hset := vecDequeRingBuf_set_physIdx A.repAlloc x.G.linksCap x.G.linksPtr head1 (epochs2.zip links2)
      (gce_i, { ce_i with send := send' }) hhead hcap_lt hptr hzip_le hzip_i
    dsimp only at hset
    have hzip_set : (epochs2.zip links2).set i (gce_i, { ce_i with send := send' }) = epochs2.zip links' :=
      zip_set_snd epochs2 links2 i gce_i _ (List.getElem?_eq_getElem (by omega))
    rw [hzip_set] at hset
    simp only [RustCliAllocBudget.repAlloc_live] at hset
    have hlen_links' : links'.length = links2.length := List.length_set
    have hpack := chainRepr_pack_sendKey A.repAlloc x.selfPtr x.G x.self head1 epochs2 links' sendEpoch1 (by omega)
    rw [hlen_links'] at hpack
    refine SepWPp.fold hced (by sep_focus) ?_; refine SepWPp.fold hce (by sep_focus) ?_
    refine SepWPp.fold hset (by sep_focus) ?_
    refine SepWPp.fold hpack (by sep_focus) ?_
    let st_alloc := M.stepEvents nextKeyInternalEvents st_pop
    have h436_pre :
        chainRepr A.repAlloc x.selfPtr { x.self with sendEpoch := sendEpoch1, links := links' } ∗
        nextKeyOutAt (s0.sp - 132#64) (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr) ∗
        A.pool lim st_alloc sf ∗ stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗ memRegion x.out 40 ∗
        sendKeyScratchAt s0.sp l0 l1 l2 ∗ ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
        ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗ calleeSavedSendKeyAt s0 ⊢
        from436Pre0 M A lim st_alloc s0 sf x { x.self with sendEpoch := sendEpoch1, links := links' }
          (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr) l0 l1 l2 q0 q1 q2 q3 := by
      unfold from436Pre0; sep_frame
    refine SepWPp.fold h436_pre (by sep_focus) ?_
    have hev_eq : M.stepEvents (rustAllocEvents 32 1) st_alloc = M.stepEvents (chainSendKeyEvents x) st0 := by
      dsimp only [st_alloc, st_pop]
      simp only [chainSendKeyEvents, ← AllocCostModel.stepEvents_append, List.append_assoc]
    rw [sepConj_emp]
    have htr_sf0 : sf.trace = s0.trace := hacp_0_sf.2.1
    exact h_from436 st_alloc
      { x.self with sendEpoch := sendEpoch1, links := links' }
      (ce_i.send.ctr + 1#32) (nextKeyOut hkdf ce_i.send.next ce_i.send.ctr)
      hout_len hsend_ok hfits_alloc hev_eq l0 l1 l2 q0 q1 q2 q3 (R := R) sf hpc_sf hrun_sf
      (hsp_sf'.trans hsp) (hx19_sf.trans hx19) (hx29_sf.trans hx29) htr_sf0 (hv_sf.trans hv) hacp_0_sf

theorem sendKey_from_344_full_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (s0 : State) (hsp0_align : s0.spAligned = true) (x : ChainSendKeyGhost) (st0 : M.σ)
    (hfits_env : FitsEnv M lim st0 (ChainSendKeyAllocEnv hkdf x))
    (head1 : BitVec 64) (epochs1 : List ChainEpochGhost) (links1 : List ChainEpoch)
    (h1 : 1 < links1.length) (hlen_le : links1.length ≤ x.G.linksCap.toNat) (hlen_eq : epochs1.length = links1.length)
    (hres_eq :
      let h0 : 0 < links1.length := by omega
      let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
      have h1' : 1 < links2.length := by simp [links2]; omega
      Chain.sendKey hkdf x.self x.epoch = sendKeyTail hkdf x.self x.epoch links2 1 h1')
    (l0 l1 l2 q0 q1 q2 q3 : BitVec 64) {R : SepProp} (s : State) (hF : LsCallInv lsmpl s.mem)
    (hpc : s.pc = (blkPl_367).base + 344#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) (hx20 : s.readReg64 (.gpr 20#5) = x.selfPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 links1.length)
    (hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hacp : AllocCallPreserved s0 s) :
    SepWPp ((blkPC_367).rebase (blkPl_367).base H) (s0.readReg64 (.gpr 30#5)) s
      (from380Pre0 M A lim (M.stepEvents (chainSendKeyPopEvents x) st0) s0 s x x.epoch head1
        epochs1 links1 l0 l1 l2 q0 q1 q2 q3)
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainSendKeySpecX hkdf M A lim).post (x, st0) s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainSendKeySpecX hkdf M A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have h0 : 0 < links1.length := by omega
  let links2 := links1.set 0 { links1[0] with send := links1[0].send.clearNext }
  have h1' : 1 < links2.length := by simp [links2]; omega
  have hlen2_eq : links2.length = links1.length := List.length_set
  let st_pop := M.stepEvents (chainSendKeyPopEvents x) st0
  let F_344 : State → SepProp := fun st_s =>
    memRegion x.out 40 ∗ ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 links1.length) ∗
    ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗ ((x.selfPtr + 64#64) ↦₆₄ x.epoch) ∗
    CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts.chainRestSendKeyAt A.repAlloc x.selfPtr x.G x.self ∗
    stackAt (s0.sp - 208#64) nextKeyInternalStackX ∗
    sendKeyScratchAt s0.sp l0 l1 l2 ∗ ((s0.sp - 176#64) ↦₆₄ q0) ∗ ((s0.sp - 168#64) ↦₆₄ q1) ∗
    ((s0.sp - 160#64) ↦₆₄ q2) ∗ ((s0.sp - 152#64) ↦₆₄ q3) ∗ memRegion (s0.sp - 132#64) 36 ∗
    calleeSavedSendKeyAt s0 ∗ A.pool lim st_pop st_s
  have hstep344 := sendKey_from_344_placed (M := M) (A := A) (H := H)
    x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 h0 hlen_le hlen_eq s hpc hrun hsp_align hx20
  dsimp only at hstep344
  have hpre344 : from380Pre0 M A lim st_pop s0 s x x.epoch head1 epochs1 links1 l0 l1 l2 q0 q1 q2 q3 ⊢
      clearFrontPre A.repAlloc x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links1 ∗ F_344 s := by
    unfold from380Pre0 clearFrontPre F_344; sep_frame
  have hF_vm : ∀ sm, VmPreserved s sm → (F_344 s ⊢ F_344 sm) := by
    intro sm hvm; dsimp only [F_344]
    rw [A.pool_of_vmPreserved hvm]; exact Entails.refl _
  have hpost344 : ∀ sm, clearFrontPre A.repAlloc x.selfPtr x.G.linksCap x.G.linksPtr head1 epochs1 links2 ∗ F_344 sm ⊢
      from380Pre0 M A lim st_pop s0 sm x x.epoch head1 epochs1 links2 l0 l1 l2 q0 q1 q2 q3 := by
    intro sm; unfold from380Pre0 clearFrontPre F_344; rw [hlen2_eq]; sep_frame
  refine SepWPp.seq_entails_lsCallInv_state hF (SepWP.conseq_entails_vm hstep344 hpre344 hF_vm hpost344) ?_
  rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx27_m, hx28_m, hx29_m, htr_m, hv_m, hacp_m⟩
  exact sendKey_from_380_placed hnextKey hnextKeyPanic hshim halloc s0 hsp0_align x st0 hfits_env
    x.epoch head1 epochs1 links2 1 h1' (by rw [hlen2_eq]; exact hlen_le)
    (by rw [hlen2_eq]; exact hlen_eq) hres_eq l0 l1 l2 q0 q1 q2 q3
    sm hFm hpcm hrunm (hsp_m.trans hsp) hsp_align_m (hx19_m.trans hx19) hx20_m
    (by rw [hlen2_eq]; exact hx27_m.trans hx27) hx28_m (hx29_m.trans hx29) (htr_m.trans htr)
    (hv_m.trans hv) (allocCallPreserved_trans hacp hacp_m)

set_option maxHeartbeats 1600000 in
theorem chainSendKey_placed_ok_of_contracts [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hdealloc : subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpecWithStack M A lim extHookStack)) :
    ChainSendKeyPlacedOkX hkdf M A lim H := by
  unfold ChainSendKeyPlacedOkX; wpp_init x_st s0
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x_st with ⟨⟨out, selfPtr, epoch, G, self⟩, st0⟩
  dsimp only [withLsCallInv, chainSendKeySpecX] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹LibsignalRoLoaded lsmpl s0.mem›, ‹LibsignalCodeLoaded lsmpl s0.mem›⟩
  have hfits_env : FitsEnv M lim st0
      (ChainSendKeyAllocEnv hkdf ⟨out, selfPtr, epoch, G, self⟩) := ‹_›
  subst out selfPtr epoch
  let x₀ : ChainSendKeyGhost :=
    ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
  refine SepWPp.rw_pre (by rw [stackAt_chainSendKeyX_split s0.sp]) ?_
  sep_elim_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c_18 c_17 c_16 c_15 c_14 c_13 c_12
  refine SepWPp.fold (chainAt_unpack_sendKey A.repAlloc (s0.readReg64 (.gpr 0#5)) G self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_; rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have h_from380 := @sendKey_from_380_placed _ hkdf M A lim H hnextKey hnextKeyPanic hshim halloc
    s0 hsp0_align ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩ st0 hfits_env
  have h_from344 := @sendKey_from_344_full_placed _ hkdf M A lim H hnextKey hnextKeyPanic hshim halloc
    s0 hsp0_align ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩ st0 hfits_env
  have h_poploop := @sendKey_pop_loop_placed _ M A lim H hdealloc (s0.readReg64 (.gpr 0#5)) G.linksCap G.linksPtr hcap_lt
  clear hnextKey hnextKeyPanic hshim halloc hdealloc
  by_cases hlt_send : s0.readReg64 (.gpr 1#5) < self.sendEpoch
  · have ⟨hult_send, hule_send⟩ := lt_props hlt_send
    wp_norm_hyp hult_send; wp_norm_hyp hule_send
    refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
    sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
    refine SepWP.fold (sendKeyErrAt_sendKeyEpochDecreased_intro (s0.readReg64 (.gpr 8#5))
      self.sendEpoch (s0.readReg64 (.gpr 1#5))) (by sep_focus) ?_
    refine SepWP.fold (chainRepr_pack_sendKey A.repAlloc (s0.readReg64 (.gpr 0#5)) G self
      G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
    refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
      (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
      (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
    have hsend_err := sendKey_of_lt hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send
    refine Entails.sepExists_right [] ?_
    rw [AllocCostModel.stepEvents_nil, hsend_err]; dsimp only [sendKeyPostAt]
    refine Entails.pure_right ⟨by simp [ChainSendKeyAllocEnv, hsend_err], by wp_norm_goal,
      by unfold AllocCallPreserved; wp_norm_goal⟩ ?_
    sep_frame
  · have ⟨hult_send, hule_send⟩ := ge_props hlt_send
    wp_norm_hyp hult_send; wp_norm_hyp hule_send
    by_cases hgt_curr : s0.readReg64 (.gpr 1#5) > self.currentEpoch
    · have ⟨hult_curr, hule_curr⟩ := lt_props hgt_curr
      wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
      refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
      sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
      refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
        (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
      refine SepWP.fold (chainRepr_pack_sendKey A.repAlloc (s0.readReg64 (.gpr 0#5)) G self
        G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
      refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
        (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
        (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
        (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
      have hsend_err := sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
        (epochIdx_of_gt self (s0.readReg64 (.gpr 1#5)) hgt_curr)
      refine Entails.sepExists_right [] ?_
      rw [AllocCostModel.stepEvents_nil, hsend_err]; dsimp only [sendKeyPostAt]
      refine Entails.pure_right ⟨by simp [ChainSendKeyAllocEnv, hsend_err], by wp_norm_goal,
        by unfold AllocCallPreserved; wp_norm_goal⟩ ?_
      sep_frame
    · have ⟨hult_curr, hule_curr⟩ := ge_props hgt_curr
      wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
      by_cases hback_ge : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat ≥ self.links.length
      · have ⟨hult_back, hule_back⟩ := back_ge_props hback_ge (by omega : self.links.length < 2 ^ 63)
        wp_norm_hyp hult_back; wp_norm_hyp hule_back
        refine SepWPp.fold (Entails.of_eq (memRegion_40_err_split (s0.readReg64 (.gpr 8#5)))) (by sep_focus) ?_
        sep_elim_err4 w0 b0 w2 c_22; apply SepWPp.of_sepWP_ret
        wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
        refine SepWP.fold (sendKeyErrAt_epochOutOfRange_intro (s0.readReg64 (.gpr 8#5))
          (s0.readReg64 (.gpr 1#5)) w0) (by sep_focus) ?_
        refine SepWP.fold (chainRepr_pack_sendKey A.repAlloc (s0.readReg64 (.gpr 0#5)) G self
          G.linksHead G.epochs self.links self.sendEpoch hlen_eq) (by sep_focus) ?_
        refine SepWP.fold (rejoin_stack_chainSendKeyX s0.sp c_18 c_17 c_16 c_15 c_14 c_13 c_12
          (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 28#5)) (s0.readReg64 (.gpr 27#5))
          (s0.readReg64 (.gpr 26#5)) (s0.readReg64 (.gpr 25#5)) (s0.readReg64 (.gpr 24#5)) (s0.readReg64 (.gpr 23#5))
          (s0.readReg64 (.gpr 22#5)) (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5)))
          (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
        have hsend_err := sendKey_of_epochIdx_err hkdf self (s0.readReg64 (.gpr 1#5)) _ hlt_send
          (epochIdx_of_back_ge self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_ge)
        refine Entails.sepExists_right [] ?_
        rw [AllocCostModel.stepEvents_nil, hsend_err]; dsimp only [sendKeyPostAt]
        refine Entails.pure_right ⟨by simp [ChainSendKeyAllocEnv, hsend_err], by wp_norm_goal,
          by unfold AllocCallPreserved; wp_norm_goal⟩ ?_
        sep_frame
      · have hback_lt : (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat < self.links.length := by omega
        have ⟨hult_back, hule_back⟩ := back_lt_props hback_lt (by omega : self.links.length < 2 ^ 63)
        let idx0 := self.links.length - 1 - (self.currentEpoch - s0.readReg64 (.gpr 1#5)).toNat
        have hidx0_lt : idx0 < self.links.length := by dsimp [idx0]; omega
        have hidx_eq : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok idx0 :=
          epochIdx_of_lt self (s0.readReg64 (.gpr 1#5)) hgt_curr hback_lt
        have hadd_not : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
            BitVec.ofNat 64 idx0 := add_not_eq_ofNat_sub hback_lt
        wp_norm_hyp hult_back; wp_norm_hyp hule_back; wp_norm_hyp hadd_not
        by_cases heq_send : self.sendEpoch = s0.readReg64 (.gpr 1#5)
        · have heq_beq : (self.sendEpoch == s0.readReg64 (.gpr 1#5)) = true := by simp [heq_send]
          have heq_sub : (self.sendEpoch - s0.readReg64 (.gpr 1#5) == 0#64) = true := by simp [heq_send]
          wp_norm_hyp heq_beq; wp_norm_hyp heq_sub
          have hres_eq := sendKey_eq_tail_of_eq hkdf self (s0.readReg64 (.gpr 1#5)) idx0 hlt_send hidx_eq hidx0_lt heq_send
          have hpop_eq : chainSendKeyPopEvents x₀ = [] := by
            simp [chainSendKeyPopEvents, x₀, ← heq_send]
          have hst_pop0 : M.stepEvents (chainSendKeyPopEvents x₀) st0 = st0 := by
            rw [hpop_eq, AllocCostModel.stepEvents_nil]
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 380#64) hinv0 ?_
          wp_steps_sync_pool ((blkPl_367).base + 380#64)
          refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
          wp_conv_pre => rw [← hst_pop0]
          refine SepWP.fold (from380Pre_intro M A lim (M.stepEvents (chainSendKeyPopEvents x₀) st0) s0 _ G self
            self.sendEpoch G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
          exact h_from380 self.sendEpoch G.linksHead G.epochs self.links idx0 hidx0_lt hlen_le hlen_eq hres_eq
            c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by unfold AllocCallPreserved; wp_norm_goal)
        · have ⟨hne_beq, hne_sub, hne_add⟩ := ne_branch_props heq_send
          wp_norm_hyp hne_beq; wp_norm_hyp hne_sub; wp_norm_hyp hne_add
          have hnot_le_send : ¬ (s0.readReg64 (.gpr 1#5) ≤ self.sendEpoch) := by
            simp only [BitVec.le_def, BitVec.lt_def] at hlt_send ⊢
            intro hle
            exact heq_send (BitVec.eq_of_toNat_eq (by omega))
          rcases hidx0_cases : idx0 with _ | _ | k
          · have h0_lt : 0 < self.links.length := by omega
            have hidx_0 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 0 := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_zero hkdf self (s0.readReg64 (.gpr 1#5)) hlt_send hidx_0 h0_lt heq_send
            have hadd_not0 : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 0#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not0
            have hpop_eq : chainSendKeyPopEvents x₀ = [] := by
              simp [chainSendKeyPopEvents, x₀, hnot_le_send, hidx_0]
            have hst_pop0 : M.stepEvents (chainSendKeyPopEvents x₀) st0 = st0 := by
              rw [hpop_eq, AllocCostModel.stepEvents_nil]
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 380#64) hinv0 ?_
            wp_steps_sync_pool ((blkPl_367).base + 380#64)
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            wp_conv_pre => rw [← hst_pop0]
            refine SepWP.fold (from380Pre_intro M A lim (M.stepEvents (chainSendKeyPopEvents x₀) st0) s0 _ G self
              (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
            exact h_from380 (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links 0 h0_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by unfold AllocCallPreserved; wp_norm_goal)
          · have h1_lt : 1 < self.links.length := by omega
            have hidx_1 : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok 1 := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) 1
              hlt_send hidx_1 h1_lt heq_send (by omega)
            dsimp only [Nat.sub_self, List.drop_zero] at hres_eq
            have hadd_not1 : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) = 1#64 := by
              simpa [hidx0_cases] using hadd_not
            wp_norm_hyp hadd_not1
            have hpop_eq : chainSendKeyPopEvents x₀ = [] := by
              simp [chainSendKeyPopEvents, x₀, hnot_le_send, hidx_1]
            have hst_pop0 : M.stepEvents (chainSendKeyPopEvents x₀) st0 = st0 := by
              rw [hpop_eq, AllocCostModel.stepEvents_nil]
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 344#64) hinv0 ?_
            wp_steps_sync_pool ((blkPl_367).base + 344#64)
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (sendKeyScratchAt_def s0.sp c_18 c_17 c_16).symm) (by sep_focus) ?_
            wp_conv_pre => rw [← hst_pop0]
            refine SepWP.fold (from380Pre_intro M A lim (M.stepEvents (chainSendKeyPopEvents x₀) st0) s0 _ G self
              (s0.readReg64 (.gpr 1#5)) G.linksHead G.epochs self.links c_18 c_17 c_16 c_15 c_14 c_13 c_12) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1; rw [sepConj_emp]
            exact h_from344 G.linksHead G.epochs self.links h1_lt hlen_le hlen_eq hres_eq
              c_18 c_17 c_16 c_15 c_14 c_13 c_12 _ hinv1 (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
              (by unfold AllocCallPreserved; wp_norm_goal)
          · have hk_lt : k + 2 < self.links.length := by omega
            have hidx_k : self.epochIdx (s0.readReg64 (.gpr 1#5)) = .ok (k + 2) := by simpa [hidx0_cases] using hidx_eq
            have hres_eq := sendKey_eq_tail_of_ne_pos hkdf self (s0.readReg64 (.gpr 1#5)) (k + 2)
              hlt_send hidx_k hk_lt heq_send (by omega)
            dsimp only [Nat.add_sub_cancel] at hres_eq
            have hadd_notk : BitVec.ofNat 64 self.links.length + ~~~(self.currentEpoch - s0.readReg64 (.gpr 1#5)) =
                BitVec.ofNat 64 (k + 2) := by simpa [hidx0_cases] using hadd_not
            have ⟨hult_k2, hule_k2⟩ := k_plus_2_ge_2_props k (by omega)
            wp_norm_hyp hadd_notk; wp_norm_hyp hult_k2; wp_norm_hyp hule_k2
            have hpop_eq : chainSendKeyPopEvents x₀ = (G.epochs.take (k + 1)).flatMap chainEpochPopEvents := by
              simp [chainSendKeyPopEvents, x₀, hnot_le_send, hidx_k]
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_367).base + 164#64) hinv0 ?_
            wp_steps_sync_pool ((blkPl_367).base + 164#64)
            refine SepWP.fold (Entails.of_eq (calleeSavedSendKeyAt_def s0).symm) (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 208#64))) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1
            let F_loop : SepProp :=
              memRegion (s0.readReg64 (.gpr 8#5)) 40 ∗
              (s0.readReg64 (.gpr 0#5) ↦₆₄ G.linksCap) ∗ ((s0.readReg64 (.gpr 0#5) + 8#64) ↦₆₄ G.linksPtr) ∗
              ((s0.readReg64 (.gpr 0#5) + 56#64) ↦₆₄ self.currentEpoch) ∗
              ((s0.readReg64 (.gpr 0#5) + 64#64) ↦₆₄ s0.readReg64 (.gpr 1#5)) ∗
              CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts.chainRestSendKeyAt A.repAlloc (s0.readReg64 (.gpr 0#5)) G self ∗
              memRegion (s0.sp - 208#64 - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗
              memRegion (s0.sp - 208#64) 8 ∗ ((s0.sp - 176#64) ↦₆₄ c_15) ∗ ((s0.sp - 168#64) ↦₆₄ c_14) ∗
              ((s0.sp - 160#64) ↦₆₄ c_13) ∗ ((s0.sp - 152#64) ↦₆₄ c_12) ∗ memRegion (s0.sp - 144#64) 12 ∗
              memRegion (s0.sp - 132#64) 36 ∗ calleeSavedSendKeyAt s0
            refine SepWPp.seq_entails_lsCallInv_state hinv1
              (SepWP.conseq_entails_state (F := F_loop)
                (P_mid := fun sm => from380Pre0 M A lim (M.stepEvents (chainSendKeyPopEvents x₀) st0) s0 sm
                  ⟨s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), G, self⟩
                  (s0.readReg64 (.gpr 1#5)) (iterHead G.linksCap.toNat G.linksHead (k + 1))
                  (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
                  G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12)
                (h_poploop k G.linksHead c_16 G.epochs self.links (by omega) hlen_le hlen_eq st0
                  _ (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
                  (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
                (by unfold popLoopPre F_loop
                    simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_sub_add_lit, Nat.reduceSub]
                    sep_frame)
                (fun sm hφ_sm => by
                  have hsp_sm : sm.sp = s0.sp - 208#64 := by
                    simpa only [wp_norm, arm64_norm] using hφ_sm.1
                  unfold popLoopPre F_loop from380Pre0 sendKeyScratchAt
                  rw [hsp_sm, ← hpop_eq, stackAt_nextKeyInternalX_top_split (s0.sp - 208#64)]
                  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
                  sep_frame)) ?_
            rintro sm hpcm hrunm hFm ⟨hsp_m, hsp_align_m, hx19_m, hx20_m, hx22_m, hx27_m, hx28_m, hx29_m, htr_m, hvregs_m, hacp_m⟩
            have hacp_0_m : AllocCallPreserved s0 sm := by
              refine allocCallPreserved_trans ?_ hacp_m
              unfold AllocCallPreserved; wp_norm_goal
            exact h_from344
              (iterHead G.linksCap.toNat G.linksHead (k + 1))
              (G.epochs.drop (k + 1)) (self.links.drop (k + 1))
              (by simp; omega) (by simp; omega) (by simp [hlen_eq]) hres_eq
              G.linksPtr G.linksCap (iterL2 c_16 G.epochs (k + 1)) c_15 c_14 c_13 c_12
              sm hFm hpcm hrunm (by rw [hsp_m]; wp_norm_goal) hsp_align_m
              (by rw [hx19_m]; wp_norm_goal) hx20_m hx27_m
              (by rw [hx29_m]; wp_norm_goal) (by rw [htr_m]; wp_norm_goal) (by rw [hvregs_m]; wp_norm_goal)
              hacp_0_m

abbrev chainSendKey_placed_ok := @chainSendKey_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyBudget
