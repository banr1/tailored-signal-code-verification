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
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGc
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `KeyHistory::gc` and Post-GC Tail Proofs for `Chain::recv_key` (Block `366`)

Proves `recvKey_from_660_placed`, `recvKey_gc_loop_step_placed`, `recvKey_gc_loop_placed`, and
`recvKey_gc_from_616_placed` (Block `366`) under `RustCliAllocBudget M` with event schedule
`nextKeyInternalEvents ++ rustAllocEvents 32 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGcBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_366 blkPl_366)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chain ChainEpochDirection ChainParamsPB ChainResult HkdfFn KeyHistory bytesLt
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost ChainRecvKeyGhost NextKeyInternalGhost SepWPp.mono_pre VecPin
  bytesLt_4_eq_ult_rev32Trunc chainOuterRecvAt chainOuterRecvAt_pack chainRepr
  exists_cells4_of_length_32 exists_entry36_at_cells exists_entry36_last_cells
  gcLoop_of_bounds gcLoop_of_ge gcLoop_of_remove gcLoop_of_skip
  keyHistory_gc_of_lt keyHistory_gc_of_ok keyHistory_gc_of_underflow
  memRegion_36_split_u32 nextKeyInternalPanicSpecX nextKeyInternalStackX
  nextKeyInternal_eq_ok nextKeyInternal_isError_of_bad nextKeyNext nextKeyOut nextKeyOutAt
  pack32LE pointsTo32_cells4_entails_memRegion_36_sp120 pointsTo32_memRegion_32_entails_36
  pointsToBytes_split_u32_at pointsToBytes_write_moved36_at prev_remove_swap_repack
  recvKeyFrameRestAt recvKey_nextKeyNext_length_of_nextKeyOut_length
  recvKey_nextKeyOutAt_dup_len remove_data_eq_of_ge remove_length_of_lt rev32Trunc
  trimSize_mul36_eq vecDequePhysIdx vecU8At_pack_prev vecU8At_pack_remove_last
)
open CryptoVerification.SpqrV1.ChainProofs.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochFacts (vecU8Rest)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (
  SepWPp.pure_left_focus memRegion_32_cells4
)
open CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts (stackAt_nextKeyInternalX_top_split)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWP.pure_left_focus SepWPp.call_allowPanic_lsCallInv_mid
  SepWPp.call_allowPanic_lsCallInv_ret SepWPp.of_sepWP_lsCallInv withLsCallInv
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
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget (
  RecvKeyPlacedStateInv allowPanic_recvKey_panic recvKeyPanic recvKeyPost recvKey_ok_from_708_placed
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (
  chainRecvKeyEvents chainRecvKeySpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomSpecWithStack rustAllocSpecWithStack withStack
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

private theorem onPanic_recv_budget_of_trace_eq {s0 s sf : State} {P : Prop} {F : SepProp}
    (hP : P) (hs : s.trace = s0.trace) :
    (⌜sf.trace = s.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜P ∧ sf.trace = s0.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  exact Entails.pure_left fun htr => Entails.pure_right ⟨hP, htr.trans hs⟩ (entails_anyHeap _)

private theorem gc_iter_arith_props {i len : Nat} (hi_lt : i < len) (hlen : len < 2 ^ 63) :
    BitVec.ofNat 64 i + 4#64 = BitVec.ofNat 64 (i + 4) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 4)) = decide (len < i + 4) ∧
    BitVec.ule (BitVec.ofNat 64 (i + 4)) (BitVec.ofNat 64 len) = !decide (len < i + 4) ∧
    BitVec.ofNat 64 i + 36#64 = BitVec.ofNat 64 (i + 36) ∧
    BitVec.ult (BitVec.ofNat 64 (i + 36)) (BitVec.ofNat 64 len) = decide (i + 36 < len) ∧
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 36)) = !decide (i + 36 < len) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 i) = false ∧
    BitVec.ule (BitVec.ofNat 64 i) (BitVec.ofNat 64 len) = true ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 i) = false ∧
    BitVec.ule (BitVec.ofNat 64 i) (BitVec.ofNat 64 i) = true := by
  have hi64 : i < 2 ^ 64 := by omega
  have hi4_64 : i + 4 < 2 ^ 64 := by omega
  have hi36_64 : i + 36 < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  refine ⟨by bv_omega, ?_, ?_, by bv_omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi4_64]
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi4_64, Nat.mod_eq_of_lt hlen64]
    by_cases h : len < i + 4 <;> simp [h] <;> omega
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi36_64, Nat.mod_eq_of_lt hlen64]
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi36_64]
    by_cases h : i + 36 < len <;> simp [h] <;> omega
  · rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hi64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hlen64]; omega
  · simp [BitVec.ult]
  · simp [BitVec.ule]

private theorem gc_swap_arith_props {i len : Nat} (hlt : i + 36 < len) (hlen : len < 2 ^ 63) :
    BitVec.ofNat 64 len - 36#64 = BitVec.ofNat 64 (len - 36) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len - 36)) = false ∧
    BitVec.ule (BitVec.ofNat 64 (len - 36)) (BitVec.ofNat 64 len) = true ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 (len - 36)) = true ∧
    BitVec.ule (BitVec.ofNat 64 (len - 36)) (BitVec.ofNat 64 i) = false := by
  have hi64 : i < 2 ^ 64 := by omega
  have hsub64 : len - 36 < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  refine ⟨by bv_omega, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hlen64]; omega
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsub64]; omega
  · rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hi64]; omega

private theorem ule_eq_not_ult_32 (a b : BitVec 32) : BitVec.ule a b = !BitVec.ult b a := by
  rw [BitVec.ule_eq_decide, BitVec.ult_eq_decide]
  by_cases h : a.toNat ≤ b.toNat <;> simp [h] <;> omega

private theorem gc_cmp_props {ek : List (BitVec 8)} (hek : ek.length = 4) (thVal : BitVec 32) :
    let w9 := rev32Trunc (rev32Trunc thVal)
    let w11 := rev32Trunc (pack32LE ek)
    BitVec.ult w11 w9 = bytesLt ek (toBEBytes 4 thVal) ∧
    BitVec.ule w9 w11 = !bytesLt ek (toBEBytes 4 thVal) := by
  intro w9 w11
  have hlt := (bytesLt_4_eq_ult_rev32Trunc hek thVal).symm
  exact ⟨hlt, by rw [ule_eq_not_ult_32, hlt]⟩

private theorem gc_entry_arith_props (len : Nat) (ctr : BitVec 32) (params : ChainParamsPB)
    (hlen : len < 2 ^ 63) :
    let trimBytes := params.trimSize * KeyHistory.KEY_SIZE
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 trimBytes) = !decide (len ≥ trimBytes) ∧
    BitVec.ule (BitVec.ofNat 64 trimBytes) (BitVec.ofNat 64 len) = decide (len ≥ trimBytes) ∧
    BitVec.ult ctr params.maxOooKeysOrDefault = decide (ctr < params.maxOooKeysOrDefault) ∧
    BitVec.ule params.maxOooKeysOrDefault ctr = !decide (ctr < params.maxOooKeysOrDefault) := by
  intro trimBytes
  have hlen64 : len < 2 ^ 64 := by omega
  have hm := params.maxOooKeysOrDefault.isLt
  have htrim64 : trimBytes < 2 ^ 64 := by dsimp [trimBytes, ChainParamsPB.trimSize, KeyHistory.KEY_SIZE]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt htrim64]
    by_cases h : len ≥ trimBytes <;> simp [h] <;> omega
  · rw [BitVec.ule_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt htrim64, Nat.mod_eq_of_lt hlen64]
  · simp only [BitVec.ult_eq_decide, BitVec.lt_def]
  · simp only [BitVec.ule_eq_decide, BitVec.lt_def]
    by_cases h : ctr.toNat < params.maxOooKeysOrDefault.toNat <;> simp [h] <;> omega

set_option maxHeartbeats 800000 in
set_option maxRecDepth 400000 in
theorem recvKey_from_660_placed [LibsignalPlacement] {M : AllocCostModel}
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
    (x : ChainRecvKeyGhost) (st0 st_gc : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv2 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv2.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0)
    (hfits_tail : FitsEvents M lim st_gc (nextKeyInternalEvents ++ rustAllocEvents 32 1))
    (hev_tail : M.stepEvents (nextKeyInternalEvents ++ rustAllocEvents 32 1) st_gc =
      M.stepEvents (chainRecvKeyEvents hkdf x) st0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 660#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv2.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv2.next) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr recv2.next.length ∗
        vecU8At A.repAlloc (epPtr + 0x50#64) prevPin.cap prevPin.ptr recv2.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv2.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool lim st_gc s)
      (recvKeyPost M A lim hkdf x st0 s0) (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro prog s_idx epPtr
  have halloc_nooom := subroutine_ok_allocNoOomWithStack_of_budget halloc
  have h_ok708 := @recvKey_ok_from_708_placed _ M A lim hkdf H x st0 s0 c3 R
  clear halloc
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have hsp0_align' := hsp0_align; wp_norm_hyp hsp0_align'
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 362) hF ?_
  wp_steps_sync_pool (lsmpl.base 362)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  by_cases hbad : recv2.next.length ≠ 32 ∨ recv2.ctr = 0xffffffff#32
  · obtain ⟨p, hp_err⟩ := nextKeyInternal_isError_of_bad hkdf hbad
    have hpan_eq : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by rw [hres, hp_err]; rfl
    have hlen_lt64 : recv2.next.length < 2 ^ 64 := by omega
    let x_nkp : NextKeyInternalGhost :=
      ⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩
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
      refine Entails.pure_right ⟨by wp_norm_goal, by dsimp [epPtr]; wp_norm_goal, hlen_lt64, hbad⟩ ?_
      simp only [wp_norm, arm64_norm, hsp]
      sep_frame
    · intro _
      dsimp only [nextKeyInternalPanicSpecX, recvKeyPanic, chainRecvKeySpecX]
      apply onPanic_recv_budget_of_trace_eq hpan_eq
      simp only [wp_norm, arm64_norm, htrace]
    · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
    · intro _ _ _ _ _ _
      dsimp only [nextKeyInternalPanicSpecX]
      exact SepWP.pure_left_focus _ (by sep_focus) False.elim
  · have hlen32 : recv2.next.length = 32 := by omega
    have hctr_ne : recv2.ctr ≠ 0xffffffff#32 := fun hc => hbad (Or.inr hc)
    have hlen32_bv : BitVec.ofNat 64 recv2.next.length = 32#64 := by rw [hlen32]
    wp_norm_hyp hlen32_bv
    have hfits_pair := (fitsEvents_append M lim nextKeyInternalEvents (rustAllocEvents 32 1) st_gc).mp hfits_tail
    rcases hfits_pair with ⟨hfits_nk, hfits_alloc⟩
    have hfits_nk_env : FitsEnv M lim st_gc NextKeyInternalEnv := by
      intro evs hevs; rw [hevs]; exact hfits_nk
    let x_nk : NextKeyInternalGhost :=
      ⟨s0.sp - 120#64, gce.recv.next.ptr, recv2.next, epPtr + 0x68#64, recv2.ctr⟩
    change subroutine_ok _ _ (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)) at hnextKey
    apply (SepWPp.call_allowPanic_lsCallInv_mid hnextKey (x := (x_nk, st_gc)) hinv1)
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
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by dsimp [epPtr]; wp_norm_goal,
         hlen32, hctr_ne, hfits_nk_env⟩ ?_
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
    have hsp_sf' : sf.sp = s0.sp - 128#64 := (by simpa only [wp_norm, arm64_norm] using hsp_sf : sf.sp = s.sp).trans hsp
    have hcs_sf' := hcs_sf
    unfold CalleeSavedPreserved at hcs_sf'
    simp only [wp_norm, arm64_norm] at hcs_sf'
    rcases hcs_sf' with ⟨hx19_sf, _, _, _, _, _, _, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    dsimp only [epPtr]
    (conv => arg 4; simp only [wp_norm, arm64_norm, hsp])
    refine SepWPp.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 128#64))) (by sep_focus) ?_
    refine SepWPp.fold (recvKey_nextKeyOutAt_dup_len (s0.sp - 120#64) (recv2.ctr + 1#32)
      (nextKeyOut hkdf recv2.next recv2.ctr)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro hout_len
    have hnext'_len : (nextKeyNext hkdf recv2.next recv2.ctr).length = 32 :=
      recvKey_nextKeyNext_length_of_nextKeyOut_length hout_len
    let next' := nextKeyNext hkdf recv2.next recv2.ctr
    let ctr' := recv2.ctr + 1#32
    let outKey := nextKeyOut hkdf recv2.next recv2.ctr
    let recv' : ChainEpochDirection := { recv2 with next := next', ctr := ctr' }
    let self' : Chain :=
      { x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }
    have hlen_eq_next' : next'.length = recv2.next.length := by rw [hnext'_len, hlen32]
    have ha40 : epPtr + 0x38#64 + 8#64 = epPtr + 0x40#64 := by bv_kernel
    have ha48 : epPtr + 0x38#64 + 16#64 = epPtr + 0x48#64 := by bv_kernel
    have hpack_next := vecU8At_pack_prev A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next'
      (by rw [hlen_eq_next']; exact hn_le) hn_cap hn_ptr
    rw [ha40, ha48, hlen_eq_next'] at hpack_next
    clear ha40 ha48
    dsimp only [epPtr] at hpack_next
    refine SepWPp.fold hpack_next (by sep_focus) ?_
    have hpack_chain := chainOuterRecvAt_pack A.repAlloc x epochIndex hi_ep gce prevPin recv'
      hhead hcap_lt hptr hlen_le hlen_eq
    dsimp only at hpack_chain
    refine SepWPp.fold hpack_chain (by sep_focus) ?_
    unfold nextKeyOutAt
    refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
    obtain ⟨k0, k1, k2, k3, hout_pack⟩ := exists_cells4_of_length_32 hout_len
    have hout_unpack := hout_pack (s0.sp - 116#64)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hout_unpack
    refine SepWPp.fold (Entails.of_eq hout_unpack) (by sep_focus) ?_
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf'] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    let st_alloc := M.stepEvents nextKeyInternalEvents st_gc
    wp_norm_hyp hsp_sf'; wp_norm_hyp hsp_sf_align
    wp_norm_hyp hx19_sf; wp_norm_hyp hx26_sf; wp_norm_hyp hx27_sf; wp_norm_hyp hx28_sf; wp_norm_hyp hvregs_sf
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hF_sf ?_
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    have hstack_sf0 : stackAt (s0.sp - 128#64) extHookStack = stackAt sf.sp extHookStack :=
      congrArg (stackAt · extHookStack) hsp_sf'.symm
    refine SepWP.fold (Entails.of_eq hstack_sf0) (by sep_focus) ?_
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack :=
      congrArg (stackAt · extHookStack) (by wp_norm_goal)
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    wp_call halloc_nooom (32, 1, st_alloc)
    let p_key := sf_2.readReg64 (Reg.gpr 0#5)
    have hoom_64 : p_key ≠ 0#64 := ‹_›
    refine SepWP.fold (Entails.of_eq (memRegion_32_cells4 p_key)) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u1
    apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u3
    have hsp_sf2 : sf_2.sp = s0.sp - 128#64 := by rw [hsp_sf_2, hsp_sf_1, hsp_sf']
    have hsp_sf2_align : sf_2.spAligned = true := by
      simp only [State.spAligned, hsp_sf2] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    wp_norm_hyp hsp_sf2; wp_norm_hyp hsp_sf2_align
    wp_steps_sync_pool ((blkPl_366).base + 708#64)
    refine SepWP.fold (Entails.of_eq (hout_pack p_key).symm) (by sep_focus) ?_
    refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr' k0 k1 k2 k3) (by sep_focus) ?_
    have hstack_sf_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 128#64) extHookStack := by
      rw [hsp_sf_1, hsp_sf']
    refine SepWP.fold (Entails.of_eq hstack_sf_back) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_top_split (s0.sp - 128#64)).symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF5
    have hacp_shim : AllocCallPreserved sf sf_1 := by
      have h := ‹AllocCallPreserved _ sf_1›
      unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
    have hacp_alloc : AllocCallPreserved sf_1 sf_2 := by
      have h := ‹AllocCallPreserved _ sf_2›
      unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
    have hacp_0_2 : AllocCallPreserved s0 sf_2 :=
      allocCallPreserved_trans hacp_0_sf (allocCallPreserved_trans hacp_shim hacp_alloc)
    have htr_2 : sf_2.trace = s0.trace := hacp_0_2.2.1
    have hinv5 : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF5, (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
       (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal),
       (by simp only [arm64_norm, htr_2]),
       (by wp_norm_goal),
       allocCallPreserved_trans hacp_0_2 (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hx19_5 : sf_2.readReg64 (.gpr 19#5) = x.out := by wp_norm_goal
    have hres_ok : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey) := by
      rw [hres, nextKeyInternal_eq_ok hkdf hlen32 hctr_ne]; rfl
    have hev_final : M.stepEvents (rustAllocEvents 32 1) st_alloc =
        M.stepEvents (chainRecvKeyEvents hkdf x) st0 := by
      dsimp only [st_alloc]
      rw [← AllocCostModel.stepEvents_append, hev_tail]
    refine SepWPp.mono_pre _ ?_
      (h_ok708 self' outKey p_key hoom_64 hout_len hres_ok _ hinv5
        (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by rw [← hx19_5]; wp_norm_goal))
    rw [hev_final]
    sep_frame

set_option maxHeartbeats 1200000 in
theorem recvKey_gc_loop_step_placed [LibsignalPlacement] {M : AllocCostModel}
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
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (st0 st_gc : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (kh : KeyHistory) (thVal : BitVec 32) (i : Nat)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : kh.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0) (hi_lt : i < kh.data.length)
    (hfits_tail : FitsEvents M lim st_gc (nextKeyInternalEvents ++ rustAllocEvents 32 1))
    (hev_tail : M.stepEvents (nextKeyInternalEvents ++ rustAllocEvents 32 1) st_gc =
      M.stepEvents (chainRecvKeyEvents hkdf x) st0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (h_next : ∀ (kh' : KeyHistory) (i' : Nat)
      (_hp_le' : kh'.data.length ≤ prevPin.cap.toNat) (_hi_lt' : i' < kh'.data.length)
      (_hdec : kh'.data.length - i' < kh.data.length - i)
      (_hres' : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh' (toBEBytes 4 thVal) x.self.params i')
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ←
          ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s' : State) (_hinv' : RecvKeyPlacedStateInv lsmpl s0 s')
      (_hpc' : s'.pc = (blkPl_366).base + 932#64)
      (_hx0' : s'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i')
      (_hx2' : s'.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh'.data.length)
      (_hx8' : s'.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19' : s'.readReg64 (.gpr 19#5) = x.out)
      (_hx21' : s'.readReg64 (.gpr 21#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22' : s'.readReg64 (.gpr 22#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := (blkPC_366).rebase (blkPl_366).base H
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗ chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh'.data.length) ∗ (prevPin.ptr ↦ₛ kh'.data) ∗
          vecU8Rest A.repAlloc prevPin.cap prevPin.ptr kh'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool lim st_gc s')
        (recvKeyPost M A lim hkdf x st0 s0) (recvKeyPanic M A lim hkdf x st0 s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 932#64)
    (hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
    (hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
        vecU8Rest A.repAlloc prevPin.cap prevPin.ptr kh.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
        memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool lim st_gc s)
      (recvKeyPost M A lim hkdf x st0 s0) (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro prog s_idx epPtr
  have h_from660 := @recvKey_from_660_placed _ M A lim hkdf H hnextKey hnextKeyPanic hshim halloc
    x st0 st_gc s0 c3 R epochIndex hi_ep gce prevPin
  clear hnextKey hnextKeyPanic hshim halloc
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have hsp0_align' := hsp0_align; wp_norm_hyp hsp0_align'
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : kh.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hi4_add, hult_i4, hule_i4, hi36_add, hult_i36, hule_i36,
        hult_len_i, hule_i_len, hult_ii, hule_ii⟩ := gc_iter_arith_props hi_lt hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx0
  wp_norm_hyp hx2; wp_norm_hyp hx8; wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hi4_add; wp_norm_hyp hult_i4; wp_norm_hyp hule_i4; wp_norm_hyp hi36_add
  wp_norm_hyp hult_i36; wp_norm_hyp hule_i36; wp_norm_hyp hult_len_i; wp_norm_hyp hule_i_len
  wp_norm_hyp hult_ii; wp_norm_hyp hule_ii
  by_cases hbounds : kh.data.length < i + 4
  · have hb_t : decide (kh.data.length < i + 4) = true := decide_eq_true hbounds
    wp_norm_hyp hb_t
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hslice_ext) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, gcLoop_of_bounds kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
  · have hb_f : decide (kh.data.length < i + 4) = false := decide_eq_false hbounds
    have hi4_le : i + 4 ≤ kh.data.length := by omega
    have hlen_ek : (kh.data.extract i (i + 4)).length = 4 := by
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
    have ⟨hcmp_ult, hcmp_ule⟩ := gc_cmp_props hlen_ek thVal
    wp_norm_hyp hb_f; wp_norm_hyp hcmp_ult; wp_norm_hyp hcmp_ule
    have hsplit4 := pointsToBytes_split_u32_at prevPin.ptr kh.data i hi4_le
    refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
    by_cases hrem : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = true
    · wp_norm_hyp hrem
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        have ⟨hsub36, hult_sub1, hule_sub1, hult_sub2, hule_sub2⟩ := gc_swap_arith_props hlt36 hbs_lt
        wp_norm_hyp hlt36_t; wp_norm_hyp hsub36; wp_norm_hyp hult_sub1; wp_norm_hyp hule_sub1
        wp_norm_hyp hult_sub2; wp_norm_hyp hule_sub2
        obtain ⟨el0, el1, el2, el3, el4, hel_split, hel_pack⟩ := exists_entry36_last_cells kh.data (by omega)
        obtain ⟨ei0, ei1, ei2, ei3, ei4, hei_split, _⟩ := exists_entry36_at_cells kh.data i (by omega)
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 996#64)
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr)) (by sep_focus) ?_
        wp_steps_sync_pool ((blkPl_366).base + 1004#64)
        refine SepWP.fold (Entails.of_eq (hel_split prevPin.ptr).symm) (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hei_split prevPin.ptr)) (by sep_focus) ?_
        wp_steps_sync_pool ((blkPl_366).base + 932#64)
        have hwrite := pointsToBytes_write_moved36_at kh.data i (by omega) (by omega)
          el0 el1 el2 el3 el4 hel_pack prevPin.ptr
        refine SepWP.fold (Entails.of_eq hwrite) (by sep_focus) ?_
        have hrepack := prev_remove_swap_repack A.repAlloc prevPin.cap prevPin.ptr kh.data i x.self.params hlt36 hp_le
        dsimp only [KeyHistory.KEY_SIZE] at hrepack
        refine SepWP.fold hrepack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic
                (KeyHistory.gcLoop (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i)
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop]
        have hrem_len : (kh.remove i x.self.params).data.length = kh.data.length - 36 :=
          remove_length_of_lt kh.data i x.self.params hlt36
        have hp_le' : (kh.remove i x.self.params).data.length ≤ prevPin.cap.toNat := by omega
        have hi_lt' : i < (kh.remove i x.self.params).data.length := by omega
        have hdec : (kh.remove i x.self.params).data.length - i < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next (kh.remove i x.self.params) i hp_le' hi_lt' hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by rw [hrem_len]; wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        rw [hrem_len]; sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 660#64)
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_rem := vecU8At_pack_remove_last A.repAlloc
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data i x.self.params hi_lt hlt36 hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_rem; clear ha58 ha60
        refine SepWP.fold hpack_rem (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hrem_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = true := by rwa [← hex_eq]
        have hrem_len : (kh.remove i x.self.params).data.length = i := by
          rw [← remove_data_eq_of_ge kh.data i x.self.params hlt36, List.length_take_of_le (Nat.le_of_lt hi_lt)]
        have hnot_lt : ¬ (i < (kh.remove i x.self.params).data.length) := by omega
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh.remove i x.self.params }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_remove kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hrem_drop,
            gcLoop_of_ge (kh.remove i x.self.params) (toBEBytes 4 thVal) x.self.params i hnot_lt]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh.remove i x.self.params }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hfits_tail hev_tail hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
    · have hskip : bytesLt (kh.data.extract i (i + 4)) (toBEBytes 4 thVal) = false := Bool.eq_false_of_ne_true hrem
      wp_norm_hyp hskip
      by_cases hlt36 : i + 36 < kh.data.length
      · have hlt36_t : decide (i + 36 < kh.data.length) = true := decide_eq_true hlt36
        wp_norm_hyp hlt36_t
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 932#64)
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres' :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params (i + 36))
              let recv2 := { recv1 with prev := prevGc }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop]; rfl
        have hdec : kh.data.length - (i + 36) < kh.data.length - i := by omega
        refine SepWPp.mono_pre _ ?_
          (h_next kh (i + 36) hp_le hlt36 hdec hres' _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · have hlt36_f : decide (i + 36 < kh.data.length) = false := decide_eq_false hlt36
        wp_norm_hyp hlt36_f
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 660#64)
        refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
        have hpack_prev := vecU8At_pack_prev A.repAlloc
          (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
          prevPin.cap prevPin.ptr kh.data hp_le hp_cap hp_ptr
        have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
        have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
            x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
        rw [ha58, ha60] at hpack_prev; clear ha58 ha60
        refine SepWP.fold hpack_prev (by sep_focus) ?_
        refine SepWP.fold (pointsTo32_memRegion_32_entails_36 s0.sp (rev32Trunc thVal)) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
           (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hex_eq : kh.data.extract i (i + 4) = (kh.data.drop i).take 4 := by
          rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
        have hskip_drop : bytesLt ((kh.data.drop i).take 4) (toBEBytes 4 thVal) = false := by rwa [← hex_eq]
        have hres660 :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv2 := { recv1 with prev := kh }
              let (next', ctr', (_, outKey)) ←
                ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
              let recv' := { recv2 with next := next', ctr := ctr' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, gcLoop_of_skip kh (toBEBytes 4 thVal) x.self.params i hi_lt hbounds hskip_drop,
            gcLoop_of_ge kh (toBEBytes 4 thVal) x.self.params (i + KeyHistory.KEY_SIZE) hlt36]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_from660 { recv1 with prev := kh }
            hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hfits_tail hev_tail hres660 _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame

theorem recvKey_gc_loop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf M A lim)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362) (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (st0 st_gc : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length) (gce : ChainEpochGhost) (prevPin : VecPin)
    (recv1 : ChainEpochDirection) (thVal : BitVec 32)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hfits_tail : FitsEvents M lim st_gc (nextKeyInternalEvents ++ rustAllocEvents 32 1))
    (hev_tail : M.stepEvents (nextKeyInternalEvents ++ rustAllocEvents 32 1) st_gc =
      M.stepEvents (chainRecvKeyEvents hkdf x) st0)
    (fuel : Nat) :
    ∀ (kh : KeyHistory) (i : Nat) (_hfuel : kh.data.length - i ≤ fuel)
      (_hp_le : kh.data.length ≤ prevPin.cap.toNat) (_hi_lt : i < kh.data.length)
      (_hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
        let prevGc ← ChainResult.ofPanic (KeyHistory.gcLoop kh (toBEBytes 4 thVal) x.self.params i)
        let recv2 := { recv1 with prev := prevGc }
        let (next', ctr', (_, outKey)) ← ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
        let recv' := { recv2 with next := next', ctr := ctr' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey)))
      (s : State) (_hinv : RecvKeyPlacedStateInv lsmpl s0 s)
      (_hpc : s.pc = (blkPl_366).base + 932#64)
      (_hx0 : s.readReg64 (.gpr 0#5) = BitVec.ofNat 64 i) (_hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 kh.data.length)
      (_hx8 : s.readReg64 (.gpr 8#5) = prevPin.ptr) (_hx19 : s.readReg64 (.gpr 19#5) = x.out)
      (_hx21 : s.readReg64 (.gpr 21#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
      (_hx22 : s.readReg64 (.gpr 22#5) = x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)),
      let prog := (blkPC_366).rebase (blkPl_366).base H
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
      SepWPp prog (s0.readReg64 (.gpr 30#5)) s
        (memRegion x.out 32 ∗ chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
          vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
          ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 kh.data.length) ∗ (prevPin.ptr ↦ₛ kh.data) ∗
          vecU8Rest A.repAlloc prevPin.cap prevPin.ptr kh.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ ((s0.sp - 120#64) ↦₃₂ rev32Trunc thVal) ∗
          memRegion (s0.sp - 116#64) 32 ∗ recvKeyFrameRestAt s0 c3 ∗ A.pool lim st_gc s)
        (recvKeyPost M A lim hkdf x st0 s0) (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  induction fuel with
  | zero => intro kh i hfuel _ hi_lt; omega
  | succ fuel ih =>
    intro kh i hfuel hp_le hi_lt hres s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22
    exact recvKey_gc_loop_step_placed hnextKey hnextKeyPanic hshim halloc hslice_ext
      x st0 st_gc s0 c3 epochIndex hi_ep gce prevPin recv1 kh thVal i
      hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hi_lt hfits_tail hev_tail hres
      (fun kh' i' hp_le' hi_lt' hdec => ih kh' i' (by omega) hp_le' hi_lt')
      s hinv hpc hx0 hx2 hx8 hx19 hx21 hx22

set_option maxHeartbeats 800000 in
theorem recvKey_gc_from_616_placed [LibsignalPlacement] {M : AllocCostModel}
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
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (st0 st_gc : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin) (recv1 : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat) (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64) (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hn_le : recv1.next.length ≤ gce.recv.next.cap.toNat) (hn_cap : gce.recv.next.cap.toNat < 2 ^ 63)
    (hn_ptr : gce.recv.next.ptr ≠ 0) (hp_le : recv1.prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hfits_tail : FitsEvents M lim st_gc (nextKeyInternalEvents ++ rustAllocEvents 32 1))
    (hev_tail : M.stepEvents (nextKeyInternalEvents ++ rustAllocEvents 32 1) st_gc =
      M.stepEvents (chainRecvKeyEvents hkdf x) st0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let prevGc ← ChainResult.ofPanic (recv1.prev.gc recv1.ctr x.self.params)
      let recv2 := { recv1 with prev := prevGc }
      let (next', ctr', (_, outKey)) ←
        ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
      let recv' := { recv2 with next := next', ctr := ctr' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 616#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = recv1.ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗ ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 recv1.next.length) ∗ (gce.recv.next.ptr ↦ₛ recv1.next) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr recv1.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗ ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv1.prev.data.length) ∗ (prevPin.ptr ↦ₛ recv1.prev.data) ∗
        vecU8Rest A.repAlloc prevPin.cap prevPin.ptr recv1.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv1.ctr) ∗ memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool lim st_gc s)
      (recvKeyPost M A lim hkdf x st0 s0) (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro prog s_idx epPtr
  have h_from660 := @recvKey_from_660_placed _ M A lim hkdf H hnextKey hnextKeyPanic hshim halloc
    x st0 st_gc s0 c3 R epochIndex hi_ep gce prevPin
  have h_loop := @recvKey_gc_loop_placed _ M A lim hkdf H hnextKey hnextKeyPanic hshim halloc hslice_ext
    x st0 st_gc s0 c3 R epochIndex hi_ep gce prevPin recv1
    (recv1.ctr - x.self.params.maxOooKeysOrDefault)
    hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hp_cap hp_ptr hfits_tail hev_tail
  clear hnextKey hnextKeyPanic hshim halloc hslice_ext
  dsimp only [prog, s_idx, epPtr]; clear prog s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  have hsp0_align' := hsp0_align; wp_norm_hyp hsp0_align'
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have hbs_lt : recv1.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have htrim_eq := trimSize_mul36_eq x.self.params
  dsimp only at htrim_eq
  have ⟨hult_trim, hule_trim, hult_uf, hule_uf⟩ :=
    gc_entry_arith_props recv1.prev.data.length recv1.ctr x.self.params hbs_lt
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx19; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp htrace
  wp_norm_hyp htrim_eq; wp_norm_hyp hult_trim; wp_norm_hyp hule_trim; wp_norm_hyp hult_uf; wp_norm_hyp hule_uf
  by_cases hge : recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE
  · have hge_t : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = true :=
      decide_eq_true hge
    wp_norm_hyp hge_t
    by_cases huf : recv1.ctr < x.self.params.maxOooKeysOrDefault
    · have huf_t : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = true := decide_eq_true huf
      wp_norm_hyp huf_t
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic_ext) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_gc_of_underflow recv1.prev recv1.ctr x.self.params hge huf]; rfl
      exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have huf_f : decide (recv1.ctr < x.self.params.maxOooKeysOrDefault) = false := decide_eq_false huf
      wp_norm_hyp huf_f
      refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u32 s0.sp)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro d_sp8
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 932#64) hF ?_
      wp_steps_sync_pool ((blkPl_366).base + 932#64)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
         (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
         allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
      have hres_loop :
          Chain.recvKey hkdf x.self x.epoch x.index = (do
            let prevGc ← ChainResult.ofPanic
              (KeyHistory.gcLoop recv1.prev (toBEBytes 4 (recv1.ctr - x.self.params.maxOooKeysOrDefault)) x.self.params 0)
            let recv2 := { recv1 with prev := prevGc }
            let (next', ctr', (_, outKey)) ←
              ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv2.next recv2.ctr)
            let recv' := { recv2 with next := next', ctr := ctr' }
            let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
            return ({ x.self with links := links' }, outKey)) := by
        rw [hres, keyHistory_gc_of_ok recv1.prev recv1.ctr x.self.params hge huf]
      have htrim_pos : 0 < x.self.params.trimSize * KeyHistory.KEY_SIZE := by
        dsimp [ChainParamsPB.trimSize, KeyHistory.KEY_SIZE]; omega
      have hpos : 0 < recv1.prev.data.length := by omega
      refine SepWPp.mono_pre _ ?_
        (h_loop recv1.prev.data.length recv1.prev 0 (Nat.sub_le _ _) hp_le hpos hres_loop _ hinv'
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
          (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  · have hge_f : decide (recv1.prev.data.length ≥ x.self.params.trimSize * KeyHistory.KEY_SIZE) = false :=
      decide_eq_false hge
    wp_norm_hyp hge_f
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 660#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 660#64)
    have hpack_prev := vecU8At_pack_prev A.repAlloc
      (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
      prevPin.cap prevPin.ptr recv1.prev.data hp_le hp_cap hp_ptr
    have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
    have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
    rw [ha58, ha60] at hpack_prev; clear ha58 ha60
    refine SepWP.fold hpack_prev (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align,
       (by wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal), htrace, (by wp_norm_goal),
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hres660 :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (next', ctr', (_, outKey)) ←
            ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf recv1.next recv1.ctr)
          let recv' := { recv1 with next := next', ctr := ctr' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, keyHistory_gc_of_lt recv1.prev recv1.ctr x.self.params hge]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_from660 recv1 hhead hcap_lt hptr hlen_le hlen_eq hn_le hn_cap hn_ptr hfits_tail hev_tail hres660 _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGcBudget
