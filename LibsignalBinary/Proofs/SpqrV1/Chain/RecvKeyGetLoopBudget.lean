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
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `KeyHistory::get` Proofs for `<spqr::chain::Chain>::recv_key` (Block `366`)

Proves the relocatable `[LibsignalPlacement]` `KeyHistory::get` entry (`+276`), linear-scan loop
(`+740`), and swap-remove hit continuation (`+788`) of `<spqr::chain::Chain>::recv_key`
(`blkPC_366`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoopBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_366 blkPl_366)
open CryptoVerification.LibsignalSpqrV1 (Chain HkdfFn KeyHistory)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.RustHeap (LayoutOk vecU8At)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost ChainRecvKeyGhost
  SepWP.seq_cps SepWPp.mono_pre
  chainOuterRecvAt chainOuterRecvAt_pack chainOuterRecvAt_pack_unchanged
  exists_entry36_get_cells exists_entry36_swap_cells getLoop_of_ge getLoop_of_hit getLoop_of_miss
  get_entry_div36_props get_entry_ovf_props get_loop_idx_props get_swap_idx_props
  keyHistory_get_addOverflow keyHistory_get_loop keyHistory_get_trimmed keyHistory_get_unaligned
  maxOooKeysOrDefault_eq_ite memRegion_36_split_u64 nextKeyInternalStackX pack32LE
  pack32LE_beq_rev32Trunc_iff pointsTo64_memRegion_28_entails_36 pointsToBytes_split_u32_at
  recvKeyFrameRestAt rev32Trunc vecDequePhysIdx vecU8At_pack_remove_last
  vecU8At_pack_remove_swap
)
open CryptoVerification.SpqrV1.ChainProofs.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochFacts (vecU8At_unpack vecU8Rest)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (
  SepWPp.pure_left_focus memRegion_32_cells4
)
open CryptoVerification.SpqrV1.ChainProofs.ChainSendKeyFacts (stackAt_nextKeyInternalX_top_split)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (SepWPp.of_sepWP_lsCallInv)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans subroutine_ok_allocNoOomWithStack_of_budget
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget (
  RecvKeyPlacedStateInv allowPanic_recvKey_panic recvKeyPanic recvKeyPost
  recvKey_err_keyAlreadyRequested_from_880_placed recvKey_err_keyTrimmed_from_884_placed
  recvKey_ok_from_708_placed
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (
  ChainRecvKeyEnv chainRecvKeyEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

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

set_option maxHeartbeats 1200000 in
/-- Hit continuation of `KeyHistory::get` (`+788 -> s0.lr`) under `RustCliAllocBudget`: allocates
the 32-byte output key without OOM under `FitsEvents M lim st (rustAllocEvents 32 1)`, performs
in-place swap-remove on `recv.prev`, and finishes via `recvKey_ok_from_708_placed`. -/
theorem recvKey_get_hit_from_788_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hev : chainRecvKeyEvents hkdf x = rustAllocEvents 32 1)
    (hfits : FitsEvents M lim st (rustAllocEvents 32 1))
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (_hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (_hi_mod : i % 36 = 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index =
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let recv' := { recv with prev := recv.prev.remove i x.self.params }
      let outKey := (recv.prev.data.drop (i + 4)).take 32
      .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 788#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr)
    (hx25 : s.readReg64 (.gpr 25#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st s)
      (recvKeyPost M A lim hkdf x st s0)
      (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro s_idx epPtr recv
  have halloc_nooom := subroutine_ok_allocNoOomWithStack_of_budget halloc
  have h_ok708 := @recvKey_ok_from_708_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨_, _, _, _, hi_add36, hult_i36, hult_i⟩ := get_loop_idx_props hi36 hbs_lt
  have ⟨hule_swap, hswap_lt⟩ := get_swap_idx_props hi36 hbs_lt
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx19; wp_norm_hyp hx21
  wp_norm_hyp hx22; wp_norm_hyp hx23; wp_norm_hyp hx24; wp_norm_hyp hx25; wp_norm_hyp htrace
  wp_norm_hyp hi_add36; wp_norm_hyp hult_i36; wp_norm_hyp hult_i
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 820#64) hF ?_
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  have hstack_s0 : stackAt (s0.sp - 128#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wp_call halloc_nooom (32, 1, st)
  have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
  have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom_64
  wp_norm_hyp hoom_beq
  have hacp_shim : AllocCallPreserved s sf := by
    have h := ‹AllocCallPreserved _ sf›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_alloc : AllocCallPreserved sf sf_1 := by
    have h := ‹AllocCallPreserved _ sf_1›; unfold AllocCallPreserved at h ⊢; simpa only [wp_norm, arm64_norm] using h
  have hacp_s1 : AllocCallPreserved s0 sf_1 :=
    allocCallPreserved_trans hacp (allocCallPreserved_trans hacp_shim hacp_alloc)
  have htr_sf1 : sf_1.trace = s0.trace := hacp_s1.2.1
  wp_norm_hyp htr_sf1
  wp_steps_sync_pool ((blkPl_366).base + 820#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  let p_key := sf_1.readReg64 (Reg.gpr 0#5)
  have hstack_back :
      memRegion (s.sp - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗ stackAt sf.sp extHookStack =
        stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
    rw [‹sf.sp = s.sp›, ← stackAt_nextKeyInternalX_top_split s.sp, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold (Entails.of_eq (memRegion_32_cells4 p_key)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
  obtain ⟨k0, k1, k2, k3, hget_cells⟩ :=
    exists_entry36_get_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i hi36
  have ⟨hbs_get, hkey_pack⟩ := hget_cells gce.recv.prev.ptr
  refine SepWPp.fold (Entails.of_eq hbs_get) (by sep_focus) ?_
  have hsp_sf1 : sf_1.sp = s0.sp - 128#64 := by rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
  have hsp1_align : sf_1.spAligned = true := by
    simp only [State.spAligned, hsp_sf1] at hsp0_align ⊢; revert hsp0_align; bv_kernel
  wp_norm_hyp hsp_sf1; wp_norm_hyp hsp1_align; wp_norm_hyp hule_swap
  let outKey := ((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop (i + 4)).take 32
  have houtKey_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.extract (i + 4) (i + 36) = outKey := by
    rw [List.extract_eq_take_drop, show i + 36 - (i + 4) = 32 by omega]
  have houtKey_len : outKey.length = 32 := by
    rw [← houtKey_eq]; simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  by_cases hlt_end : i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length
  · have hule_f : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = false :=
      decide_eq_false (not_not.mpr hlt_end)
    have ⟨hsub36, hult_sub36⟩ := hswap_lt hlt_end
    wp_norm_hyp hule_f; wp_norm_hyp hsub36; wp_norm_hyp hult_sub36
    obtain ⟨ei0, ei1, ei2, ei3, ei4, el0, el1, el2, el3, el4, hswap_cells⟩ :=
      exists_entry36_swap_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega) (by omega)
    have ⟨hbs_swap_in, hbs_swap_out⟩ := hswap_cells gce.recv.prev.ptr
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hinv4 ?_
    apply SepWP.seq_cps (mid := (blkPl_366).base + 840#64)
    wp_steps_sync_pool ((blkPl_366).base + 840#64)
    refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hbs_swap_in) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    wp_steps_sync_pool ((blkPl_366).base + 708#64)
    refine SepWP.fold (Entails.of_eq hbs_swap_out) (by sep_focus) ?_
    have hrem := vecU8At_pack_remove_swap A.repAlloc
      (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
      gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params hlt_end hp_le hp_cap hp_ptr
    dsimp only [KeyHistory.KEY_SIZE] at hrem
    have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
    have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
    rw [ha58, ha60] at hrem
    refine SepWP.fold hrem (by sep_focus) ?_
    have hpack := chainOuterRecvAt_pack A.repAlloc x epochIndex hi_ep gce gce.recv.prev
      { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
      hhead hcap_lt hptr hlen_le hlen_eq
    dsimp only at hpack
    refine SepWP.fold hpack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal),
       allocCallPreserved_trans hacp_s1 (by unfold AllocCallPreserved; wp_norm_goal)⟩
    refine SepWPp.mono_pre _ ?_
      (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
        (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
    rw [houtKey_eq, hev]; sep_frame
  · have hule_t : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = true :=
      decide_eq_true hlt_end
    wp_norm_hyp hule_t
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hinv4 ?_
    wp_steps_sync_pool ((blkPl_366).base + 708#64)
    refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
    have hrem := vecU8At_pack_remove_last A.repAlloc
      (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
      gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params (by omega) hlt_end hp_le hp_cap hp_ptr
    have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
    have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
    rw [ha58, ha60] at hrem
    refine SepWP.fold hrem (by sep_focus) ?_
    have hpack := chainOuterRecvAt_pack A.repAlloc x epochIndex hi_ep gce gce.recv.prev
      { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
      hhead hcap_lt hptr hlen_le hlen_eq
    dsimp only at hpack
    refine SepWP.fold hpack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal),
       allocCallPreserved_trans hacp_s1 (by unfold AllocCallPreserved; wp_norm_goal)⟩
    refine SepWPp.mono_pre _ ?_
      (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
        (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
    rw [houtKey_eq, hev]; sep_frame

set_option maxHeartbeats 800000 in
/-- Loop-exhaustion base case (`+740 -> +880 -> s0.lr`) of `KeyHistory::get` under
`RustCliAllocBudget`. -/
theorem recvKey_get_loop_zero_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hev : chainRecvKeyEvents hkdf x = [])
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (i : Nat) (hi_eq : i = (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 740#64)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st s)
      (recvKeyPost M A lim hkdf x st s0)
      (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro s_idx epPtr recv; subst hi_eq
  have h_err880 := @recvKey_err_keyAlreadyRequested_from_880_placed _ M A lim hkdf H x st s0 c3 R
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have hadd36 : (BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length - 36#64) + 36#64 =
      BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by bv_omega
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx9; wp_norm_hyp hx11
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hadd36
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 880#64) hF ?_
  wp_steps_sync_pool ((blkPl_366).base + 880#64)
  have hpack := chainOuterRecvAt_pack_unchanged A.repAlloc x epochIndex hi_ep gce
    hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
  dsimp only at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal),
     allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
  have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)) := by
    rw [hres, getLoop_of_ge _ _ _ _ _ (Nat.lt_irrefl _)]; rfl
  refine SepWPp.mono_pre _ ?_
    (h_err880 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  rw [hev, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; sep_frame

set_option maxHeartbeats 800000 in
/-- Single iteration of `KeyHistory::get` loop at `+740` under `RustCliAllocBudget`. -/
theorem recvKey_get_loop_step_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hi_mod : i % 36 = 0)
    (hev_ok : ∀ prev' outKey,
      KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
        (toBEBytes 4 x.index) x.self.params i = .ok (prev', outKey) →
      chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 ∧
        FitsEvents M lim st (rustAllocEvents 32 1))
    (hev_err : ∀ e,
      KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
        (toBEBytes 4 x.index) x.self.params i = .error e →
      chainRecvKeyEvents hkdf x = [])
    (h_ih :
      (∀ prev' outKey,
        KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (toBEBytes 4 x.index) x.self.params (i + 36) = .ok (prev', outKey) →
        chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 ∧
          FitsEvents M lim st (rustAllocEvents 32 1)) →
      (∀ e,
        KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (toBEBytes 4 x.index) x.self.params (i + 36) = .error e →
        chainRecvKeyEvents hkdf x = []) →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyPlacedStateInv lsmpl s0 s →
        s.pc = (blkPl_366).base + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
            vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool lim st s)
          (recvKeyPost M A lim hkdf x st s0)
          (recvKeyPanic M A lim hkdf x st s0 R))
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 740#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st s)
      (recvKeyPost M A lim hkdf x st s0)
      (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro s_idx epPtr recv
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have hprops := get_loop_idx_props hi36 hbs_lt
  have hadd40 : BitVec.ofNat 64 i + 4#64 = BitVec.ofNat 64 (i + 4) := by bv_omega
  have hneq_len := hprops.2.2.1; have hult_i4 := hprops.2.2.2.1; clear hprops
  have h_hit := @recvKey_get_hit_from_788_placed _ hkdf M A lim H hshim halloc x st s0 c3 R
  clear hshim halloc
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have hsplit4 := pointsToBytes_split_u32_at gce.recv.prev.ptr
    (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega)
  refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx9; wp_norm_hyp hx10; wp_norm_hyp hx11; wp_norm_hyp hx19
  wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hx24
  wp_norm_hyp hadd40; wp_norm_hyp hneq_len; wp_norm_hyp hult_i4
  have hex_len : ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)).length = 4 := by
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  have hcmp_eq :
      (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) =
        (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) := by
    rw [pack32LE_beq_rev32Trunc_iff hex_len x.index, List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
  by_cases hhit : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = true
  · have hbeq_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = true := by
      rw [hcmp_eq, hhit]
    have hbne_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = false := by
      simp only [bne, hbeq_t, Bool.not_true]
    wp_norm_hyp hbeq_t; wp_norm_hyp hbne_f
    have hloop_hit := getLoop_of_hit (x.self.links[epochIndex]'hi_ep).recv.prev x.index
      (toBEBytes 4 x.index) x.self.params i (by omega) hhit
    have ⟨hev_hit, hfits_hit⟩ := hev_ok _ _ hloop_hit
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 788#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 788#64)
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal),
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hres_hit :
        Chain.recvKey hkdf x.self x.epoch x.index =
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let recv' := { recv with prev := recv.prev.remove i x.self.params }
          let outKey := (recv.prev.data.drop (i + 4)).take 32
          .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey) := by
      rw [hres, hloop_hit]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_hit hev_hit hfits_hit epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
        hp_le hp_cap hp_ptr hlen_mod i hi36 hi_mod hres_hit _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhit_f : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = false :=
      Bool.eq_false_iff.mpr hhit
    have hbeq_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = false := by
      rw [hcmp_eq, hhit_f]
    have hbne_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = true := by
      simp only [bne, hbeq_f, Bool.not_false]
    wp_norm_hyp hbeq_f; wp_norm_hyp hbne_t
    have hloop_miss := getLoop_of_miss (x.self.links[epochIndex]'hi_ep).recv.prev x.index
      (toBEBytes 4 x.index) x.self.params i (by omega) hhit_f
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 740#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 740#64)
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal),
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hres_miss :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
          let recv' := { recv with prev := prev' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, hloop_miss]; rfl
    have hptr_i_next : gce.recv.prev.ptr + BitVec.ofNat 64 i =
        gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    have hi_next : BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    refine SepWPp.mono_pre _ ?_
      (h_ih (fun p' k' h => hev_ok p' k' (hloop_miss.trans h))
        (fun e' h => hev_err e' (hloop_miss.trans h))
        hres_miss _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hptr_i_next]; wp_norm_goal) (by rw [← hi_next]; wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

/-- Full linear-scan loop (`+740`) of `KeyHistory::get` under `RustCliAllocBudget`. -/
theorem recvKey_get_loop_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (k : Nat) :
    ∀ (i : Nat),
      i ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
      i % 36 = 0 →
      ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length - i) / 36 = k →
      (∀ prev' outKey,
        KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (toBEBytes 4 x.index) x.self.params i = .ok (prev', outKey) →
        chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 ∧
          FitsEvents M lim st (rustAllocEvents 32 1)) →
      (∀ e,
        KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (toBEBytes 4 x.index) x.self.params i = .error e →
        chainRecvKeyEvents hkdf x = []) →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyPlacedStateInv lsmpl s0 s →
        s.pc = (blkPl_366).base + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
            vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A.repAlloc gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool lim st s)
          (recvKeyPost M A lim hkdf x st s0)
          (recvKeyPanic M A lim hkdf x st s0 R) := by
  induction k with
  | zero =>
    intro i hi_le hi_mod hk _hev_ok hev_err hres s hinv hpc _ hx9 _ hx11 hx19 hw20 _ _ _
    have hi_eq : i = (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    have hev_nil : chainRecvKeyEvents hkdf x = [] :=
      hev_err (.err (.keyAlreadyRequested x.index))
        (by rw [hi_eq]; exact getLoop_of_ge _ _ _ _ _ (Nat.lt_irrefl _))
    exact recvKey_get_loop_zero_placed x st s0 c3 hev_nil epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
      i hi_eq hres s hinv hpc hx9 hx11 hx19 hw20
  | succ k ih =>
    intro i hi_le hi_mod hk hev_ok hev_err hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24
    have hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    exact recvKey_get_loop_step_placed hshim halloc x st s0 c3 epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr hlen_mod
      i hi36 hi_mod hev_ok hev_err (ih (i + 36) hi36 (by omega) (by omega))
      hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24

set_option maxHeartbeats 800000 in
/-- Entry of `KeyHistory::get` at `+276` (`x.index < link.recv.ctr`) under `RustCliAllocBudget`. -/
theorem recvKey_get_from_276_placed [LibsignalPlacement] {hkdf : HkdfFn}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack))
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hnot_zero : (x.epoch == 0#64 && x.index == 0#32) = false)
    (hepIdx : x.self.epochIdx x.epoch = .ok epochIndex)
    (hlt_ctr : x.index < (x.self.links[epochIndex]'hi_ep).recv.ctr)
    (hfits_env : FitsEnv M lim st (ChainRecvKeyEnv hkdf x))
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 276#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = (x.self.links[epochIndex]'hi_ep).recv.ctr)
    (hw10 : (s.readReg64 (.gpr 10#5)).setWidth 32 = x.self.params.maxOooKeys)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        vecU8At A.repAlloc (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        vecU8At A.repAlloc (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st s)
      (recvKeyPost M A lim hkdf x st s0)
      (recvKeyPanic M A lim hkdf x st s0 R) := by
  intro s_idx epPtr recv
  have hev_branch :
      chainRecvKeyEvents hkdf x =
        match (x.self.links[epochIndex]'hi_ep).recv.prev.get x.index
          (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params with
        | .ok _ => rustAllocEvents 32 1
        | .error _ => [] := by
    unfold chainRecvKeyEvents
    rw [hnot_zero, hepIdx]
    simp only [Bool.false_eq_true, ↓reduceIte, hi_ep, ↓reduceDIte, hlt_ctr]
    rfl
  have hfits_self : FitsEvents M lim st (chainRecvKeyEvents hkdf x) :=
    hfits_env (chainRecvKeyEvents hkdf x) rfl
  have h_err884 := @recvKey_err_keyTrimmed_from_884_placed _ M A lim hkdf H x st s0 c3 R
  have h_loop := @recvKey_get_loop_placed _ hkdf M A lim H hshim halloc x st s0 c3 R
    epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
  clear hshim halloc
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hunpack := vecU8At_unpack A.repAlloc
    (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
    gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data
  have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
  have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack; clear ha58 ha60
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hp_le, hp_cap, hp_ptr⟩
  refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u64 s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u_sp8
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hmul36, hsub36, hbeq_div36, hbne_div36, hbeq_mod36⟩ := get_entry_div36_props hbs_lt
  have hmaxOoo := maxOooKeysOrDefault_eq_ite x.self.params
  have ⟨hadd_comm, hovf_iff, huadd_ovf, hult_ovf1, hult_ovf2, hult_trim, hule_trim⟩ :=
    get_entry_ovf_props x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hw10
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hmul36; wp_norm_hyp hsub36; wp_norm_hyp hbeq_div36; wp_norm_hyp hbne_div36
  wp_norm_hyp hbeq_mod36; wp_norm_hyp hmaxOoo; wp_norm_hyp hadd_comm; wp_norm_hyp huadd_ovf
  wp_norm_hyp hult_ovf1; wp_norm_hyp hult_ovf2; wp_norm_hyp hult_trim; wp_norm_hyp hule_trim
  by_cases hmod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0
  · have hmod_t : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = true := decide_eq_true hmod
    have hdiv_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36 * 36 =
        (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    wp_norm_hyp hmod_t
    by_cases hovf : x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
    · have hovf_t : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = true :=
        decide_eq_true hovf
      wp_norm_hyp hovf_t
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
      wp_steps_sync_pool (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hadd_ext) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_get_addOverflow _ _ _ _ hmod hovf]; rfl
      exact allowPanic_recvKey_panic (M := M) (A := A) (lim := lim) hpan
        (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have hovf_f : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = false :=
        decide_eq_false hovf
      wp_norm_hyp hovf_f
      by_cases htrim : x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr
      · have htrim_t : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = true :=
          decide_eq_true htrim
        wp_norm_hyp htrim_t
        have hget_trim := keyHistory_get_trimmed (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params hmod hovf htrim
        have hev_trim : chainRecvKeyEvents hkdf x = [] := by rw [hev_branch, hget_trim]
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 884#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 884#64)
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        have hpack := chainOuterRecvAt_pack_unchanged A.repAlloc x epochIndex hi_ep gce
          hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
        dsimp only at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
           (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hres_trim : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)) := by
          rw [hres, hget_trim]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_err884 hres_trim _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        rw [hev_trim, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; sep_frame
      · have htrim_f : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = false :=
          decide_eq_false htrim
        wp_norm_hyp htrim_f
        have hget_loop := keyHistory_get_loop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
          (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params hmod hovf htrim
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 740#64) hF ?_
        wp_steps_sync_pool ((blkPl_366).base + 740#64)
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
           (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal),
           allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
        have hres_loop :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params 0
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, hget_loop]
        have hptr0 : gce.recv.prev.ptr - 36#64 = gce.recv.prev.ptr + BitVec.ofNat 64 0 - 36#64 := by
          simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        have hev_ok0 : ∀ prev' outKey,
            KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
              (toBEBytes 4 x.index) x.self.params 0 = .ok (prev', outKey) →
            chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 ∧
              FitsEvents M lim st (rustAllocEvents 32 1) := by
          intro prev' outKey hok0
          have hev_eq : chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 := by
            rw [hev_branch, hget_loop, hok0]
          exact ⟨hev_eq, hev_eq ▸ hfits_self⟩
        have hev_err0 : ∀ e,
            KeyHistory.getLoop (x.self.links[epochIndex]'hi_ep).recv.prev x.index
              (toBEBytes 4 x.index) x.self.params 0 = .error e →
            chainRecvKeyEvents hkdf x = [] := by
          intro e herr0
          rw [hev_branch, hget_loop, herr0]
        refine SepWPp.mono_pre _ ?_
          (h_loop hp_le hp_cap hp_ptr hmod
            ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36) 0
            (Nat.zero_le _) (Nat.zero_mod _) rfl hev_ok0 hev_err0 hres_loop _ hinv'
            (by wp_norm_goal) (by wp_norm_goal)
            (by rw [← hdiv_eq]; wp_norm_goal)
            (by rw [← hptr0]; wp_norm_goal)
            (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
  · have hmod_f : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = false := decide_eq_false hmod
    wp_norm_hyp hmod_f
    apply SepWPp.of_sepWP (mid := lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_")
    wp_steps_sync_pool (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_")
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hassert_ext) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, keyHistory_get_unaligned _ _ _ _ hmod]; rfl
    exact allowPanic_recvKey_panic (M := M) (A := A) (lim := lim) hpan
      (by simp only [Rust.panicked, arm64_norm, htrace]) hm

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoopBudget
