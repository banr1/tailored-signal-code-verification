/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Core
public import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.FetchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPaths
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Panic-Path Proofs for `consume_message_key` (Block 24)

Proves `EpiloguePanicPlacedSpec`, `EpiloguePanicPlacedRoSpec`, `LoopNoChainPanicPlacedSpec`, and
`LoopNoChainPanicPlacedRoSpec` under `RustCliAllocBudget M` and `SeamBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.CoreBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey RatchetState)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen lsLogFilterAddr lsmpl lsρ
)
open CryptoVerification.LibsignalSessionRepr (RatchetGhost chainAt)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkDummyImg cmkExpectFailedSym cmkLoopHeap_placed_eq
  cmkPanicAddOverflowSym cmkRustAllocSym cmkRustNoAllocShimSym
  cmk_externAt?_of_mem cmk_hook_ok_of_mem
  logFilterAddr_cmkDummyImg
)
open CryptoVerification.LibsignalSession.PanicPaths (
  cmkLoopHeap_decompose_panicPaths cmkPanicPathsUsed hmacWith_length keyToBytes32_length
  pointsTo8_eq_pointsToBytes reaches_outcome_panic_of_sepWPp sepWPp_seq_lscl
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  EpiloguePanicPlacedRoSpec EpiloguePanicPlacedSpec
  LoopNoChainPanicPlacedRoSpec LoopNoChainPanicPlacedSpec cmkShimSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.FetchBudget (
  call_alloc_32_placed call_findIndex_none_placed call_hmac_placed
  call_hmac_ro_placed call_shim_placed cmkPlacedSpec_onPanic_eq panic_cmk_placed
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem chainAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    chainAt (A.atState lim st s) = chainAt A.repAlloc :=
  rfl

private theorem sepWPp_seq_lscro_pp {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen
    (Φ := fun m => LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    ⟨hcl, hro⟩
    (SepWP.mono h fun _ _ _ _ hcont ⟨hc, hr⟩ => hcont hc hr)

theorem epiloguePanic_placed_ok' [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    EpiloguePanicPlacedSpec F A lim H := by
  intro hexp hovf hfind hhmac x st_init st _remEnv Gc stc ckc R s0 s hidx hcond hpan ⟨_hsb, hstate⟩
  obtain ⟨hpc, ⟨hrun, hsp, _hsp0_align, hsp_align, _hx29, htrace, hcl, _⟩,
    ⟨_hx21, hx23, hx26, hx27, hx28⟩, _, hmem⟩ := hstate
  rw [cmkLoopHeap_placed_eq] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_panicPaths hmem
  have hpan_ovf : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkPanicAddOverflowSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hovf
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hexp
  have hpc' : s.pc = (blkPl_24).base + 1244#64 := hpc
  clear hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsed
  rw [logFilterAddr_cmkDummyImg, chainAt_atState, RustCliAllocBudget.atState_pool]
  apply sepWPp_seq_lscl hcl (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 2#8]
  refine call_hmac_placed ((blkPl_24).base + bv% (1276)) (s0.sp - 224#64) x.ckA (keyToBytes32 ckc.key)
    (s0.sp - 320#64) [2#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length ckc.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 _hvmm1 hcl2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : s1.readReg64 .x28 = BitVec.zeroExtend 64 ckc.index := by
    simpa [CalleeSavedPreserved, hx28, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1
  by_cases hc : x.counter = BitVec.allOnes 32
  · have hckc_max : ckc.index = 0xffffffff#32 := hidx.trans hc
    rw [hckc_max] at hx28_1
    apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkPanicAddOverflowSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro _
    exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) hpan_ovf hpan
      (by simp [htr1, htrace, arm64_norm])
  · have hnone : stc.findReceiverChainIndex x.their = none := hcond.resolve_left hc
    have hz2 : (x.counter + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hc; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := x.counter.isLt
      rw [BitVec.toNat_add] at h1
      change (x.counter.toNat + 1) % 4294967296 = 0 at h1
      change x.counter.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 ckc.key) [2#8])
    rw [hw32 (s0.sp - 224#64)]
    refine CryptoVerification.LibsignalSession.PanicPaths.SepWPp.fold_cell64_320 (by wp_sep_access) fun u0 => ?_
    apply sepWPp_seq_lscl hcl2 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro hcl3
    refine call_findIndex_none_placed ((blkPl_24).base + bv% (1312)) Gc.chainsPtr x.theirA (s0.sp - 480#64)
      Gc stc x.their hfind
      (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
      (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
      hcl3 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 _hvmm2 hcl4 _ hx0_2
    apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    intro _
    exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) hpan_exp hpan
      (by simp [htr2, htr1, htrace, arm64_norm])

theorem epiloguePanic_placed_ro_ok' [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    EpiloguePanicPlacedRoSpec F A lim H := by
  intro hexp hovf hfind hhmac x st_init st _remEnv Gc stc ckc R s0 s hidx hcond hpan ⟨_hsb, hstate⟩ hro
  obtain ⟨hpc, ⟨hrun, hsp, _hsp0_align, hsp_align, _hx29, htrace, hcl, _⟩,
    ⟨_hx21, hx23, hx26, hx27, hx28⟩, _, hmem⟩ := hstate
  rw [cmkLoopHeap_placed_eq] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_panicPaths hmem
  have hpan_ovf : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkPanicAddOverflowSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hovf
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hexp
  have hpc' : s.pc = (blkPl_24).base + 1244#64 := hpc
  clear hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsed
  rw [logFilterAddr_cmkDummyImg, chainAt_atState, RustCliAllocBudget.atState_pool]
  apply sepWPp_seq_lscro_pp hcl hro (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1 hro1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 2#8]
  refine call_hmac_ro_placed ((blkPl_24).base + bv% (1276)) (s0.sp - 224#64) x.ckA (keyToBytes32 ckc.key)
    (s0.sp - 320#64) [2#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 hro1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length ckc.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 _hvmm1 hcl2 _hro2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : s1.readReg64 .x28 = BitVec.zeroExtend 64 ckc.index := by
    simpa [CalleeSavedPreserved, hx28, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1
  by_cases hc : x.counter = BitVec.allOnes 32
  · have hckc_max : ckc.index = 0xffffffff#32 := hidx.trans hc
    rw [hckc_max] at hx28_1
    apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkPanicAddOverflowSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro _
    exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) hpan_ovf hpan
      (by simp [htr1, htrace, arm64_norm])
  · have hnone : stc.findReceiverChainIndex x.their = none := hcond.resolve_left hc
    have hz2 : (x.counter + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hc; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := x.counter.isLt
      rw [BitVec.toNat_add] at h1
      change (x.counter.toNat + 1) % 4294967296 = 0 at h1
      change x.counter.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 ckc.key) [2#8])
    rw [hw32 (s0.sp - 224#64)]
    refine CryptoVerification.LibsignalSession.PanicPaths.SepWPp.fold_cell64_320 (by wp_sep_access) fun u0 => ?_
    apply sepWPp_seq_lscl hcl2 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro hcl3
    refine call_findIndex_none_placed ((blkPl_24).base + bv% (1312)) Gc.chainsPtr x.theirA (s0.sp - 480#64)
      Gc stc x.their hfind
      (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
      (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
      hcl3 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 _hvmm2 hcl4 _ hx0_2
    apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    intro _
    exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) hpan_exp hpan
      (by simp [htr2, htr1, htrace, arm64_norm])

theorem loopNoChainPanic_placed_ok' [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedSpec F A lim H := by
  intro hA hfind hhmac x st_init st R s0 s _ hnone hpan ⟨hsb, hstate⟩
  obtain ⟨hpc, ⟨hrun, hsp, _hsp0_align, hsp_align, _hx29, htrace, hcl, _⟩,
    ⟨_hx21, hx23, hx26, hx27, _hx28⟩, hloop_x19, hmem⟩ := hstate
  have hx19 : s.readReg64 .x19 = 1#64 := hloop_x19 rfl
  have hfit32 : FitsEvents M lim st (rustAllocEvents 32 1) :=
    hsb.1 (rustAllocEvents 32 1) (Or.inr rfl)
  rw [cmkLoopHeap_placed_eq] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_panicPaths hmem
  have halloc' :
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym)
        (rustCliAllocBudgetSpec M A lim false) :=
    cmk_hook_ok_of_mem hA.1
  have hshim' :
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.2.1
  have hpc' : s.pc = (blkPl_24).base + 820#64 := hpc
  clear hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsed
  rw [logFilterAddr_cmkDummyImg, chainAt_atState, RustCliAllocBudget.atState_pool]
  apply sepWPp_seq_lscl hcl (mid := lsmpl.base 73)
  wp_steps_sync_pool (lsmpl.base 73)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun, wp_norm, arm64_norm])
  intro hcl1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 1#8]
  refine call_hmac_placed ((blkPl_24).base + bv% (848)) (s0.sp - 224#64) x.ckA (keyToBytes32 x.ck.key)
    (s0.sp - 320#64) [1#8] (s0.sp - 480#64) hhmac
    (by simp [wp_norm, arm64_norm]) (by simp [hrun, wp_norm, arm64_norm])
    (by simp [hsp, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    hcl1 (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (keyToBytes32_length x.ck.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hvmm1 hcl2 hcs1
  refine SepWPp.transport_budgetPool hvmm1 (hnext := ?_)
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, wp_norm, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, wp_norm, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, wp_norm, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun1, wp_norm, arm64_norm])
  intro hcl3
  refine call_shim_placed ((blkPl_24).base + bv% (852)) (s0.sp - 480#64) hshim'
    (by simp [wp_norm, arm64_norm]) (by simp [hrun1, wp_norm, arm64_norm])
    (by simp [hsp1, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_align)
    hcl3 (by simp [wp_norm, arm64_norm]) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hvmm2 hcl4 hcs2
  refine SepWPp.transport_budgetPool hvmm2 (hnext := ?_)
  have hx23_2 : s2.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.1
  have hx26_2 : s2.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.2.2.2.1
  have hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkRustAllocSym)
  wp_steps_sync_pool (lsρ cmkRustAllocSym)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2, wp_norm, arm64_norm])
  intro hcl5
  refine call_alloc_32_placed ((blkPl_24).base + bv% (864)) (s0.sp - 480#64) halloc' hfit32
    (by simp [wp_norm, arm64_norm]) (by simp [hrun2, wp_norm, arm64_norm])
    (by simp [hsp2, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_align)
    hcl5 (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) ?_
  intro s3 a0 a1 a2 a3 hpc3 hrun3 hsp3 hsp3_align hacp3 hcl6 hcs3 hx0_3
  have htr3 := hacp3.2.1
  have hx23_3 : s3.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.1
  have hx26_3 : s3.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.2.2.2.1
  have hx27_3 : s3.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.2.2.2.2.1
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 x.ck.key) [1#8])
  rw [hw32 (s0.sp - 224#64)]
  apply sepWPp_seq_lscl hcl6 (mid := lsmpl.base 26)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
  intro hcl7
  refine call_findIndex_none_placed ((blkPl_24).base + bv% (900)) x.G.chainsPtr x.theirA (s0.sp - 480#64)
    x.G x.st x.their hfind
    (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    (by simp [hsp3, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp3_align)
    hcl7 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    hlen_chains hxs_lt hnone (by wp_sep_access) ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align htr4 _hvmm4 hcl8 _ hx0_4
  apply sepWPp_seq_lscl hcl8 (mid := lsρ cmkExpectFailedSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
  intro _
  exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) hpan_exp hpan
    (by simp [htr4, htr3, htr2, htr1, htrace, wp_norm, arm64_norm])

theorem loopNoChainPanic_placed_ro_ok' [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedRoSpec F A lim H := by
  intro hA hfind hhmac x st_init st R s0 s _ hnone hpan ⟨hsb, hstate⟩ hro
  obtain ⟨hpc, ⟨hrun, hsp, _hsp0_align, hsp_align, _hx29, htrace, hcl, _⟩,
    ⟨_hx21, hx23, hx26, hx27, _hx28⟩, hloop_x19, hmem⟩ := hstate
  have hx19 : s.readReg64 .x19 = 1#64 := hloop_x19 rfl
  have hfit32 : FitsEvents M lim st (rustAllocEvents 32 1) :=
    hsb.1 (rustAllocEvents 32 1) (Or.inr rfl)
  rw [cmkLoopHeap_placed_eq] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeap_decompose_panicPaths hmem
  have halloc' :
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym)
        (rustCliAllocBudgetSpec M A lim false) :=
    cmk_hook_ok_of_mem hA.1
  have hshim' :
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.2.1
  have hpc' : s.pc = (blkPl_24).base + 820#64 := hpc
  clear hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsed
  rw [logFilterAddr_cmkDummyImg, chainAt_atState, RustCliAllocBudget.atState_pool]
  apply sepWPp_seq_lscro_pp hcl hro (mid := lsmpl.base 73)
  wp_steps_sync_pool (lsmpl.base 73)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun, wp_norm, arm64_norm])
  intro hcl1 hro1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 1#8]
  refine call_hmac_ro_placed ((blkPl_24).base + bv% (848)) (s0.sp - 224#64) x.ckA (keyToBytes32 x.ck.key)
    (s0.sp - 320#64) [1#8] (s0.sp - 480#64) hhmac
    (by simp [wp_norm, arm64_norm]) (by simp [hrun, wp_norm, arm64_norm])
    (by simp [hsp, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    hcl1 hro1 (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (keyToBytes32_length x.ck.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hvmm1 hcl2 _hro2 hcs1
  refine SepWPp.transport_budgetPool hvmm1 (hnext := ?_)
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, wp_norm, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, wp_norm, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, wp_norm, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun1, wp_norm, arm64_norm])
  intro hcl3
  refine call_shim_placed ((blkPl_24).base + bv% (852)) (s0.sp - 480#64) hshim'
    (by simp [wp_norm, arm64_norm]) (by simp [hrun1, wp_norm, arm64_norm])
    (by simp [hsp1, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_align)
    hcl3 (by simp [wp_norm, arm64_norm]) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hvmm2 hcl4 hcs2
  refine SepWPp.transport_budgetPool hvmm2 (hnext := ?_)
  have hx23_2 : s2.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.1
  have hx26_2 : s2.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.2.2.2.1
  have hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_1, wp_norm, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkRustAllocSym)
  wp_steps_sync_pool (lsρ cmkRustAllocSym)
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2, wp_norm, arm64_norm])
  intro hcl5
  refine call_alloc_32_placed ((blkPl_24).base + bv% (864)) (s0.sp - 480#64) halloc' hfit32
    (by simp [wp_norm, arm64_norm]) (by simp [hrun2, wp_norm, arm64_norm])
    (by simp [hsp2, wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_align)
    hcl5 (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by wp_sep_access) ?_
  intro s3 a0 a1 a2 a3 hpc3 hrun3 hsp3 hsp3_align hacp3 hcl6 hcs3 hx0_3
  have htr3 := hacp3.2.1
  have hx23_3 : s3.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.1
  have hx26_3 : s3.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.2.2.2.1
  have hx27_3 : s3.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_2, wp_norm, arm64_norm] using hcs3.2.2.2.2.2.2.2.2.1
  obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
    exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 x.ck.key) [1#8])
  rw [hw32 (s0.sp - 224#64)]
  apply sepWPp_seq_lscl hcl6 (mid := lsmpl.base 26)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
  intro hcl7
  refine call_findIndex_none_placed ((blkPl_24).base + bv% (900)) x.G.chainsPtr x.theirA (s0.sp - 480#64)
    x.G x.st x.their hfind
    (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    (by simp [hsp3, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp3_align)
    hcl7 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    hlen_chains hxs_lt hnone (by wp_sep_access) ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align htr4 _hvmm4 hcl8 _ hx0_4
  apply sepWPp_seq_lscl hcl8 (mid := lsρ cmkExpectFailedSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
  intro _
  exact panic_cmk_placed (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) hpan_exp hpan
    (by simp [htr4, htr3, htr2, htr1, htrace, wp_norm, arm64_norm])

end LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.CoreBudget
