/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget Allocation & Decapsulation

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of `mac`/`ct2_128` allocation
(`+224 .. +292`, OOM-free under `FitsEvents`) and `decapsulate_compressed_key` (`+292 .. +480`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1bPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPl_350 lsProg_350 lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSpqrV1 (Bytes MlKem PolyDecoder mlkemDecapsSpec spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (
  AuthenticatorGhost SepWPp.pure_left_focus authenticatorPinAt vecBufAt
)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof (
  sp_add_neg688_eq_hsp sp_add_neg96_eq_hsp_592 sp_sub_688_eq_hsp sp_sub_96_eq_hsp_592
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost authenticatorPinAt_of_sp_1328 bytes_rem_entails_ct2DeallocAt ct2DeallocAt
  ct2DeallocAt_of_cells_drop ekSentCt1ReceivedCells_entails_memRegion_504 ekSentCt1ReceivedUcAt
  ekSentCt1ReceivedUcAt_expose_entails exists_unpack64_of_length_128 memRegion_128_cells
  memRegion_128_sp_288 memRegion_24_sp_1280 memRegion_48_sp_1328 ofNat_beq_2400_iff
  ofNat_beq_960_iff ofNat_sub_128_eq_zero_iff pointsToBytes_128_of_sp_288
  recv_ct2_chunk_isPanic_of_ct1_len_ne recv_ct2_chunk_isPanic_of_dk_len_ne someBranchFrameAt
  someBranchFrameAt_expose_decaps spqrMlkemDecapsSym spqrUnwrapFailedSym unusedFrameAt
  vecBufAt_of_bytes_live vecBufAt_zero_one vecU8At_of_sp_1280 vecU8HeapAt_expose_nonempty
  vecU8HeapAt_pure_bounds
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
  fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2ChunkEnv RecvCt2PlacedAlloc allowPanic_isPanic_budget_recvCt2 mlkem_decaps_placed_lscro
  recvCt2MacCt2AllocEvents recvCt2PlacedPostQ recvCt2PlacedPostQOfEnv
  recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp sepWPp_of_sepWP_lscro
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  session2MemcpyBudgetSpecX session2ShimBudgetSpecX
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``sp_sub_688_eq_hsp,
    ``sp_add_neg688_eq_hsp,
    ``sp_sub_96_eq_hsp_592,
    ``sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase nm `arm64_norm

/-! ## `mac` and `ct2` Heap Allocation (`+224 .. +292` + `len == 128` shortcut `+140 .. +152`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_alloc_mac_ct2_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 c6 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hfits : FitsEvents M lim st_cur (recvCt2MacCt2AllocEvents ct2Full.length))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_350).base + 224#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_ct2_128 : BitVec 64),
      ptr_ct2_128 ≠ 0#64 →
      st'.pc = (blkPl_350).base + 292#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x0 = ptr_ct2_128 →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = x.selfA →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st'.readReg64 .x27 = cap_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion ptr_ct2_128 128 ∗
          A.live ptr_ct2_128 128 1 ∗
          ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
          A.pool lim (M.stepEvents (recvCt2MacCt2AllocEvents ct2Full.length) st_cur) st' ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 2448#64) ↦₆₄ c6) ∗
        ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_shim := hA.shim_lscro
  have h_alloc := hA.allocNoOom_lscro
  have h_mc := hA.memcpy_lscro
  clear hA
  simp only [lsProg_350, session2ShimBudgetSpecX, session2MemcpyBudgetSpecX,
    rustCliAllocNoOomSpecWithStack] at h_shim h_alloc h_mc hcont ⊢
  have hzero_iff := ofNat_sub_128_eq_zero_iff hge128 hlt_max
  have hlay128 : RustLayoutOk 128 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  by_cases hlen128 : ct2Full.length = 128
  · have hzero : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = true := by
      rw [hzero_iff, decide_eq_true hlen128]
    have hmac_evs : recvCt2MacCt2AllocEvents ct2Full.length = rustAllocEvents 128 1 := by
      simp [recvCt2MacCt2AllocEvents, DefsPlacedBudget.recvCt2MacCt2AllocEvents,
        DefsBudget.recvCt2MacCt2AllocEvents, hlen128]
    have hfit_128 : FitsEvents M lim st_cur (rustAllocEvents 128 1) := hmac_evs ▸ hfits
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2_budget h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr1, hvm1⟩
    refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm1]) ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2_budget h_alloc (128, 1, st_cur) hinv2
    conv => arg 4; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp1, hoom128, _⟩
    have htr2 : sf_1.trace = sf.trace := hacp1.2.1
    have hoom128_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom128
    refine sepWPp_of_sepWP_lscro (mid := (blkPl_350).base + 292#64) hF_sf_1 ?_
    wp_steps_sync_pool ((blkPl_350).base + 292#64)
    simp only [State.setMem_setMem]
    have hdrop0 : (ct2Full.drop 128).length = 0 := by rw [List.length_drop, hlen128]
    have hsub0 : BitVec.ofNat 64 (ct2Full.length - 128) = 0#64 := by rw [hlen128]
    have hvb0 : ((s0.sp - 2448#64) ↦₆₄ 1#64) ⊢
        ((s0.sp - 2448#64) ↦₆₄ 1#64) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) 1#64 (ct2Full.drop 128) := by
      rw [hsub0]
      refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
      exact sepConj_mono_right (vecBufAt_zero_one A.repAlloc (ct2Full.drop 128) hdrop0)
    refine SepWP.fold hvb0 (by sep_focus) ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
      rw [← hstack_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv_end
    refine SepWPp.rw_pre (by rw [← hmac_evs]; sep_ac_rfl)
      (hcont _ 1#64 (sf_1.readReg64 Reg.x0) hoom128
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv_end
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hzero : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false := by
      rw [hzero_iff, decide_eq_false hlen128]
    have hnot_le : ¬ ct2Full.length ≤ 128 := by omega
    have hmac_evs : recvCt2MacCt2AllocEvents ct2Full.length =
        rustAllocEvents (ct2Full.length - 128) 1 ++ rustAllocEvents 128 1 := by
      simp [recvCt2MacCt2AllocEvents, DefsPlacedBudget.recvCt2MacCt2AllocEvents,
        DefsBudget.recvCt2MacCt2AllocEvents, hnot_le]
    have ⟨hfit_mac, hfit_128⟩ := (fitsEvents_append M lim
      (rustAllocEvents (ct2Full.length - 128) 1) (rustAllocEvents 128 1) st_cur).mp
      (hmac_evs ▸ hfits)
    let st_mac := M.stepEvents (rustAllocEvents (ct2Full.length - 128) 1) st_cur
    have hfit_128_mac : FitsEvents M lim st_mac (rustAllocEvents 128 1) := hfit_128
    have hlay_mac : RustLayoutOk (ct2Full.length - 128) 1 :=
      ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hsub_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdrop_len : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2_budget h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr1, hvm1⟩
    refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm1]) ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2_budget h_alloc (ct2Full.length - 128, 1, st_cur) hinv2
    conv => arg 4; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp1, hoom_mac, _⟩
    have htr2 : sf_1.trace = sf.trace := hacp1.2.1
    have hoom_mac_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_mac
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf_1 ?_
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
      rw [hsp_sf_1]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_lscro_recvCt2_budget h_mc
      (sf_1.readReg64 Reg.x0, ptr_ct2 + 128#64, ct2Full.drop 128) hinv3
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr3, hvm3⟩
    refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_mac _ _ hvm3]) ?_
    have hfold_mac :
        ((sf_1.readReg64 Reg.x0) ↦ₛ ct2Full.drop 128) ∗
          A.live (sf_1.readReg64 Reg.x0) (ct2Full.length - 128) 1 ⊢
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128))
          (sf_1.readReg64 Reg.x0) (ct2Full.drop 128) := by
      rw [← hdrop_len]
      exact vecBufAt_of_bytes_live A.repAlloc (sf_1.readReg64 Reg.x0) (ct2Full.drop 128)
        (by omega) (by omega)
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
    refine SepWP.fold hfold_mac (by sep_focus) ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
      rw [hsp_sf_2]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    wpp_call_lscro_recvCt2_budget h_shim () hinv4
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr4, hvm4⟩
    refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_mac _ _ hvm4]) ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf_3 ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
      rw [hsp_sf_3]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    wpp_call_lscro_recvCt2_budget h_alloc (128, 1, st_mac) hinv5
    conv => arg 4; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp2, hoom128, _⟩
    have htr5 : sf_4.trace = sf_3.trace := hacp2.2.1
    have hoom128_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom128
    refine sepWPp_of_sepWP_lscro (mid := (blkPl_350).base + 292#64) hF_sf_4 ?_
    wp_steps_sync_pool ((blkPl_350).base + 292#64)
    have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
      rw [← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv_end
    have hst_end :
        M.stepEvents (rustAllocEvents 128 1) st_mac =
          M.stepEvents (recvCt2MacCt2AllocEvents ct2Full.length) st_cur := by
      dsimp only [st_mac]
      rw [hmac_evs, M.stepEvents_append]
    refine SepWPp.rw_pre (by rw [hst_end]; sep_ac_rfl)
      (hcont _ (sf_1.readReg64 Reg.x0) (sf_4.readReg64 Reg.x0) hoom128
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv_end
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

theorem recv_ct2_chunk_alloc_mac_ct2_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 c6 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hfits : FitsEvents M lim st_cur (recvCt2MacCt2AllocEvents ct2Full.length))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_350).base + 224#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_ct2_128 : BitVec 64),
      ptr_ct2_128 ≠ 0#64 →
      st'.pc = (blkPl_350).base + 292#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x0 = ptr_ct2_128 →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = x.selfA →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st'.readReg64 .x27 = cap_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion ptr_ct2_128 128 ∗
          A.live ptr_ct2_128 128 1 ∗
          ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
          A.pool lim (M.stepEvents (recvCt2MacCt2AllocEvents ct2Full.length) st_cur) st' ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 2448#64) ↦₆₄ c6) ∗
        ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_alloc_mac_ct2_placed_wpp_ofPrePostEnv hA x ct2Full cap_ct2 ptr_ct2 c6 st0 st_cur
    s0 st F_frame R hfits hge128 hlt_max hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx26 hx27 hx29 hcont

theorem recv_ct2_chunk_alloc_mac_ct2_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 c6 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hfits : FitsEvents M lim st_cur (recvCt2MacCt2AllocEvents ct2Full.length))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_350).base + 224#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_ct2_128 : BitVec 64),
      ptr_ct2_128 ≠ 0#64 →
      st'.pc = (blkPl_350).base + 292#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x0 = ptr_ct2_128 →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = x.selfA →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st'.readReg64 .x27 = cap_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion ptr_ct2_128 128 ∗
          A.live ptr_ct2_128 128 1 ∗
          ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
          A.pool lim (M.stepEvents (recvCt2MacCt2AllocEvents ct2Full.length) st_cur) st' ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 2448#64) ↦₆₄ c6) ∗
        ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_alloc_mac_ct2_placed_wpp_ofEnv hA x ct2Full cap_ct2 ptr_ct2 c6 st0 st_cur
    s0 st F_frame R hfits hge128 hlt_max hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx23 hx26 hx27 hx29 hcont

/-! ## Copy `ct2[..128]`, Move `uc`, and Call `decapsulate_compressed_key` (`+292 .. +480`) -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_to_decaps_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c7 c8 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (R F_frame : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hle_cap : ct2Full.length ≤ cap_ct2.toNat)
    (hmax_cap : cap_ct2.toNat < 2 ^ 63)
    (hptr_ct2 : ptr_ct2 ≠ 0#64)
    (hcap_ct2 : cap_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 292#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_ct2_128)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State) (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64)
      (hct1_len : x.self.uc.ct1.length = 960)
      (htake128_len : (ct2Full.take 128).length = 128)
      (hdk_len : x.self.uc.dk.length = 2400),
      cap_ct1 ≠ 0#64 →
      960 ≤ cap_ct1.toNat →
      cap_ct1.toNat < 2 ^ 63 →
      ptr_ct1 ≠ 0#64 →
      st2.pc = (blkPl_350).base + 480#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 2496#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = s0.sp - 288#64 →
      st2.readReg64 .x21 = ptr_ct2 →
      st2.readReg64 .x22 = x.epoch →
      st2.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st2.readReg64 .x24 = ptr_dk →
      st2.readReg64 .x25 = ptr_ct2_128 →
      st2.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st2.readReg64 .x27 = cap_ct2 →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
          ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          A.live ptr_ct2_128 128 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
          vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
          ((s0.sp - 152#64) ↦ₛ (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList) ∗
          ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          memRegion (s0.sp - 1344#64) 16 ∗
          unusedFrameAt (s0.sp - 2496#64) ∗
          ((s0.sp - 2496#64) ↦₆₄ c0) ∗
          ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2472#64) ↦₆₄ c3) ∗
          ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
          ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
          ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
          ((s0.sp - 2432#64) ↦₆₄ c8) ∗
          A.pool lim st_cur st2 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        (ptr_ct2 ↦ₛ ct2Full.take 128) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        memRegion (ptr_ct2 + BitVec.ofNat 64 ct2Full.length) (cap_ct2.toNat - ct2Full.length) ∗
        A.live ptr_ct2 cap_ct2.toNat 1 ∗
        memRegion ptr_ct2_128 128 ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        ((s0.sp - 2496#64) ↦₆₄ c0) ∗
        ((s0.sp - 2488#64) ↦₆₄ c1) ∗
        ((s0.sp - 2480#64) ↦₆₄ c2) ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        ((s0.sp - 2464#64) ↦₆₄ c4) ∗
        ((s0.sp - 2456#64) ↦₆₄ c5) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ c7) ∗
        ((s0.sp - 2432#64) ↦₆₄ c8) ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_mc := hA.memcpy_lscro
  have h_decaps := mlkem_decaps_placed_lscro hdecaps
  have h_pan_unwrap := hA.panic_unwrap_failed
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx19 hx20 hx21 hx22 hx23 hx26 hx27 hx29
  clear hA hdecaps
  simp only [lsProg_350, session2MemcpyBudgetSpecX, mlkemDecapsSpec, withVmPreserved]
    at h_mc h_decaps h_pan_unwrap hcont ⊢
  have htake128_len : (ct2Full.take 128).length = 128 := by
    rw [List.length_take]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, ha_ct2⟩ :=
    exists_unpack64_of_length_128 htake128_len
  refine SepWPp.rw_pre (by
    rw [ha_ct2 ptr_ct2, memRegion_128_cells ptr_ct2_128,
        someBranchFrameAt_expose_decaps s0.sp,
        memRegion_48_sp_1328 s0.sp,
        memRegion_24_sp_1280 s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.fold (ekSentCt1ReceivedUcAt_expose_entails A.repAlloc x.selfA x.self.uc)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
  refine SepWPp.fold (vecU8HeapAt_pure_bounds A.repAlloc cap_ct1 ptr_ct1 x.self.uc.ct1)
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hle_ct1, hmax_ct1, hptr_ct1⟩
  have hct1_iff := ofNat_beq_960_iff (by omega : x.self.uc.ct1.length < 2 ^ 63)
  by_cases hct1_len : x.self.uc.ct1.length = 960
  · have hct1_beq : (BitVec.ofNat 64 x.self.uc.ct1.length == 960#64) = true := by
      rw [hct1_iff, decide_eq_true hct1_len]
    refine SepWPp.fold
      (vecU8HeapAt_expose_nonempty A.repAlloc cap_ct1 ptr_ct1 x.self.uc.ct1 (by omega))
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, _, hcap_ct1⟩
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    have hfold_ct2 := ct2DeallocAt_of_cells_drop A.repAlloc cap_ct2 ptr_ct2 ct2Full
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      hge128 hle_cap hmax_cap hptr_ct2 hcap_ct2
    rw [RustCliAllocBudget.repAlloc_live_norm] at hfold_ct2
    refine SepWP.fold hfold_ct2 (by sep_focus) ?_
    refine SepWP.fold
      (ekSentCt1ReceivedCells_entails_memRegion_504 x.selfA _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP.fold
      (authenticatorPinAt_of_sp_1328 A.repAlloc s0.sp g_auth x.self.uc.auth)
      (by sep_focus) ?_
    have hmr_ct1 :
        memRegion (s0.sp - 1248#64) 960 = memRegion (s0.sp - 1248#64) x.self.uc.ct1.length := by
      rw [hct1_len]
    refine SepWP.fold (Entails.of_eq hmr_ct1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2_budget h_mc (s0.sp - 1248#64, ptr_ct1, x.self.uc.ct1) hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr1, hvm1⟩
    refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm1]) ?_
    refine SepWPp.rw_pre (by rw [memRegion_128_sp_288 s0.sp]) ?_
    sep_elim_exists
    refine SepWPp.fold (vecU8HeapAt_pure_bounds A.repAlloc cap_dk ptr_dk x.self.uc.dk)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hle_dk, hmax_dk, hptr_dk⟩
    have hdk_iff := ofNat_beq_2400_iff (by omega : x.self.uc.dk.length < 2 ^ 63)
    have hptr_dk_beq : (ptr_dk == 0#64) = false := beq_false_of_ne hptr_dk
    by_cases hdk_len : x.self.uc.dk.length = 2400
    · have hdk_beq : (BitVec.ofNat 64 x.self.uc.dk.length == 2400#64) = true := by
        rw [hdk_iff, decide_eq_true hdk_len]
      refine SepWPp.fold
        (vecU8HeapAt_expose_nonempty A.repAlloc cap_dk ptr_dk x.self.uc.dk (by omega))
        (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, _, _, hcap_dk⟩
      refine sepWPp_of_sepWP_lscro (mid := lsρ spqrMlkemDecapsSym) hF_sf ?_
      wp_steps_sync_pool (lsρ spqrMlkemDecapsSym)
      simp only [State.setMem_setMem]
      have hfold_ptr128 :
          (ptr_ct2_128 ↦₆₄ w0) ∗ ((ptr_ct2_128 + 8#64) ↦₆₄ w1) ∗
            ((ptr_ct2_128 + 16#64) ↦₆₄ w2) ∗ ((ptr_ct2_128 + 24#64) ↦₆₄ w3) ∗
            ((ptr_ct2_128 + 32#64) ↦₆₄ w4) ∗ ((ptr_ct2_128 + 40#64) ↦₆₄ w5) ∗
            ((ptr_ct2_128 + 48#64) ↦₆₄ w6) ∗ ((ptr_ct2_128 + 56#64) ↦₆₄ w7) ∗
            ((ptr_ct2_128 + 64#64) ↦₆₄ w8) ∗ ((ptr_ct2_128 + 72#64) ↦₆₄ w9) ∗
            ((ptr_ct2_128 + 80#64) ↦₆₄ w10) ∗ ((ptr_ct2_128 + 88#64) ↦₆₄ w11) ∗
            ((ptr_ct2_128 + 96#64) ↦₆₄ w12) ∗ ((ptr_ct2_128 + 104#64) ↦₆₄ w13) ∗
            ((ptr_ct2_128 + 112#64) ↦₆₄ w14) ∗ ((ptr_ct2_128 + 120#64) ↦₆₄ w15) ⊢
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) :=
        Entails.of_eq (ha_ct2 ptr_ct2_128).symm
      refine SepWP.fold hfold_ptr128 (by sep_focus) ?_
      refine SepWP.fold
        (pointsToBytes_128_of_sp_288 s0.sp (ct2Full.take 128)
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ha_ct2)
        (by sep_focus) ?_
      have h1264 : ((s0.sp - 1264#64) ↦₆₄ 960#64) ⊢
          ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) := by
        rw [hct1_len]; exact Entails.refl _
      refine SepWP.fold h1264 (by sep_focus) ?_
      have hfold_ct1_vec :=
        vecU8At_of_sp_1280 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1
          hle_ct1 hmax_ct1 hptr_ct1 hcap_ct1
      rw [RustCliAllocBudget.repAlloc_live_norm] at hfold_ct1_vec
      refine SepWP.fold hfold_ct1_vec (by sep_focus) ?_
      have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
        rw [hsp_sf]
      refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv2
      wpp_call_lscro_recvCt2_budget h_decaps
        ⟨s0.sp - 152#64, ptr_dk, ⟨x.self.uc.dk, hdk_len⟩,
         s0.sp - 1248#64, ⟨x.self.uc.ct1, hct1_len⟩,
         s0.sp - 288#64, ⟨ct2Full.take 128, htake128_len⟩⟩ hinv2
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hvm2, htr2⟩
      refine SepWPp.rw_pre (by rw [← A.pool_transport lim st_cur _ _ hvm2]) ?_
      have hdk_toList : List.Vector.toList ⟨x.self.uc.dk, hdk_len⟩ = x.self.uc.dk := rfl
      have hct1_toList : List.Vector.toList ⟨x.self.uc.ct1, hct1_len⟩ = x.self.uc.ct1 := rfl
      have hct2_toList :
          List.Vector.toList ⟨ct2Full.take 128, htake128_len⟩ = ct2Full.take 128 := rfl
      refine SepWPp.rw_pre (by rw [hdk_toList, hct1_toList, hct2_toList]) ?_
      have hfold_dk := bytes_rem_entails_ct2DeallocAt A.repAlloc cap_dk ptr_dk x.self.uc.dk
        hle_dk hmax_dk hptr_dk hcap_dk
      rw [RustCliAllocBudget.repAlloc_live_norm] at hfold_dk
      have hfold_ct1_buf :
          ((s0.sp - 1248#64) ↦ₛ x.self.uc.ct1) ⊢ memRegion (s0.sp - 1248#64) 960 :=
        hct1_len ▸ pointsToBytes_entails_memRegion (s0.sp - 1248#64) x.self.uc.ct1
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
        rw [← hstack_sf, hsp]
      refine SepWPp.fold hfold_dk (by sep_focus) ?_
      refine SepWPp.fold hfold_ct1_buf (by sep_focus) ?_
      refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      refine SepWPp.rw_pre (by sep_ac_rfl)
        (hcont _ g_auth cap_dk ptr_dk cap_ct1 ptr_ct1 hct1_len htake128_len hdk_len
          hcap_ct1 (by omega) hmax_ct1 hptr_ct1
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hF_sf_1
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
    · have hdk_beq : (BitVec.ofNat 64 x.self.uc.dk.length == 2400#64) = false := by
        rw [hdk_iff, decide_eq_false hdk_len]
      have hdk_bne : (BitVec.ofNat 64 x.self.uc.dk.length != 2400#64) = true := by
        simp [bne, hdk_beq]
      have hpan_dk := recv_ct2_chunk_isPanic_of_dk_len_ne (K := K) x.self x.epoch x.chunk
        receivingCt2 ct2Full hepoch hadd hdec (by omega) hct1_len hdk_len
      apply SepWPp.of_sepWP (mid := lsρ spqrUnwrapFailedSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_isPanic_budget_recvCt2 hpan_dk
        (by simp only [wp_norm, arm64_norm, htr1, htr]) hm
  · have hct1_beq : (BitVec.ofNat 64 x.self.uc.ct1.length == 960#64) = false := by
      rw [hct1_iff, decide_eq_false hct1_len]
    have hct1_bne : (BitVec.ofNat 64 x.self.uc.ct1.length != 960#64) = true := by
      simp [bne, hct1_beq]
    have hpan_ct1 := recv_ct2_chunk_isPanic_of_ct1_len_ne (K := K) x.self x.epoch x.chunk
      receivingCt2 ct2Full hepoch hadd hdec (by omega) hct1_len
    apply SepWPp.of_sepWP (mid := lsρ spqrUnwrapFailedSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    exact allowPanic_isPanic_budget_recvCt2 hpan_ct1
      (by simp only [wp_norm, arm64_norm, htr]) hm

theorem recv_ct2_chunk_to_decaps_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c7 c8 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (R F_frame : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hle_cap : ct2Full.length ≤ cap_ct2.toNat)
    (hmax_cap : cap_ct2.toNat < 2 ^ 63)
    (hptr_ct2 : ptr_ct2 ≠ 0#64)
    (hcap_ct2 : cap_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 292#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_ct2_128)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State) (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64)
      (hct1_len : x.self.uc.ct1.length = 960)
      (htake128_len : (ct2Full.take 128).length = 128)
      (hdk_len : x.self.uc.dk.length = 2400),
      cap_ct1 ≠ 0#64 →
      960 ≤ cap_ct1.toNat →
      cap_ct1.toNat < 2 ^ 63 →
      ptr_ct1 ≠ 0#64 →
      st2.pc = (blkPl_350).base + 480#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 2496#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = s0.sp - 288#64 →
      st2.readReg64 .x21 = ptr_ct2 →
      st2.readReg64 .x22 = x.epoch →
      st2.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st2.readReg64 .x24 = ptr_dk →
      st2.readReg64 .x25 = ptr_ct2_128 →
      st2.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st2.readReg64 .x27 = cap_ct2 →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
          ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          A.live ptr_ct2_128 128 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
          vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
          ((s0.sp - 152#64) ↦ₛ (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList) ∗
          ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          memRegion (s0.sp - 1344#64) 16 ∗
          unusedFrameAt (s0.sp - 2496#64) ∗
          ((s0.sp - 2496#64) ↦₆₄ c0) ∗
          ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2472#64) ↦₆₄ c3) ∗
          ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
          ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
          ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
          ((s0.sp - 2432#64) ↦₆₄ c8) ∗
          A.pool lim st_cur st2 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        (ptr_ct2 ↦ₛ ct2Full.take 128) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        memRegion (ptr_ct2 + BitVec.ofNat 64 ct2Full.length) (cap_ct2.toNat - ct2Full.length) ∗
        A.live ptr_ct2 cap_ct2.toNat 1 ∗
        memRegion ptr_ct2_128 128 ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        ((s0.sp - 2496#64) ↦₆₄ c0) ∗
        ((s0.sp - 2488#64) ↦₆₄ c1) ∗
        ((s0.sp - 2480#64) ↦₆₄ c2) ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        ((s0.sp - 2464#64) ↦₆₄ c4) ∗
        ((s0.sp - 2456#64) ↦₆₄ c5) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ c7) ∗
        ((s0.sp - 2432#64) ↦₆₄ c8) ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_to_decaps_placed_wpp_ofPrePostEnv hA hdecaps x receivingCt2 ct2Full
    cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c0 c1 c2 c3 c4 c5 c7 c8 st0 st_cur s0 st R F_frame
    hepoch hadd hdec hge128 hlt_max hle_cap hmax_cap hptr_ct2 hcap_ct2
    hpc hrun hsp hsp_s0 htr hvregs hinv hx0 hx19 hx20 hx21 hx22 hx23 hx26 hx27 hx29 hcont

theorem recv_ct2_chunk_to_decaps_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c7 c8 : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (R F_frame : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length)
    (hlt_max : ct2Full.length < 2 ^ 63)
    (hle_cap : ct2Full.length ≤ cap_ct2.toNat)
    (hmax_cap : cap_ct2.toNat < 2 ^ 63)
    (hptr_ct2 : ptr_ct2 ≠ 0#64)
    (hcap_ct2 : cap_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 292#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx0 : st.readReg64 .x0 = ptr_ct2_128)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st2 : State) (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64)
      (hct1_len : x.self.uc.ct1.length = 960)
      (htake128_len : (ct2Full.take 128).length = 128)
      (hdk_len : x.self.uc.dk.length = 2400),
      cap_ct1 ≠ 0#64 →
      960 ≤ cap_ct1.toNat →
      cap_ct1.toNat < 2 ^ 63 →
      ptr_ct1 ≠ 0#64 →
      st2.pc = (blkPl_350).base + 480#64 →
      st2.status = .Running →
      st2.sp = s0.sp - 2496#64 →
      st2.trace = s0.trace →
      calleeSavedVRegs st2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st2.mem →
      st2.readReg64 .x19 = x.outA →
      st2.readReg64 .x20 = s0.sp - 288#64 →
      st2.readReg64 .x21 = ptr_ct2 →
      st2.readReg64 .x22 = x.epoch →
      st2.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st2.readReg64 .x24 = ptr_dk →
      st2.readReg64 .x25 = ptr_ct2_128 →
      st2.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length →
      st2.readReg64 .x27 = cap_ct2 →
      st2.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st2
        (memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
          ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
          ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          A.live ptr_ct2_128 128 1 ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
          vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
          ((s0.sp - 152#64) ↦ₛ (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, htake128_len⟩).toList) ∗
          ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          memRegion (s0.sp - 1344#64) 16 ∗
          unusedFrameAt (s0.sp - 2496#64) ∗
          ((s0.sp - 2496#64) ↦₆₄ c0) ∗
          ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2472#64) ↦₆₄ c3) ∗
          ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
          ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
          ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
          ((s0.sp - 2432#64) ↦₆₄ c8) ∗
          A.pool lim st_cur st2 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ekSentCt1ReceivedUcAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        (ptr_ct2 ↦ₛ ct2Full.take 128) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        memRegion (ptr_ct2 + BitVec.ofNat 64 ct2Full.length) (cap_ct2.toNat - ct2Full.length) ∗
        A.live ptr_ct2 cap_ct2.toNat 1 ∗
        memRegion ptr_ct2_128 128 ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        ((s0.sp - 2496#64) ↦₆₄ c0) ∗
        ((s0.sp - 2488#64) ↦₆₄ c1) ∗
        ((s0.sp - 2480#64) ↦₆₄ c2) ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        ((s0.sp - 2464#64) ↦₆₄ c4) ∗
        ((s0.sp - 2456#64) ↦₆₄ c5) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ c7) ∗
        ((s0.sp - 2432#64) ↦₆₄ c8) ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_to_decaps_placed_wpp_ofEnv hA hdecaps x receivingCt2 ct2Full
    cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c0 c1 c2 c3 c4 c5 c7 c8 st0 st_cur s0 st R F_frame
    hepoch hadd hdec hge128 hlt_max hle_cap hmax_cap hptr_ct2 hcap_ct2
    hpc hrun hsp hsp_s0 htr hvregs hinv hx0 hx19 hx20 hx21 hx22 hx23 hx26 hx27 hx29 hcont

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1bPlacedBudget
