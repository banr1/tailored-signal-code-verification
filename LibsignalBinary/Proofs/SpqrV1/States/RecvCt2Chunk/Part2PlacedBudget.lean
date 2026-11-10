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
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget `ss` Allocation, HKDF & `auth.update`

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of `+480 .. +664`, discharging
`ss_raw`/`ss` allocations without OOM and threading `A.pool` through `hkdf_to_slice` and `auth.update`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_379 blkPl_350 blkPl_379 lsProg_350 lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes MlKem sckaKeyInfoPrefix spqrAuthApi spqrHkdfWith spqrPolyApi
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extHookStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (
  AuthUpdateGhost AuthenticatorGhost SepWPp.pure_left_focus authUpdateStackX authenticatorAt
  authenticatorAt_eq_exists_pinned authenticatorPinAt authenticatorPinAt_entails_authenticatorAt
  pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (replicate_32_zero_length)
open CryptoVerification.SpqrV1.ChainProofs (
  HkdfToSliceGhost SliceConcat2Ghost bytesAt_false bytesAt_true hkdfToSliceSpec hkdfToSliceSpqrSpec
)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof (
  sp_add_neg688_eq_hsp sp_add_neg96_eq_hsp_592 sp_sub_688_eq_hsp sp_sub_96_eq_hsp_592
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost bytes_rem_entails_ct2DeallocAt ct2DeallocAt fold_ptr_ss_raw fold_sp_152_24_8
  memRegion_128_split_8_120 memRegion_32_cells memRegion_960_split_32_928
  pointsToBytes_replicate_32_entails_memRegion recvCt2RoPlacedAt rejoin_memRegion_128_8_120
  rejoin_memRegion_960_32_928 sckaKeyInfoPrefixSym sckaKeyInfoPrefix_length sckaKeyInfo_length
  stackAt_extHook_eq_authUpdate vecU8_expose_nonempty_152 zeros32Sym
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (
  AuthUpdateEnv AuthUpdateLenEnv authUpdateSpec authUpdateSpecAt
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  SliceConcat2Env sliceConcat2Events sliceConcat2Spec
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2ChunkEnv RecvCt2PlacedAlloc hkdfToSlice_placed_lscro recvCt2PlacedPostQ
  recvCt2PlacedPostQOfEnv recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp
  recvCt2PreAuthUpdateEvents sepWPp_of_sepWP_lscro
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith CryptoVerification.LibsignalSpqrV1.Authenticator.update
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``sp_sub_688_eq_hsp,
    ``sp_add_neg688_eq_hsp,
    ``sp_sub_96_eq_hsp_592,
    ``sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase nm `arm64_norm

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (x : RecvCt2ChunkGhost F) (ss_raw ct2Full : Bytes)
    (ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 : BitVec 64)
    (g_auth : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hroot_lt : x.self.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hfit_pre : FitsEvents M lim st_cur recvCt2PreAuthUpdateEvents)
    (hfit_upd : FitsEnv M lim (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)
      (AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32))
    (hpc : st.pc = (blkPl_350).base + 480#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 288#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (_hx24 : st.readReg64 .x24 = ptr_dk)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (_hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (_hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (cap_info ptr_info ptr_ss_raw ptr_ss : BitVec 64)
      (g_auth' : AuthenticatorGhost) (evs_upd : List AllocEvent)
      (_hevs_upd : AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32 evs_upd),
      ptr_ss_raw ≠ 0#64 →
      ptr_ss ≠ 0#64 →
      st'.pc = (blkPl_350).base + 664#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = 41#64 →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x24 = ptr_ss_raw →
      st'.readReg64 .x25 = ptr_ct2_128 →
      st'.readReg64 .x26 = ptr_info →
      st'.readReg64 .x27 = ptr_ss →
      st'.readReg64 .x28 = rev64 x.epoch →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvCt2RoPlacedAt ∗
          authenticatorPinAt A.repAlloc g_auth' (s0.sp - 1328#64)
            (x.self.uc.auth.update F x.epoch
              (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
          (ptr_ss_raw ↦ₛ ss_raw) ∗
          A.live ptr_ss_raw 32 1 ∗
          (ptr_ss ↦ₛ
            spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
          A.live ptr_ss 32 1 ∗
          ct2DeallocAt A.repAlloc cap_info ptr_info ∗
          ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
          ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
          ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
          memRegion (s0.sp - 128#64) 8 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
          A.pool lim (M.stepEvents evs_upd (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)) st' ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
        ((s0.sp - 152#64) ↦ₛ ss_raw) ∗
        ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        A.pool lim st_cur st ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_shim := hA.shim_lscro
  have h_alloc := hA.allocNoOom_lscro
  have h_allocZeroed := hA.allocZeroedNoOom_lscro
  have h_concat2 := hA.sliceConcat2_lscro
  have h_hkdf := hkdfToSlice_placed_lscro hhkdf
  have h_update := hA.authUpdate_lscro hhkdf
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx25 hx29
  clear hA hhkdf
  simp only [lsProg_350, session2ShimBudgetSpecX, rustCliAllocNoOomSpecWithStack,
      sliceConcat2Spec, hkdfToSliceSpqrSpec, hkdfToSliceSpec, withVmPreserved,
      authUpdateSpec, authUpdateSpecAt]
    at h_shim h_alloc h_allocZeroed h_concat2 h_hkdf h_update hcont ⊢
  have hpre_eq : recvCt2PreAuthUpdateEvents =
      (rustAllocEvents 32 1 ++ sliceConcat2Events 41) ++ rustAllocEvents 32 1 := rfl
  have ⟨hfit_12, hfit_ss_step⟩ := (fitsEvents_append M lim
    (rustAllocEvents 32 1 ++ sliceConcat2Events 41) (rustAllocEvents 32 1) st_cur).mp
    (hpre_eq ▸ hfit_pre)
  have ⟨hfit_ss_raw, hfit_cat41⟩ := (fitsEvents_append M lim
    (rustAllocEvents 32 1) (sliceConcat2Events 41) st_cur).mp hfit_12
  let st1 := M.stepEvents (rustAllocEvents 32 1) st_cur
  have hfit_concat2 : FitsEnv M lim st1
      (SliceConcat2Env ⟨s0.sp - 152#64, s0.sp - 1248#64,
        true, lsρ sckaKeyInfoPrefixSym, sckaKeyInfoPrefix,
        false, s0.sp - 288#64, toBEBytes 8 x.epoch⟩) := by
    intro evs hevs
    rw [hevs]
    simpa [SliceConcat2Env, sckaKeyInfoPrefix_length, toBEBytes_8_length] using hfit_cat41
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  unfold recvCt2RoPlacedAt
  obtain ⟨u0, u1, u2, u3, hss_raw_eq, ha_ss_raw⟩ := exists_unpack64_of_length_32 hss_raw_len
  clear hss_raw_eq
  have h152_8 : (s0.sp - 152#64) + 8#64 = s0.sp - 144#64 := by bv_kernel
  have h152_16 : (s0.sp - 152#64) + 16#64 = s0.sp - 136#64 := by bv_kernel
  have h152_24 : (s0.sp - 152#64) + 24#64 = s0.sp - 128#64 := by bv_kernel
  have htake128_mr : ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ⊢ memRegion (s0.sp - 288#64) 128 := by
    conv_rhs => rw [← htake128_len]
    exact pointsToBytes_entails_memRegion (s0.sp - 288#64) (ct2Full.take 128)
  refine SepWPp.fold htake128_mr (by sep_focus) ?_
  refine SepWPp.rw_pre (by
    rw [ha_ss_raw (s0.sp - 152#64), h152_8, h152_16, h152_24,
        memRegion_128_split_8_120 s0.sp,
        memRegion_960_split_32_928 s0.sp]) ?_
  sep_elim_exists
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
  have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2_budget h_alloc (32, 1, st_cur) hinv2
  conv => arg 4; simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp1, hoom1, _⟩
  have htr2 : sf_1.trace = sf.trace := hacp1.2.1
  have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
  refine SepWPp.rw_pre (by rw [memRegion_32_cells (sf_1.readReg64 Reg.x0)]) ?_
  sep_elim_exists
  refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 386) hF_sf_1 ?_
  wp_steps_sync_pool (lsmpl.base 386)
  refine SepWP.fold
    (fold_ptr_ss_raw (sf_1.readReg64 Reg.x0) ss_raw u0 u1 u2 u3 ha_ss_raw)
    (by sep_focus) ?_
  refine SepWP.fold (fold_sp_152_24_8 s0.sp u0 u1 u2 u3) (by sep_focus) ?_
  clear ha_ss_raw h152_8 h152_16 h152_24 htake128_mr
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 288#64) x.epoch))
    (by sep_focus) ?_
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by rw [hsp_sf_1]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lscro_recvCt2_budget h_concat2
    (⟨s0.sp - 152#64, s0.sp - 1248#64,
      true, lsρ sckaKeyInfoPrefixSym, sckaKeyInfoPrefix,
      false, s0.sp - 288#64, toBEBytes 8 x.epoch⟩, st1)
    hinv3
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs_cat
  apply SepWPp.exists_elim; intro ptr_info_0
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr3, _, hevs_cat⟩
  have hevs_cat41 : evs_cat = sliceConcat2Events 41 := by
    simpa [SliceConcat2Env, sckaKeyInfoPrefix_length, toBEBytes_8_length] using hevs_cat
  have hst2_eq : M.stepEvents evs_cat st1 =
      M.stepEvents (rustAllocEvents 32 1 ++ sliceConcat2Events 41) st_cur := by
    dsimp only [st1]
    rw [hevs_cat41, M.stepEvents_append]
  refine SepWPp.rw_pre (by rw [hst2_eq]) ?_
  have hfold_vecU8 :
      vecU8At A.repAlloc (s0.sp - 152#64)
        (BitVec.ofNat 64 (sckaKeyInfoPrefix.length + (toBEBytes 8 x.epoch).length))
        ptr_info_0 (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) ⊢
      vecU8 A.repAlloc (s0.sp - 152#64) (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) :=
    Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))
  refine SepWPp.fold hfold_vecU8 (by sep_focus) ?_
  have hinfo_pos : 0 < (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length := by simp
  refine SepWPp.fold
    (vecU8_expose_nonempty_152 A.repAlloc s0.sp (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) hinfo_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_info ptr_info
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_info_ne, hlay_info, hptr_info_ne, hle_info⟩
  have ⟨_, _, hmax_info⟩ := hlay_info
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by rw [hsp_sf_2]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  wpp_call_lscro_recvCt2_budget h_shim () hinv4
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr4, hvm4⟩
  refine SepWPp.rw_pre
    (by rw [← A.pool_transport lim (M.stepEvents (rustAllocEvents 32 1 ++ sliceConcat2Events 41) st_cur) _ _ hvm4]) ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustAllocZeroedSym) hF_sf_3 ?_
  wp_steps_sync_pool (lsρ spqrRustAllocZeroedSym)
  have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by rw [hsp_sf_3]
  refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv5
  wpp_call_lscro_recvCt2_budget h_allocZeroed
    (32, 1, M.stepEvents (rustAllocEvents 32 1 ++ sliceConcat2Events 41) st_cur) hinv5
  conv => arg 4; simp only [↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp2, hoom2, _⟩
  have htr5 : sf_4.trace = sf_3.trace := hacp2.2.1
  have hoom2_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom2
  have hst_pre_eq :
      M.stepEvents (rustAllocEvents 32 1)
        (M.stepEvents (rustAllocEvents 32 1 ++ sliceConcat2Events 41) st_cur) =
      M.stepEvents recvCt2PreAuthUpdateEvents st_cur := by
    simp only [hpre_eq, M.stepEvents_append]
  refine SepWPp.rw_pre (by rw [hst_pre_eq]) ?_
  refine SepWPp.fold
    (pointsToBytes_replicate_32_entails_memRegion (sf_4.readReg64 Reg.x0))
    (by sep_focus) ?_
  refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 379) hF_sf_4 ?_
  wp_steps_sync_pool (lsmpl.base 379)
  have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by rw [hsp_sf_4]
  refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv6
  have hinfo_ge : 32 ≤ (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length := by simp
  have hinfo_lt : (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length < 55 := by simp
  wpp_call_lscro_recvCt2_budget h_hkdf
    (⟨true, lsρ zeros32Sym, List.replicate 32 0#8,
      false, sf_1.readReg64 Reg.x0, ss_raw,
      false, ptr_info, sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch,
      sf_4.readReg64 Reg.x0, 32⟩ : HkdfToSliceGhost)
    hinv6
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_hkdf, hss_len, htr6⟩
  refine SepWPp.rw_pre
    (by rw [← A.pool_transport lim (M.stepEvents recvCt2PreAuthUpdateEvents st_cur) _ _ hvm_hkdf]) ?_
  have hroot_ss_lt :
      x.self.uc.auth.rootKey.length +
        (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32).length < 2 ^ 63 := by
    rw [hss_len]; exact hroot_lt
  have hfit_upd_g :
      FitsEnv M lim (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)
        (AuthUpdateEnv ⟨s0.sp - 1328#64, x.self.uc.auth, x.epoch,
          false, sf_4.readReg64 Reg.x0,
          spqrHkdfWith F (List.replicate 32 0#8) ss_raw
            (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32⟩) := by
    dsimp only [AuthUpdateEnv]
    rw [hss_len]
    exact hfit_upd
  refine SepWPp.fold
    (authenticatorPinAt_entails_authenticatorAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth)
    (by sep_focus) ?_
  refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 341) hF_sf_5 ?_
  wp_steps_sync_pool (lsmpl.base 341)
  have hstack_upd :
      memRegion (s0.sp - 19552#64) 672 ∗ stackAt sf_4.sp extHookStack ⊢
        memRegion (s0.sp - 19552#64) 512 ∗ stackAt sf_5.sp authUpdateStackX := by
    rw [hsp_sf_5, hsp_sf_4, hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp,
      stackAt_extHook_eq_authUpdate s0.sp]
    exact Entails.refl _
  refine SepWP.fold hstack_upd (by sep_focus) ?_
  have hss_len_bv :
      BitVec.ofNat 64
        (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32).length = 32#64 := by
    rw [hss_len]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv7
  wpp_call_lscro_recvCt2_budget h_update
    (⟨s0.sp - 1328#64, x.self.uc.auth, x.epoch,
      false, sf_4.readReg64 Reg.x0,
      spqrHkdfWith F (List.replicate 32 0#8) ss_raw
        (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32⟩,
     M.stepEvents recvCt2PreAuthUpdateEvents st_cur)
    hinv7
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs_upd
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr7, hevs_upd_g⟩
  have hevs_upd : AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32 evs_upd := by
    dsimp only [AuthUpdateEnv] at hevs_upd_g
    rwa [hss_len] at hevs_upd_g
  refine SepWPp.rw_pre (by
    rw [authenticatorAt_eq_exists_pinned A.repAlloc (s0.sp - 1328#64)
      (x.self.uc.auth.update F x.epoch
        (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32))]) ?_
  sep_elim_exists
  rename_i g_auth'
  have hfold_info :=
    bytes_rem_entails_ct2DeallocAt A.repAlloc cap_info ptr_info
      (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) hle_info hmax_info hptr_info_ne hcap_info_ne
  rw [RustCliAllocBudget.repAlloc_live_norm] at hfold_info
  refine SepWPp.fold hfold_info (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_128_8_120 s0.sp (toBEBytes 8 x.epoch) (by simp))
    (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_960_32_928 s0.sp
      (lsρ sckaKeyInfoPrefixSym) 33#64 (s0.sp - 288#64) 8#64)
    (by sep_focus) ?_
  have hstack_back :
      memRegion (s0.sp - 19552#64) 512 ∗ stackAt sf_5.sp authUpdateStackX ⊢
        memRegion (s0.sp - 19552#64) 672 ∗ stackAt (s0.sp - 2496#64) extHookStack := by
    rw [hsp_sf_5, hsp_sf_4, hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp,
      ← stackAt_extHook_eq_authUpdate s0.sp]
    exact Entails.refl _
  refine SepWPp.fold hstack_back (by sep_focus) ?_
  refine SepWPp.rw_pre (by unfold recvCt2RoPlacedAt; sep_ac_rfl)
    (hcont sf_6 cap_info ptr_info (sf_1.readReg64 Reg.x0) (sf_4.readReg64 Reg.x0)
      g_auth' evs_upd hevs_upd
      hoom1 hoom2
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf_6
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *])
      (by simp only [wp_norm, arm64_norm, sckaKeyInfo_length, *]))

theorem recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (x : RecvCt2ChunkGhost F) (ss_raw ct2Full : Bytes)
    (ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 : BitVec 64)
    (g_auth : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hroot_lt : x.self.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hfit_pre : FitsEvents M lim st_cur recvCt2PreAuthUpdateEvents)
    (hfit_upd : FitsEnv M lim (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)
      (AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32))
    (hpc : st.pc = (blkPl_350).base + 480#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 288#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_dk)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (cap_info ptr_info ptr_ss_raw ptr_ss : BitVec 64)
      (g_auth' : AuthenticatorGhost) (evs_upd : List AllocEvent)
      (_hevs_upd : AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32 evs_upd),
      ptr_ss_raw ≠ 0#64 →
      ptr_ss ≠ 0#64 →
      st'.pc = (blkPl_350).base + 664#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = 41#64 →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x24 = ptr_ss_raw →
      st'.readReg64 .x25 = ptr_ct2_128 →
      st'.readReg64 .x26 = ptr_info →
      st'.readReg64 .x27 = ptr_ss →
      st'.readReg64 .x28 = rev64 x.epoch →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvCt2RoPlacedAt ∗
          authenticatorPinAt A.repAlloc g_auth' (s0.sp - 1328#64)
            (x.self.uc.auth.update F x.epoch
              (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
          (ptr_ss_raw ↦ₛ ss_raw) ∗
          A.live ptr_ss_raw 32 1 ∗
          (ptr_ss ↦ₛ
            spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
          A.live ptr_ss 32 1 ∗
          ct2DeallocAt A.repAlloc cap_info ptr_info ∗
          ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
          ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
          ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
          memRegion (s0.sp - 128#64) 8 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
          A.pool lim (M.stepEvents evs_upd (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)) st' ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
        ((s0.sp - 152#64) ↦ₛ ss_raw) ∗
        ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        A.pool lim st_cur st ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofPrePostEnv hA hhkdf x ss_raw ct2Full
    ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 g_auth st0 st_cur s0 st F_frame R
    hss_raw_len htake128_len hroot_lt hfit_pre hfit_upd
    hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx29 hcont

theorem recv_ct2_chunk_ss_hkdf_update_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (x : RecvCt2ChunkGhost F) (ss_raw ct2Full : Bytes)
    (ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 : BitVec 64)
    (g_auth : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hroot_lt : x.self.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hfit_pre : FitsEvents M lim st_cur recvCt2PreAuthUpdateEvents)
    (hfit_upd : FitsEnv M lim (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)
      (AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32))
    (hpc : st.pc = (blkPl_350).base + 480#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 288#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_dk)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 ct2Full.length)
    (hx27 : st.readReg64 .x27 = cap_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (cap_info ptr_info ptr_ss_raw ptr_ss : BitVec 64)
      (g_auth' : AuthenticatorGhost) (evs_upd : List AllocEvent)
      (_hevs_upd : AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32 evs_upd),
      ptr_ss_raw ≠ 0#64 →
      ptr_ss ≠ 0#64 →
      st'.pc = (blkPl_350).base + 664#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = 41#64 →
      st'.readReg64 .x21 = ptr_ct2 →
      st'.readReg64 .x22 = x.epoch →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x24 = ptr_ss_raw →
      st'.readReg64 .x25 = ptr_ct2_128 →
      st'.readReg64 .x26 = ptr_info →
      st'.readReg64 .x27 = ptr_ss →
      st'.readReg64 .x28 = rev64 x.epoch →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvCt2RoPlacedAt ∗
          authenticatorPinAt A.repAlloc g_auth' (s0.sp - 1328#64)
            (x.self.uc.auth.update F x.epoch
              (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
          (ptr_ss_raw ↦ₛ ss_raw) ∗
          A.live ptr_ss_raw 32 1 ∗
          (ptr_ss ↦ₛ
            spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
          A.live ptr_ss 32 1 ∗
          ct2DeallocAt A.repAlloc cap_info ptr_info ∗
          ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
          ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
          ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
          memRegion (s0.sp - 128#64) 8 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
          A.pool lim (M.stepEvents evs_upd (M.stepEvents recvCt2PreAuthUpdateEvents st_cur)) st' ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        authenticatorPinAt A.repAlloc g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
        ((s0.sp - 152#64) ↦ₛ ss_raw) ∗
        ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        A.pool lim st_cur st ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofEnv hA hhkdf x ss_raw ct2Full
    ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 g_auth st0 st_cur s0 st F_frame R
    hss_raw_len htake128_len hroot_lt hfit_pre hfit_upd
    hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx29 hcont

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2PlacedBudget
