/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import Lean -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget `ct1.reserve`, Append & HMAC

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of `ct1.reserve(128)` (`+664 .. +684`)
and `ct2` append, `sliceConcat3`, `libcrux_hmac`, and `mac_data` deallocation (`+684 .. +860`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2bPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkLib_eq_350 blkPC_350 blkPl_350 lsProg_350 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes LibcruxHmacCall MlKem spqrAuthApi spqrHkdfWith spqrPolyApi
)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall LibsignalCodeRoLoaded doReserveStackX extHookStack reserveCap
)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.SpqrV1.Alloc (SliceConcat3Ghost)
open CryptoVerification.SpqrV1.Auth (
  AuthenticatorGhost authenticatorPinAt pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost bytes_rem_entails_ct2DeallocAt bytes_rem_entails_memRegion ct2DeallocAt
  exists_unpack64_of_length_128 fold_sp_1248_24_24 le_of_not_ule_sub_960
  macCtUnchecked_eq_hmacWith memRegion_128_cells memRegion_128_split_24_104
  memRegion_144_split_80_8_56 memRegion_960_split_48_912 memRegion_ct1_split_128
  pointsToBytes_append_960_128 rejoin_memRegion_128_24_104 rejoin_memRegion_144_80_8_56
  reserveCap_bound_of_ule_sub_960 reserveCap_ge_1088 reserveCap_ne_zero
  spqrLibcruxHmacSym' spqrRustDeallocSym' stackAt_extHook_eq_doReserveX
  vecU8At_expose_sp_1280 vecU8At_expose_sp_1304 vecU8At_of_sp_1280 vecU8_expose_nonempty_288
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk fitsEvents_append rustCliDeallocBudgetExternSpecWithStack
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec libcruxHmacSha256Events)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env fitsEnv_sliceConcat3_iff sliceConcat3Events sliceConcat3Spec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget (libcruxHmacSafeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  RecvCt2PlacedAlloc RecvCt2ReserveCt1Env ctLabelSym fitsEnv_doReserve_of_reserveCt1
  freeOnlyEvs_rustDealloc1 libcrux_hmac_safe_placed_lscro recvCt2HmacEvents
  recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp recvCt2ReserveCt1Env_nil
  recvCt2ReserveCt1Env_of_doReserve sepWPp_of_sepWP_lscro
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpecWithStack
)

private theorem ctLabel_length : Authenticator.ctLabel.length = 35 := rfl
private theorem replicate_32_zero_length : (List.replicate 32 0#8).length = 32 := rfl

private theorem sepWPp_rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post_err : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post post_err) :
    SepWPp prog pc s P post post_err := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length ctLabel_length

local elab "erase_hkdf_sp_norm" : command =>
  Lean.Elab.Command.liftCoreM do
    for nm in [
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
    ] do
      try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()

erase_hkdf_sp_norm

/-! ## `ct1.reserve(128)` (`+664 .. +684` + `+1940 .. +1980`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_reserve_ct1_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hfit_res : FitsEnv M lim σ RecvCt2ReserveCt1Env)
    (hct1_len : x.self.uc.ct1.length = 960)
    (hcap_ct1_ne : cap_ct1 ≠ 0#64)
    (hct1_le : 960 ≤ cap_ct1.toNat)
    (hct1_lt : cap_ct1.toNat < 2 ^ 63)
    (hptr_ct1_ne : ptr_ct1 ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 664#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (eRes : List AllocEvent),
      RecvCt2ReserveCt1Env eRes →
      cap_ct1' ≠ 0#64 →
      1088 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_350).base + 684#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x8 = 960#64 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = st.readReg64 .x28 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
          (ptr_ct1' ↦ₛ x.self.uc.ct1) ∗
          memRegion (ptr_ct1' + 960#64) (cap_ct1'.toNat - 960) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
          A.pool lim (M.stepEvents eRes σ) st' ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1) ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        (ptr_ct1 ↦ₛ x.self.uc.ct1) ∗
        memRegion (ptr_ct1 + 960#64) (cap_ct1.toNat - 960) ∗
        A.live ptr_ct1 cap_ct1.toNat 1 ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
        A.pool lim σ st ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_res := hA.doReserve7_lscro
  dsimp only [doReserveSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
    doReserveSpecWithStack] at h_res
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  clear hA
  simp only [lsProg_350] at h_res hcont ⊢
  by_cases hls : ¬ (cap_ct1 - 960#64).ule 127#64 = true
  · have hls_f : (cap_ct1 - 960#64).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge1088 : 1088 ≤ cap_ct1.toNat := le_of_not_ule_sub_960 hct1_le hls
    refine sepWPp_of_sepWP_lscro (mid := (blkPl_350).base + 684#64) hinv ?_
    wp_steps_sync_pool ((blkPl_350).base + 684#64)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    refine sepWPp_rw_pre (by sep_ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 [] recvCt2ReserveCt1Env_nil
        hcap_ct1_ne hge1088 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
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
  · have hls_t : (cap_ct1 - 960#64).ule 127#64 = true := Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_960 hct1_le hls_t
    have hbound' : reserveCap cap_ct1.toNat x.self.uc.ct1.length 128 + 1 ≤ 2 ^ 63 := by
      rwa [hct1_len]
    have hlt1088 : cap_ct1.toNat < 1088 := by
      have hsub : (cap_ct1 - 960#64).toNat ≤ 127 := by
        simpa only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat] using hls_t
      have hle_bv : 960#64 ≤ cap_ct1 := BitVec.le_def.mpr (by simpa using hct1_le)
      rw [BitVec.toNat_sub_of_le hle_bv] at hsub
      change cap_ct1.toNat - 960 ≤ 127 at hsub
      omega
    have hfit_doRes :
        FitsEnv M lim σ (DoReserveEnv ⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩) :=
      fitsEnv_doReserve_of_reserveCt1
        ⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩
        hct1_len rfl hct1_le hlt1088 hfit_res
    refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 320) hinv ?_
    wp_steps_sync_pool (lsmpl.base 320)
    simp only [State.setMem_setMem]
    have h1264 : ((s0.sp - 1264#64) ↦₆₄ 960#64) ⊢
        ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) := by
      rw [hct1_len]; exact Entails.refl _
    refine SepWP.fold h1264 (by sep_focus) ?_
    have hmr_ct1 :
        memRegion (ptr_ct1 + 960#64) (cap_ct1.toNat - 960) ⊢
          memRegion (ptr_ct1 + BitVec.ofNat 64 x.self.uc.ct1.length) (cap_ct1.toNat - x.self.uc.ct1.length) := by
      rw [hct1_len]; exact Entails.refl _
    refine SepWP.fold hmr_ct1 (by sep_focus) ?_
    have hfold_1280 :
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1) ∗
          ((s0.sp - 1272#64) ↦₆₄ ptr_ct1) ∗
          ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) ∗
          (ptr_ct1 ↦ₛ x.self.uc.ct1) ∗
          memRegion (ptr_ct1 + BitVec.ofNat 64 x.self.uc.ct1.length)
            (cap_ct1.toNat - x.self.uc.ct1.length) ∗
          A.live ptr_ct1 cap_ct1.toNat 1 ⊢
          vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 :=
      vecU8At_of_sp_1280 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1
        (by omega) hct1_lt hptr_ct1_ne hcap_ct1_ne
    refine SepWP.fold hfold_1280 (by sep_focus) ?_
    have hstack_res :
        memRegion (s0.sp - 19552#64) 672 ∗ stackAt (s0.sp - 2496#64) extHookStack ⊢
          memRegion (s0.sp - 19552#64) 560 ∗ stackAt (s0.sp - 2496#64) doReserveStackX :=
      Entails.of_eq (stackAt_extHook_eq_doReserveX s0.sp)
    refine SepWP.fold hstack_res (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2_budget h_res
      ((⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩ : DoReserveCall), σ)
      hinv1
    conv => arg 4; simp only [State.sp, hsp_sf, hsp, hsp_norm]
    refine sepWPp_rw_pre (emp_sepConj _).symm ?_
    sep_elim_exists
    rename_i ptr_ct1'
    refine sepWPp_rw_pre (emp_sepConj _) ?_
    refine sepWPp_pure_left_focus (sf.trace = _) (by sep_focus) fun htr1 => ?_
    have hexp_1280 :
        vecU8At A.repAlloc (s0.sp - 1280#64)
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128))
          ptr_ct1' x.self.uc.ct1 ⊢
          ⌜x.self.uc.ct1.length ≤
              (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat ∧
            (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat < 2 ^ 63 ∧
            ptr_ct1' ≠ 0#64 ∧
            BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128) ≠ 0#64⌝ ∗
            ((s0.sp - 1280#64) ↦₆₄
              BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)) ∗
            ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
            ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) ∗
            (ptr_ct1' ↦ₛ x.self.uc.ct1) ∗
            memRegion (ptr_ct1' + BitVec.ofNat 64 x.self.uc.ct1.length)
              ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat -
                x.self.uc.ct1.length) ∗
            A.live ptr_ct1'
              (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat 1 :=
      vecU8At_expose_sp_1280 A.repAlloc s0.sp
        (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128))
        ptr_ct1' x.self.uc.ct1 (by omega)
    refine SepWPp.fold hexp_1280 (by sep_focus) ?_
    refine sepWPp_pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, hmax_ct1', hptr_ct1'_ne, hcap_ct1'_ne⟩
    have hge1088' :
        1088 ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.self.uc.ct1.length 128)).toNat := by
      rw [hct1_len]
      exact reserveCap_ge_1088 hbound
    refine sepWPp_rw_pre (by rw [hct1_len]) ?_
    refine sepWPp_of_sepWP_lscro (mid := (blkPl_350).base + 684#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_350).base + 684#64)
    simp only [State.setMem_setMem]
    have hstack_back :
        memRegion (s0.sp - 19552#64) 560 ∗ stackAt (s0.sp - 2496#64) doReserveStackX ⊢
          memRegion (s0.sp - 19552#64) 672 ∗ stackAt (s0.sp - 2496#64) extHookStack := by
      rw [← stackAt_extHook_eq_doReserveX s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_back (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    have henv_res :
        RecvCt2ReserveCt1Env
          (doReserveEvents ⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩) :=
      recvCt2ReserveCt1Env_of_doReserve
        ⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩
        hct1_len rfl hct1_le hlt1088
    refine sepWPp_rw_pre (by sep_ac_rfl)
      (hcont _ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat 960 128)) ptr_ct1'
        (doReserveEvents ⟨s0.sp - 1280#64, cap_ct1, ptr_ct1, x.self.uc.ct1, 128⟩)
        henv_res
        (reserveCap_ne_zero hbound)
        (by simpa [hct1_len] using hge1088')
        (by simpa [hct1_len] using hmax_ct1')
        hptr_ct1'_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv2
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
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

/-! ## Append `ct2` to `ct1`, `sliceConcat3`, `libcrux_hmac`, and dealloc (`+684 .. +860`) -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_append_hmac_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacBudgetSpec F M A lim))
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (ct2Full : Bytes)
    (auth' : Authenticator)
    (g_auth' : AuthenticatorGhost)
    (cap_ct1' ptr_ct1' ptr_ct2_128 s_2496 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hfit_hmac : FitsEvents M lim σ recvCt2HmacEvents)
    (hct1_len : x.self.uc.ct1.length = 960)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hmk_len : auth'.macKey.length = 32)
    (hcap_ct1'_ne : cap_ct1' ≠ 0#64)
    (hge1088 : 1088 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hptr_ct1'_ne : ptr_ct1' ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 684#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx8 : st.readReg64 .x8 = 960#64)
    (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx28 : st.readReg64 .x28 = rev64 x.epoch)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (eMdFree : List AllocEvent),
      FreeOnlyEvs eMdFree →
      g_auth'.macKey.cap ≠ 0#64 →
      32 ≤ g_auth'.macKey.cap.toNat →
      g_auth'.macKey.cap.toNat < 2 ^ 63 →
      g_auth'.macKey.ptr ≠ 0#64 →
      st'.pc = (blkPl_350).base + 860#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = ptr_ct2_128 →
      st'.readReg64 .x26 = g_auth'.macKey.ptr →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
          ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
          ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
          ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
          ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗
          (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
          memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
          A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
          ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          vecU8 A.repAlloc (s0.sp - 1248#64)
            (auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)) ∗
          memRegion (s0.sp - 1224#64) 24 ∗
          memRegion (s0.sp - 1200#64) 912 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 2000#64) 144 ∗
          ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim (M.stepEvents eMdFree (M.stepEvents recvCt2HmacEvents σ)) st' ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
        (recvCt2PlacedPostQp K x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
        (ptr_ct1' ↦ₛ x.self.uc.ct1) ∗
        memRegion (ptr_ct1' + 960#64) (cap_ct1'.toNat - 960) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
        authenticatorPinAt A.repAlloc g_auth' (s0.sp - 1328#64) auth' ∗
        ((s0.sp - 2496#64) ↦₆₄ s_2496) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 2000#64) 144 ∗
        ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have h_concat3 := hA.sliceConcat3_lscro
  dsimp only [sliceConcat3Spec] at h_concat3
  have h_hmac := libcrux_hmac_safe_placed_lscro hhmac
  dsimp only [libcruxHmacSafeBudgetSpec] at h_hmac
  have h_dealloc := hA.dealloc_lscro
  dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack] at h_dealloc
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx8 hx25 hx28 hx29
  have ⟨hfit_cat_ev, hfit_hm_ev⟩ :
      FitsEvents M lim σ (sliceConcat3Events 1131) ∧
        FitsEvents M lim (M.stepEvents (sliceConcat3Events 1131) σ) libcruxHmacSha256Events :=
    (fitsEvents_append M lim (sliceConcat3Events 1131) libcruxHmacSha256Events σ).mp hfit_hmac
  have hfit_cat :
      FitsEnv M lim σ
        (SliceConcat3Env
          ⟨s0.sp - 288#64, s0.sp - 1248#64,
            true, lsρ ctLabelSym, Authenticator.ctLabel,
            false, s0.sp - 1920#64, toBEBytes 8 x.epoch,
            false, ptr_ct1', x.self.uc.ct1 ++ ct2Full.take 128⟩) := by
    rw [fitsEnv_sliceConcat3_iff]
    simpa [ctLabel_length, toBEBytes_8_length, List.length_append, hct1_len, htake128_len]
      using hfit_cat_ev
  clear hA hhmac
  simp only [lsProg_350] at h_concat3 h_hmac h_dealloc hcont ⊢
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_eq⟩ :=
    exists_unpack64_of_length_128 htake128_len
  dsimp only [authenticatorPinAt]
  have hexp_1304 :
      vecU8At A.repAlloc (s0.sp - 1328#64 + 0x18#64) g_auth'.macKey.cap g_auth'.macKey.ptr
        auth'.macKey ⊢
        ⌜auth'.macKey.length ≤ g_auth'.macKey.cap.toNat ∧
          g_auth'.macKey.cap.toNat < 2 ^ 63 ∧
          g_auth'.macKey.ptr ≠ 0#64 ∧
          g_auth'.macKey.cap ≠ 0#64⌝ ∗
          ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
          ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          ((s0.sp - 1288#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length) ∗
          (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
          memRegion (g_auth'.macKey.ptr + BitVec.ofNat 64 auth'.macKey.length)
            (g_auth'.macKey.cap.toNat - auth'.macKey.length) ∗
          A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 :=
    vecU8At_expose_sp_1304 A.repAlloc s0.sp g_auth'.macKey.cap g_auth'.macKey.ptr
      auth'.macKey (by omega)
  refine SepWPp.fold hexp_1304 (by sep_focus) ?_
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ptr_ne, hmk_cap_ne⟩
  refine sepWPp_rw_pre (by
    rw [hmk_len,
      memRegion_ct1_split_128 ptr_ct1' hge1088 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + 960#64),
      hct2_eq ptr_ct2_128,
      memRegion_128_split_24_104 s0.sp,
      memRegion_960_split_48_912 s0.sp,
      memRegion_144_split_80_8_56 s0.sp]) ?_
  sep_elim_exists
  refine sepWPp_of_sepWP_lscro (mid := lsmpl.base 386) hinv ?_
  wp_steps_sync_pool (lsmpl.base 386)
  simp only [State.setMem_setMem]
  refine SepWP.fold (Entails.of_eq (hct2_eq ptr_ct2_128).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (hct2_eq (ptr_ct1' + 960#64)).symm) (by sep_focus) ?_
  refine SepWP.fold
    (pointsToBytes_append_960_128 ptr_ct1' x.self.uc.ct1 (ct2Full.take 128) hct1_len)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 1920#64) x.epoch))
    (by sep_focus) ?_
  have hct1_full_len :
      BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088#64 := by
    rw [List.length_append, hct1_len, htake128_len]
  have hconcat3_bound :
      43 + (x.self.uc.ct1 ++ ct2Full.take 128).length < 9223372036854775808 := by
    rw [List.length_append, hct1_len, htake128_len]
    decide
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2_budget h_concat3
    ((⟨s0.sp - 288#64, s0.sp - 1248#64,
        true, lsρ ctLabelSym, Authenticator.ctLabel,
        false, s0.sp - 1920#64, toBEBytes 8 x.epoch,
        false, ptr_ct1', x.self.uc.ct1 ++ ct2Full.take 128⟩ : SliceConcat3Ghost), σ)
    hinv1
  conv => arg 4; simp only [State.sp, hsp_sf, hsp, hsp_norm]
  refine sepWPp_rw_pre (emp_sepConj _).symm ?_
  sep_elim_exists
  rename_i evs_cat ptr_md0
  refine sepWPp_rw_pre (emp_sepConj _) ?_
  refine sepWPp_pure_left_focus (sf.trace = _ ∧ AllocCallPreserved _ sf ∧ _) (by sep_focus) ?_
  rintro ⟨htr1, _, hevs_cat⟩
  have hevs_cat_eq : evs_cat = sliceConcat3Events 1131 := by
    simpa [SliceConcat3Env, ctLabel_length, toBEBytes_8_length,
      List.length_append, hct1_len, htake128_len] using hevs_cat
  rw [hevs_cat_eq]
  have hfold_vec288 :
      ∀ (cap₀ : BitVec 64) (bs : List (BitVec 8)),
        vecU8At A.repAlloc (s0.sp - 288#64) cap₀ ptr_md0 bs ⊢
          vecU8 A.repAlloc (s0.sp - 288#64) bs :=
    fun cap₀ _ => Entails.sepExists_right cap₀ (Entails.sepExists_right ptr_md0 (Entails.refl _))
  refine SepWPp.fold (hfold_vec288 _ _) (by sep_focus) ?_
  rw [← List.append_assoc Authenticator.ctLabel]
  have hdata_len :
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length = 1131 := by
    simp [List.length_append, ctLabel_length, hct1_len, htake128_len]
  have hdata_pos :
      0 < (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length := by
    omega
  have hexp_288 :
      vecU8 A.repAlloc (s0.sp - 288#64)
        (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)) ⊢
        ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜cap ≠ 0#64 ∧ CryptoVerification.RustHeap.LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧
            (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++
              (x.self.uc.ct1 ++ ct2Full.take 128)).length ≤ cap.toNat⌝ ∗
            ((s0.sp - 288#64) ↦₆₄ cap) ∗
            ((s0.sp - 280#64) ↦₆₄ ptr) ∗
            ((s0.sp - 272#64) ↦₆₄
              BitVec.ofNat 64
                (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++
                  (x.self.uc.ct1 ++ ct2Full.take 128)).length) ∗
            (ptr ↦ₛ
              (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++
                (x.self.uc.ct1 ++ ct2Full.take 128))) ∗
            memRegion
              (ptr +
                BitVec.ofNat 64
                  (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++
                    (x.self.uc.ct1 ++ ct2Full.take 128)).length)
              (cap.toNat -
                (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++
                  (x.self.uc.ct1 ++ ct2Full.take 128)).length) ∗
            A.live ptr cap.toNat 1 :=
    vecU8_expose_nonempty_288 A.repAlloc s0.sp
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))
      hdata_pos
  refine SepWPp.fold hexp_288 (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine sepWPp_pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_md_ne
  refine SepWPp.fold
    (fold_sp_1248_24_24 s0.sp
      (lsρ ctLabelSym) 35#64
      (s0.sp - 1920#64) 8#64 ptr_ct1'
      (BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length))
    (by sep_focus) ?_
  refine SepWPp.fold
    (rejoin_memRegion_144_80_8_56 s0.sp (bs := toBEBytes 8 x.epoch) (by simp))
    (by sep_focus) ?_
  have hct1_1088 :
      BitVec.ofNat 64 (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088#64 := hct1_full_len
  have hct1_len_nat : (x.self.uc.ct1 ++ ct2Full.take 128).length = 1088 := by
    rw [List.length_append, hct1_len, htake128_len]
  have hfold_ct1 :
      (ptr_ct1' ↦ₛ (x.self.uc.ct1 ++ ct2Full.take 128)) ∗
        memRegion (ptr_ct1' + 1088#64) (cap_ct1'.toNat - 1088) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ⊢
        ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' := by
    rw [← hct1_1088, ← hct1_len_nat]
    exact bytes_rem_entails_ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1'
      (x.self.uc.ct1 ++ ct2Full.take 128) (by omega) hmax_ct1' hptr_ct1'_ne hcap_ct1'_ne
  refine SepWPp.fold hfold_ct1 (by sep_focus) ?_
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrLibcruxHmacSym') hF_sf ?_
  wp_steps_sync_pool (lsρ spqrLibcruxHmacSym')
  simp only [State.setMem_setMem]
  have hmk_len_bv : BitVec.ofNat 64 auth'.macKey.length = 32#64 := by rw [hmk_len]
  have hmk_lt32 : auth'.macKey.length < 2 ^ 32 := by omega
  have hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)).length < 2 ^ 32 := by
    omega
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2_budget h_hmac
    ((⟨s0.sp - 1248#64, g_auth'.macKey.ptr, auth'.macKey,
        ptr_md, Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128)⟩ : LibcruxHmacCall),
      M.stepEvents (sliceConcat3Events 1131) σ)
    hinv2
  conv => arg 4; simp only [State.sp, hsp_sf_1, hsp_sf, hsp, hsp_norm]
  refine sepWPp_pure_left_focus (sf_1.trace = _) (by sep_focus) fun htr2 => ?_
  have hstep_hmac :
      M.stepEvents libcruxHmacSha256Events (M.stepEvents (sliceConcat3Events 1131) σ) =
        M.stepEvents recvCt2HmacEvents σ :=
    (M.stepEvents_append (sliceConcat3Events 1131) libcruxHmacSha256Events σ).symm
  rw [hstep_hmac, ← List.append_assoc Authenticator.ctLabel,
    ← macCtUnchecked_eq_hmacWith F auth' x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)]
  refine SepWPp.fold
    (bytes_rem_entails_memRegion ptr_md cap_md
      (Authenticator.ctLabel ++ toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))
      hle_md hmax_md)
    (by sep_focus) ?_
  have hrlay_md : RustLayoutOk cap_md.toNat 1 := ⟨hlay_md, by decide⟩
  refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_1 ?_
  wp_steps_sync_pool (lsρ spqrRustDeallocSym')
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lscro_recvCt2_budget h_dealloc
    (ptr_md, cap_md.toNat, 1, M.stepEvents recvCt2HmacEvents σ)
    hinv3
  conv => arg 4; simp only [State.sp, hsp_sf_2, hsp_sf_1, hsp_sf, hsp, hsp_norm]
  refine sepWPp_pure_left_focus (sf_2.trace = _) (by sep_focus) fun htr3 => ?_
  refine SepWPp.fold
    (rejoin_memRegion_128_24_104 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ (toBEBytes 8 x.epoch ++ (x.self.uc.ct1 ++ ct2Full.take 128))).length))
    (by sep_focus) ?_
  refine sepWPp_rw_pre (by sep_ac_rfl)
    (hcont sf_2 (rustDeallocEvents cap_md.toNat 1) (freeOnlyEvs_rustDealloc1 cap_md.toNat)
      hmk_cap_ne (by omega) hmk_max hmk_ptr_ne
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf_2
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2bPlacedBudget
