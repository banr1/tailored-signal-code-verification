/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable `ss` Allocation, HKDF & `auth.update`

Relocatable `[LibsignalPlacement]` proof of `+480 .. +664`: `ss_raw`/`ss` allocation, `sliceConcat2`
(Block `386`), `hkdf_to_slice` (Block `379`), and `Authenticator::update` (Block `341`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_ss_hkdf_update_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))))
    (x : RecvCt2ChunkGhost F) (ss_raw ct2Full : Bytes)
    (ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 : BitVec 64)
    (g_auth : AuthenticatorGhost)
    (s0 st : State) (F_frame R : SepProp)
    (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hroot_lt : x.self.uc.auth.rootKey.length + 32 < 2 ^ 63)
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
      (g_auth' : AuthenticatorGhost),
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
          authenticatorPinAt A g_auth' (s0.sp - 1328#64)
            (x.self.uc.auth.update F x.epoch
              (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
          (ptr_ss_raw ↦ₛ ss_raw) ∗
          A.live ptr_ss_raw 32 1 ∗
          (ptr_ss ↦ₛ
            spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
          A.live ptr_ss 32 1 ∗
          ct2DeallocAt A cap_info ptr_info ∗
          ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
          ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
          ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
          memRegion (s0.sp - 128#64) 8 ∗
          memRegion (s0.sp - 288#64) 128 ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
          A.pool ∗
          memRegion (s0.sp - 19552#64) 672 ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        authenticatorPinAt A g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
        ((s0.sp - 152#64) ↦ₛ ss_raw) ∗
        ((s0.sp - 288#64) ↦ₛ ct2Full.take 128) ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        ((s0.sp - 2472#64) ↦₆₄ c3) ∗
        A.pool ∗
        memRegion (s0.sp - 19552#64) 672 ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have h_shim := hA.shim_lscro
  have h_alloc := hA.alloc_lscro
  have h_allocZeroed := hA.allocZeroed_lscro
  have h_concat2 := hA.sliceConcat2_lscro
  have h_hkdf := hkdfToSlice_placed_lscro hhkdf
  simp only [hkdfToSliceSpqrSpec, hkdfToSliceSpec] at h_hkdf
  have h_update := hA.authUpdate_lscro hhkdf
  simp only [authUpdateSpec] at h_update
  have h_pan_oom := hA.panic_handle_error (prog := lsProg_350 (Rust.withPanics ext))
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx25 hx29
  clear hA hhkdf
  simp only [lsProg_350] at h_shim h_alloc h_allocZeroed h_concat2 h_hkdf h_update h_pan_oom hcont ⊢
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
  refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2 h_shim () hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
  refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
  wp_steps
  have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  wpp_call_lscro_recvCt2 h_alloc (32, 1) hinv2
  by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
  · conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    exact allowPanic_oom_recvCt2
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
    conv => arg 4; simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr2⟩
    refine SepWPp.rw_pre (by rw [memRegion_32_cells (sf_1.readReg64 Reg.x0)]) ?_
    sep_elim_exists
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 386) hF_sf_1 ?_
    wp_steps
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
    wpp_call_lscro_recvCt2 h_concat2
      (⟨s0.sp - 152#64, s0.sp - 1248#64,
        true, lsρ sckaKeyInfoPrefixSym, sckaKeyInfoPrefix,
        false, s0.sp - 288#64, toBEBytes 8 x.epoch⟩ : SliceConcat2Ghost)
      hinv3
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
    have hinfo_pos : 0 < (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length := by simp
    refine SepWPp.fold
      (vecU8_expose_nonempty_152 A s0.sp (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) hinfo_pos)
      (by sep_focus) ?_
    sep_elim_exists
    rename_i cap_info ptr_info
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hcap_info_ne, hlay_info, hptr_info_ne, hle_info⟩
    have ⟨_, _, hmax_info⟩ := hlay_info
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
    wp_steps
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by rw [hsp_sf_2]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    wpp_call_lscro_recvCt2 h_shim () hinv4
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocZeroedSym) hF_sf_3 ?_
    wp_steps
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by rw [hsp_sf_3]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    wpp_call_lscro_recvCt2 h_allocZeroed (32, 1) hinv5
    by_cases hoom2 : sf_4.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr5 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom2_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom2
      conv => arg 4; simp only [hoom2, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr5⟩
      refine SepWPp.fold
        (pointsToBytes_replicate_32_entails_memRegion (sf_4.readReg64 Reg.x0))
        (by sep_focus) ?_
      refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 379) hF_sf_4 ?_
      wp_steps
      have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by rw [hsp_sf_4]
      refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv6
      have hinfo_ge : 32 ≤ (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length := by simp
      have hinfo_lt : (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch).length < 55 := by simp
      wpp_call_lscro_recvCt2 h_hkdf
        (⟨true, lsρ zeros32Sym, List.replicate 32 0#8,
          false, sf_1.readReg64 Reg.x0, ss_raw,
          false, ptr_info, sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch,
          sf_4.readReg64 Reg.x0, 32⟩ : HkdfToSliceGhost)
        hinv6
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hss_len, htr6⟩
      have hroot_ss_lt :
          x.self.uc.auth.rootKey.length +
            (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32).length < 2 ^ 63 := by
        rw [hss_len]; exact hroot_lt
      refine SepWPp.fold
        (authenticatorPinAt_entails_authenticatorAt A g_auth (s0.sp - 1328#64) x.self.uc.auth)
        (by sep_focus) ?_
      refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 341) hF_sf_5 ?_
      wp_steps
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
      wpp_call_lscro_recvCt2 h_update
        (⟨s0.sp - 1328#64, x.self.uc.auth, x.epoch,
          false, sf_4.readReg64 Reg.x0,
          spqrHkdfWith F (List.replicate 32 0#8) ss_raw
            (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32⟩ : AuthUpdateGhost)
        hinv7
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr7 => ?_
      refine SepWPp.rw_pre (by
        rw [authenticatorAt_eq_exists_pinned A (s0.sp - 1328#64)
          (x.self.uc.auth.update F x.epoch
            (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
              (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32))]) ?_
      sep_elim_exists
      rename_i g_auth'
      have hfold_info :=
        bytes_rem_entails_ct2DeallocAt A cap_info ptr_info
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) hle_info hmax_info hptr_info_ne hcap_info_ne
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
      refine SepWPp.rw_pre (by unfold recvCt2RoPlacedAt; ac_rfl)
        (hcont sf_6 cap_info ptr_info (sf_1.readReg64 Reg.x0) (sf_4.readReg64 Reg.x0) g_auth'
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

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
