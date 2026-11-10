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
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3bPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable `Ok(Done)` Deallocations

Relocatable `[LibsignalPlacement]` proof of `x.epoch + 1` overflow check, 32-byte `secret` allocation,
and 7-buffer deallocation chain (`+1308 .. +1520`), handing off to `Part3bPlaced`.
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1600000 in
/-- `+1308 .. +1520` + `+1980` + `+2044`: verifies the `Ok(Done)` branch from the
`x.epoch + 1` overflow check through the 32-byte `secret` allocation, `ss` copy, `auth'` header
staging, and 7-buffer deallocation chain, handing off at `+1520` to
`recv_ct2_chunk_ok_done_write_out_placed_wpp`. -/
theorem recv_ct2_chunk_ok_done_dealloc_placed_wpp [LibsignalPlacement] {K : MlKem}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
      ptr_ss_raw cap_info ptr_info ptr_ss : BitVec 64)
    (ss_raw ss : Bytes) (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length) (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hct1_len : x.self.uc.ct1.length = 960) (hdk_len : x.self.uc.dk.length = 2400)
    (hm_le32 : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
       let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
       let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
       let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
       compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false)
    (hss_eq :
      let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32)
    (hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss)
    (hss_len : ss.length = 32) (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat) (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 1308#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw) (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss) (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗ ct2DeallocAt A cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A cap_dk ptr_dk ∗
        vecU8At A (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A cap_ct2 ptr_ct2 ∗ memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗ memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have hge_not_lt : ¬ ct2Full.length < 128 := by omega
  by_cases hep_max : (x.self.uc.epoch == BitVec.allOnes 64) = true
  · have hult_t : (x.self.uc.epoch + 1#64).ult x.self.uc.epoch = true :=
      (add_one_ult_self_eq_beq_allOnes x.self.uc.epoch).trans hep_max
    have hult_t' : (x.epoch + 1#64).ult x.epoch = true := by rw [hepoch]; exact hult_t
    have hpan_model := recv_ct2_chunk_isPanic_of_epoch_allOnes (K := K)
      x.self x.epoch x.chunk receivingCt2 ct2Full hepoch hadd hdec hge_not_lt
      hct1_len hdk_len hm_le32 hcmp hep_max
    have h_pan_add := hA.panic_add_overflow
    have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx22
    clear hA
    simp only [lsProg_350] at h_pan_add ⊢
    apply SepWPp.of_sepWP (mid := lsρ spqrPanicConstAddOverflowSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    exact allowPanic_isPanic_recvCt2 hpan_model (by simp only [Rust.panicked, wp_norm, arm64_norm, *]) hm
  · have hep_max_f : (x.self.uc.epoch == BitVec.allOnes 64) = false :=
      Bool.eq_false_iff.mpr hep_max
    have hult_f : (x.self.uc.epoch + 1#64).ult x.self.uc.epoch = false :=
      (add_one_ult_self_eq_beq_allOnes x.self.uc.epoch).trans hep_max_f
    have hult_f' : (x.epoch + 1#64).ult x.epoch = false := by rw [hepoch]; exact hult_f
    have hres_raw := recv_ct2_chunk_eq_done (K := K)
      x.self x.epoch x.chunk receivingCt2 ct2Full hepoch hadd hdec hge_not_lt
      hct1_len hdk_len hm_le32 hcmp hep_max_f
    dsimp only at hres_raw hss_eq
    have hres : x.self.recv_ct2_chunk K x.epoch x.chunk =
        .ok (.done ({ uc := { epoch := x.epoch + 1#64, auth := auth' },
                       receiving_hdr := polyDecoderNew96 },
                     { epoch := x.epoch, secret := ss })) := by
      rw [hres_raw, ← hss_eq, ← hauth'_eq, ← hepoch]
    have h_shim := hA.shim_lscro
    have h_alloc := hA.alloc_lscro
    have h_dealloc := hA.dealloc_lscro
    have h_pan_oom := hA.panic_handle_error (prog := lsProg_350 (Rust.withPanics ext))
    have h_write := @recv_ct2_chunk_ok_done_write_out_placed_wpp _ K F A ext hA x receivingCt2
      cap_ct2 ptr_ct2
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hss_raw_mr : (ptr_ss_raw ↦ₛ ss_raw) ⊢ memRegion ptr_ss_raw 32 := by
      rw [← hss_raw_len]; exact pointsToBytes_entails_memRegion ptr_ss_raw ss_raw
    have hct2_128_mr : (ptr_ct2_128 ↦ₛ ct2Full.take 128) ⊢ memRegion ptr_ct2_128 128 := by
      have h := pointsToBytes_entails_memRegion ptr_ct2_128 (ct2Full.take 128)
      rwa [htake128_len] at h
    have hmk_heap :
        (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
          memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
          A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ⊢
        vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey :=
      bytes_rem_entails_vecU8HeapAt_32 A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey
        hmk_len hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
    refine SepWPp.fold hss_raw_mr (by sep_focus) ?_
    refine SepWPp.fold hct2_128_mr (by sep_focus) ?_
    refine SepWPp.fold hmk_heap (by sep_focus) ?_
    refine SepWPp.fold
      (vecU8At_expose_cells_heap_sp_1328 A s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey hrk_len)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus (g_auth'.rootKey.cap.toNat < 2 ^ 63) (by sep_focus) fun hcap_rk_lt => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A cap_info ptr_info) (by sep_focus) ?_
    refine SepWPp.pure_left_focus (Ct2DeallocProp cap_info ptr_info) (by sep_focus)
      fun ⟨hinfo_beq, hinfo_pos, hinfo_max, hinfo_ptr⟩ => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A cap_ct1' ptr_ct1') (by sep_focus) ?_
    refine SepWPp.pure_left_focus (Ct2DeallocProp cap_ct1' ptr_ct1') (by sep_focus)
      fun ⟨hct1_beq, hct1_pos, hct1_max, hct1_ptr⟩ => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A cap_dk ptr_dk) (by sep_focus) ?_
    refine SepWPp.pure_left_focus (Ct2DeallocProp cap_dk ptr_dk) (by sep_focus)
      fun ⟨hdk_beq, hdk_pos, hdk_max, hdk_ptr⟩ => ?_
    refine SepWPp.rw_pre (by
      rw [ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 32) (k := 112) (b' := s0.sp - 1968#64) rfl (by bv_omega) (by decide)]) ?_
    refine SepWPp.fold (memRegion_split_4cells
      (s0.sp - 1968#64) (s0.sp - 1960#64) (s0.sp - 1952#64) (s0.sp - 1944#64)
      (s0.sp - 1936#64) 112 80 rfl
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
    sep_elim_exists; rename_i z0 z1 z2 z3
    refine SepWPp.rw_pre (by
      rw [ProofLib.memRegion_split' (b := s0.sp - 1936#64) (n := 8) (k := 72) (b' := s0.sp - 1928#64) rfl (by bv_omega) (by decide)]) ?_
    refine SepWPp.fold (memRegion_8_eq_cell (s0.sp - 1936#64)) (by sep_focus) ?_
    sep_elim_exists; rename_i z4
    have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx29
    clear hA
    simp only [lsProg_350] at h_shim h_alloc h_dealloc h_pan_oom h_write ⊢
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1
    wpp_call_lscro_recvCt2 h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps
    have hst_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hst_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv2
    have hlay32 : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    wpp_call_lscro_recvCt2 h_alloc (32, 1) hinv2
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      conv => arg 4; simp only [hoom, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      obtain ⟨s0_w, s1_w, s2_w, s3_w, _, ha_ss⟩ := exists_unpack64_of_length_32 hss_len
      refine SepWPp.rw_pre (by
        rw [memRegion_32_cells (sf_1.readReg64 Reg.x0), ha_ss ptr_ss]) ?_
      sep_elim_exists
      refine SepWPp.fold (Entails.of_eq (shift_5words_1320 s0.sp
        g_auth'.rootKey.ptr 32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_1 ?_
      wp_steps
      refine SepWP.fold
        (fold_ptr_ss_raw (sf_1.readReg64 Reg.x0) ss s0_w s1_w s2_w s3_w ha_ss)
        (by sep_focus) ?_
      refine SepWP.fold
        (fold_4cells_memRegion_32 ptr_ss s0_w s1_w s2_w s3_w)
        (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (shift_5words_1320 s0.sp
        g_auth'.rootKey.ptr 32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64).symm) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (reshape_x20_1960_to_1929 s0.sp
        32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64 z4)) (by sep_focus) ?_
      wp_steps
      have hst_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by rw [hsp_sf_1]
      refine SepWP.fold (Entails.of_eq hst_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv3
      wpp_call_lscro_recvCt2 h_dealloc (ptr_ss, 32, 1) hinv3
      refine SepWPp.pure_left_focus (sf_2.trace = sf_1.trace) (by sep_focus) fun htr3 => ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_2 ?_
      wp_steps
      have hst_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by rw [hsp_sf_2]
      refine SepWP.fold (Entails.of_eq hst_sf2) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv4
      wpp_call_lscro_recvCt2 h_dealloc (ptr_info, cap_info.toNat, 1) hinv4
      refine SepWPp.pure_left_focus (sf_3.trace = sf_2.trace) (by sep_focus) fun htr4 => ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_3 ?_
      wp_steps
      have hst_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by rw [hsp_sf_3]
      refine SepWP.fold (Entails.of_eq hst_sf3) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv5
      wpp_call_lscro_recvCt2 h_dealloc (ptr_ss_raw, 32, 1) hinv5
      refine SepWPp.pure_left_focus (sf_4.trace = sf_3.trace) (by sep_focus) fun htr5 => ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_4 ?_
      wp_steps
      have hst_sf4 : stackAt sf_3.sp extHookStack = stackAt sf_4.sp extHookStack := by rw [hsp_sf_4]
      refine SepWP.fold (Entails.of_eq hst_sf4) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv6
      wpp_call_lscro_recvCt2 h_dealloc (ptr_ct1', cap_ct1'.toNat, 1) hinv6
      refine SepWPp.pure_left_focus (sf_5.trace = sf_4.trace) (by sep_focus) fun htr6 => ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_5 ?_
      wp_steps
      have hst_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by rw [hsp_sf_5]
      refine SepWP.fold (Entails.of_eq hst_sf5) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv7
      wpp_call_lscro_recvCt2 h_dealloc (ptr_dk, cap_dk.toNat, 1) hinv7
      refine SepWPp.pure_left_focus (sf_6.trace = sf_5.trace) (by sep_focus) fun htr7 => ?_
      by_cases heq128 : ct2Full.length = 128
      · have hsub0 : ct2Full.length - 128 = 0 := by omega
        have hx23_0 : BitVec.ofNat 64 (ct2Full.length - 128) = 0#64 := by rw [hsub0]
        have hdrop_nil : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
        have hmac_emp : vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢ emp := by
          rw [hx23_0]; exact vecBufAt_zero_entails_emp A ptr_mac (ct2Full.drop 128) hdrop_nil
        refine SepWPp.fold hmac_emp (by sep_focus) ?_
        refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_6 ?_
        wp_steps
        have hst_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by rw [hsp_sf_6]
        refine SepWP.fold (Entails.of_eq hst_sf6) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv8
        wpp_call_lscro_recvCt2 h_dealloc (ptr_ct2_128, 128, 1) hinv8
        refine SepWPp.pure_left_focus (sf_7.trace = sf_6.trace) (by sep_focus) fun htr8 => ?_
        have hst_end : stackAt sf_6.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
          rw [hsp_sf_6, hsp_sf_5, hsp_sf_4, hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
        refine SepWPp.fold (Entails.of_eq hst_end) (by sep_focus) ?_
        refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
        refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
        refine SepWPp.fold
          (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
            32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
          (by sep_focus) ?_
        refine SepWPp.fold
          (rejoin_cells_5_sp_2464 s0.sp cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
          (by sep_focus) ?_
        refine SepWPp.rw_pre ?_
          (h_write (sf_1.readReg64 Reg.x0) ptr_dk ptr_info (b7 z4) auth' g_auth' ss s0 sf_7 R
            hrk_len hmk_len hss_len hoom hcap_rk_lt hres
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *]) hsp_s0
            (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hF_sf_7
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by rw [hepoch]; simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
        · dsimp only [recvCt2RoPlacedAt, Reg.x0]
          rw [← hepoch]
          ac_rfl
      · have hmac_mr_live :
            vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢
              memRegion ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat ∗
                A.live ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 := by
          have hlen : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
          rw [← hlen]; exact vecBufAt_entails_memRegion_live A ptr_mac (ct2Full.drop 128) (by omega) (by omega)
        have hmac_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hmac_pos : 0 < (BitVec.ofNat 64 (ct2Full.length - 128)).toNat := by omega
        have hmac_max : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat < 2 ^ 63 := by omega
        have hmac_beq : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false := by
          apply beq_false_of_ne; intro h0
          have h1 := congrArg BitVec.toNat h0; change (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = 0 at h1; omega
        refine SepWPp.fold hmac_mr_live (by sep_focus) ?_
        refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_6 ?_
        wp_steps
        have hst_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by rw [hsp_sf_6]
        refine SepWP.fold (Entails.of_eq hst_sf6) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv8
        wpp_call_lscro_recvCt2 h_dealloc (ptr_mac, (BitVec.ofNat 64 (ct2Full.length - 128)).toNat, 1) hinv8
        refine SepWPp.pure_left_focus (sf_7.trace = sf_6.trace) (by sep_focus) fun htr8 => ?_
        refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_7 ?_
        wp_steps
        have hst_sf7 : stackAt sf_6.sp extHookStack = stackAt sf_7.sp extHookStack := by rw [hsp_sf_7]
        refine SepWP.fold (Entails.of_eq hst_sf7) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv9
        wpp_call_lscro_recvCt2 h_dealloc (ptr_ct2_128, 128, 1) hinv9
        refine SepWPp.pure_left_focus (sf_8.trace = sf_7.trace) (by sep_focus) fun htr9 => ?_
        have hst_end : stackAt sf_7.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
          rw [hsp_sf_7, hsp_sf_6, hsp_sf_5, hsp_sf_4, hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
        refine SepWPp.fold (Entails.of_eq hst_end) (by sep_focus) ?_
        refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
        refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
        refine SepWPp.fold
          (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
            32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
          (by sep_focus) ?_
        refine SepWPp.fold
          (rejoin_cells_5_sp_2464 s0.sp cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
          (by sep_focus) ?_
        refine SepWPp.rw_pre ?_
          (h_write (sf_1.readReg64 Reg.x0) ptr_dk ptr_info (b7 z4) auth' g_auth' ss s0 sf_8 R
            hrk_len hmk_len hss_len hoom hcap_rk_lt hres
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *]) hsp_s0
            (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hF_sf_8
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by rw [hepoch]; simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
        · dsimp only [recvCt2RoPlacedAt, Reg.x0]
          rw [← hepoch]
          ac_rfl

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
