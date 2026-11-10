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
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable Allocation & Decapsulation

Relocatable `[LibsignalPlacement]` proof of `mac`/`ct2_128` heap allocation (`+224 .. +292`)
and `decapsulate_compressed_key` (`+292 .. +480`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

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
open CryptoVerification.SpqrV1.States
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

/-! ## `mac` and `ct2` Heap Allocation (`+224 .. +292` + `+1244 .. +1284`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_alloc_mac_ct2_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 c6 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
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
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion ptr_ct2_128 128 ∗
          A.live ptr_ct2_128 128 1 ∗
          ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
          A.pool ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 2448#64) ↦₆₄ c6) ∗
        ((s0.sp - 2016#64) ↦₆₄ ptr_ct2) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have h_shim := hA.shim_lscro
  have h_alloc := hA.alloc_lscro
  have h_mc := hA.memcpy_lscro
  have h_pan_oom := hA.panic_handle_error (prog := lsProg_350 (Rust.withPanics ext))
  clear hA
  simp only [lsProg_350] at h_shim h_alloc h_mc h_pan_oom hcont ⊢
  have hzero_iff := ofNat_sub_128_eq_zero_iff hge128 hlt_max
  have hlay128 : LayoutOk 128 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  by_cases hlen128 : ct2Full.length = 128
  · have hzero : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = true := by
      rw [hzero_iff, decide_eq_true hlen128]
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2 h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2 h_alloc (128, 1) hinv2
    by_cases hoom128 : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom128, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom128_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom128
      conv => arg 4; simp only [hoom128, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 292#64) hF_sf_1 ?_
      wp_steps
      have hdrop0 : (ct2Full.drop 128).length = 0 := by rw [List.length_drop, hlen128]
      have hsub0 : BitVec.ofNat 64 (ct2Full.length - 128) = 0#64 := by rw [hlen128]
      have hvb0 : ((s0.sp - 2448#64) ↦₆₄ 1#64) ⊢
          ((s0.sp - 2448#64) ↦₆₄ 1#64) ∗
            vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) 1#64 (ct2Full.drop 128) := by
        rw [hsub0]
        refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
        exact sepConj_mono_right (vecBufAt_zero_one A (ct2Full.drop 128) hdrop0)
      refine SepWP.fold hvb0 (by sep_focus) ?_
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
        rw [← hstack_sf, hsp]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_end
      refine SepWPp.rw_pre (by ac_rfl)
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
    have hlay_mac : LayoutOk (ct2Full.length - 128) 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
    have hsub_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdrop_len : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2 h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2 h_alloc (ct2Full.length - 128, 1) hinv2
    by_cases hoom_mac : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom_mac_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_mac
      conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf_1 ?_
      wp_steps
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [hsp_sf_1]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      wpp_call_lscro_recvCt2 h_mc (sf_1.readReg64 Reg.x0, ptr_ct2 + 128#64, ct2Full.drop 128) hinv3
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr3⟩
      have hfold_mac :
          ((sf_1.readReg64 Reg.x0) ↦ₛ ct2Full.drop 128) ∗
            A.live (sf_1.readReg64 Reg.x0) (ct2Full.length - 128) 1 ⊢
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128))
            (sf_1.readReg64 Reg.x0) (ct2Full.drop 128) := by
        rw [← hdrop_len]
        exact vecBufAt_of_bytes_live A (sf_1.readReg64 Reg.x0) (ct2Full.drop 128)
          (by omega) (by omega)
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
      refine SepWP.fold hfold_mac (by sep_focus) ?_
      wp_steps
      have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
        rw [hsp_sf_2]
      refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      wpp_call_lscro_recvCt2 h_shim () hinv4
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf_3 ?_
      wp_steps
      have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
        rw [hsp_sf_3]
      refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      wpp_call_lscro_recvCt2 h_alloc (128, 1) hinv5
      by_cases hoom128 : sf_4.readReg64 Reg.x0 = 0#64
      · conv => arg 4; simp only [hoom128, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htr5 => ?_
        apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
        exact allowPanic_oom_recvCt2
          (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · have hoom128_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom128
        conv => arg 4; simp only [hoom128, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, htr5⟩
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 292#64) hF_sf_4 ?_
        wp_steps
        have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
          rw [← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf, hsp]
        refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_end
        refine SepWPp.rw_pre (by ac_rfl)
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

/-! ## Copy `ct2[..128]`, Move `uc`, and Call `decapsulate_compressed_key` (`+292 .. +480`) -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_to_decaps_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K))
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c7 c8 : BitVec 64)
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
          ct2DeallocAt A cap_ct2 ptr_ct2 ∗
          ct2DeallocAt A cap_dk ptr_dk ∗
          (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
          A.live ptr_ct2_128 128 1 ∗
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          authenticatorPinAt A g_auth (s0.sp - 1328#64) x.self.uc.auth ∗
          vecU8At A (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
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
          A.pool ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ekSentCt1ReceivedUcAt A x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        (ptr_ct2 ↦ₛ ct2Full.take 128) ∗
        ((ptr_ct2 + 128#64) ↦ₛ ct2Full.drop 128) ∗
        memRegion (ptr_ct2 + BitVec.ofNat 64 ct2Full.length) (cap_ct2.toNat - ct2Full.length) ∗
        A.live ptr_ct2 cap_ct2.toNat 1 ∗
        memRegion ptr_ct2_128 128 ∗
        A.live ptr_ct2_128 128 1 ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
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
        A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have h_mc := hA.memcpy_lscro
  have h_decaps := mlkem_decaps_placed_lscro hdecaps
  have h_pan_unwrap := hA.panic_unwrap_failed
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx19 hx20 hx21 hx22 hx23 hx26 hx27 hx29
  clear hA hdecaps
  simp only [lsProg_350] at h_mc h_decaps h_pan_unwrap hcont ⊢
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
  refine SepWPp.fold (ekSentCt1ReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  rename_i g_auth cap_dk ptr_dk cap_ct1 ptr_ct1
  refine SepWPp.fold (vecU8HeapAt_pure_bounds A cap_ct1 ptr_ct1 x.self.uc.ct1) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hle_ct1, hmax_ct1, hptr_ct1⟩
  have hct1_iff := ofNat_beq_960_iff (by omega : x.self.uc.ct1.length < 2 ^ 63)
  by_cases hct1_len : x.self.uc.ct1.length = 960
  · have hct1_beq : (BitVec.ofNat 64 x.self.uc.ct1.length == 960#64) = true := by
      rw [hct1_iff, decide_eq_true hct1_len]
    refine SepWPp.fold (vecU8HeapAt_expose_nonempty A cap_ct1 ptr_ct1 x.self.uc.ct1 (by omega)) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, _, hcap_ct1⟩
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
    wp_steps
    refine SepWP.fold
      (ct2DeallocAt_of_cells_drop A cap_ct2 ptr_ct2 ct2Full
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        hge128 hle_cap hmax_cap hptr_ct2 hcap_ct2)
      (by sep_focus) ?_
    refine SepWP.fold
      (ekSentCt1ReceivedCells_entails_memRegion_504 x.selfA _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP.fold
      (authenticatorPinAt_of_sp_1328 A s0.sp g_auth x.self.uc.auth)
      (by sep_focus) ?_
    have hmr_ct1 : memRegion (s0.sp - 1248#64) 960 = memRegion (s0.sp - 1248#64) x.self.uc.ct1.length := by
      rw [hct1_len]
    refine SepWP.fold (Entails.of_eq hmr_ct1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2 h_mc (s0.sp - 1248#64, ptr_ct1, x.self.uc.ct1) hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, htr1⟩
    refine SepWPp.rw_pre (by rw [memRegion_128_sp_288 s0.sp]) ?_
    sep_elim_exists
    refine SepWPp.fold (vecU8HeapAt_pure_bounds A cap_dk ptr_dk x.self.uc.dk) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hle_dk, hmax_dk, hptr_dk⟩
    have hdk_iff := ofNat_beq_2400_iff (by omega : x.self.uc.dk.length < 2 ^ 63)
    have hptr_dk_beq : (ptr_dk == 0#64) = false := beq_false_of_ne hptr_dk
    by_cases hdk_len : x.self.uc.dk.length = 2400
    · have hdk_beq : (BitVec.ofNat 64 x.self.uc.dk.length == 2400#64) = true := by
        rw [hdk_iff, decide_eq_true hdk_len]
      refine SepWPp.fold (vecU8HeapAt_expose_nonempty A cap_dk ptr_dk x.self.uc.dk (by omega)) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, _, _, hcap_dk⟩
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMlkemDecapsSym) hF_sf ?_
      wp_steps
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
      refine SepWP.fold
        (vecU8At_of_sp_1280 A s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1 hle_ct1 hmax_ct1 hptr_ct1 hcap_ct1)
        (by sep_focus) ?_
      have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
        rw [hsp_sf]
      refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv2
      wpp_call_lscro_recvCt2 h_decaps
        ⟨s0.sp - 152#64, ptr_dk, ⟨x.self.uc.dk, hdk_len⟩,
         s0.sp - 1248#64, ⟨x.self.uc.ct1, hct1_len⟩,
         s0.sp - 288#64, ⟨ct2Full.take 128, htake128_len⟩⟩ hinv2
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      conv => arg 4; dsimp only [List.Vector.toList]
      have hfold_dk := bytes_rem_entails_ct2DeallocAt A cap_dk ptr_dk x.self.uc.dk
        hle_dk hmax_dk hptr_dk hcap_dk
      have hfold_ct1_buf : ((s0.sp - 1248#64) ↦ₛ x.self.uc.ct1) ⊢ memRegion (s0.sp - 1248#64) 960 :=
        hct1_len ▸ pointsToBytes_entails_memRegion (s0.sp - 1248#64) x.self.uc.ct1
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
        rw [← hstack_sf, hsp]
      refine SepWPp.fold hfold_dk (by sep_focus) ?_
      refine SepWPp.fold hfold_ct1_buf (by sep_focus) ?_
      refine SepWPp.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      refine SepWPp.rw_pre (by ac_rfl)
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
      exact allowPanic_isPanic_recvCt2 hpan_dk
        (by simp only [wp_norm, arm64_norm, htr1, htr, List.prefix_refl]) hm
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
    exact allowPanic_isPanic_recvCt2 hpan_ct1
      (by simp only [wp_norm, arm64_norm, htr, List.prefix_refl]) hm

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
