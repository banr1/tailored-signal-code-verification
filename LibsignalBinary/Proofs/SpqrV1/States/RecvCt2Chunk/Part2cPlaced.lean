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
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable Constant-Time MAC Comparison

Relocatable `[LibsignalPlacement]` proof of the bytewise XOR-OR loop (`+904 .. +928`) and MAC
verification + tag deallocation (`+860 .. +968` / `+1308`, calling `is_non_zero` at Block `380`).
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

/-! ## Constant-Time Bytewise Comparison Loop (`+904 .. +928`) -/

set_option maxHeartbeats 1200000 in
theorem recv_ct2_chunk_compare_loop_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (x : RecvCt2ChunkGhost F)
    (s0 : State) (R : SepProp) :
    ∀ (lhs rhs : List (BitVec 8)) (ptr_lhs ptr_rhs : BitVec 64) (acc : BitVec 8)
      (st : State) (F_loop : SepProp),
      lhs ≠ [] →
      lhs.length ≤ rhs.length →
      lhs.length ≤ 32 →
      st.pc = (blkPl_350).base + 904#64 →
      st.status = .Running →
      st.sp = s0.sp - 2496#64 →
      st.trace = s0.trace →
      calleeSavedVRegs st = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st.mem →
      st.readReg64 .x0 = BitVec.zeroExtend 64 acc →
      st.readReg64 .x8 = BitVec.ofNat 64 lhs.length →
      st.readReg64 .x9 = ptr_lhs →
      st.readReg64 .x10 = ptr_rhs →
      (∀ (st' : State),
        st'.pc = (blkPl_350).base + 928#64 →
        st'.status = .Running →
        st'.sp = s0.sp - 2496#64 →
        st'.trace = s0.trace →
        calleeSavedVRegs st' = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st'.mem →
        st'.readReg64 .x0 =
          BitVec.zeroExtend 64 ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) acc) →
        st'.readReg64 .x19 = st.readReg64 .x19 →
        st'.readReg64 .x21 = st.readReg64 .x21 →
        st'.readReg64 .x22 = st.readReg64 .x22 →
        st'.readReg64 .x23 = st.readReg64 .x23 →
        st'.readReg64 .x24 = st.readReg64 .x24 →
        st'.readReg64 .x25 = st.readReg64 .x25 →
        st'.readReg64 .x26 = st.readReg64 .x26 →
        st'.readReg64 .x27 = st.readReg64 .x27 →
        st'.readReg64 .x28 = st.readReg64 .x28 →
        st'.readReg64 .x29 = st.readReg64 .x29 →
        st'.readReg64 .x30 = st.readReg64 .x30 →
        SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
          ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
          (recvCt2PlacedPostQ K F A x s0 R)
          (recvCt2PlacedPostQp K F A x s0 R)) →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
        ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R) := by
  simp only [lsProg_350]
  intro lhs
  induction lhs with
  | nil =>
    intro _ _ _ _ _ _ hne
    exact (hne rfl).elim
  | cons a lhs' ih =>
    intro rhs ptr_lhs ptr_rhs acc st F_loop _ hle hle32 hpc hrun hsp htr hvregs hinv hx0 hx8 hx9 hx10 hcont
    cases rhs with
    | nil => simp at hle
    | cons b rhs' =>
      cases lhs' with
      | nil =>
        have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
        simp only [List.length_cons, List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat,
          wp_norm, arm64_norm] at hsp_norm hx0 hx8 hx9 hx10
        refine SepWPp.rw_pre (by
          rw [pointsToBytes_cons ptr_lhs a [], pointsToBytes_nil, sepConj_emp,
              pointsToBytes_cons ptr_rhs b rhs', sepConj_assoc]) ?_
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 928#64) hinv ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv1
        refine SepWPp.rw_pre (by
          rw [show ptr_lhs ↦₈ a ∗ ptr_rhs ↦₈ b ∗ (ptr_rhs + 1#64) ↦ₛ rhs' ∗ F_loop =
                (ptr_lhs ↦₈ a ∗ (ptr_lhs + 1#64) ↦ₛ []) ∗
                  (ptr_rhs ↦₈ b ∗ (ptr_rhs + 1#64) ↦ₛ rhs') ∗ F_loop by
                rw [pointsToBytes_nil]; ac_rfl,
              ← pointsToBytes_cons ptr_lhs a [],
              ← pointsToBytes_cons ptr_rhs b rhs']) ?_
        refine hcont _
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv1
          ?_
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
        · simp only [List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
            wp_norm, arm64_norm, *]
          exact xor_orr_loop_step acc a b
      | cons a2 lhs'' =>
        have hsub1 := sub_one_ofNat_cons2 a a2 lhs'' hle32
        have hbne1 := bne_one_ofNat_cons2 a a2 lhs'' hle32
        have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
        simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx8 hx9 hx10
        refine SepWPp.rw_pre (by
          rw [pointsToBytes_cons ptr_lhs a (a2 :: lhs''),
              pointsToBytes_cons ptr_rhs b rhs']) ?_
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 904#64) hinv ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv1
        refine SepWPp.rw_pre (show
            _ =
            ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs'')) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs') ∗
              ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop) by ac_rfl) ?_
        refine ih rhs' (ptr_lhs + 1#64) (ptr_rhs + 1#64) (acc ||| (a ^^^ b))
          _ ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop)
          (List.cons_ne_nil _ _)
          (by simp only [List.length_cons] at hle ⊢; omega)
          (by simp only [List.length_cons] at hle32 ⊢; omega)
          (by simp only [hbne1, ↓reduceIte, wp_norm, arm64_norm, *])
          (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv1
          (by simp only [wp_norm, arm64_norm, *]; exact xor_orr_loop_step acc a b)
          (by simp only [hsub1, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (fun st' hpc' hrun' hsp' htr' hvregs' hinv' hx0' hx19' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hx30' => ?_)
        refine SepWPp.rw_pre (by
          rw [show ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs'')) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs') ∗
                ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop) =
              ((ptr_lhs ↦₈ a) ∗ ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs''))) ∗
                ((ptr_rhs ↦₈ b) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs')) ∗ F_loop by ac_rfl,
              ← pointsToBytes_cons ptr_lhs a (a2 :: lhs''),
              ← pointsToBytes_cons ptr_rhs b rhs']) ?_
        exact hcont st' hpc' hrun' hsp' htr' hvregs' hinv'
          (by simpa only [List.zip_cons_cons, List.foldl_cons] using hx0')
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

/-! ## Full MAC Compare + Tag Dealloc (`+860 .. +968` / `+1308`) -/

set_option maxHeartbeats 1600000 in
theorem recv_ct2_chunk_mac_compare_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F)
    (receivingCt2 : PolyDecoder)
    (ct2Full : Bytes)
    (auth' : Authenticator)
    (ptr_mac : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : ¬ ct2Full.length < 128)
    (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hct1_len : x.self.uc.ct1.length = 960)
    (hdk_len : x.self.uc.dk.length = 2400)
    (hpc : st.pc = (blkPl_350).base + 860#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hcont_err : ∀ (st' : State),
      (ct2Full.drop 128).length ≤ 32 →
      (compare_prefix (ct2Full.drop 128)
        (auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)) != 0#8) = true →
      st'.pc = (blkPl_350).base + 968#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = s0.sp - 2000#64 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          A.pool ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R))
    (hcont_ok : ∀ (st' : State),
      (ct2Full.drop 128).length ≤ 32 →
      (compare_prefix (ct2Full.drop 128)
        (auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)) != 0#8) = false →
      st'.pc = (blkPl_350).base + 1308#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 2496#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = s0.sp - 2000#64 →
      st'.readReg64 .x21 = st.readReg64 .x21 →
      st'.readReg64 .x22 = st.readReg64 .x22 →
      st'.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128) →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
          ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
          memRegion (s0.sp - 1248#64) 960 ∗
          A.pool ∗
          stackAt (s0.sp - 2496#64) extHookStack ∗
          F_frame)
        (recvCt2PlacedPostQ K F A x s0 R)
        (recvCt2PlacedPostQp K F A x s0 R)) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8 A (s0.sp - 1248#64)
          (auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)) ∗
        memRegion (s0.sp - 1224#64) 24 ∗
        memRegion (s0.sp - 1200#64) 912 ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack ∗
        F_frame)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  let tag := auth'.macCtUnchecked F x.epoch (x.self.uc.ct1 ++ ct2Full.take 128)
  have htag_len : tag.length = 32 := by simp [tag]
  have htag_pos : 0 < tag.length := by omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_1248 A s0.sp tag htag_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_tag ptr_tag
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_tag_ne, hlay_tag, hptr_tag_ne, hle_tag⟩
  have ⟨_, _, hmax_tag⟩ := hlay_tag
  have hcap_tag_beq : (cap_tag == 0#64) = false := beq_false_of_ne hcap_tag_ne
  have h_inz := isNonZero_placed_lscro ext
  simp only [isNonZeroSpec] at h_inz
  have h_dealloc := hA.dealloc_lscro
  have h_pan_bounds := hA.panic_bounds_check
  have h_loop := @recv_ct2_chunk_compare_loop_placed_wpp _ K F A ext x s0 R
  by_cases heq128 : ct2Full.length = 128
  · have hsub0 : ct2Full.length - 128 = 0 := by omega
    have hdrop_nil : ct2Full.drop 128 = [] := by
      rw [List.drop_eq_nil_iff]; omega
    have hmac_le32 : (ct2Full.drop 128).length ≤ 32 := by simp [hdrop_nil]
    have hx23_0 : st.readReg64 .x23 = 0#64 := by rw [hx23, hsub0]
    have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx23_0
    clear hA h_pan_bounds h_loop hcont_err
    simp only [lsProg_350] at h_inz h_dealloc hcont_ok ⊢
    refine SepWPp.rw_pre (by rw [htag_len]) ?_
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 380) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2 h_inz (0#8 : BitVec 8) hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hx0_sf, htr1⟩
    have hfold_tag :
        (ptr_tag ↦ₛ tag) ∗ memRegion (ptr_tag + 32#64) (cap_tag.toNat - 32) ⊢
          memRegion ptr_tag cap_tag.toNat := by
      rw [← htag_len]
      exact bytes_rem_entails_memRegion ptr_tag cap_tag tag hle_tag hmax_tag
    refine SepWPp.fold hfold_tag (by sep_focus) ?_
    refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf ?_
    wp_steps
    have hstack_sf :
        memRegion (s0.sp - 18880#64) 16368 ∗ stackAt st.sp 16 ⊢
          stackAt sf.sp extHookStack := by
      rw [hsp_sf, hsp, ← stackAt_extHook_eq_16 s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_sf (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2 h_dealloc (ptr_tag, cap_tag.toNat, 1) hinv2
    refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr2 => ?_
    have hstack_back : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    refine SepWPp.fold
      (rejoin_memRegion_960_24_24_912 s0.sp cap_tag ptr_tag 32#64)
      (by sep_focus) ?_
    have hcmp_nil : (compare_prefix (ct2Full.drop 128) tag != 0#8) = false := by
      simp [compare_prefix, isNonZero, inz, hdrop_nil]
    have htst := tst_ff_zeroExtend_64_true_of_bne_false (v := isNonZero 0#8) (by simp [isNonZero, inz])
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 1308#64) hF_sf_1 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont_ok _ hmac_le32 hcmp_nil
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv3
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by rw [hsub0]; simp only [BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge129 : 129 ≤ ct2Full.length := by omega
    have hsub_ne0 : ct2Full.length - 128 ≠ 0 := by omega
    have hdrop_len : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
    have hdrop_ne0 : (ct2Full.drop 128).length ≠ 0 := by omega
    have hdrop_lt : (ct2Full.drop 128).length < 2 ^ 63 := by omega
    have hx23_ne : BitVec.ofNat 64 (ct2Full.length - 128) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change ct2Full.length - 128 = 0 at h1
      omega
    have hx23_beq : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false :=
      beq_false_of_ne hx23_ne
    by_cases hgt32 : ¬ (ct2Full.drop 128).length ≤ 32
    · have hgt32' : ¬ (ct2Full.length - 128 ≤ 32) := by
        rwa [List.length_drop] at hgt32
      have hule_t : (32#64 : BitVec 64).ule (BitVec.ofNat 64 ct2Full.length - 129#64) = true :=
        (ule_32_sub_129_iff hge129 hmax_ct2).mpr hgt32'
      have hpan_model := recv_ct2_chunk_isPanic_of_mac_gt_32 (K := K)
        x.self x.epoch x.chunk receivingCt2 ct2Full hepoch hadd hdec hge128 hct1_len hdk_len hgt32
      have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
      simp only [wp_norm, arm64_norm] at hsp_norm hx23
      clear hA h_inz h_dealloc h_loop hcont_err hcont_ok
      simp only [lsProg_350] at h_pan_bounds ⊢
      refine SepWPp.rw_pre (by rw [htag_len]) ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrPanicBoundsCheckSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      exact allowPanic_isPanic_recvCt2 hpan_model (by simp only [Rust.panicked, wp_norm, arm64_norm, *]) hm
    · have hle32 : (ct2Full.drop 128).length ≤ 32 := Classical.not_not.mp hgt32
      have hle32' : ct2Full.length - 128 ≤ 32 := by rwa [List.length_drop] at hle32
      have hule_f : (32#64 : BitVec 64).ule (BitVec.ofNat 64 ct2Full.length - 129#64) = false := by
        rw [Bool.eq_false_iff]
        intro ht
        exact ((ule_32_sub_129_iff hge129 hmax_ct2).mp ht) hle32'
      have hexpose_mac :
          vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢
            (ptr_mac ↦ₛ ct2Full.drop 128) ∗ A.live ptr_mac (ct2Full.length - 128) 1 := by
        rw [← hdrop_len]
        exact vecBufAt_expose_of_bytes_live A ptr_mac (ct2Full.drop 128) hdrop_ne0 hdrop_lt
      have hfold_mac :
          (ptr_mac ↦ₛ ct2Full.drop 128) ∗ A.live ptr_mac (ct2Full.length - 128) 1 ⊢
            vecBufAt A (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) := by
        rw [← hdrop_len]
        exact vecBufAt_of_bytes_live A ptr_mac (ct2Full.drop 128) hdrop_ne0 hdrop_lt
      refine SepWPp.fold hexpose_mac (by sep_focus) ?_
      refine SepWPp.rw_pre (by rw [htag_len]) ?_
      have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
      simp only [wp_norm, arm64_norm] at hsp_norm hx23
      clear hA h_pan_bounds
      simp only [lsProg_350] at h_inz h_dealloc h_loop hcont_err hcont_ok ⊢
      refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 904#64) hinv ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      refine SepWPp.rw_pre (show
          _ =
          (ptr_mac ↦ₛ ct2Full.drop 128) ∗ (ptr_tag ↦ₛ tag) ∗
            (((s0.sp - 1248#64) ↦₆₄ cap_tag) ∗ ((s0.sp - 1240#64) ↦₆₄ ptr_tag) ∗
              ((s0.sp - 1232#64) ↦₆₄ 32#64) ∗
              memRegion (ptr_tag + 32#64) (cap_tag.toNat - 32) ∗ A.live ptr_tag cap_tag.toNat 1 ∗
              memRegion (s0.sp - 1224#64) 24 ∗ memRegion (s0.sp - 1200#64) 912 ∗
              ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
              ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
              A.live ptr_mac (ct2Full.length - 128) 1 ∗
              A.pool ∗ stackAt (s0.sp - 2496#64) extHookStack ∗ F_frame) by ac_rfl) ?_
      have hmac_ne_nil : ct2Full.drop 128 ≠ [] := by
        intro hnil
        have hlen0 := congrArg List.length hnil
        rw [List.length_drop, List.length_nil] at hlen0
        omega
      refine h_loop (ct2Full.drop 128) tag ptr_mac ptr_tag 0#8 _ _
        hmac_ne_nil (by rw [htag_len]; exact hle32) hle32
        (by wp_norm_goal)
        (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv1
        (by simp only [wp_norm, arm64_norm, *])
        (by rw [List.length_drop]; simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun st1 hpc1 hrun1 hsp1 htr1 hvregs1 hinv2 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1 => ?_)
      have hsp1_norm : st1.readReg64 .sp = s0.sp - 2496#64 := hsp1
      simp only [wp_norm, arm64_norm] at hsp1_norm hx0_1 hx28_1 hx30_1
      refine SepWPp.fold hfold_mac (by sep_focus) ?_
      refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 380) hinv2 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      wpp_call_lscro_recvCt2 h_inz
        (((ct2Full.drop 128).zip tag).foldl (fun r (a, b) => r ||| (a ^^^ b)) 0#8)
        hinv3
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hx0_sf, htr2⟩
      have hfold_tag :
          (ptr_tag ↦ₛ tag) ∗ memRegion (ptr_tag + 32#64) (cap_tag.toNat - 32) ⊢
            memRegion ptr_tag cap_tag.toNat := by
        rw [← htag_len]
        exact bytes_rem_entails_memRegion ptr_tag cap_tag tag hle_tag hmax_tag
      refine SepWPp.fold hfold_tag (by sep_focus) ?_
      refine SepWPp.of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf ?_
      wp_steps
      have hstack_sf :
          memRegion (s0.sp - 18880#64) 16368 ∗ stackAt st1.sp 16 ⊢
            stackAt sf.sp extHookStack := by
        rw [hsp_sf, hsp1, ← stackAt_extHook_eq_16 s0.sp]
        exact Entails.refl _
      refine SepWP.fold hstack_sf (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      wpp_call_lscro_recvCt2 h_dealloc (ptr_tag, cap_tag.toNat, 1) hinv4
      refine SepWPp.pure_left_focus (sf_1.trace = sf.trace) (by sep_focus) fun htr3 => ?_
      have hstack_back : stackAt sf.sp extHookStack = stackAt (s0.sp - 2496#64) extHookStack := by
        rw [hsp_sf, hsp1]
      refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_memRegion_960_24_24_912 s0.sp cap_tag ptr_tag 32#64)
        (by sep_focus) ?_
      rw [isNonZero_foldl_eq_compare_prefix] at *
      by_cases hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true
      · have htst := tst_ff_zeroExtend_64_false_of_bne hcmp
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 968#64) hF_sf_1 ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv5
        refine SepWPp.rw_pre (by ac_rfl)
          (hcont_err _ hle32 hcmp
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv5
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
      · have hcmp_f : (compare_prefix (ct2Full.drop 128) tag != 0#8) = false :=
          Bool.eq_false_iff.mpr hcmp
        have htst := tst_ff_zeroExtend_64_true_of_bne_false hcmp_f
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 1308#64) hF_sf_1 ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv5
        refine SepWPp.rw_pre (by ac_rfl)
          (hcont_ok _ hle32 hcmp_f
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv5
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
