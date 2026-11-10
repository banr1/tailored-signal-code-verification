/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 6 (Relocatable)

Relocatable `[LibsignalPlacement]` proofs for Path 5c (`outMsg = some decoded`,
`recv_ek = .ok uc_ek`, `ack = true`) and epilogue convergence (`+16596 -> +18996`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272

/-! ## 1. `Split928` Assembly and Reconstruction for `States.ct2Sampled` (Path 5c) -/

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_send_ct2_mid_step_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64)
    (g_uc : AuthWords) (epoch : BitVec 64)
    (ct2Cap ct2Ptr ct2Len macCap macPtr macLen : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11636#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_382).base) s_in
      (wordsAt (fsp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((fsp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((fsp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((fsp + 4064#64) ↦₆₄ ct2Len) ∗
        ((fsp + 4072#64) ↦₆₄ macCap) ∗
        ((fsp + 4080#64) ↦₆₄ macPtr) ∗
        ((fsp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (fsp + 2256#64) 56 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion (fsp + 3992#64) 104 ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc epoch) ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x0 = fsp + 1856#64 ∧
        sf.readReg64 .x1 = ct2Ptr ∧
        sf.readReg64 .x2 = ct2Len ∧
        sf.readReg64 .x3 = macPtr ∧
        sf.readReg64 .x4 = macLen ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = macCap ∧
        sf.readReg64 .x21 = fsp + 3856#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = ct2Cap ∧
        sf.readReg64 .x26 = ct2Ptr ∧
        sf.readReg64 .x27 = macPtr ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        sf.readReg64 .x30 = (blkPl_332).base + 11696#64 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hpre :
      wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗
        ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗
        ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (s_in.sp + 2256#64) 56 ∗
        Rest ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
        wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗
        ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗
        ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        (((s_in.sp + 2256#64) ↦₆₄ v0) ∗
          ((s_in.sp + 2264#64) ↦₆₄ v1) ∗
          ((s_in.sp + 2272#64) ↦₆₄ v2) ∗
          ((s_in.sp + 2280#64) ↦₆₄ v3) ∗
          ((s_in.sp + 2288#64) ↦₆₄ v4) ∗
          ((s_in.sp + 2296#64) ↦₆₄ v5) ∗
          ((s_in.sp + 2304#64) ↦₆₄ v6)) ∗
        Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (cells_7_unfold (s_in.sp + 2256#64)))))))))) ?_
    simp only [wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro v4
    apply Entails.sepExists_elim; intro v5
    apply Entails.sepExists_elim; intro v6
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.of_eq (by ac_rfl))))))))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v1
  apply ProofLib.SepWP.exists_left; intro v2
  apply ProofLib.SepWP.exists_left; intro v3
  apply ProofLib.SepWP.exists_left; intro v4
  apply ProofLib.SepWP.exists_left; intro v5
  apply ProofLib.SepWP.exists_left; intro v6
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        (wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
          wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]) ∗
        wordsAt (s_in.sp + 2256#64) (ct2SentWordsList g_uc epoch) ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x0 = s_in.sp + 1856#64 ∧
      sf.readReg64 .x1 = ct2Ptr ∧
      sf.readReg64 .x2 = ct2Len ∧
      sf.readReg64 .x3 = macPtr ∧
      sf.readReg64 .x4 = macLen ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x20 = macCap ∧
      sf.readReg64 .x21 = s_in.sp + 3856#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x25 = ct2Cap ∧
      sf.readReg64 .x26 = ct2Ptr ∧
      sf.readReg64 .x27 = macPtr ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      sf.readReg64 .x30 = (blkPl_332).base + 11696#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
    dsimp only [ct2SentWordsList, authWordsList, vecWordsList]
    simp only [List.cons_append, List.nil_append,
      wordsAt_7, wordsAt_6, BitVec.add_assoc, BitVec.reduceAdd, hx21, hx29]
    wp_steps
    wp_done
  · have h56 := wordsAt_entails_memRegion (ct2SentWordsList g_uc epoch) (s_in.sp + 3992#64) 56 rfl
    have h48 := wordsAt_entails_memRegion [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]
      (s_in.sp + 4048#64) 48 rfl
    have h104 :
        wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
          wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen] ⊢
        memRegion (s_in.sp + 3992#64) 104 := by
      refine Entails.trans (sepConj_mono h56 h48) ?_
      rw [← ProofLib.memRegion_split' (b := s_in.sp + 3992#64) (n := 56) (k := 48)
            (b' := s_in.sp + 4048#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono_left h104

theorem ct1Sampled_send_ct2_and_encode_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)))
    (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (Frame R : SepProp)
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11624#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (blkPl_332).base + 11696#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 →
      sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap →
      sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr →
      sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP (lsProg_332 (Rust.withPanics ext))
        ((blkPl_332).base + 11696#64) sf
        ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A ct2Cap ct2Ptr ∗
          vecCapPtrDealloc A macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗
          memRegion (fsp + 3992#64) 104 ∗
          Unchunked.unchunkedSendCt2PlacedRoAt ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX) ∗ Frame)
        (fun sm Pm =>
          SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_347).base) s_in
      ((memRegion (fsp + 1856#64) 400 ∗
        memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
        memRegion (fsp + 3992#64) 104 ∗
        Unchunked.unchunkedSendCt2PlacedRoAt ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX) ∗ Frame)
      (fun sm Pm =>
        SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  subst hsp
  have hsc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_347).base) (withLsCodeLoaded lsmpl (Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) := hsendCt2
  have henc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_382).base) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)) := hsendCt2Enc
  have hsplit_sc := stackAt_statesRecvCallee_eq_unchunkedSendCt2' s_in.sp
  have hsplit_enc := stackAt_statesRecvCallee_eq_sendCt2Encoder' s_in.sp
  have hmid_lem := @ct1Sampled_send_ct2_mid_step_placed _ ext
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat]
    at hpc hsc_raw henc_raw hsplit_sc hsplit_enc hmid_lem hnext ⊢
  rw [hsplit_sc]
  wp_steps
  refine call_sendCt2_statesRecv_placed (P_pan := P_pan) hsc_raw
    (s_in.sp + 3992#64) (s_in.sp + 3856#64) uc_ek outUc ct2 mac hsc
    (ret_pc := (blkPl_332).base + 11636#64) (next_pc := (blkPl_382).base) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcl)
    (by simp only [State.pc, arm64_norm]; rfl) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm, hx29])
    (by simp only [Reg.x1, arm64_norm, hx21])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hcl1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  simp only [arm64_norm, hx21, hx29] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have h56_eq : (s_in.sp + 3992#64) + 56#64 = s_in.sp + 4048#64 := by bv_omega
  have h80_eq : (s_in.sp + 3992#64) + 80#64 = s_in.sp + 4072#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s_in.sp + 3992#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s_in.sp + 4048#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s_in.sp + 4072#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  have hmid := hmid_lem
    sf1 s_in.sp g_uc outUc.epoch
    ct2Cap ct2Ptr (BitVec.ofNat 64 ct2.length) macCap macPtr (BitVec.ofNat 64 mac.length)
    (relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
      (ct2Ptr ↦ₛ ct2) ∗ vecU8Tail A ct2Cap ct2Ptr ct2 ∗
      (macPtr ↦ₛ mac) ∗ vecU8Tail A macCap macPtr mac ∗
      memRegion (s_in.sp + 1856#64) 400 ∗
      memRegion (s_in.sp + 3856#64) 128 ∗
      Unchunked.unchunkedSendCt2PlacedRoAt ∗
      A.pool ∗
      (memRegion (s_in.sp - 19552#64) 2832 ∗ stackAt s_in.sp unchunkedSendCt2Stack) ∗
      Frame)
    hfsp_align hpc1 hrun1 hsp1 hx21_1 hx29_1
  refine SepWP.weaken_pre ?_
    (ct1Sampled_seq_clean_lscl hcl1 hmid (fun sf2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2,
      hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hx30_2, htr2⟩ => ?_))
  · exact Entails.of_eq (by ac_rfl)
  wp_conv_pre => rw [← hsplit_sc, hsplit_enc]
  conv in (_ ∗ (anyHeap ∗ R)) => rw [← sepConj_assoc]
  refine call_sendCt2Encoder_statesRecv_placed (P_pan := P_pan) henc_raw
    (s_in.sp + 1856#64) ct2Ptr macPtr ct2 mac outEnc
    hct2_ne hmac_ne henc
    (s0 := s0) (ret_pc := (blkPl_332).base + 11696#64) (next_pc := (blkPl_332).base + 11696#64) (sp_call := s_in.sp)
    hcl2
    hpc2 hrun2 hsp2 hfsp_align
    hx30_2 (htr2.trans htr1)
    hx0_2 hx1_2 hx2_2 hx3_2 hx4_2
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hcl3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2,
    hx19_1, hx24_1, hx28_1] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsplit_enc.symm) (by sep_focus) ?_
  refine SepWP.weaken_pre ?_
    (hnext sf3 g_uc ct2Cap ct2Ptr macCap macPtr
      hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3 hcl3)
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_ack_stage_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp stA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11696#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 12072#64) s_in
      (words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          words50At (fsp + 1856#64) c_enc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
          copyScratchStackAt fsp
            { (copyFullScratchCt2 sc d) with
              c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }
              w88 := sc.w88 } ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = c_enc.c1.w11 ∧
        sf.readReg64 .x21 = g.v2.w2 ∧
        sf.readReg64 .x22 = g.v2.w1 ∧
        sf.readReg64 .x23 = c_enc.c0.w0 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x27 = s_in.readReg64 .x27 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At,
    ct2SentWordsList, authWordsList, vecWordsList, Words16.toList]
  simp only [List.cons_append, List.nil_append,
    wordsAt_16, wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd, hx29]
  wp_steps
  wp_done

theorem ct1Sampled_dealloc_mac_12072_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp macCap macPtr : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12072#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = macCap)
    (hx27 : s_in.readReg64 .x27 = macPtr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 12088#64) s_in
      (vecCapPtrDealloc A macCap macPtr ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx27
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  dsimp only [lsProg_332, spqrDeallocSym, spqrRustDeallocSym, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_raw hsplit ⊢
  rw [hsplit]
  dsimp only [vecCapPtrDealloc]
  by_cases hmac : (s_in.readReg64 .x1 == 0#64) = true <;>
    simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    rw [← hsplit]
    wp_done
  · wp_steps
    wp_apply
    rw [← hsplit]
    wp_done

theorem ct1Sampled_dealloc_ct2_12088_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp ct2Cap ct2Ptr : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12088#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx25 : s_in.readReg64 .x25 = ct2Cap)
    (hx26 : s_in.readReg64 .x26 = ct2Ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 12108#64) s_in
      (vecCapPtrDealloc A ct2Cap ct2Ptr ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx25 hx26
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  dsimp only [lsProg_332, spqrDeallocSym, spqrRustDeallocSym, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_raw hsplit ⊢
  rw [hsplit]
  dsimp only [vecCapPtrDealloc]
  by_cases hct2 : (s_in.readReg64 .x25 == 0#64) = true <;>
    simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    rw [← hsplit]
    wp_done
  · wp_steps
    wp_apply
    rw [← hsplit]
    wp_done

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_drop_and_finish_stage_12108_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp stA : BitVec 64)
    (vecs_enc : List (List GF16)) (hvecs_enc_len : vecs_enc.length = NUM_POLYS)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12108#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = c_enc.c1.w11)
    (hx21 : s_in.readReg64 .x21 = g.v2.w2)
    (hx22 : s_in.readReg64 .x22 = g.v2.w1)
    (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16596#64) s_in
      (((fsp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs_enc ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗
        memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc d) with
            c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }
            w88 := sc.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 8#64) 384 ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 4#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        copyScratchStackAt s_in.sp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 4#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine ct1Sampled_seq_clean_lscl hcl (mid := lsmpl.base 265)
      (P_mid := ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs_enc ∗
        vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
        memRegion (s_in.sp + 3136#64) 16 ∗
        copyScratchStackAt s_in.sp
          { (copyFullScratchCt2 sc d) with
            c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }
            w88 := sc.w88 } ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗
        memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗
        Rest)
      (Q := fun sm => sm.sp = s_in.sp ∧
        sm.readReg64 .x0 = stA + 8#64 ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sm.readReg64 .x21 = g.v2.w2 ∧
        sm.readReg64 .x22 = g.v2.w1 ∧
        sm.readReg64 .x23 = c_enc.c0.w0 ∧
        sm.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sm.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sm.readReg64 .x29 = s_in.readReg64 .x29 ∧
        sm.readReg64 .x30 = (blkPl_332).base + 12124#64 ∧
        TraceCalleeSaved sm s_in) ?_ ?_
    · dsimp only [lsProg_332,
        d, mkSplit928Ct2Sampled, epilogueStoreStackPart1At, epilogueStackOfSplit928,
        Words16.toList, BitVec.ofNat_eq_ofNat]
        at hpc ⊢
      wp_steps
      wp_done
    · intro sm hpcm hrunm hclm ⟨hspm, hx0m, hx19m, hx21m, hx22m, hx23m, hx24m, hx28m, hx29m, hx30m, htrm⟩
      refine ct1Sampled_seq_clean_lscl hclm (mid := lsmpl.base 264)
        (P_mid := ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 8#64) 384 ∗
          vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 ∗
          copyScratchStackAt s_in.sp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At s_in.sp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          A.pool ∗
          memRegion (s_in.sp - 19552#64) 15424 ∗
          stackAt s_in.sp dropGluePoly16Stack ∗
          Rest)
        (Q := fun sm2 => sm2.sp = s_in.sp ∧
          sm2.readReg64 .x0 = s_in.sp + 2752#64 ∧
          sm2.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sm2.readReg64 .x20 = 4#64 ∧
          sm2.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sm2.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sm2.readReg64 .x29 = s_in.readReg64 .x29 ∧
          sm2.readReg64 .x30 = (blkPl_332).base + 16176#64 ∧
          TraceCalleeSaved sm2 s_in) ?_ ?_
      · have hdrop_poly := drop_glue_poly16_mem_on
          (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hclm
        dsimp only [lsProg_332, withMemEq, dropGluePoly16Spec, polyArrayBytes,
          d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
          epilogueStoreStackPart1At, epilogueStackOfSplit928, Words16.toList, BitVec.ofNat_eq_ofNat]
          at hpcm hdrop_poly ⊢
        rw [← hspm]
        wp_call hdrop_poly ⟨stA + 8#64, vecs_enc⟩
        rw [hspm]
        simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd, hx21m, hx22m, hx23m]
        wp_steps
        wp_done
      · intro sm2 hpcm2 hrunm2 hclm2 ⟨hspm2, hx0m2, hx19m2, hx20m2, hx24m2, hx28m2, hx29m2, hx30m2, htrm2⟩
        have hdrop_ss := drop_glue_sorted_set_pt16_mem_on
          (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hclm2
        dsimp only [lsProg_332, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, BitVec.ofNat_eq_ofNat]
          at hpcm2 hdrop_ss ⊢
        rw [← hspm2]
        wp_call hdrop_ss ⟨sm2.sp + 2752#64, vecs_dec⟩
        wp_steps
        rw [hspm2]
        wp_done
  · have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr))

/-! ## 2. Path 5c Epilogue Convergence (`+16596 -> +16800 -> +17464 -> +18892 -> +18996`) -/

theorem ct1Sampled_copy_some_ack_part2a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 4#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = 3#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976,
      hsplit, show memRegion (s_in.sp + 3272#64) 376 = memRegion (s_in.sp + 3272#64) (mid376Bytes w0 w8 w16 bs352_976).length by rw [hmid376_len]]
  dsimp only [lsProg_332, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  wp_steps
  wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976)
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_ack_part2b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (v576 v584 v592 : BitVec 64) (bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16800#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = 3#64)
    (hx19 : s_in.readReg64 .x19 = outA) :
    let d := mkSplit928Ct2Sampled c_enc g epoch (s_in.readReg64 .x2)
      k.wf8 k.w3c0 k.w3c8 k.w100 (mid376Bytes v576 v584 v592 bs352_576) k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        statesRecvRoPlacedAt ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          statesRecvRoPlacedAt ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  dsimp only [lsProg_332, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt,
    lsLogFilterAddr, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes v576 v584 v592 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) v576 v584 v592 bs352_576]
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8]
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_send_ct2_mid_step_placed
  ct1Sampled_send_ct2_and_encode_placed
  ct1Sampled_copy_some_ack_stage_placed
  ct1Sampled_dealloc_mac_12072_placed
  ct1Sampled_dealloc_ct2_12088_placed
  ct1Sampled_drop_and_finish_stage_12108_placed
  ct1Sampled_copy_some_ack_part2a_placed
  ct1Sampled_copy_some_ack_part2b_placed
)

end CryptoVerification.SpqrV1.States.Recv
