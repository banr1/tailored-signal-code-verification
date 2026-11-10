/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm, Part 2

Verifies the `msg.epoch = st.uc.epoch ∧ msg.payload = .ct2 chunk` branch (`<EkSentCt1Received>::
recv_ct2_chunk` at `0x5ec2c` with `.error`, `.stillReceiving`, and `.done` continuations) and
assembles `states_recv_arm_ekSentCt1Received` (`+228 -> s0.x30`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

theorem ekSentCt1ReceivedAt_eq_chunked (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    ekSentCt1ReceivedAt A a st = chunkedEkSentCt1ReceivedAt A a st := rfl

@[local arm64_norm, local wp_norm]
theorem none2Cap_add_two_beq_zero :
    (18446744073709551614#64 + 2#64 == 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem none2Cap_add_two_bne_zero :
    (18446744073709551614#64 + 2#64 != 0#64) = false := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_two_beq_zero :
    (18446744073709551615#64 + 2#64 == 0#64) = false := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_two_bne_zero :
    (18446744073709551615#64 + 2#64 != 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_one_beq_zero :
    (18446744073709551615#64 + 1#64 == 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_one_bne_zero :
    (18446744073709551615#64 + 1#64 != 0#64) = false := rfl

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  rw [bne_iff_ne]
  bv_omega

theorem cap_add_one_beq_zero_false_recv {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_one_bne_zero_true_recv {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  rw [bne_iff_ne]
  bv_omega

/-! ## 1. Post-Call `.error (.err e)` Path (`0x56574..0x565a4 -> 0x59fd0..0x59ff0`) -/

/-- The only non-panic error returned by `EkSentCt1Received.recv_ct2_chunk` is `.macVerifyFailed`. -/
theorem recv_ct2_chunk_err_eq_macVerifyFailed {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (e : Error)
    (herr : self.recv_ct2_chunk K epoch chunk = .error (.err e)) :
    e = .macVerifyFailed := by
  rw [recv_ct2_chunk_eq_do] at herr
  by_cases h0 : (epoch != self.uc.epoch) = true
  · simp only [h0, ↓reduceIte] at herr; cases herr
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at herr
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, StatesResult.ofPanic,
      Except.mapError] at herr
    cases h1 : PolyDecoder.addChunk self.receiving_ct2 chunk with
    | error p => rw [h1] at herr; cases herr
    | ok recCt2 =>
      rw [h1] at herr
      dsimp only at herr
      cases h2 : recCt2.decodedMessage with
      | error p => rw [h2] at herr; cases herr
      | ok decOpt =>
        rw [h2] at herr
        dsimp only at herr
        cases decOpt with
        | none => cases herr
        | some ct2Full =>
          dsimp only at herr
          by_cases h3 : ct2Full.length < 128
          · simp only [h3, ↓reduceIte] at herr; cases herr
          · simp only [h3, ↓reduceIte] at herr
            cases h4 : decaps K self.uc.dk self.uc.ct1 (ct2Full.take 128) with
            | error p => rw [h4] at herr; cases herr
            | ok ssRaw =>
              rw [h4] at herr
              dsimp only at herr
              cases h5 : Authenticator.verifyCtError F
                (Authenticator.update F self.uc.auth self.uc.epoch
                  (spqrHkdfWith F (List.replicate 32 0#8) ssRaw
                    (sckaKeyInfoPrefix ++ CryptoGames.HMAC.toBEBytes 8 self.uc.epoch) 32))
                self.uc.epoch (self.uc.ct1 ++ ct2Full.take 128) (ct2Full.drop 128) with
              | error p => rw [h5] at herr; cases herr
              | ok vRes =>
                rw [h5] at herr
                dsimp only at herr
                cases vRes with
                | error _ => cases herr; rfl
                | ok u =>
                  cases u
                  dsimp only at herr
                  by_cases h6 : (self.uc.epoch == BitVec.allOnes 64) = true
                  · simp only [h6, ↓reduceIte] at herr; cases herr
                  · simp only [h6, Bool.false_eq_true, ↓reduceIte] at herr; cases herr

/-! ## 2. Post-Call `.ok (.stillReceiving outSt)` Path (`0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0`) -/

theorem vecU8_extract_with_cap_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hcap_lt ?_)
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst
    simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [hhdr dst, wordsAt_eq_pointsToBytes]
  refine sepConj_mono_right (Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ (Entails.refl _))

theorem unchunkedEkSentCt1ReceivedAt_extract_cap (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ g : FourVecWords,
        ⌜g.v1.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (ekSentCt1ReceivedWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
          (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st3 : Unchunked.SendEk.EkSent (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.dk⟩, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentAt A (dst + 24#64) st3 =
        unchunkedEkSentCt1ReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.dk) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ct1 ∗ (((dst + 24#64) + 72#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.dk ∗
        vecU8 A (dst + 72#64) st.ct1 ∗ ((dst + 96#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_with_cap_lt A a r0)
    (unchunkedEkSentAt_extract A (a + 24#64) st3)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  rw [sepConj_assoc (⌜v1.w0.toNat < 2 ^ 63⌝)]
  apply Entails.pure_left; intro hcap
  refine Entails.sepExists_right ⟨v1, rest⟩ (Entails.pure_right hcap ?_)
  exact wordsExtract_sepConj rfl heq

theorem chunkedEkSentCt1ReceivedAt_extract63_cap (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ w : Words63,
        ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w2 = st.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) := by
  unfold chunkedEkSentCt1ReceivedAt
  refine Entails.trans (sepConj_mono
    (unchunkedEkSentCt1ReceivedAt_extract_cap A a st.uc)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ct2) (a + 104#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  rw [sepConj_assoc (⌜g.v1.w0.toNat < 2 ^ 63⌝)]
  apply Entails.pure_left; intro hcap
  let w := mkWords63_13_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right ⟨hcap, rfl⟩ ?_)
  rw [words63At_eq_wordsAt, ← words63List_mkWords63_13_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem stillReceiving_result_976_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) a (.ok (.stillReceiving outSt)) ⊢
      ∃∗ w : Words63,
        ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w2 = outSt.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w)) := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt, ekSentCt1ReceivedAt_eq_chunked]
  apply Entails.pure_left; intro _
  exact chunkedEkSentCt1ReceivedAt_extract63_cap A a outSt

theorem sendEkUnusedAt_split_ab0_ac0 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qab0 : BitVec 128, ∃∗ qac0 : BitVec 128,
        ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
        ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2768#64) 1376 := by
  refine Entails.trans (sendEkUnusedAt_split_ac0 fsp) ?_
  apply Entails.sepExists_elim; intro qac0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 2736#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qab0
  refine Entails.sepExists_right qab0 (Entails.sepExists_right qac0 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_ab0_ac0 (fsp : BitVec 64) (qab0 qac0 : BitVec 128) :
    ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
    ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2768#64) 1376 ⊢
      sendEkUnusedAt fsp := by
  refine Entails.trans ?_ (sendEkUnusedAt_rejoin_ac0 fsp qac0)
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
    (((fsp + 2752#64) ↦₁₂₈ qac0) ∗ memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 2768#64) 1376) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 2736#64) qab0)) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Post-call block `0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0` (`+4384 -> s0.x30`)
    when `recv_ct2_chunk` returns `.ok (.stillReceiving outSt)`. -/
theorem ekSentCt1Received_post_call_still_56574
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.stillReceiving outSt)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range b (Rust.withPanics ext) 4384 28
  states_recv_fetches_range b (Rust.withPanics ext) 12612 680
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (stillReceiving_result_976_extract A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hcond1 := cap_add_two_bne_zero_true hcap
  have hcond2 := cap_add_two_beq_zero_false hcap
  have hcond3 := cap_add_one_beq_zero_false_recv hcap
  have hcond4 := cap_add_one_bne_zero_true_recv hcap
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, w_out.b3.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6,
             sp.b0.w7, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, w_out.b3.w6, sp.b1.w4, sp.b1.w5, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, w_out.b4.w9, sp.b2.w3, w_out.b4.w5, w_out.b0.w1, w_out.b4.w8,
             6#64, noneCap, sp.b2.w9⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 qac0
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ qac0) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono
      (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, noneCap]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
      ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]
    ac_rfl

/-! ## 3. Post-Call `.ok (.done (nhr, sec))` Path (`0x56574..0x5658c -> 0x58598..0x586f4 -> 0x59950..0x599c8 -> 0x59a7c..0x59b34 -> 0x59e88..0x59ff0`) -/

set_option maxHeartbeats 1600000 in
/-- Post-call block `0x56574..0x5658c -> 0x58598..0x586f4 -> 0x59950..0x599c8 -> 0x59a7c..0x59b34 -> 0x59e88..0x59ff0`
    (`+4384 -> s0.x30`) when `recv_ct2_chunk` returns `.ok (.done (nhr, sec))`. -/
theorem ekSentCt1Received_post_call_done_56574
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.done (nhr, sec))) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hadrp := fnAddr_adrp_59974 (b := b) (H := Rust.withPanics ext) hb
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range b (Rust.withPanics ext) 4384 28
  states_recv_fetches_range b (Rust.withPanics ext) 12612 348
  states_recv_fetches_range b (Rust.withPanics ext) 17660 124
  states_recv_fetches_range b (Rust.withPanics ext) 17960 188
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hadrp hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (done_result_976_extract A ((s0.sp - 4240#64) + 976#64) nhr sec)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g p v_sec w_pad
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let w_out := mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At, mkWords63_done, noneCap]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨p.b4.w5, p.b2.w8, w_out.b3.w2, w_out.b3.w0, sp.b0.w4, p.b3.w4, sp.b0.w6,
             p.b3.w1, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, p.b4.w8, p.b3.w2, w_out.b3.w7, p.b4.w6, p.b3.w0, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨p.b4.w0, p.b4.w4, w_out.b5.w0, p.b3.w6, w_out.b4.w6, w_out.b0.w2, w_out.b4.w9,
             7#64, w_out.b5.w8, w_out.b4.w3⟩
      b3 := ⟨sp.b3.w0, sp.b3.w1, w_out.b1.w9, w_out.b2.w2, w_out.b2.w8, w_out.b0.w8,
             w_out.b1.w4, w_out.b2.w6, w_out.b3.w1, w_out.b2.w9⟩
      b4 := ⟨w_out.b2.w7, w_out.b1.w3, w_out.b2.w0, w_out.b1.w1, w_out.b2.w3, w_out.b0.w6,
             w_out.b0.w5, w_out.b1.w2, w_out.b2.w1, w_out.b2.w4⟩
      b5 := ⟨w_out.b1.w0, w_out.b4.w5, w_out.b1.w5, w_out.b0.w9, w_out.b1.w8, w_out.b5.w1,
             w_out.b0.w4, w_out.b2.w5, w_out.b4.w7, w_out.b5.w5⟩
      w60 := w_out.b5.w7
      w61 := w_out.b0.w3
      w62 := w_out.b0.w7
      q200 := w_out.q60
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 w_out.q60
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
       ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w_out.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono
      (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1, w_out, mkWords63_done, noneCap]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec)) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_noHeaderReceived_some_entails_resultV1RecvAt A (F := F) outA nhr sec g p v_sec
      p.b2.w5 sp.b3.w0 w_out.b5.w9 sp.q3c0 sp.b3.w1
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, w_out, mkWords63_done, mkWords63_nhr_tail,
      Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm]
    ac_rfl

/-! ## 4. `eq_ct2` Arm and Complete `.ekSentCt1Received` Arm -/

theorem Relocatable.of_chunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedEkSentCt1ReceivedAt A a st) := by
  intro a
  refine Entails.trans (chunkedEkSentCt1ReceivedAt_extract63 A a st) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; intro _
  rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right (wordsBytes (words63List w)) ?_
  exact Entails.pure_right (by rw [length_wordsBytes, length_words63List]) (Entails.refl _)

/-- Stack-parameterized framed call rule for `recvCt2ChunkSpecWithStack stk K F A b` (`0x5ec2c`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_stk {stk : Nat} {A : RustAlloc} {F : ShaCompress}
    {K : MlKem} {b : BitVec 64} {prog : Program} {entry ret_pc : BitVec 64} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64) (hcall : subroutine_ok prog entry
      { recvCt2ChunkSpecWithStack stk K F A b with
        pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpecWithStack stk K F A b).pre x s })
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2) (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post Q_panic : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗ ekSentCt1ReceivedAt A stA st ∗
      chunkAt chunkA chunk ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame)
    (hpanic : ∀ sf P_f, ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 → SepWP prog (s0.readReg64 Reg.lr) sf
        ((ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => P_inv sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun; intro hinv_s
  refine SepWPp.call hcall (x := ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [recvCt2ChunkSpecWithStack]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨hinv_s, ⟨hb, hx0, hx1, hx2, hx3, hsort, hroot⟩, hm⟩
  · dsimp only [recvCt2ChunkSpecWithStack] at hmem; refine allowPanic_frame (fun ⟨hdisj, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hdisj ⊢; rw [htrace.1] at hdisj htr_sub; exact ⟨hdisj, htr_sub⟩
  · dsimp only [recvCt2ChunkSpecWithStack]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => SepWPp.of_sepWP_ret ?_
    have hassoc : (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
        memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame =
      (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
        (memRegion stA chunkedEkSentCt1ReceivedSize ∗ (chunkAt chunkA chunk ∗
          (tokenInitAt b ∗ (reduceTableAt b ∗ (A.pool ∗ stackAt sp_call stk)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Framed call rule for `recvCt2ChunkSpec K F A b` (`0x5ec2c`), parameterized by `P_inv`. -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_gen {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {prog : Program} {entry ret_pc : BitVec 64} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry
      { recvCt2ChunkSpec K F A b with pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpec K F A b).pre x s })
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2) (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post Q_panic : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A stA st ∗ chunkAt chunkA chunk ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm => P_inv sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) :=
  call_ekSentCt1ReceivedRecvCt2Chunk_stk (stk := recvCt2ChunkStackX) hb hcall outA stA chunkA
    st chunk hsort hroot hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit hpanic hnext

theorem subroutine_ok_pure_true {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry { spec with pre := fun x s => ⌜True⌝ ∗ spec.pre x s } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

set_option maxHeartbeats 1600000 in
/-- Stack-parameterized `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct2 chunk`. -/
theorem ekSentCt1Received_arm_eq_ct2_stk {stk : Nat} {P_extra : SepProp}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName)
      { recvCt2ChunkSpecWithStack stk K F A b with
        pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpecWithStack stk K F A b).pre x s })
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hsplit_stk : stackAt (s0.sp - 4240#64) stk = P_extra ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ (P_rest ∗ P_extra) ∗ resultV1RecvAt A (F := F) outA (States.recv K (.ekSentCt1Received st) msg) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f, ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
          allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) stk ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm =>
        P_inv sm → SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        (bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hpost_err := @ekSentCt1Received_post_call_err_56574 A F b ext s0
  have hpost_still := @ekSentCt1Received_post_call_still_56574 A F b ext hmemcpy s0
  have hpost_done := @ekSentCt1Received_post_call_done_56574 A F b ext hb hmemcpy s0
  rw [fnAddr_fwd_recvCt2Chunk] at hcall ⊢
  states_recv_fetches_range b (Rust.withPanics ext) 228 292
  states_recv_fetches_range b (Rust.withPanics ext) 4336 48
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw hcall hpost_err hpost_still hpost_done hdone ⊢
  rcases hinv with ⟨hsort, hroot⟩
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12, heq, hpay, messagePayloadAt_ct2 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 120
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9, w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7, sp.b2.w8, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, sp.b3.w8, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_pre_memcpy :
      (words63At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        (memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
        (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗ memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (recompose63 (selfA + 8#64) w)
      (sepConj_mono
        (Entails.of_eq (memRegion_880_split_504_376_ct2 ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
        (sepConj_mono_left
          (Entails.of_eq (memRegion_880_split_504_376_ct2 ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)))))
  refine SepWP.fold
    (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 512#64) 416 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) stk ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
    hfold_pre_memcpy ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12, heq]; simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]; ac_rfl
  · refine call_memcpy_relocate_cs (ret_pc := entry + 4364#64)
      hmemcpy_raw (Relocatable.of_chunkedEkSentCt1ReceivedAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64) rfl hrun hsp hfsp_align rfl htr
      (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hx1])
      (by simp only [Reg.x2, arm64_norm]) (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
    have hx24_1 : sf1.readReg64 .x24 = msgA := hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, arm64_norm, hx24])
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch := hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, arm64_norm])
    have hfold_self :
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 1856#64) st ∗
        ((selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416) ⊢
          (ekSentCt1ReceivedUcAt A ((s0.sp - 4240#64) + 1856#64) st.uc ∗
           polyDecoderAt A ((s0.sp - 4240#64) + 1960#64) st.receiving_ct2) ∗
          memRegion selfA chunkedStatesSize := by
      unfold chunkedEkSentCt1ReceivedAt unchunkedEkSentCt1ReceivedAt
      rw [show ((s0.sp - 4240#64) + 1856#64) + 104#64 = (s0.sp - 4240#64) + 1960#64 by bv_omega]
      exact sepConj_mono_right (self_504_416_entails_memRegion_928 selfA 6#64)
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
    wp_steps 10
    subst hsp0
    refine call_ekSentCt1ReceivedRecvCt2Chunk_stk (stk := stk) hb hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64) st chunk hsort hroot
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := entry + 4384#64) (R := R)
      (Frame := P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ statesRecvSavedCells s0)
      rfl hrun1 hsp1 hfsp_align (by simp only [Reg.lr, arm64_norm]) htr1
      (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm, hx25_1]) (by simp only [Reg.x3, arm64_norm, hx24_1])
      (by dsimp only [chunkedEkSentCt1ReceivedSize, ekSentCt1ReceivedAt, BitVec.ofNat_eq_ofNat]; simp only [arm64_norm]; ac_rfl)
      hpanic ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct2 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA := hcs2.1.trans (by simp only [Reg.x19, arm64_norm, hx19_1])
    cases hres : st.recv_ct2_chunk K st.uc.epoch chunk with
    | error err =>
      cases err with
      | panic p =>
        dsimp only [ekSentCt1ReceivedRecvChunkResultAt]; rw [sepConj_assoc]
        exact SepWP.pure_elim (fun hfalse => False.elim hfalse)
      | err e =>
        have he := recv_ct2_chunk_err_eq_macVerifyFailed st st.uc.epoch chunk e hres
        subst he
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_err K st msg chunk .macVerifyFailed heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_err sf2 outA sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]; simp only [arm64_norm]; ac_rfl
    | ok outRes =>
      cases outRes with
      | stillReceiving outSt =>
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_still K st msg chunk outSt heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_still sf2 outA outSt sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]; simp only [arm64_norm]; ac_rfl
      | done pair =>
        rcases pair with ⟨nhr, sec⟩
        have hmodel := states_recv_ekSentCt1Received_eq_ct2_done K st msg chunk nhr sec heq hpay hres
        refine SepWP.weaken_pre (Entails.of_eq ?_)
          (SepWP.mono
            (hpost_done sf2 outA nhr sec sp1
              ((P_rest ∗ P_extra) ∗ memRegion selfA chunkedStatesSize ∗
               ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
               tokenInitAt b ∗ reduceTableAt b ∗ A.pool)
              hpc2 hrun2 hsp2 hsp_align hx19_2 htr2)
            (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              hdone sf Pf hpc_f hrun_f ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩))
        rw [← hmsg_eq, hsplit_stk]; dsimp only [chunkedEkSentCt1ReceivedSize]; simp only [arm64_norm]; ac_rfl

/-- `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct2 chunk`
    (`+228 -> s0.x30`, `0x55538..0x5565c -> 0x56544..0x56574 -> 0x56574..0x59ff0`). -/
theorem ekSentCt1Received_arm_eq_ct2
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName)
      { recvCt2ChunkSpec K F A b with pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpec K F A b).pre x s })
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (States.recv K (.ekSentCt1Received st) msg) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt b ∗ reduceTableAt b ∗
        A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm =>
        P_inv sm → SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) :=
  ekSentCt1Received_arm_eq_ct2_stk (stk := statesRecvCalleeStackX) (P_extra := emp)
    hb hcall hmemcpy s0 s outA selfA msgA st msg chunk P_rest R
    (emp_sepConj _).symm hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
    (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => by
      rw [sepConj_emp] at hPf; exact hdone sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩)
    hpanic

/-- Parameterized `.ekSentCt1Received` arm of `<States>::recv` (`+228 -> s0.x30`). -/
theorem states_recv_arm_ekSentCt1Received_gen
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName)
      { recvCt2ChunkSpec K F A b with pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpec K F A b).pre x s })
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hwrap : ∀ {mid P Q Q_panic},
      SepWP (tripleRatchetProgAtExt b ext) mid s P
        (fun sm Pm => P_inv sm → SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm Q Q_panic) →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P Q Q_panic)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K b (.ekSentCt1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K b (.ekSentCt1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
    rw [states_recv_ekSentCt1Received_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (ekSentCt1Received_arm_gt hdealloc s0 s outA selfA msgA st msg (statesRecvRoAt b)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
      rw [states_recv_ekSentCt1Received_lt K st msg hlt, hpre_comm]
      refine SepWP.mono
        (ekSentCt1Received_arm_lt hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
          hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct2 chunk =>
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt b ∗
                (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt b ∗ reduceTableAt b) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTableAt b ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by ac_rfl]
        refine hwrap
          (ekSentCt1Received_arm_eq_ct2 (K := K) hb hcall hmemcpy s0 s outA selfA msgA st msg chunk
            (statesRecvJumpTableAt b ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
            hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]; ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpec, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          refine ⟨⟨?_, hpan'.1.2⟩, hpan'.2⟩
          cases hpan'.1.1 with
          | inl hp => exact Or.inl (states_recv_ekSentCt1Received_eq_ct2_panic K st msg chunk heq hpay hp)
          | inr haf => exact Or.inr haf
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1 _ | ct1Ack _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
        rw [states_recv_ekSentCt1Received_eq_other K st msg heq hct2, hpre_comm]
        refine SepWP.mono
          (ekSentCt1Received_arm_eq_other hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
            heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-- Complete `.ekSentCt1Received` arm of `<States>::recv` (`+228 -> s0.x30`, `0x55538 -> 0x59ff0`). -/
theorem states_recv_arm_ekSentCt1Received
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName) (recvCt2ChunkSpec K F A b))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hinv : statesRecvPreInv (.ekSentCt1Received st))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K b (.ekSentCt1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K b (.ekSentCt1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) :=
  states_recv_arm_ekSentCt1Received_gen hb hdealloc (subroutine_ok_pure_true hcall) hmemcpy
    s0 s outA selfA msgA st msg R
    (fun hwp => SepWPp.of_sepWP (SepWP.mono hwp fun _ _ _ _ h => h trivial))
    hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- Complete `.ekSentCt1Received` arm of `<States>::recv` under `ImgCallInv img` (`RecvCt2ChunkOkX`). -/
theorem states_recv_arm_ekSentCt1Received_inImage
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt img.base A ext)
    (hcall : RecvCt2ChunkOkX img K F A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hinv : statesRecvPreInv (.ekSentCt1Received st)) (himg_s : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K img.base (.ekSentCt1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K img.base (.ekSentCt1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) :=
  states_recv_arm_ekSentCt1Received_gen hb hdealloc hcall hmemcpy
    s0 s outA selfA msgA st msg R (fun hwp => SepWPp.of_sepWP_inImage himg_s hwp)
    hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr

theorem sepWPp_seq_clean_inImage_ct2 {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Q_panic : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  SepWPp.of_sepWP_inImage hinv (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQm⟩ hinv_sm =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hinv_sm hQm))

/-- Per-variant `.inImage img` specification proof for `States.ekSentCt1Received st` (`tag = 6#64`). -/
theorem states_recv_ekSentCt1Received_ok_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext) (hcall : RecvCt2ChunkOkX img K F A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base (.ekSentCt1Received st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ct2 himg0 hpro ?_
  intro s1 hpc1 hrun1 himg1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 6#64
    (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_ct2 himg1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 himg2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_ekSentCt1Received_inImage hb hdealloc hcall hmemcpy s0 s2 outA selfA msgA st msg R
      hinv himg2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1))

end CryptoVerification.SpqrV1.States.Recv
