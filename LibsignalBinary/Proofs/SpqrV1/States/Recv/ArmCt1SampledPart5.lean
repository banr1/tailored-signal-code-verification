/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 5 (`outMsg = some decoded`)

**Checked by Lean.** Verifies the `<Unchunked.SendCt.Ct1Sent>::recv_ek` call (`+11508 -> +11528`),
Path 5a (`recv_ek = .error`), `.ok uc_ek` staging (`+11528 -> +11620`), and Path 5b
(`recv_ek = .ok uc_ek, ack = false` → `States.ekReceivedCt1Sampled`).
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

/-! ## 1. Calling `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`+11508 -> +11528`, `0x58148..0x5815c`) -/

/-- Sets `x0 = fsp + 1856#64`, `x1 = fsp + 3696#64`, `x2 = x20` (`st.uc.epoch`),
    `x3 = fsp + 3832#64`, and calls `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`0x5dac0`,
    `+11508 -> +11528`). -/
theorem ct1Sampled_call_recv_ek
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K))
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11508#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗
        unchunkedCt1SentAt A (fsp + 3696#64) uc ∗
        vecU8 A (fsp + 3832#64) decoded ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3832#64) 24 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcall := unchunkedRecvEk_ok_at_statesRecv hrecv_ek
  have hsplit := stackAt_statesRecvCallee_eq_unchunkedRecvEk' s_in.sp
  states_recv_fetches_range b (Rust.withPanics ext) 11508 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hcall hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit, ← hx20]
  wp_steps
  wp_call hcall ⟨s_in.sp + 1856#64, s_in.sp + 3696#64, s_in.sp + 3832#64, uc, decoded, res⟩
  wp_done

/-! ## 2. Path 5a (`recv_ek = .error (.err err)`): `+11528 -> +15716 -> +19324` -/

theorem unchunkedCt1SentRecvEkResAt_error_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : Error) :
    unchunkedCt1SentRecvEkResAt A (F := F) a (.error err) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ bs7 : List (BitVec 8),
        ⌜bs7.length = 7 ∧ unpack64 w8 = 12#8 :: bs7⌝ ∗
        (a ↦₆₄ noneCap) ∗
        ((a + 8#64) ↦₆₄ w8) ∗
        ((a + 16#64) ↦₆₄ w16) ∗
        ((a + 24#64) ↦₆₄ w24) ∗
        memRegion (a + 32#64) 96 := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := a + 9#64) (n := 7) (k := 112)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 104)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 96)
        (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eq_exists_bytes (a + 9#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro bs7
  rw [sepConj_assoc, sepConj_left_comm ((a + 8#64) ↦₈ 12#8), sepConj_left_comm (a ↦₆₄ noneCap)]
  apply Entails.pure_left; intro hlen7
  have hlen8 : (12#8 :: bs7).length = 8 := by simp [hlen7]
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 hlen8
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right bs7 ?_)))
  refine Entails.pure_right ⟨hlen7, hw8.symm⟩ ?_
  have h8 : ((a + 8#64) ↦₈ 12#8) ∗ ((a + 9#64) ↦ₛ bs7) = ((a + 8#64) ↦₆₄ w8) := by
    rw [pointsTo64_eq_pointsToBytes (a + 8#64) w8, ← hw8,
        pointsToBytes_cons (a + 8#64) 12#8 bs7]
    have h9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
    rw [h9]
  rw [← sepConj_assoc ((a + 8#64) ↦₈ 12#8), h8]
  exact Entails.of_eq (by ac_rfl)

theorem err_words_entails_resultV1RecvAt_erroneous (A : RustAlloc) {F : ShaCompress}
    (outA w8 w16 w24 : BitVec 64) {bs7 : List (BitVec 8)}
    (hlen7 : bs7.length = 7) (hw8 : unpack64 w8 = 12#8 :: bs7) :
    (outA ↦₆₄ noneCap) ∗
      ((outA + 8#64) ↦₆₄ w8) ∗
      ((outA + 16#64) ↦₆₄ w16) ∗
      ((outA + 24#64) ↦₆₄ w24) ∗
      memRegion (outA + 32#64) 928 ⊢
    resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  have h8 : ((outA + 8#64) ↦₆₄ w8) ⊢ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes (outA + 8#64) w8, hw8,
        pointsToBytes_cons (outA + 8#64) 12#8 bs7]
    have h9 : outA + 8#64 + 1#64 = outA + 9#64 := by bv_omega
    rw [h9, ← hlen7]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion (outA + 9#64) bs7)
  have h16 : ((outA + 16#64) ↦₆₄ w16) ∗ ((outA + 24#64) ↦₆₄ w24) ∗ memRegion (outA + 32#64) 928 ⊢
      memRegion (outA + 16#64) 944 := by
    rw [ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
          (b' := outA + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
          (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have h9 : memRegion (outA + 9#64) 7 ∗ memRegion (outA + 16#64) 944 = memRegion (outA + 9#64) 951 :=
    (ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944)
      (b' := outA + 16#64) rfl (by bv_omega) (by decide)).symm
  rw [← h9, ← sepConj_assoc ((outA + 8#64) ↦₈ 12#8)]
  exact sepConj_mono_right (sepConj_mono h8 h16)

/-- On `Err(Error::ErroneousDataReceived)` from `<Ct1Sent>::recv_ek` (`+11528 -> +15716 -> +19324`),
    drops `stA + 8` (`[Poly; 16]`) and `fsp + 2752` (`[SortedSet<Pt>; 16]`), writes
    `Err(Error::ErroneousDataReceived)` to `outA` (`x19`), and jumps to `+19324` (`0x59fd0`). -/
theorem ct1Sampled_recv_ek_err_to_19324
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp stA outA : BitVec 64)
    (vecs : List (List GF16)) (hvecs_len : vecs.length = NUM_POLYS)
    (dec' : PolyDecoder) (err : Error)
    (Rest : SepProp)
    (herr : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s_in
      (unchunkedCt1SentRecvEkResAt A (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
          memRegion (fsp + 1856#64) 128 ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 8#64) 384 ∗
          memRegion (fsp + 2752#64) 400 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx19 herr
  have hout_split :
      memRegion (s_in.readReg64 .x19) v1RecvSize ⊢
        ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 := by
    unfold v1RecvSize
    rw [ProofLib.memRegion_split (s_in.readReg64 .x19) 32 928 (by decide)]
    refine Entails.trans (sepConj_mono_left (memRegion_32_entails_words4 (s_in.readReg64 .x19))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro v24
    apply Entails.sepExists_elim; intro v16
    apply Entails.sepExists_elim; intro v8
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v8
      (Entails.sepExists_right v16 (Entails.sepExists_right v24 (Entails.refl _))))
  have hdec_entails :
      polyDecoderAt A (s_in.sp + 2752#64) dec' ⊢
        ∃∗ vecs_dec : List (List Pt),
          ⌜vecs_dec.length = NUM_POLYS⌝ ∗
          vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 := by
    have h3136 : (s_in.sp + 2752#64) + 384#64 = s_in.sp + 3136#64 := by bv_omega
    have h := polyDecoderAt_entails_vecs_tail A (s_in.sp + 2752#64) dec'
    rwa [h3136] at h
  have hpre :
      unchunkedCt1SentRecvEkResAt A (F := F) (s_in.sp + 1856#64) (.error .erroneousDataReceived) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        polyDecoderAt A (s_in.sp + 2752#64) dec' ∗
        memRegion (s_in.readReg64 .x19) v1RecvSize ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ bs7 : List (BitVec 8),
      ∃∗ vecs_dec : List (List Pt),
      ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
        ⌜bs7.length = 7 ∧ unpack64 w8 = 12#8 :: bs7⌝ ∗
        ⌜vecs_dec.length = NUM_POLYS⌝ ∗
        (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ∗
          ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          vecGF16ListOf A (stA + 8#64) vecs ∗
          vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 ∗
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
          A.pool ∗
          stackAt s_in.sp statesRecvCalleeStackX ∗
          Rest) := by
    refine Entails.trans (sepConj_mono (unchunkedCt1SentRecvEkResAt_error_entails A (s_in.sp + 1856#64) .erroneousDataReceived)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hdec_entails (sepConj_mono_left hout_split))))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w16
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w24
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro bs7
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vecs_dec
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v8
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v16
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v24
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24
      (Entails.sepExists_right bs7 (Entails.sepExists_right vecs_dec
        (Entails.sepExists_right v0 (Entails.sepExists_right v8
          (Entails.sepExists_right v16 (Entails.sepExists_right v24 ?_))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro bs7
  apply ProofLib.SepWP.exists_left; intro vecs_dec
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v24
  wp_focus_pure; intro ⟨hlen7, hw8⟩
  wp_focus_pure; intro hvecs_dec_len
  have hdrop_poly := dropPoly16_ok_at_statesRecv hdealloc
  have hdrop_ss := dropSortedSetPt16_ok_at_statesRecv hdealloc
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        (((s_in.readReg64 .x19) ↦₆₄ noneCap) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ w8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ w16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ w24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928) ∗
        (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        A.pool ∗
        (memRegion (s_in.sp - 19552#64) 15424 ∗ stackAt s_in.sp dropGluePoly16Stack) ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 11528 24
    states_recv_fetches_range b (Rust.withPanics ext) 15716 44
    dsimp only [tripleRatchetProgAtExt, statesRecvName, polyArrayBytes,
      noneCap, BitVec.ofNat_eq_ofNat] at hpc hdrop_poly hdrop_ss hsplit ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    rw [hsplit]
    wp_steps
    wp_call hdrop_poly ⟨stA + 8#64, vecs⟩
    wp_steps
    wp_call hdrop_ss ⟨s_in.sp + 2752#64, vecs_dec⟩
    wp_steps
    wp_done
  · rw [← hsplit]
    have herr_out := err_words_entails_resultV1RecvAt_erroneous A (F := F)
      (s_in.readReg64 .x19) w8 w16 w24 hlen7 hw8
    have h1856_mr :
        ((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ⊢
        memRegion (s_in.sp + 1856#64) 128 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 1856#64) (n := 8) (k := 120)
            (b' := s_in.sp + 1864#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1864#64) (n := 8) (k := 112)
            (b' := s_in.sp + 1872#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1872#64) (n := 8) (k := 104)
            (b' := s_in.sp + 1880#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1880#64) (n := 8) (k := 96)
            (b' := s_in.sp + 1888#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono herr_out (sepConj_mono h1856_mr
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr))))

/-! ## 3. `recv_ek = .ok uc_ek` Staging (`+11528 -> +11620`, `0x5815c..0x581b8`) -/

theorem vecU8_extract_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ _)]
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hlt ?_)
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
  rw [sepConj_left_comm (dst ↦ₛ _)]
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

def fiveVecToWords16 (g : FiveVecWords) (ep : BitVec 64) : Words16 :=
  ⟨g.v1.w0, g.v1.w1, g.v1.w2,
   g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
   g.rest.rest.v1.w0, g.rest.rest.v1.w1, g.rest.rest.v1.w2,
   g.rest.rest.auth.v1.w0, g.rest.rest.auth.v1.w1, g.rest.rest.auth.v1.w2,
   g.rest.rest.auth.v2.w0, g.rest.rest.auth.v2.w1, g.rest.rest.auth.v2.w2,
   ep⟩

@[simp]
theorem fiveVecToWords16_toList (g : FiveVecWords) (ep : BitVec 64) :
    (fiveVecToWords16 g ep).toList = fiveVecWordsList g ep := rfl

theorem unchunkedCt1SentEkReceivedAt_extract_words16 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ c : Words16,
        ⌜c.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a c.toList ∗
        relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst st) (wordsBytes c.toList) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.es⟩, st.ek, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentEkReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.es) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ek ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.es ∗
        vecU8 A (dst + 72#64) st.ek ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_lt A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.sepExists_right (fiveVecToWords16 ⟨v1, rest⟩ st.epoch) ?_
  refine Entails.pure_right hlt ?_
  rw [fiveVecToWords16_toList]
  exact wordsExtract_sepConj rfl heq

/-- On `Ok(uc_ek)` from `<Ct1Sent>::recv_ek` (`+11528 -> +11620`, `0x5815c -> 0x581b8`),
    copies `c_ek : Words16` from `fsp + 1856` to `fsp + 3856..3984`, stores `c_ek.w1` to
    `fsp + 176`, and loads `x8, x25, x9, x10`. -/
theorem ct1Sampled_recv_ek_ok_copy
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (fsp vb0 : BitVec 64)
    (c_ek : Words16)
    (Rest : SepProp)
    (hcap : c_ek.w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗
        memRegion (fsp + 3856#64) 128 ∗
        ((fsp + 176#64) ↦₆₄ vb0) ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt (fsp + 1856#64) c_ek.toList ∗
          wordsAt (fsp + 3856#64) c_ek.toList ∗
          ((fsp + 176#64) ↦₆₄ c_ek.w1) ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = c_ek.w0 ∧
        sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcmn := cap_add_one_beq_zero_false hcap
  have hpre :
      wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        memRegion (s_in.sp + 3856#64) 128 ∗
        ((s_in.sp + 176#64) ↦₆₄ vb0) ∗
        Rest ⊢
      ∃∗ c_dst : Words16,
        wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        wordsAt (s_in.sp + 3856#64) c_dst.toList ∗
        ((s_in.sp + 176#64) ↦₆₄ vb0) ∗
        Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (memRegion_128_entails_words16 (s_in.sp + 3856#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c_dst
    exact Entails.sepExists_right c_dst (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  states_recv_fetches_range b (Rust.withPanics ext) 11528 92
  dsimp only [tripleRatchetProgAtExt, statesRecvName, Words16.toList, BitVec.ofNat_eq_ofNat]
    at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_done

/-- Branches on `tbz w22, #0` to `+15760` (`0x591e4`) when `x22 = 0#64` (`ack = false`,
    `+11620 -> +15760`). -/
theorem ct1Sampled_ok_branch_no_ack
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 15760#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧
        sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  states_recv_fetches_range b (Rust.withPanics ext) 11620 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Falls through `tbz w22, #0` to `+11624` (`0x581bc`) when `x22 = 1#64` (`ack = true`,
    `+11620 -> +11624`). -/
theorem ct1Sampled_ok_branch_ack
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11624#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧
        sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  states_recv_fetches_range b (Rust.withPanics ext) 11620 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 4. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`): `+15760 -> +18996` -/

def mkSplit928EkReceivedCt1Sampled (c_enc : Words50) (c_ek : Words16)
    (bs352 : List (BitVec 8)) (tail5 : Words5) : Split928 where
  c0 := {
    w0 := 10#64
    w1 := c_enc.c0.w0
    w2 := c_enc.c0.w1
    w3 := c_enc.c0.w2
    w4 := c_enc.c0.w3
    w5 := c_enc.c0.w4
    w6 := c_enc.c0.w5
    w7 := c_enc.c0.w6
    w8 := c_enc.c0.w7
    w9 := c_enc.c0.w8
    w10 := c_enc.c0.w9
    w11 := c_enc.c0.w10
    w12 := c_enc.c0.w11
    w13 := c_enc.c0.w12
    w14 := c_enc.c0.w13
    w15 := c_enc.c0.w14
  }
  c1 := {
    w0 := c_enc.c0.w15
    w1 := c_enc.c1.w0
    w2 := c_enc.c1.w1
    w3 := c_enc.c1.w2
    w4 := c_enc.c1.w3
    w5 := c_enc.c1.w4
    w6 := c_enc.c1.w5
    w7 := c_enc.c1.w6
    w8 := c_enc.c1.w7
    w9 := c_enc.c1.w8
    w10 := c_enc.c1.w9
    w11 := c_enc.c1.w10
    w12 := c_enc.c1.w11
    w13 := c_enc.c1.w12
    w14 := c_enc.c1.w13
    w15 := c_enc.c1.w14
  }
  c2 := {
    w0 := c_enc.c1.w15
    w1 := c_enc.c2.w0
    w2 := c_enc.c2.w1
    w3 := c_enc.c2.w2
    w4 := c_enc.c2.w3
    w5 := c_enc.c2.w4
    w6 := c_enc.c2.w5
    w7 := c_enc.c2.w6
    w8 := c_enc.c2.w7
    w9 := c_enc.c2.w8
    w10 := c_enc.c2.w9
    w11 := c_enc.c2.w10
    w12 := c_enc.c2.w11
    w13 := c_enc.c2.w12
    w14 := c_enc.c2.w13
    w15 := c_enc.c2.w14
  }
  c3 := {
    w0 := c_enc.c2.w15
    w1 := c_enc.w48
    w2 := c_enc.w49
    w3 := c_ek.w0
    w4 := c_ek.w1
    w5 := c_ek.w2
    w6 := c_ek.w3
    w7 := c_ek.w4
    w8 := c_ek.w5
    w9 := c_ek.w6
    w10 := c_ek.w7
    w11 := c_ek.w8
    w12 := c_ek.w9
    w13 := c_ek.w10
    w14 := c_ek.w11
    w15 := c_ek.w12
  }
  mid := mid376Bytes c_ek.w13 c_ek.w14 c_ek.w15 bs352
  tail := tail5

theorem mkSplit928EkReceivedCt1Sampled_mid_length (c_enc : Words50) (c_ek : Words16)
    {bs352 : List (BitVec 8)} (tail5 : Words5) (h : bs352.length = 352) :
    (mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352 tail5).mid.length = 376 :=
  mid376Bytes_length c_ek.w13 c_ek.w14 c_ek.w15 h

set_option maxHeartbeats 1600000 in
/-- Part 1 of Path 5b (`+15760 -> +16596`, `0x591e4..0x59388`):
    loads `c_enc` (`st.sending_ct1` at `stA`) and `c_ek` (`uc_ek` at `fsp + 3856`) into the stack
    staging slots, calls `drop_glue::<[SortedSet<Pt>; 16]>(fsp + 2752)` to drop `dec'`, sets
    `x23 = 3#64`, and branches to `+16596` (`0x59528`). -/
theorem ct1Sampled_copy_some_no_ack_part1
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp stA : BitVec 64)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_mid : List (BitVec 8)) (tail5_mid : Words5)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 15760#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = c_ek.w0)
    (hx9 : s_in.readReg64 .x9 = c_ek.w2)
    (hx10 : s_in.readReg64 .x10 = c_ek.w3)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_mid tail5_mid
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64) s_in
      (words50At stA c_enc ∗
        wordsAt (fsp + 3856#64) c_ek.toList ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗
        memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗
        ((fsp + 4112#64) ↦₆₄ v4112) ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          words50At stA c_enc ∗
          memRegion (fsp + 3856#64) 128 ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((fsp + 976#64) ↦₆₄ c_ek.w13) ∗
          ((fsp + 984#64) ↦₆₄ c_ek.w14) ∗
          ((fsp + 992#64) ↦₆₄ c_ek.w15) ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          memRegion (fsp + 4096#64) 24 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 3#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hdrop := dropSortedSetPt16_ok_at_statesRecv hdealloc
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        words50At stA c_enc ∗
        wordsAt (s_in.sp + 3856#64) c_ek.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_ek.w13) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_ek.w14) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_ek.w15) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_ek.w11) ∗
        (((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15)) ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 3#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 15760 424
    dsimp only [tripleRatchetProgAtExt, statesRecvName, polyArrayBytes, BitVec.ofNat_eq_ofNat]
      at hpc hdrop hsplit ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    rw [hsplit]
    dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd,
      hx8, hx9, hx10, hx21, hx23, hx29]
    wp_steps
    wp_call hdrop ⟨s_in.sp + 2752#64, vecs_dec⟩
    wp_steps
    wp_done
  · have h3856_mr := wordsAt_entails_memRegion c_ek.toList (s_in.sp + 3856#64) 128 rfl
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    have h4096_mr :
        ((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15) ⊢
        memRegion (s_in.sp + 4096#64) 24 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 4096#64) (n := 8) (k := 16)
            (b' := s_in.sp + 4104#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 4104#64) (n := 8) (k := 8)
            (b' := s_in.sp + 4112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono h3856_mr (sepConj_mono_right (sepConj_mono h2752_mr
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left h4096_mr)))))))))))

theorem fnAddr_adrp_59648 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 16884#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

/-- Part 2a of Path 5b (`+16596 -> +16800`, `0x59528..0x59568`):
    copies `376`B from `fsp + 976` to `fsp + 3272` (`x28`), copies `fsp + 1352..1392` to `fsp + 3232..3272`,
    and branches on `x23 = 3#64` (`x8 = 2#64 > 1`) to `+16800` (`0x595f4`). -/
theorem ct1Sampled_copy_some_no_ack_part2a
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 3#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = 2#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976]
  states_recv_fetches_range b (Rust.withPanics ext) 16596 64
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  wp_steps
  wp_call hmemcpy_raw ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976⟩
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
/-- Part 2b of Path 5b (`+16800 -> +17024 -> +18996`, `0x595f4..0x59658` and `0x596d4..0x59778`):
    checks `x8 = 2#64`, checks `MAX_LOG_LEVEL_FILTER` (`0 <= 2`), writes `c_ek.w13, c_ek.w14, c_ek.w15`
    to `fsp + 576..600`, writes `we0 = 10#64` and `we8 = noneCap`, loads registers from `copyScratchStackAt`,
    and jumps to `+18996`. -/
theorem ct1Sampled_copy_some_no_ack_part2b
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_976 bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v576 v584 v592 vf10 vf18 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16800#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = 2#64)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_576 k.tail
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
        mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗
        ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoAt b ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3864#64) ↦₆₄ c_ek.w11) ∗
          statesRecvRoAt b ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  have hadrp := fnAddr_adrp_59648 (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 16800 104
  states_recv_fetches_range b (Rust.withPanics ext) 17024 168
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt, unchunkedSendCt2RoAt,
    logOff, BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes c_ek.w13 c_ek.w14 c_ek.w15 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_576]
  dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8, hx28]
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.Recv
