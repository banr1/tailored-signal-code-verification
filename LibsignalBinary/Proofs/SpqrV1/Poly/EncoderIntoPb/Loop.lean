/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder>::into_pb`: Inner Loops and OOM Helpers

Pure `GF16` big-endian serialization bridges, inner serialization loops (`polys_inner_loop` and
`points_inner_loop`), outer-iteration finish blocks, and OOM panic helpers for
`<spqr::encoding::polynomial::PolyEncoder>::into_pb` (`0x6285c..0x62b1c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Fetch Helper Macro -/

gen_decodes libsignalSessionCode_tree spqrEncoderIntoPbBin
  [0x5d464 → 0x5d724]

@[simp, arm64_norm] theorem encoderIntoPb_fnOff :
    libsignalSessionCode.fnOff encoderIntoPbName = 0x5d464 :=
  libsignalSessionCode_fnOff_0x5d464

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside `0x6285c`. -/
macro "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrEncoderIntoPbBin $b $H libsignalSessionCode_fnOff_0x5d464 0x5d464 $k0 $len)

/-! ## Inner Serialization Loops -/

/-- Inner serialization loop for the `.polys` branch (`0x6294c..0x62978`, `+240 -> +336`). -/
theorem polys_inner_loop {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 240#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 .x28 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 336#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 120#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 240 48
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine DropGlueFacts.seq_clean (mid := entry + 272#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x27 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x28 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      rw [off_add_two done]
      refine DropGlueFacts.align_pre ?_ ?_
      · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
        dsimp only [gf16At]
        ac_rfl
      · wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx27_1, hx28_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx27_1 ⊢
        wp_steps
        have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
          simp [serializeGF16List]
        rw [hser1]
        wp_done
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := entry + 240#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x27 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x28 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x26 = s0.readReg64 .x26 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · nth_rw 1 [arrayAt_cons]
          dsimp only [gf16At]
          wp_steps
          rw [ofNat_succ_sub_one (g2 :: rem'').length]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx27_2, hx28_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx27_2 hx28_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 htrace2 hvregs2 hpc2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
              (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
            arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
          have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
            rw [serializeGF16List_cons]
            exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
              (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
              (by simp [length_u16ToBeBytes]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

/-- Inner serialization loop for the `.points` branch (`0x62a54..0x62a80`, `+504 -> +588`). -/
theorem points_inner_loop {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 588#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 72#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 504 48
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine DropGlueFacts.seq_clean (mid := entry + 536#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      rw [off_add_two done]
      refine DropGlueFacts.align_pre ?_ ?_
      · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
        dsimp only [gf16At]
        ac_rfl
      · wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx26_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx26_1 ⊢
        wp_steps
        have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
          simp [serializeGF16List]
        rw [hser1]
        wp_done
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := entry + 504#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x26 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x21 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · nth_rw 1 [arrayAt_cons]
          dsimp only [gf16At]
          wp_steps
          rw [ofNat_succ_sub_one (g2 :: rem'').length]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx26_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx28_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx26_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2 htrace2 hvregs2 hpc2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
              (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
            arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
          have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
            rw [serializeGF16List_cons]
            exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
              (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
              (by simp [length_u16ToBeBytes]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

/-! ## OOM Panic Helpers -/

/-- Common `onPanic` postcondition for `encoderIntoPbSpec` and `encoderIntoPbSpecX`. -/
abbrev intoPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- OOM panic block at `+0x2a8` (`+680..+688`: `mov w0, #1; mov x1, x21; bl handle_error`). -/
theorem into_pb_panic_680 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 680#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encoderIntoPbName)
    (k := ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb" "alloc::raw_vec::handle_error")
  into_pb_fetches_range b (Rust.withPanics ext) 680 12
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + BitVec.ofNat 64 (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-- OOM panic block at `+0x2b4` (`+692..+700`: `mov w0, #8; mov w1, #0x180; bl handle_error`). -/
theorem into_pb_panic_692 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 692#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encoderIntoPbName)
    (k := ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb" "alloc::raw_vec::handle_error")
  into_pb_fetches_range b (Rust.withPanics ext) 692 12
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + BitVec.ofNat 64 (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## Outer Loop Finish-Iteration Blocks -/

/-- Finish one iteration of the `.polys` outer loop (`+352 -> +144 -> +188 / +616`). -/
theorem polys_outer_finish_iter {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c s80 s88 s96 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = fsp)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = 1#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 j)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if j + 1 = 16 then
        (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 616#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 188#64)
      s
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 80#64) ↦₆₄ s80) ∗
        ((fsp + 88#64) ↦₆₄ s88) ∗
        ((fsp + 96#64) ↦₆₄ s96) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x24 = fsp ∧
        sm.readReg64 .x25 = 24#64 ∧
        sm.readReg64 .x26 = 1#64 ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (j + 1) ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 352 28
  into_pb_fetches_range b (Rust.withPanics ext) 144 44
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_polys j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_polys + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 80#64) ↦₆₄ cap_c) ∗
        ((fsp + 88#64) ↦₆₄ ptr_c) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_polys + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 80#64) ↦₆₄ cap_c) ∗
        ((fsp + 88#64) ↦₆₄ ptr_c) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    have hgroup :
        (((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs ∗
          ((ptr_polys + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        ((((ptr_polys + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs) ∗
          (((fsp + 24#64) ↦₆₄ 16#64) ∗
            ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 80#64) ↦₆₄ cap_c) ∗
            ((fsp + 88#64) ↦₆₄ ptr_c) ∗
            ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((fsp + 104#64) ↦₆₄ cap_c) ∗
            ((fsp + 112#64) ↦₆₄ ptr_c) ∗
            ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    have hgroup2 :
        (((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        (vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
          (((fsp + 24#64) ↦₆₄ 16#64) ∗
            ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 80#64) ↦₆₄ cap_c) ∗
            ((fsp + 88#64) ↦₆₄ ptr_c) ∗
            ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((fsp + 104#64) ↦₆₄ cap_c) ∗
            ((fsp + 112#64) ↦₆₄ ptr_c) ∗
            ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    rw [hgroup, hgroup2]
    exact sepConj_mono_left hslot
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

/-- Finish one iteration of the `.points` outer loop (`+588 -> +408 -> +452 / +616`). -/
theorem points_outer_finish_iter {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_points : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if j + 1 = 16 then
        (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 616#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + 452#64)
      s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = 1#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 588 28
  into_pb_fetches_range b (Rust.withPanics ext) 408 44
  dsimp only [tripleRatchetProgAtExt, encoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::into_pb" = entry
  examples_hide_fetches
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_points j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_points + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_points + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    have hgroup :
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs ∗
          ((ptr_points + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_points + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_points + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        ((((ptr_points + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_points + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_points + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs) ∗
          ((fsp ↦₆₄ 16#64) ∗
            ((fsp + 8#64) ↦₆₄ ptr_points) ∗
            ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 56#64) ↦₆₄ cap_c) ∗
            ((fsp + 64#64) ↦₆₄ ptr_c) ∗
            ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    have hgroup2 :
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        (vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
          ((fsp ↦₆₄ 16#64) ∗
            ((fsp + 8#64) ↦₆₄ ptr_points) ∗
            ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 56#64) ↦₆₄ cap_c) ∗
            ((fsp + 64#64) ↦₆₄ ptr_c) ∗
            ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    rw [hgroup, hgroup2]
    exact sepConj_mono_left hslot
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `375`) -/

section Placed

variable [LibsignalPlacement]

theorem polys_inner_loop_placed {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 240#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 rem.length)
    (hx28 : s.readReg64 .x28 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 336#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 120#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine DropGlueFacts.seq_clean (mid := (blkPl_375).base + 272#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 120#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x27 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x28 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      rw [off_add_two done]
      refine DropGlueFacts.align_pre ?_ ?_
      · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
        dsimp only [gf16At]
        ac_rfl
      · wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx27_1, hx28_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx27_1 ⊢
        wp_steps
        have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
          simp [serializeGF16List]
        rw [hser1]
        wp_done
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := (blkPl_375).base + 240#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x27 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x28 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x26 = s0.readReg64 .x26 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · nth_rw 1 [arrayAt_cons]
          dsimp only [gf16At]
          wp_steps
          rw [ofNat_succ_sub_one (g2 :: rem'').length]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx27_2, hx28_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx27_2 hx28_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 htrace2 hvregs2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
              (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
            arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
          have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
            rw [serializeGF16List_cons]
            exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
              (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
              (by simp [length_u16ToBeBytes]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

theorem points_inner_loop_placed {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (total : Nat) (hmax : 2 * total < 2 ^ 63)
    (rem : List GF16) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * done))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 588#64)
      s
      (arrayAt gf16At 2 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * rem.length) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
        ((fsp + 72#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt gf16At 2 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List rem) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons g rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 2 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (2 * total) - BitVec.ofNat 64 (2 * done)) 1#64 = false :=
      rem_bytes_not_ule_one htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_two_cons dstPtr done rem'.length hrem_bound]
    dsimp only [gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v16
    refine DropGlueFacts.seq_clean (mid := (blkPl_375).base + 536#64)
      (P_mid :=
        arrayAt gf16At 2 srcCur (g :: rem') ∗
          ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * rem'.length) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
          ((fsp + 72#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x25 = s0.readReg64 .x25 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      rw [off_add_two done]
      refine DropGlueFacts.align_pre ?_ ?_
      · rw [pointsTo16_rev16_eq_u16ToBeBytes, arrayAt_cons]
        dsimp only [gf16At]
        ac_rfl
      · wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx26_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 2 * (done + 1) = 2 * total := by simp at htot'; omega
        rw [hdone_tot] at hx1_1
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx26_1 ⊢
        wp_steps
        have hser1 : serializeGF16List [g] = u16ToBeBytes g.value := by
          simp [serializeGF16List]
        rw [hser1]
        wp_done
      | cons g2 rem'' =>
        have hne' : g2 :: rem'' ≠ [] := List.cons_ne_nil g2 rem''
        have hpos' : 0 < (g2 :: rem'').length := by simp
        have hlt' : (g2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((g2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := (blkPl_375).base + 504#64)
          (P_mid :=
            arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * (g2 :: rem'').length) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * total)) ∗
              ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * (done + 1))) ∗
              ((srcCur ↦₁₆ g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (2 * (done + 1)) ∧
            sm.readReg64 .x26 = BitVec.ofNat 64 (g2 :: rem'').length ∧
            sm.readReg64 .x21 = srcCur + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x25 = s0.readReg64 .x25 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · nth_rw 1 [arrayAt_cons]
          dsimp only [gf16At]
          wp_steps
          rw [ofNat_succ_sub_one (g2 :: rem'').length]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx26_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx28_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 2#64)
            (BitVec.ofNat 64 (2 * (done + 1)))
            ((srcCur ↦₁₆ g.value) ∗
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx26_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2 htrace2 hvregs2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt gf16At 2 srcCur (g :: g2 :: rem'') =
              (srcCur ↦₁₆ g.value) ∗ arrayAt gf16At 2 (srcCur + 2#64) (g2 :: rem'') :=
            arrayAt_cons gf16At 2 srcCur g (g2 :: rem'')
          have hser : ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ serializeGF16List (g :: g2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (2 * done)) ↦ₛ u16ToBeBytes g.value) ∗
                ((dstPtr + BitVec.ofNat 64 (2 * (done + 1))) ↦ₛ serializeGF16List (g2 :: rem'')) := by
            rw [serializeGF16List_cons]
            exact pointsToBytes_append_off dstPtr (2 * done) (2 * (done + 1))
              (u16ToBeBytes g.value) (serializeGF16List (g2 :: rem''))
              (by simp [length_u16ToBeBytes]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

theorem into_pb_panic_680_placed {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_375).base + 680#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic :
      ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked := by
    rw [SpqrV1.Alloc.spqr_externAt?_of_mem, h_panic]
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem into_pb_panic_692_placed {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_375).base + 692#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic :
      ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked := by
    rw [SpqrV1.Alloc.spqr_externAt?_of_mem, h_panic]
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

end Placed

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb
