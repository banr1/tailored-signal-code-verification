/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: `.points` Branch and OOM Helpers

**Checked by Lean.**

Proves OOM panic blocks (`+1536`, `+1696`, `+1708`), 16-slot empty `Point` header initialization
(`+56..+260`), the inner `GF16` decoding loop (`+376..+440`), and the 16-slot `.points` outer loop
(`+260 → +1612 / +1648`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem bv_lit_add_lit (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add]; bv_omega

@[local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) + 18446744073709551615#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add]; bv_omega

theorem cells_456_eq (fsp : BitVec 64) :
    cells (fsp + 456#64) 3 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2,
        ((fsp + 456#64) ↦₆₄ v0) ∗ ((fsp + 464#64) ↦₆₄ v1) ∗ ((fsp + 472#64) ↦₆₄ v2) := by
  have h1 : fsp + 456#64 + 8#64 = fsp + 464#64 := by bv_omega
  have h2 : fsp + 464#64 + 8#64 = fsp + 472#64 := by bv_omega
  rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, ProofLib.cells_zero]
  simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]

/-! ## OOM Panic Helpers (`+1536`, `+1696`, `+1708` -> `handle_error`) -/

/-- OOM panic block at `+1536` (`0x62788`: `mov x0, x24; mov x1, x26; bl handle_error`). -/
theorem from_pb_panic_1536 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1536#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encoderFromPbName)
    (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1536 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [encoderFromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

/-- OOM panic block at `+1696` (`0x62828`: `mov w0, #2; mov w1, #2; bl handle_error`). -/
theorem from_pb_panic_1696 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1696#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encoderFromPbName)
    (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1696 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [encoderFromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

/-- OOM panic block at `+1708` (`0x62834`: `mov x0, x19; mov x1, x25; bl handle_error`). -/
theorem from_pb_panic_1708 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1708#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encoderFromPbName)
    (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1708 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [encoderFromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

/-! ## Empty `Point` Slot Initialization (`+56 -> +260`) -/

/-- Initializes 16 empty `Point` headers `(0, 2, 0)` at `fsp + 480 .. fsp + 864` (`+56 -> +260`, `0x38 -> 0x104`)
    and stores `out` (`x0`) at `[fsp + 56]`. -/
theorem pts_init_empty_headers {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ptsPtr v_out : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 260#64) s
      (memRegion (fsp + 480#64) 384 ∗
        ((fsp + 56#64) ↦₆₄ v_out) ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ emptySlotsAt (fsp + 480#64) 16 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗
          ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = pbA ∧
        sm.readReg64 .x21 = 2#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 0#64 ∧
        sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 56 204
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_cells (fsp + 480#64) 48 (by decide)]
  iterate 24 (apply sepWP_cells_succ; intro)
  iterate 24 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  refine align_pre ?_ ?_
  · simp only [emptySlotsAt, emptySlotAt, sepConj_emp, bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-! ## Inner `GF16` Decoding Loop (`+376 -> +440`, `0x178 -> 0x1b8`) -/

/-- Inner loop of `.points` (`+376 -> +440`, `0x178 -> 0x1b8`), decoding `n + 1` big-endian
    16-bit pairs from `bs` (`bs.length = 2 * (n + 1)`) at `bsPtr + 2 * k` into `outPtr + 2 * k`. -/
theorem pts_inner_loop {b : BitVec 64} {ext : String → Option (State → State)}
    (n : Nat) :
    ∀ (bs : List (BitVec 8)) (k totalBytes : Nat)
      (s : State) (fsp hdrAddr bsPtr outPtr v_len : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
      (Frame : SepProp),
      bs.length = 2 * (n + 1) →
      2 * k + bs.length = totalBytes →
      totalBytes < 2 ^ 62 →
      s.pc = (contractProg b ext).fnAddr encoderFromPbName + 376#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x8 = outPtr →
      s.readReg64 .x19 = BitVec.ofNat 64 totalBytes →
      s.readReg64 .x20 = hdrAddr →
      s.readReg64 .x22 = outPtr →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (k + 1) →
      SepWP (contractProg b ext)
        ((contractProg b ext).fnAddr encoderFromPbName + 440#64) s
        (((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
          ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 472#64) ↦₆₄ v_len) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * k)) bs.length ∗
          Frame)
        (fun sm Pm =>
          (Pm ⊢ ((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
            ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
            ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (k + n + 1)) ∗
            ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
            arrayAt gf16At 2 (outPtr + BitVec.ofNat 64 (2 * k)) (bytesToGF16ListTotal bs) ∗
            Frame) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x20 = hdrAddr ∧
          sm.readReg64 .x21 = s.readReg64 .x21 ∧
          sm.readReg64 .x22 = outPtr ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x26 = s.readReg64 .x26 ∧
          sm.readReg64 .x29 = s.readReg64 .x29 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  induction n with
  | zero =>
    intro bs k totalBytes s fsp hdrAddr bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx8 hx19 hx20 hx22 hx23 hx28
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · encoder_from_pb_fetches_range b (Rust.withPanics ext) 348 80
      dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
      examples_hide_fetches
      have htot' : 2 * k + 2 = totalBytes := by simpa using htot
      have hlt1 : 2 * k < totalBytes := by omega
      have hlt2 : 2 * k + 1 < totalBytes := by omega
      have hk_lt : k < totalBytes := by omega
      have hmax64 : totalBytes < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt2 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalBytes) = true :=
        bne_of_lt hk_lt hmax64
      have h_bne' : (BitVec.ofNat 64 totalBytes != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hmax64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalBytes) = false :=
        beq_false_of_lt hk_lt hmax64
      have h_beq' : (BitVec.ofNat 64 totalBytes == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hmax64
      have h_end_eq : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 totalBytes :=
        congrArg (BitVec.ofNat 64) htot'
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 []]
      dsimp only [pointsToBytes, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      rw [ProofLib.memRegion_two (outPtr + BitVec.ofNat 64 (2 * k))]
      simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      wp_steps
      refine align_pre ?_ ?_
      · dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, pointsToBytes]
        simp only [Nat.add_zero, sepConj_emp, rev16_pair_eq_u16FromBeBytes]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · simp at hlen
  | succ n ih =>
    intro bs k totalBytes s fsp hdrAddr bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx8 hx19 hx20 hx22 hx23 hx28
    rcases bs with _ | ⟨b0, _ | ⟨b1, bs'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : bs'.length = 2 * (n + 1) := by simp at hlen; omega
      have htot' : 2 * (k + 1) + bs'.length = totalBytes := by simp at htot; omega
      have hlt1 : 2 * k < totalBytes := by omega
      have hlt2 : 2 * k + 1 < totalBytes := by omega
      have hlt3 : 2 * k + 2 < totalBytes := by omega
      have hk_lt : k < totalBytes := by omega
      have hmax64 : totalBytes < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt2 hmax64
      have h_ule3 : BitVec.ule (BitVec.ofNat 64 totalBytes) (BitVec.ofNat 64 (2 * k + 2)) = false :=
        ule_false_of_lt hlt3 hmax64
      have h_ult3 : BitVec.ult (BitVec.ofNat 64 (2 * k + 2)) (BitVec.ofNat 64 totalBytes) = true :=
        ult_of_lt hlt3 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalBytes) = true :=
        bne_of_lt hk_lt hmax64
      have h_bne' : (BitVec.ofNat 64 totalBytes != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hmax64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalBytes) = false :=
        beq_false_of_lt hk_lt hmax64
      have h_beq' : (BitVec.ofNat 64 totalBytes == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hmax64
      have hbs_len_eq : (b0 :: b1 :: bs').length = 2 * ((n + 1) + 1) := by
        simp [hlen']; omega
      have hbs_addr : bsPtr + BitVec.ofNat 64 (2 * k + 2) = bsPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
        congr 2
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 bs',
          bv_add_lit_add_lit, hbs_addr, hbs_len_eq,
          memRegion_two_cons outPtr k (n + 1) (by omega),
          ← hlen']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      refine seq_clean
        (mid := (contractProg b ext).fnAddr encoderFromPbName + 376#64)
        (P_mid :=
          ((hdrAddr + 8#64) ↦₆₄ bsPtr) ∗
          ((hdrAddr + 16#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 totalBytes) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * (k + 1))) ↦ₛ bs') ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * (k + 1))) bs'.length ∗
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x8 = outPtr ∧
          sm.readReg64 .x19 = BitVec.ofNat 64 totalBytes ∧
          sm.readReg64 .x20 = hdrAddr ∧
          sm.readReg64 .x21 = s.readReg64 .x21 ∧
          sm.readReg64 .x22 = outPtr ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (2 * (k + 1)) ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x26 = s.readReg64 .x26 ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 ((k + 1) + 1) ∧
          sm.readReg64 .x29 = s.readReg64 .x29 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · encoder_from_pb_fetches_range b (Rust.withPanics ext) 348 80
        dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr
          "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine align_pre ?_ ?_
        · simp only [rev16_pair_eq_u16FromBeBytes]
          exact Entails.of_eq (by ac_rfl)
        · have hk2 : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * (k + 1)) := by
            congr 1
          wp_done
      · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
          hx24_1, hx25_1, hx26_1, hx28_1, hx29_1, htrace1, hvregs1⟩
        have hrec := ih bs' (k + 1) totalBytes s1 fsp hdrAddr bsPtr outPtr
          (BitVec.ofNat 64 (k + 1)) hfsp_align
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame)
          hlen' htot' hmax hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx22_1 hx23_1 hx28_1
        refine SepWP.mono hrec ?_
        intro sf Pf _ _ ⟨hPf, hspf, hx20f, hx21f, hx22f, hx24f, hx25f, hx26f, hx29f, htrf, hvregsf⟩
        refine ⟨Entails.trans hPf ?_, hspf, hx20f, hx21f.trans hx21_1, hx22f,
          hx24f.trans hx24_1, hx25f.trans hx25_1, hx26f.trans hx26_1, hx29f.trans hx29_1,
          htrf.trans htrace1, hvregsf.trans hvregs1⟩
        have hlen_idx : (k + 1) + n + 1 = k + (n + 1) + 1 := by omega
        have hout_addr : outPtr + BitVec.ofNat 64 (2 * k + 2) = outPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
          congr 2
        rw [hlen_idx, ← hbs_addr]
        dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, BitVec.ofNat_eq_ofNat]
        rw [bv_add_lit_add_lit, hout_addr]
        exact Entails.of_eq (by ac_rfl)

attribute [local arm64_norm, local wp_norm] madd_24_eq

@[local arm64_norm, local wp_norm]
theorem mul_24_eq (j : Nat) :
    BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

@[local arm64_norm, local wp_norm]
theorem fsp_add_201_add_255 (fsp : BitVec 64) :
    fsp + 201#64 + 255#64 = fsp + 456#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fsp_add_255_add_201 (fsp : BitVec 64) :
    fsp + (255#64 + 201#64) = fsp + 456#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem exists_pow_two_eq_two :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

theorem sepWPp_panic_of_sepWP_1536 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1536#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (from_pb_panic_1536 s0 sm P R hpcm hrunm htrm))

/-! ## Single-Element `.points` Deserialization Steps (`+260 -> +1612 / +476 -> +260 / +1648`) -/

/-- Odd-length error step (`+260 -> +1612`, `0x104 -> 0x64c`) when `bs.length % 2 ≠ 0`. -/
theorem pts_elem_odd_step {b : BitVec 64} {ext : String → Option (State → State)}
    (j : Nat) (bs : List (BitVec 8))
    (s : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hodd : bs.length % 2 ≠ 0)
    (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 1612#64)
      s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = s.readReg64 .x1 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 260 16
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  have hbit32 := bit0_and_32_eq_one_of_odd hodd hmax
  have hbit64 := bit0_and_64_eq_one_of_odd hodd hmax
  wp_steps
  wp_done

/-- Empty-slice step (`+260 -> +476`, `0x104 -> 0x204 -> 0x1dc`) when `bs = []`. -/
theorem pts_elem_even_empty_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (j : Nat) (s : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName + 476#64)
      s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal []).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal [])) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) ∧
        sm.readReg64 .x21 = 2#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x26 = s.readReg64 .x1 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 260 32
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 516 32
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  dsimp only [emptySlotAt]
  rw [cells_456_eq fsp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v1
  apply ProofLib.SepWP.exists_left; intro v2
  wp_steps
  refine align_pre ?_ ?_
  · dsimp only [emptySlotAt, bytesToGF16ListTotal, List.length_nil, BitVec.ofNat_eq_ofNat]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((fsp + 456#64) ↦₆₄ 0#64) ∗ ((fsp + 464#64) ↦₆₄ 2#64) ∗ ((fsp + 472#64) ↦₆₄ 0#64)) ∗
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
         (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ 0#64) ∗
          ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ 2#64) ∗
          ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64)) ∗
         Frame) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_left
        (show ((fsp + 456#64) ↦₆₄ 0#64) ∗ ((fsp + 464#64) ↦₆₄ 2#64) ∗ ((fsp + 472#64) ↦₆₄ 0#64) ⊢
          ∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗ ((fsp + 472#64) ↦₆₄ 0#64) ∗
            vecBuf A 2 2 gf16At cap outPtr [] by
          have hev := emptySlotAt_entails_vecGF16Of A (fsp + 456#64)
          have h1 : fsp + 456#64 + 8#64 = fsp + 464#64 := by bv_omega
          have h2 : fsp + 456#64 + 16#64 = fsp + 472#64 := by bv_omega
          unfold emptySlotAt vecGF16Of vecOf vecAt vecHeader gf16Stride gf16Align at hev
          dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hev
          rw [h1, h2] at hev
          simp only [sepConj_assoc] at hev
          exact hev))
      (Entails.of_eq (by ac_rfl))
  · wp_done

/-- Non-empty even-slice step (`+260 -> +476`, `0x104 -> 0x1dc`) when `bs.length = 2 * (m + 1)`. -/
theorem pts_elem_even_nonempty_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (j m : Nat) (bs : List (BitVec 8))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hlen : bs.length = 2 * (m + 1)) (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64) (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j) (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 476#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 → sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j → sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗ emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have heven : bs.length % 2 = 0 := by omega
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have h2n64 : 2 * bs.length < 2 ^ 64 := by omega
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk (2 * bs.length) 2 := ⟨by omega, hpow2, by omega⟩
  have h2len_toNat : (BitVec.ofNat 64 (2 * bs.length)).toNat = 2 * bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2n64]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbit32 := bit0_and_32_eq_zero_of_even heven hmax
  have hbit64 := bit0_and_64_eq_zero_of_even heven hmax
  have hlsr1 := lsr_62_eq_zero hmax
  have hlsr2 := lsr_62_nat_eq_zero hmax
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hlsl1 := shiftLeft_1_eq_mul_2 hmax
  have hlsl2 := shiftLeft_1_nat_eq_mul_2 hmax
  have hlen_fn : True → bs.length = 2 * (m + 1) := fun _ => hlen
  clear hlen
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc
  have hpanic1536 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_1536 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 260 220
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1536 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 308#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic1536 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    set outPtr := sf_1.readReg64 (Reg.gpr 0#5)
    rw [cells_456_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v0
    apply SepWPp.exists_elim; intro v1
    apply SepWPp.exists_elim; intro v2
    apply SepWPp.of_sepWP (mid := entry + 376#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hlen := hlen_fn trivial
    have hsplit_len : 2 * bs.length = bs.length + bs.length := by omega
    have hsplit_bound : bs.length + bs.length ≤ 2 ^ 64 := by omega
    rw [hsplit_len, ProofLib.memRegion_split outPtr bs.length bs.length hsplit_bound]
    refine SepWPp.weaken_pre
      (by dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]; simp only [BitVec.add_zero, h_1, hsp]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean
        (pts_inner_loop (b := b) (ext := ext) m bs 0 bs.length _ fsp
          (ptsPtr + BitVec.ofNat 64 (24 * j)) bsPtr outPtr 0#64 hfsp_align
          (A.live outPtr (bs.length + bs.length) 2 ∗
            memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hlen (by omega) hmax
          (by dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat]; simp only [arm64_norm, wp_norm, hentry, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, Reg.x8, outPtr, *])
          (by simp only [arm64_norm, wp_norm, Reg.x19, *])
          (by simp only [arm64_norm, wp_norm, Reg.x20, *])
          (by simp only [arm64_norm, wp_norm, Reg.x22, outPtr, *])
          (by simp only [arm64_norm, wp_norm, Reg.x23, *])
          (by simp only [arm64_norm, wp_norm, Reg.x28, *]))
        ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx20_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx29_3, htr3, hvregs3⟩
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc3
    rw [hentry] at hpc3
    dsimp only [emptySlotAt, BitVec.ofNat_eq_ofNat]
    simp only [BitVec.add_zero, Nat.zero_add]
    refine sepWPp_seq_clean
      (mid := entry + 476#64)
      (P_mid :=
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        (∃∗ cap, ∃∗ outPtr,
          ((fsp + 456#64) ↦₆₄ cap) ∗
          ((fsp + 464#64) ↦₆₄ outPtr) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
          vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun s4 =>
        s4.sp = fsp ∧
        s4.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) ∧
        s4.readReg64 .x21 = 2#64 ∧
        s4.readReg64 .x23 = 24#64 ∧
        s4.readReg64 .x24 = BitVec.ofNat 64 j ∧
        s4.readReg64 .x25 = ptsPtr ∧
        s4.readReg64 .x26 = s.readReg64 .x1 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        s4.trace = s0.trace ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s0)
      ?_ ?_
    · have hx24_s3 : s3.readReg64 .x24 = BitVec.ofNat 64 j := by
        rw [hx24_3]; simp only [arm64_norm, wp_norm, Reg.x24, *]
      wp_steps
      refine align_pre ?_ ?_
      · have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
        have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
        dsimp only [emptySlotAt]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             ((fsp + 464#64) ↦₆₄ outPtr) ∗
             ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
             A.live outPtr (bs.length + bs.length) 2 ∗
             arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
             memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ 0#64) ∗
              ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ 2#64) ∗
              ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64)) ∗
             A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono_left
            (show ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
              ((fsp + 464#64) ↦₆₄ outPtr) ∗
              ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
              A.live outPtr (bs.length + bs.length) 2 ∗
              arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ∗
              memRegion (outPtr + BitVec.ofNat 64 bs.length) bs.length ⊢
              ∃∗ cap, ∃∗ outPtr,
                ((fsp + 456#64) ↦₆₄ cap) ∗
                ((fsp + 464#64) ↦₆₄ outPtr) ∗
                ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
                vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs) by
              refine Entails.sepExists_right (BitVec.ofNat 64 bs.length)
                (Entails.sepExists_right outPtr ?_)
              unfold vecBuf
              have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := hne0
              rw [hpts_len, hcap_toNat]
              simp only [hcap_ne, ↓reduceIte]
              have hmul2 : bs.length * 2 = bs.length + bs.length := by omega
              have hm2 : (m + 1) * 2 = bs.length := by omega
              have hsub2 : (bs.length - (m + 1)) * 2 = bs.length := by omega
              rw [hmul2, hm2, hsub2]
              simp only [sepConj_pure_left_comm]
              refine Entails.pure_right ⟨by omega, by omega, hoom⟩ ?_
              exact Entails.of_eq (by ac_rfl)))
          (Entails.of_eq (by ac_rfl))
      · apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨Entails.refl _, by wp_norm_goal, by wp_norm_goal, ?_, by wp_norm_goal,
          by wp_norm_goal, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [arm64_norm, wp_norm, Reg.x21, hx21_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x25, hx25_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x26, Reg.x1, hx26_3, *]
        · simp only [arm64_norm, wp_norm, Reg.x29, hx29_3, *]
        · simp only [arm64_norm, wp_norm, htr3, *]
        · simp only [arm64_norm, wp_norm, hvregs3, *]
    · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx29_4, htr4, hvregs4⟩
      exact hcont s4 hpc4 hrun4 hsp4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4

/-- Combined even-slice step (`+260 -> +476`, `0x104 -> 0x1dc`) for any `bs` with `bs.length % 2 = 0`. -/
theorem pts_elem_even_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (j : Nat) (bs : List (BitVec 8))
    (s0 s : State) (fsp ptsPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (heven : bs.length % 2 = 0)
    (hmax : bs.length < 2 ^ 62)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 476#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x19 = fsp + 480#64 + BitVec.ofNat 64 (24 * j) →
      sm.readReg64 .x21 = 2#64 →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = BitVec.ofNat 64 j →
      sm.readReg64 .x25 = ptsPtr →
      sm.readReg64 .x26 = s.readReg64 .x1 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          (∃∗ cap, ∃∗ outPtr,
            ((fsp + 456#64) ↦₆₄ cap) ∗
            ((fsp + 464#64) ↦₆₄ outPtr) ∗
            ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
            vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        cells (fsp + 456#64) 3 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  cases bs with
  | nil =>
    have hempty := pts_elem_even_empty_step (A := A) (b := b) (ext := ext)
      j s fsp ptsPtr hfsp_align
      (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        (bsPtr ↦ₛ []) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx21 hx23 hx24 hx25
    refine SepWPp.weaken_pre
      (by dsimp only [ List.length_nil, BitVec.ofNat_eq_ofNat ]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean hempty ?_)
    intro sm hpcm hrunm ⟨hspm, hx19m, hx21m, hx23m, hx24m, hx25m, hx26m, hx29m, htrm, hvregsm⟩
    refine SepWPp.weaken_pre
      (by dsimp only [ List.length_nil, BitVec.ofNat_eq_ofNat ]; exact Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hrunm hspm hx19m hx21m hx23m hx24m hx25m hx26m hx29m (htrm.trans htrace) (hvregsm.trans hvregs))
  | cons b0 bs' =>
    have hlen_m : (b0 :: bs').length = 2 * ((b0 :: bs').length / 2 - 1 + 1) := by
      simp only [List.length_cons] at heven ⊢
      omega
    exact pts_elem_even_nonempty_step hA j ((b0 :: bs').length / 2 - 1) (b0 :: bs')
      s0 s fsp ptsPtr bsPtr hfsp_align Frame R hlen_m hmax
      hpc hrun hsp hx21 hx23 hx24 hx25 htrace hvregs hcont

/-- Finish a single `.points` element (`+476 -> if j + 1 < 16 then +260 else +1648`, `0x1dc -> 0x104 / 0x670`):
    copies `(cap, outPtr, len)` from `fsp + 456..480` into `slotAddr`,
    restoring `cells (fsp + 456#64) 3` and producing `vecGF16Of A slotAddr (bytesToGF16ListTotal bs)`. -/
theorem pts_elem_finish_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (j : Nat) (hj : j < 16) (bs : List (BitVec 8))
    (s : State) (fsp slotAddr ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 476#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = slotAddr)
    (hx21 : s.readReg64 .x21 = 2#64)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 j)
    (hx25 : s.readReg64 .x25 = ptsPtr) :
    SepWP (contractProg b ext)
      (if j + 1 < 16 then (contractProg b ext).fnAddr encoderFromPbName + 260#64
       else (contractProg b ext).fnAddr encoderFromPbName + 1648#64)
      s
      (emptySlotAt slotAddr ∗
        (∃∗ cap, ∃∗ outPtr,
          ((fsp + 456#64) ↦₆₄ cap) ∗
          ((fsp + 464#64) ↦₆₄ outPtr) ∗
          ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
          vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          vecGF16Of A slotAddr (bytesToGF16ListTotal bs) ∗
          cells (fsp + 456#64) 3 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x1 = s.readReg64 .x26 ∧
        sm.readReg64 .x21 = 2#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x25 = ptsPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 476 40
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  dsimp only [emptySlotAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro outPtr
  have hj1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := (BitVec.ofNat_add j 1).symm
  by_cases hlt : j + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have hne16 : (BitVec.ofNat 64 (j + 1) != 16#64) = true := bne_of_lt hlt (by decide)
    have hne16' : (16#64 != BitVec.ofNat 64 (j + 1)) = true := bne_of_gt hlt (by decide)
    have hbeq16 : (BitVec.ofNat 64 (j + 1) == 16#64) = false := beq_false_of_lt hlt (by decide)
    have hbeq16' : (16#64 == BitVec.ofNat 64 (j + 1)) = false := beq_false_of_gt hlt (by decide)
    wp_steps
    refine align_pre ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [cells_456_eq fsp]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((slotAddr ↦₆₄ cap) ∗
           ((slotAddr + 8#64) ↦₆₄ outPtr) ∗
           ((slotAddr + 16#64) ↦₆₄
             BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
           vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
           ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)) ∗
          Frame by ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono_left ?_)
      · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr (Entails.of_eq (by ac_rfl)))
      · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr
          (Entails.sepExists_right (BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)
            (Entails.of_eq (by ac_rfl))))
    · wp_done
  · simp only [hlt, ↓reduceIte]
    have hj15 : j = 15 := by omega
    subst hj15
    wp_steps
    refine align_pre ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [cells_456_eq fsp]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((slotAddr ↦₆₄ cap) ∗
           ((slotAddr + 8#64) ↦₆₄ outPtr) ∗
           ((slotAddr + 16#64) ↦₆₄
             BitVec.ofNat 64 (bytesToGF16ListTotal bs).length) ∗
           vecBuf A 2 2 gf16At cap outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 456#64) ↦₆₄ cap) ∗ ((fsp + 464#64) ↦₆₄ outPtr) ∗
           ((fsp + 472#64) ↦₆₄ BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)) ∗
          Frame by ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono_left ?_)
      · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr (Entails.of_eq (by ac_rfl)))
      · exact Entails.sepExists_right cap (Entails.sepExists_right outPtr
          (Entails.sepExists_right (BitVec.ofNat 64 (bytesToGF16ListTotal bs).length)
            (Entails.of_eq (by ac_rfl))))
    · wp_done

/-- Outer `.points` deserialization loop (`+260 -> +1612 / +1648`, `0x104 -> 0x64c / 0x670`)
    over `rem : List (List (BitVec 8))` starting at index `j` (`j + rem.length = 16`, `acc.length = j`). -/
theorem pts_outer_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp ptsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (j : Nat) (acc : List (List GF16))
      (s : State) (Frame R : SepProp),
      rem ≠ [] →
      j + rem.length = 16 →
      acc.length = j →
      (∀ bs ∈ rem, bs.length < 2 ^ 62) →
      s.pc = (contractProg b ext).fnAddr encoderFromPbName + 260#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x21 = 2#64 →
      s.readReg64 .x23 = 24#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 j →
      s.readReg64 .x25 = ptsPtr →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sm (tail : List Point),
        decodePbPointsTotal rem = .ok tail →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1648#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 →
        sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) (acc ++ tail.map Point.value) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      (∀ sm (errPts : List (List GF16)),
        decodePbPointsTotal rem = .error .serializationInvalid →
        errPts.length = 16 →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1612#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x1 = s.readReg64 .x1 →
        sm.readReg64 .x29 = s.readReg64 .x29 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) errPts ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j)) rem ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))
  | [], _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => (hne rfl).elim
  | bs :: rest, j, acc, s, Frame, R, _, hj_rem, hacc_len, hmax, hpc, hrun, hsp,
    hx21, hx23, hx24, hx25, htrace, hvregs, hcont_ok, hcont_err => by
    have hbs_max : bs.length < 2 ^ 62 := hmax bs List.mem_cons_self
    have hrest_max : ∀ bs' ∈ rest, bs'.length < 2 ^ 62 :=
      fun bs' hm => hmax bs' (List.mem_cons_of_mem _ hm)
    have hj_lt : j < 16 := by simp only [List.length_cons] at hj_rem; omega
    dsimp only [List.length_cons, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_left (vecU8_open A (ptsPtr + BitVec.ofNat 64 (24 * j)) bs))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap
    apply SepWPp.exists_elim; intro bsPtr
    by_cases hodd_bool : (bs.length % 2 != 0) = true
    · have hodd : bs.length % 2 ≠ 0 := bne_iff_ne.mp hodd_bool
      have hdec_err : decodePbPointsTotal (bs :: rest) = .error .serializationInvalid := by
        simp [decodePbPointsTotal, hodd_bool]
      have hstep := pts_elem_odd_step (b := b) (ext := ext) j bs s fsp ptsPtr hfsp_align
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hodd hbs_max hpc hrun hsp hx23 hx24 hx25
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hstep ?_)
      intro sm hpcm hrunm ⟨hspm, hx1m, hx29m, htrm, hvregsm⟩
      have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
        simp only [List.length_cons] at hj_rem
        rw [List.length_append, List.length_replicate, hacc_len]
        omega
      refine SepWPp.weaken_pre ?_
        (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
          hpcm hrunm hspm hx1m hx29m (htrm.trans htrace) (hvregsm.trans hvregs))
      have heq_pre :
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame =
          (vecGF16ListOf A (fsp + 480#64) acc ∗
           emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
          (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (bsPtr ↦ₛ bs) ∗
           vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
        dsimp only [emptySlotsAt]
        ac_rfl
      rw [heq_pre]
      have hslots := emptySlotsAt_entails_vecGF16ListOf A (rest.length + 1)
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
      have happ := vecGF16ListOf_append A acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
      rw [hacc_len] at happ
      have hclose := vecU8_close A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
          (sepConj_mono_left hclose))
        (Entails.of_eq (by ac_rfl))
    · have heven : bs.length % 2 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd_bool
        exact hodd_bool
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (pts_elem_even_step hA j bs s0 s fsp ptsPtr bsPtr hfsp_align
          (vecGF16ListOf A (fsp + 480#64) acc ∗
            emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            Frame)
          R heven hbs_max hpc hrun hsp hx21 hx23 hx24 hx25 htrace hvregs ?_)
      intro s1 hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx29_1 htr1 hvregs1
      have hfin := pts_elem_finish_step (A := A) (b := b) (ext := ext) j hj_lt bs s1 fsp
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ptsPtr hfsp_align
        (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          vecGF16ListOf A (fsp + 480#64) acc ∗
          emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hfin ?_)
      intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx21_2, hx23_2, hx24_2, hx25_2, hx29_2, htr2, hvregs2⟩
      have hclose := vecU8_close A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
      have happ := vecGF16ListOf_append A acc [bytesToGF16ListTotal bs] (fsp + 480#64)
      rw [hacc_len] at happ
      have hsingle : vecGF16ListOf A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) [bytesToGF16ListTotal bs] =
          vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) := by
        dsimp only [vecGF16ListOf, arrayAt]; simp only [sepConj_emp]
      rw [hsingle] at happ
      cases rest with
      | nil =>
        have hj15 : j = 15 := by simp only [List.length_cons, List.length_nil] at hj_rem; omega
        have hlt_false : ¬(j + 1 < 16) := by omega
        simp only [hlt_false, ↓reduceIte] at hpc2
        have hdec_ok : decodePbPointsTotal [bs] = .ok [{ value := bytesToGF16ListTotal bs }] := by
          simp [decodePbPointsTotal, hodd_bool]
        refine SepWPp.weaken_pre ?_
          (hcont_ok s2 [{ value := bytesToGF16ListTotal bs }] hdec_ok hpc2 hrun2 hsp2
            (hx1_2.trans hx26_1) (hx29_2.trans hx29_1) (htr2.trans htr1) (hvregs2.trans hvregs1))
        dsimp only [List.map, List.length_nil, emptySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
        simp only [sepConj_emp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (vecGF16ListOf A (fsp + 480#64) acc ∗
             vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
            (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
            cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
          (Entails.of_eq (by ac_rfl))
      | cons bs' rest' =>
        have hlt_true : j + 1 < 16 := by simp only [List.length_cons] at hj_rem; omega
        simp only [hlt_true, ↓reduceIte] at hpc2
        have hj_addr1 : fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64 =
            fsp + 480#64 + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        have hj_addr2 : ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64 =
            ptsPtr + BitVec.ofNat 64 (24 * (j + 1)) := by
          rw [bv_add_lit_add_lit]; rfl
        refine SepWPp.weaken_pre ?_
          (pts_outer_loop hA s0 fsp ptsPtr hfsp_align (bs' :: rest') (j + 1)
            (acc ++ [bytesToGF16ListTotal bs]) s2
            (vecU8 A (ptsPtr + BitVec.ofNat 64 (24 * j)) bs ∗ Frame) R
            (List.cons_ne_nil _ _)
            (by simp only [List.length_cons] at hj_rem ⊢; omega)
            (by rw [List.length_append, hacc_len]; rfl)
            hrest_max hpc2 hrun2 hsp2 hx21_2 hx23_2 hx24_2 hx25_2 (htr2.trans htr1) (hvregs2.trans hvregs1)
            (fun sm tail hdec_tail hpcm hrunm hspm hx1m hx29m htrm hvregsm => ?_)
            (fun sm errPts hdec_err herr_len hpcm hrunm hspm hx1m hx29m htrm hvregsm => ?_))
        · rw [← hj_addr1, ← hj_addr2]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (vecGF16ListOf A (fsp + 480#64) acc ∗
               vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
              (((ptsPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((ptsPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               vecU8Rest A (ptsPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
              emptySlotsAt (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest').length ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptsPtr + BitVec.ofNat 64 (24 * j) + 24#64) (bs' :: rest') ∗
              cells (fsp + 456#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
            (Entails.of_eq (by ac_rfl))
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') =
              .ok ({ value := bytesToGF16ListTotal bs } :: tail) := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_tail]
          have happ_assoc : (acc ++ [bytesToGF16ListTotal bs]) ++ tail.map Point.value =
              acc ++ ({ value := bytesToGF16ListTotal bs } :: tail).map Point.value := by
            simp [List.append_assoc]
          rw [happ_assoc, ← hj_addr2]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
            (hcont_ok sm ({ value := bytesToGF16ListTotal bs } :: tail) hdec_cons
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hvregsm)
        · have hdec_cons : decodePbPointsTotal (bs :: bs' :: rest') = .error .serializationInvalid := by
            change (if bs.length % 2 != 0 then Except.error PolynomialError.serializationInvalid
              else match decodePbPointsTotal (bs' :: rest') with
              | Except.error e => Except.error e
              | Except.ok tail => Except.ok ({ value := bytesToGF16ListTotal bs } :: tail)) = _
            simp only [hodd_bool, Bool.false_eq_true, ↓reduceIte, hdec_err]
          rw [← hj_addr2]
          refine SepWPp.weaken_pre
            (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
            (hcont_err sm errPts hdec_cons herr_len
              hpcm hrunm hspm (hx1m.trans (hx1_2.trans hx26_1))
              (hx29m.trans (hx29_2.trans hx29_1)) htrm hvregsm)

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
