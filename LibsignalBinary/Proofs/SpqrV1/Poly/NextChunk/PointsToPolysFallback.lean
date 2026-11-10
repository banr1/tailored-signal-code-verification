/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Fallback Setup

**Checked by Lean.**

Verifies OOM panic blocks, `fillXsLoop` (`[(x_i, 1)]`), and `allocXsAndBasis` (`0x6aa90..0x6ab1c`,
`+1804 -> +4116`) for the dynamic Lagrange fallback path (`n ∉ {0, 1, 3, 5, 30, 34, 36}`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fb :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fb :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one_fb (i : Nat) :
    BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

private theorem add_neg_one_eq_sub_one (x : BitVec 64) :
    x + 18446744073709551615#64 = x - 1#64 := by bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one_fb (i : Nat) :
    BitVec.ofNat 64 (i + 1) + 18446744073709551615#64 = BitVec.ofNat 64 i := by
  rw [add_neg_one_eq_sub_one, ofNat_succ_sub_one_fb]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq_succ_fb (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [← BitVec.ofNat_add]

/-! ## 1. OOM Panic Blocks (`+4588`, `+4592`, `+4820`) & Bitvector Helpers -/

theorem next_chunk_panic_4588 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4588#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x11ec 4
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s P R ?_
  rw [hentry]; wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4588 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4588#64) s P
      (fun sm _ => sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm htrm =>
    next_chunk_panic_4588 s0 sm Pm R hpcm hrunm htrm)

theorem next_chunk_panic_4592 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4592#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x11f0 8
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s P R ?_
  rw [hentry]; wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4592 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4592#64) s P
      (fun sm _ => sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm htrm =>
    next_chunk_panic_4592 s0 sm Pm R hpcm hrunm htrm)

theorem next_chunk_panic_4820 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4820#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x12d4 12
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s P R ?_
  rw [hentry]; wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4820 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4820#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4820 s0 sm P R hpcm hrunm htrm))

theorem sle_four_of_le {n : Nat} (hle : n ≤ 4) :
    (BitVec.ofNat 64 n).sle 4#64 = true := by
  have h : (BitVec.ofNat 64 n : BitVec 64) ≤ 4#64 := by bv_omega
  revert h; bv_bits

theorem sle_four_of_gt {n : Nat} (hgt : 4 < n) (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n).sle 4#64 = false := by
  have h1 : (4#64 : BitVec 64) < BitVec.ofNat 64 n := by bv_omega
  have h2 : BitVec.ofNat 64 n ≤ (0x0555555555555555#64 : BitVec 64) := by bv_omega
  revert h1 h2; bv_bits

theorem slt_33_of_le {n : Nat} (hle : n ≤ 33) :
    (33#64 : BitVec 64).slt (BitVec.ofNat 64 n) = false := by
  have h : (BitVec.ofNat 64 n : BitVec 64) ≤ 33#64 := by bv_omega
  revert h; bv_bits

theorem slt_33_of_gt {n : Nat} (hgt : 33 < n) (hb : n ≤ 0x0555555555555555) :
    (33#64 : BitVec 64).slt (BitVec.ofNat 64 n) = true := by
  have h1 : (33#64 : BitVec 64) < BitVec.ofNat 64 n := by bv_omega
  have h2 : BitVec.ofNat 64 n ≤ (0x0555555555555555#64 : BitVec 64) := by bv_omega
  revert h1 h2; bv_bits

theorem ofNat_ne_ofNat_false {a b : Nat} (hne : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false ∧
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0#64) = false := by
  have h1 : (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
    apply Bool.eq_false_iff.mpr; intro h
    have heq := beq_iff_eq.mp h
    bv_omega
  refine ⟨h1, by simp [bne, h1], ?_⟩
  apply Bool.eq_false_iff.mpr; intro h
  have heq := beq_iff_eq.mp h
  bv_omega

theorem dispatch_fallback_sepWPp {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn3 : n ≠ 3) (hn5 : n ≠ 5)
    (hn30 : n ≠ 30) (hn34 : n ≠ 34) (hn36 : n ≠ 36)
    (hnb : n ≤ 0x0555555555555555)
    (u96 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ s1,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1804#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = 1#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 96#64) ↦₆₄ u96) ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_lt : n < 2 ^ 64 := by omega
  obtain ⟨hne0_a, hne0_bne, hne0_b⟩ := ofNat_ne_ofNat_false hn0 hn_lt (by decide)
  obtain ⟨hne1_a, hne1_bne, hne1_b⟩ := ofNat_ne_ofNat_false hn1 hn_lt (by decide)
  obtain ⟨hne3_a, hne3_bne, hne3_b⟩ := ofNat_ne_ofNat_false hn3 hn_lt (by decide)
  obtain ⟨hne5_a, hne5_bne, hne5_b⟩ := ofNat_ne_ofNat_false hn5 hn_lt (by decide)
  obtain ⟨hne30_a, hne30_bne, hne30_b⟩ := ofNat_ne_ofNat_false hn30 hn_lt (by decide)
  obtain ⟨hne34_a, hne34_bne, hne34_b⟩ := ofNat_ne_ofNat_false hn34 hn_lt (by decide)
  obtain ⟨hne36_a, hne36_bne, hne36_b⟩ := ofNat_ne_ofNat_false hn36 hn_lt (by decide)
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x470 40
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x554 24
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x634 16
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  by_cases hle4 : n ≤ 4
  · have hsge4 := sle_four_of_le hle4
    apply SepWPp.of_sepWP (mid := entry + 1804#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hx25, hsge4, hne0_a, hne0_bne, hne0_b, hne1_a, hne1_bne, hne1_b,
            hne3_a, hne3_bne, hne3_b, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    exact hcont _
      (by simp only [wp_norm, hx25, hsge4, hne0_a, hne0_bne, hne0_b, hne1_a, hne1_bne, hne1_b,
            hne3_a, hne3_bne, hne3_b, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htrace])
      rfl
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [wp_norm, hx25])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · have hgt4 : 4 < n := by omega
    have hsge4 := sle_four_of_gt hgt4 hnb
    by_cases hle33 : n ≤ 33
    · have hslt33 := slt_33_of_le hle33
      apply SepWPp.of_sepWP (mid := entry + 1804#64)
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, hx25, hsge4, hslt33, hne5_a, hne5_bne, hne5_b,
              hne30_a, hne30_bne, hne30_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) ?_
      exact hcont _
        (by simp only [wp_norm, hx25, hsge4, hslt33, hne5_a, hne5_bne, hne5_b,
              hne30_a, hne30_bne, hne30_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [wp_norm, hx25])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    · have hgt33 : 33 < n := by omega
      have hslt33 := slt_33_of_gt hgt33 hnb
      apply SepWPp.of_sepWP (mid := entry + 1804#64)
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, hx25, hsge4, hslt33, hne34_a, hne34_bne, hne34_b,
              hne36_a, hne36_bne, hne36_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) ?_
      exact hcont _
        (by simp only [wp_norm, hx25, hsge4, hslt33, hne34_a, hne34_bne, hne34_b,
              hne36_a, hne36_bne, hne36_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [wp_norm, hx25])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)

/-! ## 2. `fillXsLoop` (`0x6aab8..0x6aac8`, `+1844..+1860`) and `allocXsAndBasis` (`0x6aa90..0x6ab1c`) -/

/-- One step of the `[(x_i, 1)]` fill loop (`0x6aab8..0x6aac8`, `+1844..+1860`). -/
theorem fillXsLoop_step_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (src dst : BitVec 64) (pt : Pt) (rest : List Pt) (Frame : SepProp)
    (hbound : rest.length ≤ 0x0555555555555555)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1844#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = dst + 2#64)
    (hx9 : s.readReg64 .x9 = src)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (rest.length + 1))
    (hx19 : s.readReg64 .x19 = 1#64) :
    let nextPC :=
      if rest.length = 0 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1864#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1844#64
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) nextPC s
      (ptAt pt src ∗ memRegion dst (4 * (rest.length + 1)) ∗ Frame)
      (fun sf P =>
        (P ⊢ ptAt pt src ∗ ptAt { x := pt.x, y := GF16.ONE } dst ∗
             memRegion (dst + 4#64) (4 * rest.length) ∗ Frame) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x8 = (dst + 4#64) + 2#64 ∧
        sf.readReg64 .x9 = src + 4#64 ∧
        sf.readReg64 .x10 = BitVec.ofNat 64 rest.length ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5)) := by
  dsimp only
  unfold ptAt GF16.ONE
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (memRegion_split_pt dst rest.length hbound))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro ux
  apply SepWP.exists_elim; intro uy
  have hdst_x : (dst + 2#64) + 18446744073709551614#64 = dst := by bv_omega
  have hx8_next : (dst + 2#64) + 4#64 = (dst + 4#64) + 2#64 := by bv_omega
  have htrunc : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 pt.x.value)) = pt.x.value := by
    bv_bits
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x734 20
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  by_cases hrem : rest.length = 0
  · refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [hrem, ↓reduceIte, wp_norm, hx10, bne_self_eq_false, BitVec.sub_self,
        beq_self_eq_true, Bool.false_eq_true]
    · refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_, ?_, ?_,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · try simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, htrunc]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9]
      · simp only [wp_norm, hx10, hrem]
      · simp only [wp_norm, hx19]
  · have hne1 : (BitVec.ofNat 64 (rest.length + 1) != 1#64) = true := by
      have hpos : 0 < rest.length := Nat.pos_of_ne_zero hrem
      obtain ⟨_, hbne, _⟩ := ofNat_ne_ofNat_false (a := rest.length + 1) (b := 1) (by omega) (by omega) (by decide)
      exact hbne
    refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [hrem, ↓reduceIte, wp_norm, hx10, hne1]
    · refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_, ?_, ?_,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · try simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, htrunc]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9]
      · simp only [wp_norm, hx10]
      · simp only [wp_norm, hx19]

/-- Map a list of points to `[(pt.x, GF16.ONE)]` for Lagrange basis computation. -/
def toOnePts (pts : List Pt) : List Pt :=
  pts.map (fun pt => { x := pt.x, y := GF16.ONE })

@[simp] theorem toOnePts_nil : toOnePts [] = [] := rfl
@[simp] theorem toOnePts_cons (pt : Pt) (pts : List Pt) :
    toOnePts (pt :: pts) = { x := pt.x, y := GF16.ONE } :: toOnePts pts := rfl
@[simp] theorem toOnePts_length (pts : List Pt) :
    (toOnePts pts).length = pts.length := List.length_map _

/-- Full `[(x_i, 1)]` fill loop (`0x6aab8..0x6aac8`, `+1844 -> +1864`) over `pts : List Pt`. -/
theorem fillXsLoop_sepWPp {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} {R : State → SepProp → Prop}
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (s0 s : State) (src dst : BitVec 64) (Frame : SepProp)
    (hbound : pts.length ≤ 0x0555555555555555)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1844#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = dst + 2#64)
    (hx9 : s.readReg64 .x9 = src)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pts.length)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hcont : ∀ sf,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1864#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sf
        (ptSliceAt src pts ∗
         ptSliceAt dst (toOnePts pts) ∗ Frame)
        Q R) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (ptSliceAt src pts ∗ memRegion dst (4 * pts.length) ∗ Frame)
      Q R := by
  induction pts generalizing s src dst Frame with
  | nil => contradiction
  | cons pt rest ih =>
    have hsrc_cons : ptSliceAt src (pt :: rest) = ptAt pt src ∗ ptSliceAt (src + 4#64) rest := rfl
    have hdst_cons : ptSliceAt dst (toOnePts (pt :: rest)) =
        ptAt { x := pt.x, y := GF16.ONE } dst ∗
        ptSliceAt (dst + 4#64) (toOnePts rest) := rfl
    have hstep := fillXsLoop_step_sepWP (b := b) (ext := ext) s src dst pt rest
      (ptSliceAt (src + 4#64) rest ∗ Frame)
      (by simp at hbound; omega) hpc hrun hx8 hx9 hx10 hx19
    dsimp only at hstep
    cases rest with
    | nil =>
      simp only [List.length_nil, ↓reduceIte, Nat.mul_zero, ProofLib.memRegion_zero] at hstep
      refine SepWPp.weaken_pre (by rw [hsrc_cons, List.length_cons, List.length_nil]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sf P hpc_sf hrun_sf ⟨hP, hsp_sf, htr_sf, hvregs_sf, _, _, _, hx19_sf, hx20_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hx30_sf⟩
      have hP' : P ⊢ ptSliceAt src [pt] ∗
          ptSliceAt dst (toOnePts [pt]) ∗ Frame := by
        rw [hsrc_cons, hdst_cons]
        simp only [toOnePts_nil, ptSliceAt, arrayAt] at hP ⊢
        exact Entails.trans hP (Entails.of_eq (by ac_rfl))
      exact SepWPp.weaken_pre hP'
        (hcont sf hpc_sf hrun_sf hsp_sf htr_sf hvregs_sf hx19_sf hx20_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf hx30_sf)
    | cons pt' rest' =>
      have hlen_ne : (pt' :: rest').length ≠ 0 := by simp
      simp only [hlen_ne, ↓reduceIte] at hstep
      refine SepWPp.weaken_pre (by rw [hsrc_cons, List.length_cons]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sm Pm hpc_sm hrun_sm ⟨hPm, hsp_m, htr_m, hvregs_m, hx8_m, hx9_m, hx10_m, hx19_m,
        hx20_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hx30_m⟩
      refine SepWPp.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl)))
        (ih (List.cons_ne_nil pt' rest') sm (src + 4#64) (dst + 4#64)
          (ptAt pt src ∗ ptAt { x := pt.x, y := GF16.ONE } dst ∗ Frame)
          (by simp at hbound ⊢; omega) hpc_sm hrun_sm hx8_m hx9_m hx10_m hx19_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx19_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hsrc_cons, hdst_cons]; exact Entails.of_eq (by ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          hx19_f (hx20_f.trans hx20_m) (hx24_f.trans hx24_m) (hx25_f.trans hx25_m)
          (hx26_f.trans hx26_m) (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

theorem mul24_shl_eq (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (24 * n) := by
  have h1 : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n * 2#64 := by bv_bits
  have h2 : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 3#64 =
      (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) * 8#64 := by bv_bits
  rw [h1, h2]
  bv_omega

theorem mul24_shl_eq_nat (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 = BitVec.ofNat 64 (24 * n) :=
  mul24_shl_eq n

theorem ult_max_pts_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (0x0555555555555555#64).ult (BitVec.ofNat 64 n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have hlt := BitVec.ult_iff_lt.mp h
  bv_omega

/-- `0x6aa90..0x6ab1c` (`+1804 -> +4116`): allocates `xsPtr` (`4 * n` bytes), fills `[(x_i, 1)]`,
    checks `n ≤ 0x0555555555555555`, and allocates `basisPtr` (`24 * n` bytes, align 8). -/
theorem allocXsAndBasis_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (hbound : pts.length ≤ 0x0555555555555555)
    (u24 u80 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hcont : ∀ s1 xsPtr basisPtr,
      xsPtr ≠ 0#64 →
      basisPtr ≠ 0#64 →
      basisPtr.toNat % 8 = 0 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4116#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = basisPtr →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length) →
      s1.readReg64 .x25 = s.readReg64 .x20 →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         ptSliceAt ptVecPtr pts ∗
         A.live xsPtr (4 * pts.length) 2 ∗
         ptSliceAt xsPtr (toOnePts pts) ∗
         A.live basisPtr (24 * pts.length) 8 ∗
         memRegion basisPtr (24 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hlayout4 : LayoutOk (4 * pts.length) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have hlayout24 : LayoutOk (24 * pts.length) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  have h4n_toNat : (BitVec.ofNat 64 (4 * pts.length)).toNat = 4 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have h24n_toNat : (BitVec.ofNat 64 (24 * pts.length)).toNat = 24 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have h24n_ne0 : ¬(BitVec.ofNat 64 (24 * pts.length) == 0#64) = true := by
    intro h0; have heq := beq_iff_eq.mp h0; bv_omega
  have hnhi := ult_max_pts_false hbound
  have hmul24 := mul24_shl_eq pts.length
  have hmul24_nat := mul24_shl_eq_nat pts.length
  have hshim := hA.shim_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  simp only [rustAllocSpec] at halloc
  have hpanic4820 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4820 b ext Q s0 s P R
  have hpanic4588 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4588 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x70c 144
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4820 hpanic4588 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1824#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4820 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc, hx24, h4n_toNat]
    apply sepWPp_pure_mid; intro ⟨_, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have hsp1 : sf_1.sp = fsp := by rw [‹sf_1.sp = sf.sp›, h_1, hsp]
    have hx19_1 : sf_1.readReg64 (Reg.gpr 19#5) = 1#64 := by rw [h_12, h_2, hx19]
    have hx24_1 : sf_1.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (4 * pts.length) := by rw [h_17, h_7, hx24]
    have hx25_1 : sf_1.readReg64 (Reg.gpr 25#5) = s.readReg64 .x20 := by rw [h_18, h_8]
    have hx26_1 : sf_1.readReg64 (Reg.gpr 26#5) = ptVecPtr := by rw [h_19, h_9, hx26]
    apply SepWPp.of_sepWP (mid := entry + 1844#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    rw [h_1, hsp]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (fillXsLoop_sepWPp (b := b) (ext := ext) pts hpts_ne s0 _ ptVecPtr (sf_1.readReg64 (Reg.gpr 0#5))
        (A.pool ∗
         A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pts.length) 2 ∗
         ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         stackAt fsp allocHookStack ∗ Frame)
        hbound
        (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [wp_norm, hx26_1])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hx19_1]) ?_)
    intro sFill hpcFill hrunFill hspFill htrFill hvregsFill hx19Fill hx20Fill hx24Fill hx25Fill hx26Fill hx27Fill hx28Fill hx29Fill hx30Fill
    rw [hentry] at hpcFill
    simp only [arm64_norm, wp_norm] at hspFill htrFill hvregsFill hx20Fill hx24Fill hx25Fill hx26Fill hx27Fill hx28Fill hx29Fill hx30Fill
    have hspFill' : sFill.sp = fsp := by rw [hspFill, hsp1]
    have h24n_eq : (BitVec.ofNat 64 (24 * pts.length) == 0#64) = false :=
      Bool.eq_false_iff.mpr h24n_ne0
    apply SepWPp.of_sepWP (mid := entry + 1900#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hspFill', hnhi, hmul24, hmul24_nat, h24n_eq, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    apply SepWPp.of_sepWP (mid := entry + 1920#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.done hpc_sf_3 hrun_sf_3 ?_
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr3
      refine hpanic4588 _ _ ?_
      rw [‹sf_2.sp = sFill.sp›, hspFill']
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm]; rw [‹sf_2.trace = sFill.trace›, htrFill, htr1, h, htrace] at htr3; exact htr3)
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc, hspFill', hmul24, hmul24_nat, h_24, h24n_toNat]
      apply sepWPp_pure_mid; intro ⟨halign2, htr3⟩
      have hcond2 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom2
      apply SepWPp.of_sepWP (mid := entry + 4116#64)
      rw [‹sf_2.sp = sFill.sp›, hspFill']
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond2, ↓reduceIte]) (by wp_norm_lhs) ?_
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
          hoom1 hoom2 halign2
          (by simp only [wp_norm, hcond2, ↓reduceIte])
          (by wp_norm_lhs)
          (by simp only [wp_norm, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sFill.sp›, hspFill'])
          (by simp only [arm64_norm, wp_norm]; rw [htr3, ‹sf_2.trace = sFill.trace›, htrFill, htr1, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [wp_norm, h_35, h_25, hx20Fill])
          (by simp only [wp_norm])
          (by simp only [wp_norm, h_39, h_29, hx24Fill, hx24_1])
          (by simp only [wp_norm, h_40, h_30, hx25Fill, hx25_1])
          (by simp only [wp_norm, h_41, h_31, hx26Fill, hx26_1])
          (by simp only [wp_norm, h_42, h_32, hx27Fill, h_20, h_10])
          (by simp only [wp_norm, h_43, h_33, hx28Fill, h_21, h_11])
          (by simp only [wp_norm, hcs_sf_1, hpost_sf_1, hx29Fill, hcs_sf, hpost_sf]))

end CryptoVerification.SpqrV1.Poly.NextChunk
