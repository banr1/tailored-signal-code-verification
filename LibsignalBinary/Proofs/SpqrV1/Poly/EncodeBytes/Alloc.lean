/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Loop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`: Heap Allocations and Header Init

Proves the 16 `Vec<GF16>::with_capacity(msg.len() / 2)` heap allocations (`+96..+476`, grouped into
four 4-allocation chunks) and 16-slot `Point` header initialization (`+496..+724`), at fixed base
and on Block `417`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncodeBytes

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero exists_pow_two_eq_two bv_add_add_lit
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")

theorem sepWPp_panic_of_sepWP_824 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 824#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (encode_bytes_panic_824 s0 sm P R hpcm hrunm htrm))

/-- Allocations 0..3 (`+96 -> +192`, `0x60 -> 0xc0`), spilling `p0..p3` to `fsp + 64 .. fsp + 40`. -/
theorem encode_bytes_alloc_0_3 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v5 v6 v7 v8 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p0 p1 p2 p3 : BitVec 64),
      p0 ≠ 0 → p1 ≠ 0 → p2 ≠ 0 → p3 ≠ 0 →
      s4.pc = (contractProg b ext).fnAddr encodeBytesName + 192#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 →
      s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗
         ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
         (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗
         (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
         (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗
         (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗
       ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, hpow2, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range b (Rust.withPanics ext) 96 96
  dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic824 hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 116#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic824 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
    apply SepWPp.of_sepWP (mid := entry + 140#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic824 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr1⟩
      have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
      apply SepWPp.of_sepWP (mid := entry + 164#64)
      wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr2
        refine hpanic824 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr2⟩
        have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
        apply SepWPp.of_sepWP (mid := entry + 188#64)
        wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom3 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr3
          refine hpanic824 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr3⟩
          have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
          apply SepWPp.of_sepWP (mid := entry + 192#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom0 hoom1 hoom2 hoom3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · exact Entails.of_eq (by ac_rfl)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

/-- Allocations 4..7 (`+192 -> +288`, `0xc0 -> 0x120`), spilling `p4..p7` to `fsp + 32 .. fsp + 8`. -/
theorem encode_bytes_alloc_4_7 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v1 v2 v3 v4 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 192#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p4 p5 p6 p7 : BitVec 64),
      p4 ≠ 0 → p5 ≠ 0 → p6 ≠ 0 → p7 ≠ 0 →
      s4.pc = (contractProg b ext).fnAddr encodeBytesName + 288#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 →
      s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗
         ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
         (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗
         (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
         (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗
         (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
       ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, hpow2, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range b (Rust.withPanics ext) 192 96
  dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic824 hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 212#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr4
    refine hpanic824 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr4⟩
    have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
    apply SepWPp.of_sepWP (mid := entry + 236#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr5
      refine hpanic824 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr5⟩
      have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
      apply SepWPp.of_sepWP (mid := entry + 260#64)
      wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom6 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr6
        refine hpanic824 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr6⟩
        have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
        apply SepWPp.of_sepWP (mid := entry + 284#64)
        wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom7 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr7
          refine hpanic824 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr7⟩
          have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
          apply SepWPp.of_sepWP (mid := entry + 288#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom4 hoom5 hoom6 hoom7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · exact Entails.of_eq (by ac_rfl)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

/-- Allocations 8..11 (`+288 -> +384`, `0x120 -> 0x180`), placing `p8..p11` in `x23..x26`. -/
theorem encode_bytes_alloc_8_11 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0 → p9 ≠ 0 → p10 ≠ 0 → p11 ≠ 0 →
      s4.pc = (contractProg b ext).fnAddr encodeBytesName + 384#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 →
      s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = p8 →
      s4.readReg64 .x24 = p9 →
      s4.readReg64 .x25 = p10 →
      s4.readReg64 .x26 = p11 →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗
         (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
         (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗
         (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, hpow2, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range b (Rust.withPanics ext) 288 96
  dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic824 hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 304#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom8 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr8
    refine hpanic824 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr8⟩
    have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
    apply SepWPp.of_sepWP (mid := entry + 328#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom9 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr9
      refine hpanic824 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr9⟩
      have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
      apply SepWPp.of_sepWP (mid := entry + 352#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom10 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr10
        refine hpanic824 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr10⟩
        have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
        apply SepWPp.of_sepWP (mid := entry + 376#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom11 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr11
          refine hpanic824 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr11⟩
          have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
          apply SepWPp.of_sepWP (mid := entry + 384#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom8 hoom9 hoom10 hoom11 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · exact Entails.of_eq (by ac_rfl)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, Reg.x23, Reg.x24, Reg.x25, Reg.x26, *]

/-- Allocations 12..15 (`+384 -> +476`, `0x180 -> 0x1dc`), placing `p12..p15` in `x27, x28, x22, x0`. -/
theorem encode_bytes_alloc_12_15 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0 → p13 ≠ 0 → p14 ≠ 0 → p15 ≠ 0 →
      s4.pc = (contractProg b ext).fnAddr encodeBytesName + 476#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 →
      s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = s.readReg64 .x23 →
      s4.readReg64 .x24 = s.readReg64 .x24 →
      s4.readReg64 .x25 = s.readReg64 .x25 →
      s4.readReg64 .x26 = s.readReg64 .x26 →
      s4.readReg64 .x27 = p12 →
      s4.readReg64 .x28 = p13 →
      s4.readReg64 .x22 = p14 →
      s4.readReg64 .x0 = p15 →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗
         (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
         (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗
         (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, hpow2, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encodeBytesName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "__rustc::__rust_alloc"))
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range b (Rust.withPanics ext) 384 92
  dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic824 hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 400#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom12 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr12
    refine hpanic824 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr12⟩
    have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
    apply SepWPp.of_sepWP (mid := entry + 424#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom13 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr13
      refine hpanic824 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr13⟩
      have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
      apply SepWPp.of_sepWP (mid := entry + 448#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom14 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr14
        refine hpanic824 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr14⟩
        have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
        apply SepWPp.of_sepWP (mid := entry + 472#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom15 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr15
          refine hpanic824 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr15⟩
          have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
          apply SepWPp.of_sepWP (mid := entry + 476#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom12 hoom13 hoom14 hoom15 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          · exact Entails.of_eq (by ac_rfl)
          all_goals simp only [arm64_norm, wp_norm, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, *]

/-! ## Storing the 16 `Point` Headers on the Stack (`+560..+664`, `0x230..0x298`) -/

/-- Empty-message header initialization (`+496 -> +668`, `0x1f0 -> 0x29c`):
    when `x21 = 0#64`, sets all 16 pointers to `2#64`, stores 16 empty `Point` headers
    (`cap = 0#64, ptr = 2#64, len = 0#64`) at `fsp + 72 .. fsp + 456`, and falls through
    `b.hs +724` at `+664` to `+668`. -/
theorem encode_bytes_store_headers_empty {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 0#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 668#64) s
      (memRegion (fsp + 72#64) 384 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64)
            (List.replicate 16 ⟨0#64, 2#64⟩)
            (List.replicate 16 { value := [] }) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  encode_bytes_fetches_range b (Rust.withPanics ext) 496 172
  dsimp only [contractProg, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  rw [show memRegion (fsp + 72#64) 384 = cells (fsp + 72#64) 48 from
    ProofLib.memRegion_cells (fsp + 72#64) 48 (by decide)]
  iterate 48 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  refine align_pre ?_ ?_
  · have hpt0 := pointPinAt_empty_off A fsp
    have hall :=
      sepConj_mono (hpt0 72) (sepConj_mono (hpt0 96)
      (sepConj_mono (hpt0 120) (sepConj_mono (hpt0 144)
      (sepConj_mono (hpt0 168) (sepConj_mono (hpt0 192)
      (sepConj_mono (hpt0 216) (sepConj_mono (hpt0 240)
      (sepConj_mono (hpt0 264) (sepConj_mono (hpt0 288)
      (sepConj_mono (hpt0 312) (sepConj_mono (hpt0 336)
      (sepConj_mono (hpt0 360) (sepConj_mono (hpt0 384)
      (sepConj_mono (hpt0 408) (hpt0 432)))))))))))))))
    dsimp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hall
    have htarget :
        pointListPinAt A (fsp + 72#64)
          (List.replicate 16 ⟨0#64, 2#64⟩)
          (List.replicate 16 { value := [] }) ∗ Frame =
        (pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 72#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 96#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 120#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 144#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 168#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 192#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 216#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 240#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 264#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 288#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 312#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 336#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 360#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 384#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 408#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 432#64)) ∗ Frame := by
      simp only [List.replicate, pointListPinAt, bv_add_add_lit, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
    rw [htarget]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hall)
  · wp_done

/-- Non-empty header initialization (`+476..+492 -> +560..+664 -> +724`, `0x1dc -> 0x2d4`):
    loads the 8 spilled pointers `p0..p7` from `fsp + 8 .. fsp + 64`, stores all 16 `Point`
    headers `(cap = msgLen / 2, ptr = p_k, len = 0)` at `fsp + 72 .. fsp + 456`, folds them
    with the 16 freshly allocated buffers into `pointListPinAt`, and branches via `b.hs +724`
    to the distribution loop entry (`+724`). -/
theorem encode_bytes_store_headers_nonempty {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0)
    (hp4 : p4 ≠ 0) (hp5 : p5 ≠ 0) (hp6 : p6 ≠ 0) (hp7 : p7 ≠ 0)
    (hp8 : p8 ≠ 0) (hp9 : p9 ≠ 0) (hp10 : p10 ≠ 0) (hp11 : p11 ≠ 0)
    (hp12 : p12 ≠ 0) (hp13 : p13 ≠ 0) (hp14 : p14 ≠ 0) (hp15 : p15 ≠ 0)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 476#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (hx23 : s.readReg64 .x23 = p8)
    (hx24 : s.readReg64 .x24 = p9)
    (hx25 : s.readReg64 .x25 = p10)
    (hx26 : s.readReg64 .x26 = p11)
    (hx27 : s.readReg64 .x27 = p12)
    (hx28 : s.readReg64 .x28 = p13)
    (hx22 : s.readReg64 .x22 = p14)
    (hx0 : s.readReg64 .x0 = p15)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let cap := BitVec.ofNat 64 (msgLen / 2)
    let pins : List VecPin :=
      [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩,
       ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
       ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩,
       ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 724#64) s
      (memRegion (fsp + 72#64) 384 ∗
        (fsp ↦₆₄ v0) ∗
        ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗
        ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
        ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗
        ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
        (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗
        (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
        (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗
        (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
        (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗
        (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
        (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗
        (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
        (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗
        (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
        (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗
        (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
        (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗
        (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
        (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗
        (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗
          cells fsp 9 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 msgLen - 2#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  intro cap pins
  have hlsr1 : (BitVec.ofNat 64 msgLen) >>> 1 = BitVec.ofNat 64 (msgLen / 2) := by
    rw [lsr_one_nat_eq_div_two, Nat.mod_eq_of_lt (by omega)]
  have hlsr2 : (BitVec.ofNat 64 msgLen) >>> 1#64 = BitVec.ofNat 64 (msgLen / 2) := hlsr1
  have hule : (2#64).ule (BitVec.ofNat 64 msgLen) = true := by
    rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  encode_bytes_fetches_range b (Rust.withPanics ext) 476 20
  encode_bytes_fetches_range b (Rust.withPanics ext) 560 108
  dsimp only [contractProg, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  rw [show memRegion (fsp + 72#64) 384 = cells (fsp + 72#64) 48 from
    ProofLib.memRegion_cells (fsp + 72#64) 48 (by decide)]
  iterate 48 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  refine align_pre ?_ ?_
  · have h0 := pointPinAt_fresh_off A fsp p0 msgLen 72 heven hpos hle hp0; have h1 := pointPinAt_fresh_off A fsp p1 msgLen 96 heven hpos hle hp1
    have h2 := pointPinAt_fresh_off A fsp p2 msgLen 120 heven hpos hle hp2; have h3 := pointPinAt_fresh_off A fsp p3 msgLen 144 heven hpos hle hp3
    have h4 := pointPinAt_fresh_off A fsp p4 msgLen 168 heven hpos hle hp4; have h5 := pointPinAt_fresh_off A fsp p5 msgLen 192 heven hpos hle hp5
    have h6 := pointPinAt_fresh_off A fsp p6 msgLen 216 heven hpos hle hp6; have h7 := pointPinAt_fresh_off A fsp p7 msgLen 240 heven hpos hle hp7
    have h8 := pointPinAt_fresh_off A fsp p8 msgLen 264 heven hpos hle hp8; have h9 := pointPinAt_fresh_off A fsp p9 msgLen 288 heven hpos hle hp9
    have h10 := pointPinAt_fresh_off A fsp p10 msgLen 312 heven hpos hle hp10; have h11 := pointPinAt_fresh_off A fsp p11 msgLen 336 heven hpos hle hp11
    have h12 := pointPinAt_fresh_off A fsp p12 msgLen 360 heven hpos hle hp12; have h13 := pointPinAt_fresh_off A fsp p13 msgLen 384 heven hpos hle hp13
    have h14 := pointPinAt_fresh_off A fsp p14 msgLen 408 heven hpos hle hp14; have h15 := pointPinAt_fresh_off A fsp p15 msgLen 432 heven hpos hle hp15
    dsimp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    have hall :=
      sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7
      (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h11
      (sepConj_mono h12 (sepConj_mono h13 (sepConj_mono h14 h15))))))))))))))
    have hc9 := cells9_fsp_entails fsp v0 p7 p6 p5 p4 p3 p2 p1 p0
    have htarget :
        pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗
          cells fsp 9 ∗ Frame =
        (pointPinAt A ⟨cap, p0⟩ { value := [] } (fsp + 72#64) ∗
         pointPinAt A ⟨cap, p1⟩ { value := [] } (fsp + 96#64) ∗
         pointPinAt A ⟨cap, p2⟩ { value := [] } (fsp + 120#64) ∗
         pointPinAt A ⟨cap, p3⟩ { value := [] } (fsp + 144#64) ∗
         pointPinAt A ⟨cap, p4⟩ { value := [] } (fsp + 168#64) ∗
         pointPinAt A ⟨cap, p5⟩ { value := [] } (fsp + 192#64) ∗
         pointPinAt A ⟨cap, p6⟩ { value := [] } (fsp + 216#64) ∗
         pointPinAt A ⟨cap, p7⟩ { value := [] } (fsp + 240#64) ∗
         pointPinAt A ⟨cap, p8⟩ { value := [] } (fsp + 264#64) ∗
         pointPinAt A ⟨cap, p9⟩ { value := [] } (fsp + 288#64) ∗
         pointPinAt A ⟨cap, p10⟩ { value := [] } (fsp + 312#64) ∗
         pointPinAt A ⟨cap, p11⟩ { value := [] } (fsp + 336#64) ∗
         pointPinAt A ⟨cap, p12⟩ { value := [] } (fsp + 360#64) ∗
         pointPinAt A ⟨cap, p13⟩ { value := [] } (fsp + 384#64) ∗
         pointPinAt A ⟨cap, p14⟩ { value := [] } (fsp + 408#64) ∗
         pointPinAt A ⟨cap, p15⟩ { value := [] } (fsp + 432#64)) ∗
         cells fsp 9 ∗ Frame := by
      dsimp only [pins]
      simp only [List.replicate, pointListPinAt, bv_add_add_lit, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
    rw [htarget]
    dsimp only [cap]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono hall (sepConj_mono_left hc9))
  · wp_done

/-! ## Relocatable `[LibsignalPlacement]` Allocations and Header Storage (Block `417`) -/

section Placed
open CryptoVerification.SpqrV1.Alloc
variable [LibsignalPlacement]

theorem sepWPp_panic_of_sepWP_824_placed {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) ((blkPl_417).base + 824#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (encode_bytes_panic_824_placed h_panic s0 sm P R hpcm hrunm htrm))

theorem encode_bytes_alloc_0_3_placed {A : RustAlloc} {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576) (v5 v6 v7 v8 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_417).base + 96#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen) (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p0 p1 p2 p3 : BitVec 64), p0 ≠ 0 → p1 ≠ 0 → p2 ≠ 0 → p3 ≠ 0 →
      s4.pc = (blkPl_417).base + 192#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen → s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗ ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
         (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗ (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
         (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗ (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec] at hshim; simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_824_placed _ ext Q h_panic s0 s P R
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 116#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩; have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
    apply SepWPp.of_sepWP (mid := (blkPl_417).base + 140#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr1⟩; have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
      apply SepWPp.of_sepWP (mid := (blkPl_417).base + 164#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr2; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr2⟩; have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
        apply SepWPp.of_sepWP (mid := (blkPl_417).base + 188#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom3 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr3; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr3⟩; have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
          apply SepWPp.of_sepWP (mid := (blkPl_417).base + 192#64); wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
            (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom0 hoom1 hoom2 hoom3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

theorem encode_bytes_alloc_4_7_placed {A : RustAlloc} {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576) (v1 v2 v3 v4 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_417).base + 192#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen) (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p4 p5 p6 p7 : BitVec 64), p4 ≠ 0 → p5 ≠ 0 → p6 ≠ 0 → p7 ≠ 0 →
      s4.pc = (blkPl_417).base + 288#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen → s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
         (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗ (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
         (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗ (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec] at hshim; simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_824_placed _ ext Q h_panic s0 s P R
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 212#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr4; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr4⟩; have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
    apply SepWPp.of_sepWP (mid := (blkPl_417).base + 236#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr5; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr5⟩; have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
      apply SepWPp.of_sepWP (mid := (blkPl_417).base + 260#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom6 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr6; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr6⟩; have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
        apply SepWPp.of_sepWP (mid := (blkPl_417).base + 284#64); wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom7 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr7; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr7⟩; have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
          apply SepWPp.of_sepWP (mid := (blkPl_417).base + 288#64); wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
            (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom4 hoom5 hoom6 hoom7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

theorem encode_bytes_alloc_8_11_placed {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_417).base + 288#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0 → p9 ≠ 0 → p10 ≠ 0 → p11 ≠ 0 →
      s4.pc = (blkPl_417).base + 384#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = p8 → s4.readReg64 .x24 = p9 → s4.readReg64 .x25 = p10 → s4.readReg64 .x26 = p11 →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗ (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗ (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
         (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗ (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    spqr_hook_ok_of_mem halloc_sat
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824_placed _ ext Q h_panic s0 s P R
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 304#64); wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom8 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr8; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr8⟩; have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
    apply SepWPp.of_sepWP (mid := (blkPl_417).base + 328#64); wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom9 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr9; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr9⟩; have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
      apply SepWPp.of_sepWP (mid := (blkPl_417).base + 352#64); wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom10 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr10; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr10⟩; have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
        apply SepWPp.of_sepWP (mid := (blkPl_417).base + 376#64); wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom11 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr11; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr11⟩; have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
          apply SepWPp.of_sepWP (mid := (blkPl_417).base + 384#64); wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
            (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom8 hoom9 hoom10 hoom11 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, Reg.x23, Reg.x24, Reg.x25, Reg.x26, *]

theorem encode_bytes_alloc_12_15_placed {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_417).base + 384#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0 → p13 ≠ 0 → p14 ≠ 0 → p15 ≠ 0 →
      s4.pc = (blkPl_417).base + 476#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = s.readReg64 .x23 → s4.readReg64 .x24 = s.readReg64 .x24 →
      s4.readReg64 .x25 = s.readReg64 .x25 → s4.readReg64 .x26 = s.readReg64 .x26 →
      s4.readReg64 .x27 = p12 → s4.readReg64 .x28 = p13 → s4.readReg64 .x22 = p14 → s4.readReg64 .x0 = p15 →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗ (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗ (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
         (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗ (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk msgLen 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    spqr_hook_ok_of_mem halloc_sat
  simp only [rustAllocSpec] at halloc; dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824_placed _ ext Q h_panic s0 s P R
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 400#64); wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom12 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr12; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr12⟩; have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
    apply SepWPp.of_sepWP (mid := (blkPl_417).base + 424#64); wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom13 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr13; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr13⟩; have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
      apply SepWPp.of_sepWP (mid := (blkPl_417).base + 448#64); wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom14 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr14; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr14⟩; have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
        apply SepWPp.of_sepWP (mid := (blkPl_417).base + 472#64); wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom15 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr15; refine hpanic824 _ _ ?_; wp_steps; exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr15⟩; have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
          apply SepWPp.of_sepWP (mid := (blkPl_417).base + 476#64); wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          conv => arg 4; simp only [*]
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
            (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom12 hoom13 hoom14 hoom15 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, *]

theorem encode_bytes_store_headers_empty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 496#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 0#64) (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s (memRegion (fsp + 72#64) 384 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) (List.replicate 16 ⟨0#64, 2#64⟩) (List.replicate 16 { value := [] }) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  rw [show memRegion (fsp + 72#64) 384 = cells (fsp + 72#64) 48 from ProofLib.memRegion_cells (fsp + 72#64) 48 (by decide)]
  iterate 48 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps; refine align_pre ?_ ?_
  · have hpt0 := pointPinAt_empty_off A fsp
    have hall :=
      sepConj_mono (hpt0 72) (sepConj_mono (hpt0 96) (sepConj_mono (hpt0 120) (sepConj_mono (hpt0 144)
      (sepConj_mono (hpt0 168) (sepConj_mono (hpt0 192) (sepConj_mono (hpt0 216) (sepConj_mono (hpt0 240)
      (sepConj_mono (hpt0 264) (sepConj_mono (hpt0 288) (sepConj_mono (hpt0 312) (sepConj_mono (hpt0 336)
      (sepConj_mono (hpt0 360) (sepConj_mono (hpt0 384) (sepConj_mono (hpt0 408) (hpt0 432)))))))))))))))
    dsimp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hall
    have htarget :
        pointListPinAt A (fsp + 72#64) (List.replicate 16 ⟨0#64, 2#64⟩) (List.replicate 16 { value := [] }) ∗ Frame =
        (pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 72#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 96#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 120#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 144#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 168#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 192#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 216#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 240#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 264#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 288#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 312#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 336#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 360#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 384#64) ∗
         pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 408#64) ∗ pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + 432#64)) ∗ Frame := by
      simp only [List.replicate, pointListPinAt, bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
    rw [htarget]; exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hall)
  · wp_done

theorem encode_bytes_store_headers_nonempty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0) (hp4 : p4 ≠ 0) (hp5 : p5 ≠ 0) (hp6 : p6 ≠ 0) (hp7 : p7 ≠ 0)
    (hp8 : p8 ≠ 0) (hp9 : p9 ≠ 0) (hp10 : p10 ≠ 0) (hp11 : p11 ≠ 0) (hp12 : p12 ≠ 0) (hp13 : p13 ≠ 0) (hp14 : p14 ≠ 0) (hp15 : p15 ≠ 0)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 476#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (hx23 : s.readReg64 .x23 = p8) (hx24 : s.readReg64 .x24 = p9) (hx25 : s.readReg64 .x25 = p10) (hx26 : s.readReg64 .x26 = p11)
    (hx27 : s.readReg64 .x27 = p12) (hx28 : s.readReg64 .x28 = p13) (hx22 : s.readReg64 .x22 = p14) (hx0 : s.readReg64 .x0 = p15)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let cap := BitVec.ofNat 64 (msgLen / 2)
    let pins : List VecPin :=
      [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
       ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 724#64) s
      (memRegion (fsp + 72#64) 384 ∗ (fsp ↦₆₄ v0) ∗
        ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
        ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
        (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗ (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
        (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗ (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
        (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗ (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
        (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗ (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
        (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗ (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
        (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗ (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
        (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗ (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
        (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗ (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗ cells fsp 9 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = BitVec.ofNat 64 msgLen - 2#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  intro cap pins
  have hlsr1 : (BitVec.ofNat 64 msgLen) >>> 1 = BitVec.ofNat 64 (msgLen / 2) := by
    rw [lsr_one_nat_eq_div_two, Nat.mod_eq_of_lt (by omega)]
  have hlsr2 : (BitVec.ofNat 64 msgLen) >>> 1#64 = BitVec.ofNat 64 (msgLen / 2) := hlsr1
  have hule : (2#64).ule (BitVec.ofNat 64 msgLen) = true := by
    rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [show memRegion (fsp + 72#64) 384 = cells (fsp + 72#64) 48 from
    ProofLib.memRegion_cells (fsp + 72#64) 48 (by decide)]
  iterate 48 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  wp_steps
  refine align_pre ?_ ?_
  · have h0 := pointPinAt_fresh_off A fsp p0 msgLen 72 heven hpos hle hp0; have h1 := pointPinAt_fresh_off A fsp p1 msgLen 96 heven hpos hle hp1
    have h2 := pointPinAt_fresh_off A fsp p2 msgLen 120 heven hpos hle hp2; have h3 := pointPinAt_fresh_off A fsp p3 msgLen 144 heven hpos hle hp3
    have h4 := pointPinAt_fresh_off A fsp p4 msgLen 168 heven hpos hle hp4; have h5 := pointPinAt_fresh_off A fsp p5 msgLen 192 heven hpos hle hp5
    have h6 := pointPinAt_fresh_off A fsp p6 msgLen 216 heven hpos hle hp6; have h7 := pointPinAt_fresh_off A fsp p7 msgLen 240 heven hpos hle hp7
    have h8 := pointPinAt_fresh_off A fsp p8 msgLen 264 heven hpos hle hp8; have h9 := pointPinAt_fresh_off A fsp p9 msgLen 288 heven hpos hle hp9
    have h10 := pointPinAt_fresh_off A fsp p10 msgLen 312 heven hpos hle hp10; have h11 := pointPinAt_fresh_off A fsp p11 msgLen 336 heven hpos hle hp11
    have h12 := pointPinAt_fresh_off A fsp p12 msgLen 360 heven hpos hle hp12; have h13 := pointPinAt_fresh_off A fsp p13 msgLen 384 heven hpos hle hp13
    have h14 := pointPinAt_fresh_off A fsp p14 msgLen 408 heven hpos hle hp14; have h15 := pointPinAt_fresh_off A fsp p15 msgLen 432 heven hpos hle hp15
    dsimp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    have hall :=
      sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7
      (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h11
      (sepConj_mono h12 (sepConj_mono h13 (sepConj_mono h14 h15))))))))))))))
    have hc9 := cells9_fsp_entails fsp v0 p7 p6 p5 p4 p3 p2 p1 p0
    have htarget :
        pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗ cells fsp 9 ∗ Frame =
        (pointPinAt A ⟨cap, p0⟩ { value := [] } (fsp + 72#64) ∗ pointPinAt A ⟨cap, p1⟩ { value := [] } (fsp + 96#64) ∗
         pointPinAt A ⟨cap, p2⟩ { value := [] } (fsp + 120#64) ∗ pointPinAt A ⟨cap, p3⟩ { value := [] } (fsp + 144#64) ∗
         pointPinAt A ⟨cap, p4⟩ { value := [] } (fsp + 168#64) ∗ pointPinAt A ⟨cap, p5⟩ { value := [] } (fsp + 192#64) ∗
         pointPinAt A ⟨cap, p6⟩ { value := [] } (fsp + 216#64) ∗ pointPinAt A ⟨cap, p7⟩ { value := [] } (fsp + 240#64) ∗
         pointPinAt A ⟨cap, p8⟩ { value := [] } (fsp + 264#64) ∗ pointPinAt A ⟨cap, p9⟩ { value := [] } (fsp + 288#64) ∗
         pointPinAt A ⟨cap, p10⟩ { value := [] } (fsp + 312#64) ∗ pointPinAt A ⟨cap, p11⟩ { value := [] } (fsp + 336#64) ∗
         pointPinAt A ⟨cap, p12⟩ { value := [] } (fsp + 360#64) ∗ pointPinAt A ⟨cap, p13⟩ { value := [] } (fsp + 384#64) ∗
         pointPinAt A ⟨cap, p14⟩ { value := [] } (fsp + 408#64) ∗ pointPinAt A ⟨cap, p15⟩ { value := [] } (fsp + 432#64)) ∗
         cells fsp 9 ∗ Frame := by
      dsimp only [pins]
      simp only [List.replicate, pointListPinAt, bv_add_add_lit, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
    rw [htarget]; dsimp only [cap]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono hall (sepConj_mono_left hc9))
  · wp_done

end Placed

end CryptoVerification.SpqrV1.Poly.EncodeBytes
