/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Alloc
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Proof for `<PolyEncoder as Encoder>::encode_bytes`

Lifts the 16 heap allocations and top-level contracts (`encode_bytes_ok_ext_4k`,
`encode_bytes_ok_inImage_4k`, `encode_bytes_ok_x_4k`) to `AllocContracts4K`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocHookStack rustAllocSpec)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchet (contractProg sessionMemcpySpec sessionShimSpec
  subroutine_ok_inImage_of_subroutine_ok tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (CHUNK_SIZE NUM_POLYS Point)
open CryptoVerification.SpqrV1.Poly (encoderStatePinnedAt pointListPinAt polyEncoderIdxOff
  polyEncoderPadOff polyEncoderPadSize polyEncoderPinnedAt polyEncoderPointsTag polyEncoderSize
  polyEncoderVecsOff resultPolyEncoderAt resultPolyEncoderPinnedAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (EncodeBytesOkExt EncodeBytesOkX align_pre
  bv384_toNat bv_add_add_lit bytesAt distributeMsgChunksTotal
  distributeMsgChunksTotal_value_length_le distributeMsgChunks_eq_ok encodeBytesName
  encodeBytesOnPanic encodeBytesResult encodeBytesSpec encodeBytesSpecX
  encodeBytesSpecX_of_encodeBytesSpec encodeBytesStack encode_bytes_dispatch_empty
  encode_bytes_dispatch_nonempty encode_bytes_dispatch_odd encode_bytes_dispatch_too_long
  encode_bytes_dist_entry encode_bytes_epilogue encode_bytes_err_odd encode_bytes_err_too_long
  encode_bytes_prologue encode_bytes_store_headers_empty encode_bytes_store_headers_nonempty
  exists_pow_two_eq_two length_pointHeadersBytes memRegion_464_split memRegion_464_split_560
  memRegion_out_ok_open pointBufList pointHeadersBytes pointListPinAt_eq_bytes_bufs
  resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt savedCells sepWPp_cells_succ
  sepWPp_cells_zero sepWPp_panic_of_sepWP_824 sepWPp_pure_mid sepWPp_seq_clean seq_clean
  stackAt_96_split_464)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_add_add_lit BitVec.toNat_zero exists_pow_two_eq_two bv384_toNat
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")

open Lean Elab Tactic in
local elab "encode_bytes_fetches_range_ext " b:term:max H:term:max k0:num len:num : tactic => do
  let codeName := `CryptoVerification.libsignalSessionCode
  let binName := `CryptoVerification.SpqrV1.Poly.EncodeBytes.spqrEncodeBytesBin
  let eOff ← ProofLib.CodeLookup.lookup codeName .fnOff
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range $(mkCIdent codeName) $(mkIdent binName) $b $H $hfn
      $offLit $k0 $len))

/-! ## 16 Heap Allocations (`+96 -> +476`) under `AllocContracts4K` -/

private theorem encode_bytes_alloc_0_3_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
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
  simp only [rustAllocSpec] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range_ext b (Rust.withPanics ext) 96 96
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
          refine SepWPp.weaken_pre (by sep_frame) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom0 hoom1 hoom2 hoom3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

private theorem encode_bytes_alloc_4_7_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
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
  simp only [rustAllocSpec] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range_ext b (Rust.withPanics ext) 192 96
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
          refine SepWPp.weaken_pre (by sep_frame) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom4 hoom5 hoom6 hoom7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, *]

private theorem encode_bytes_alloc_8_11_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
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
  simp only [rustAllocSpec] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range_ext b (Rust.withPanics ext) 288 96
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
          refine SepWPp.weaken_pre (by sep_frame) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom8 hoom9 hoom10 hoom11 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x19, Reg.x20, Reg.x21, Reg.x23, Reg.x24, Reg.x25, Reg.x26, *]

private theorem encode_bytes_alloc_12_15_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
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
  simp only [rustAllocSpec] at halloc
  have hpanic824 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_824 b ext Q s0 s P R
  encode_bytes_fetches_range_ext b (Rust.withPanics ext) 384 92
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
          refine SepWPp.weaken_pre (by sep_frame) (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
            (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
            hoom12 hoom13 hoom14 hoom15 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          all_goals simp only [arm64_norm, wp_norm, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, *]

/-! ## Finish, Empty/Non-Empty Bodies, and Top-Level `4K` Contracts -/

private theorem encode_bytes_finish_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        memRegion out polyEncoderSize ∗
        cells fsp 9 ∗
        memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗
        stackAt fsp allocHookStack ∗
        Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  subst hfsp
  have hlen_eq : pins.length = pts.length := by rw [hpins_len, hpts_len]
  have hbs_len : (pointHeadersBytes pins pts).length = 384 := by
    rw [length_pointHeadersBytes pins pts hlen_eq, hpts_len]
  have hfsp_align : ((s0.sp - 560#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  rw [pointListPinAt_eq_bytes_bufs A ((s0.sp - 560#64) + 72#64) pins pts hlen_eq]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_ok_open out))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d392
  rw [← hbs_len]
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encodeBytesName + 692#64)
    (P_mid := savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
      (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame))
    (Q := fun sm => sm.sp = s0.sp - 560#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · have hmemcpy := hA.session_memcpy_ok_at encodeBytesName
      (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" "memcpy"))
    simp only [sessionMemcpySpec, libcMemcpySpec] at hmemcpy
    encode_bytes_fetches_range_ext b (Rust.withPanics ext) 668 24
    dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
    examples_hide_fetches
    wp_steps
    wp_apply
    wp_steps
    refine align_pre ?_ ?_
    · have hres :
          (out ↦₆₄ 0#64) ∗ (((out + 8#64) ↦ₛ pointHeadersBytes pins pts) ∗ pointBufList A pins pts) ∗
            ((out + 392#64) ↦₃₂ 0#32) ∗ memRegion (out + 396#64) 4 ⊢
          resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) := by
        rw [← pointListPinAt_eq_bytes_bufs A (out + 8#64) pins pts hlen_eq]
        refine Entails.trans ?_
          (resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt A ⟨pins⟩ out
            (.ok { idx := 0#32, s := .points pts }))
        dsimp only [resultPolyEncoderPinnedAt, polyEncoderPinnedAt, encoderStatePinnedAt,
          polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff,
          polyEncoderPadSize, NUM_POLYS, CHUNK_SIZE]
        simp only [sepConj_assoc]
        exact Entails.pure_right ⟨hpts_len, hpins_len, hpts_bound⟩ (Entails.refl _)
      have hstk :
          stackAt s.sp 4096 ∗
            cells (s0.sp - 560#64) 9 ∗
            ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ∗
            memRegion (s0.sp - 104#64) 8 ⊢
          stackAt (s0.sp - 96#64) (allocHookStack + 464) := by
        have h1 : ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ⊢
            memRegion (s0.sp - 488#64) 384 := by
          rw [← hbs_len]
          exact pointsToBytes_entails_memRegion _ _
        rw [stackAt_96_split_464 s0.sp, memRegion_464_split_560 s0.sp, ← hsp]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))
      exact Entails.trans (by sep_frame)
        (sepConj_mono_right (sepConj_mono hstk (sepConj_mono_left hres)))
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htrace1, hvregs1⟩
    simpa only [sepConj_assoc] using
      encode_bytes_epilogue s0 s1
        (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 htrace1 hvregs1

private theorem encode_bytes_nonempty_body_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (msg : List (BitVec 8))
    (s0 s : State) (fsp out msgA : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (heven : msg.length % 2 = 0)
    (hpos : 2 ≤ msg.length)
    (hle : msg.length ≤ 1048576)
    (R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msg.length)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hout : out = s0.readReg64 .x8) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗
        memRegion (fsp + 72#64) 384 ∗
        memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗
        stackAt fsp allocHookStack ∗
        memRegion out polyEncoderSize ∗
        bytesAt msgRO msgA msg ∗
        A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (⌜sf.trace = s0.trace⌝ ∗
              resultPolyEncoderAt A out
                (.ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) }) ∗
              bytesAt msgRO msgA msg ∗
              A.pool ∗
              stackAt s0.sp encodeBytesStack) ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  iterate 9 (apply sepWPp_cells_succ; intro)
  apply sepWPp_cells_zero
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  refine SepWPp.weaken_pre (by sep_frame)
    (encode_bytes_alloc_0_3_4k hA s0 s fsp hfsp_align msg.length hpos hle v5 v6 v7 v8
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
       ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc hrun hsp hx21 htrace hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 htr1 hvr1
  refine SepWPp.weaken_pre (by sep_frame)
    (encode_bytes_alloc_4_7_4k hA s0 s1 fsp hfsp_align msg.length hpos hle v1 v2 v3 v4
      ((fsp ↦₆₄ v0) ∗ ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗
       ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc1 hrun1 hsp1 hx21_1 htr1 hvr1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 htr2 hvr2
  refine SepWPp.weaken_pre (by sep_frame)
    (encode_bytes_alloc_8_11_4k hA s0 s2 fsp hfsp_align msg.length hpos hle
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc2 hrun2 hsp2 hx21_2 htr2 hvr2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx26_3 htr3 hvr3
  refine SepWPp.weaken_pre (by sep_frame)
    (encode_bytes_alloc_12_15_4k hA s0 s3 fsp hfsp_align msg.length hpos hle
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       (A.live p8 msg.length 2 ∗ memRegion p8 msg.length) ∗ (A.live p9 msg.length 2 ∗ memRegion p9 msg.length) ∗
       (A.live p10 msg.length 2 ∗ memRegion p10 msg.length) ∗ (A.live p11 msg.length 2 ∗ memRegion p11 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc3 hrun3 hsp3 hx21_3 htr3 hvr3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  let cap := BitVec.ofNat 64 (msg.length / 2)
  let pins : List VecPin :=
    [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
     ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
  have hpins_len : pins.length = 16 := rfl
  have hpins_cap : ∀ pin ∈ pins, pin.cap = cap := by
    intro pin hpin
    simp only [pins, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hhdr := encode_bytes_store_headers_nonempty (A := A) s0 s4 fsp hfsp_align
    msg.length heven hpos hle v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    (memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool)
    hpc4 hrun4 hsp4 hx21_4
    (by rw [hx23_4, hx23_3]) (by rw [hx24_4, hx24_3])
    (by rw [hx25_4, hx25_3]) (by rw [hx26_4, hx26_3])
    hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  refine SepWPp.weaken_pre (by sep_frame) (sepWPp_seq_clean hhdr ?_)
  intro s5 hpc5 hrun5 ⟨hsp5, hx8_5, hx19_5, hx20_5, htr5, hvr5⟩
  have hx19_s5 : s5.readReg64 .x19 = s0.readReg64 .x8 := by
    rw [hx19_5, hx19_4, hx19_3, hx19_2, hx19_1, hx19, hout]
  have hx20_s5 : s5.readReg64 .x20 = msgA := by
    rw [hx20_5, hx20_4, hx20_3, hx20_2, hx20_1, hx20]
  have hinit_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hinit_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)), pt.value.length ≤ 0 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hloop := encode_bytes_dist_entry (A := A) msg s0 s5 fsp msgA hfsp_align msgRO
    heven (by omega) (by omega) pins (List.replicate 16 { value := [] })
    hpins_len hinit_len hpins_cap hinit_bound
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗ A.pool)
    hpc5 hrun5 hsp5 hx8_5 hx19_s5 hx20_s5 htr5 hvr5
  refine SepWPp.weaken_pre (by sep_frame) (sepWPp_seq_clean hloop ?_)
  intro s6 hpc6 hrun6 ⟨hsp6, hx19_6, htr6, hvr6⟩
  have hpts_len : (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })).length = 16 :=
    (distributeMsgChunks_eq_ok msg 0 (List.replicate 16 { value := [] }) heven hinit_len).2
  have hpts_bound : ∀ pt ∈ distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt
    have h1 := distributeMsgChunksTotal_value_length_le msg 0
      (List.replicate 16 { value := [] }) heven hinit_len hinit_bound pt hpt
    omega
  have hfin := encode_bytes_finish_ok_4k hA s0 s6 fsp out hfsp
    pins (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }))
    hpins_len hpts_len hpts_bound
    (bytesAt msgRO msgA msg ∗ A.pool)
    hsp0_align hpc6 hrun6 hsp6 (by rw [hx19_6, hout]) htr6 hvr6
  refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (by sep_frame) hfin)
    fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
  exact Entails.trans hPf (Entails.pure_right htrf (by sep_frame))

private theorem encode_bytes_empty_body_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = 0#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗
        memRegion (fsp + 72#64) 384 ∗
        memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗
        stackAt fsp allocHookStack ∗
        memRegion out polyEncoderSize ∗
        Frame)
      (fun sf Pf =>
        (Pf ⊢
          resultPolyEncoderAt A out
            (.ok { idx := 0#32, s := .points (List.replicate 16 { value := [] }) }) ∗
          Frame ∗
          stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  have hhdr := encode_bytes_store_headers_empty (A := A) s0 s fsp hfsp_align
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗
      stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗ Frame)
    hpc hrun hsp hx21 htrace hvregs
  refine SepWP.weaken_pre (by sep_frame) (seq_clean hhdr ?_)
  intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, htr1, hvr1⟩
  have hpins_len : (List.replicate 16 (⟨0#64, 2#64⟩ : VecPin)).length = 16 := by simp
  have hpts_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hpts_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hfin := encode_bytes_finish_ok_4k hA s0 s1 fsp out hfsp
    (List.replicate 16 ⟨0#64, 2#64⟩) (List.replicate 16 { value := [] })
    hpins_len hpts_len hpts_bound Frame hsp0_align hpc1 hrun1 hsp1 (by rw [hx19_1, hx19]) htr1 hvr1
  exact SepWP.weaken_pre (by sep_frame) hfin

theorem encode_bytes_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    EncodeBytesOkExt b A ext := by
  unfold EncodeBytesOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨out, msgRO, msgA, msg⟩ R s0 hpc hrun hpre hsp0
  simp only [encodeBytesSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hmem⟩
  refine ⟨stackAt s0.sp encodeBytesStack ∗
      (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool),
    R, ?_, ?_⟩
  · exact Satisfies.mono (by sep_frame) hmem
  dsimp only [encodeBytesSpec]
  have hpro := encode_bytes_prologue s0
    (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool)
    hsp0 hpc hrun
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx19_1, hx21_1, htr1, hvr1⟩
  have hx19_s1 : s1.readReg64 .x19 = out := by rw [hx19_1, hx8]
  have hx0_s1 : s1.readReg64 .x0 = msgA := by rw [hx0_1, hx0]
  have hx21_s1 : s1.readReg64 .x21 = BitVec.ofNat 64 msg.length := by rw [hx21_1, hx1]
  by_cases hodd : (msg.length % 2 != 0) = true
  · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthEven) := by
      simp [encodeBytesResult, hodd]
    rw [hres]
    have hdisp := encode_bytes_dispatch_odd s1 msg.length hodd
      (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
        (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
      hpc1 hrun1 hx21_s1
    refine sepWPp_seq_clean hdisp ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2, hvr2⟩
    have herr := encode_bytes_err_odd (A := A) s0 s2 out
      (bytesAt msgRO msgA msg ∗ A.pool)
      hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
    refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (by sep_frame) herr)
      fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
    exact Entails.trans hPf (Entails.pure_right htrf (by sep_frame))
  · have heven : msg.length % 2 = 0 := by
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd
      exact hodd
    have hodd_false : (msg.length % 2 != 0) = false := bne_eq_false_iff_eq.mpr heven
    by_cases hlong : msg.length > 1048576
    · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthTooLong) := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE]
        omega
      rw [hres]
      have hgt : 1048576 < msg.length := hlong
      have hdisp := encode_bytes_dispatch_too_long s1 msg.length heven hgt hlen_lt
        (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
          (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
        hpc1 hrun1 hx21_s1
      refine sepWPp_seq_clean hdisp ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2, hvr2⟩
      have herr := encode_bytes_err_too_long (A := A) s0 s2 out
        (bytesAt msgRO msgA msg ∗ A.pool)
        hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
      refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (by sep_frame) herr)
        fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
      refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
      exact Entails.trans hPf (Entails.pure_right htrf (by sep_frame))
    · have hle : msg.length ≤ 1048576 := by omega
      have hres : encodeBytesResult msg =
          .ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) } := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE, hle]
      rw [hres]
      let fsp := s0.sp - 560#64
      have hfsp : fsp = s0.sp - 560#64 := rfl
      have hstk : stackAt (s0.sp - 96#64) (allocHookStack + 464) =
          stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 := by
        rw [stackAt_96_split_464 s0.sp, ← hfsp, memRegion_464_split fsp]
      rw [hstk]
      by_cases hemp : msg.length = 0
      · have hmsg_nil : msg = [] := List.eq_nil_of_length_eq_zero hemp
        subst hmsg_nil
        simp only [distributeMsgChunksTotal]
        have hx21_zero : s1.readReg64 .x21 = 0#64 := by simpa using hx21_s1
        have hdisp := encode_bytes_dispatch_empty s1
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA [] ∗ A.pool))
          hpc1 hrun1 hx21_zero
        refine sepWPp_seq_clean hdisp ?_
        intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2, hvr2⟩
        have hbody := encode_bytes_empty_body_4k (A := A) hA s0 s2 fsp out hfsp hsp0
          (bytesAt msgRO msgA [] ∗ A.pool)
          hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) hx21_2 (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
        refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (by sep_frame) hbody)
          fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
        refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
        exact Entails.trans hPf (Entails.pure_right htrf (by sep_frame))
      · have hpos : 2 ≤ msg.length := by omega
        have hdisp := encode_bytes_dispatch_nonempty s1 msg.length heven hpos hle
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
          hpc1 hrun1 hx21_s1
        refine sepWPp_seq_clean hdisp ?_
        intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, htr2, hvr2⟩
        have hbody := encode_bytes_nonempty_body_4k hA msg s0 s2 fsp out msgA hfsp hsp0 msgRO
          heven hpos hle R hpc2 hrun2 (by rw [hsp2, hsp1])
          (by rw [hx19_2, hx19_s1]) (by rw [hx20_2, hx0_s1]) hx21_2
          (by rw [htr2, htr1]) (by rw [hvr2, hvr1]) hx8.symm
        exact SepWPp.weaken_pre (by sep_frame) hbody

theorem encode_bytes_ok_inImage_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr encodeBytesName)
      ((encodeBytesSpec A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (encode_bytes_ok_ext_4k hA)

theorem encode_bytes_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    EncodeBytesOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (encodeBytesSpecX_of_encodeBytesSpec (encode_bytes_ok_ext_4k hA))

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.Poly.EncodeBytes
export LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofExt (
  encode_bytes_ok_ext_4k
  encode_bytes_ok_inImage_4k
  encode_bytes_ok_x_4k
)
end CryptoVerification.SpqrV1.Poly.EncodeBytes
-- AUTO-BRIDGE END
