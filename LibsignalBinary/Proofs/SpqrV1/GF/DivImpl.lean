/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::encoding::gf::GF16>::div_impl`

Proves fixed-offset (`0x552d0`) and relocatable `[LibsignalPlacement]` (Block `331`) subroutine
contracts for `<spqr::encoding::gf::GF16>::div_impl` against `GF16.divImpl`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.GF.DivImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

abbrev divImplName : String := "<spqr::encoding::gf::GF16>::div_impl"

theorem divImpl_fnOff : libsignalSessionCode.fnOff divImplName = 0x4fed8 :=
  ls_lemma% fnOff "<spqr::encoding::gf::GF16>::div_impl"

gen_decodes libsignalSessionCode_tree divImplBin [0x4fed8 → 0x4ff14, 0x4ff90 → 0x50058]

theorem fnAddr_adrp_552e0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr divImplName + 16#64) &&&
      0xfffffffffffff000#64) = b + 0x4f000#64 := by
  rw [Program.fnAddr_rebase, divImpl_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_552f8 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr divImplName + 40#64) &&&
      0xfffffffffffff000#64) = b + 0x4f000#64 := by
  rw [Program.fnAddr_rebase, divImpl_fnOff]
  revert hb; bv_bits

/-- Total stack budget of `div_impl`: `0x30` (`48` bytes own frame) + `0x40` (`64` bytes for `mul2_u16`). -/
abbrev divImplStack : Nat := 0x70

theorem stackAt_112_split (sp : BitVec 64) :
    stackAt sp 0x70 =
      stackAt (sp - 48#64) 0x40 ∗
      memRegion (sp - 48#64) 16 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  have hbot : sp - BitVec.ofNat 64 (0x30 + 0x40) =
      sp - 48#64 - BitVec.ofNat 64 0x40 := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x30 + 0x40) = _
  rw [ProofLib.stackAt_split_bottom sp 0x30 0x40 (by decide), hbot]
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x30 = 48#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 16) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

theorem stackAt_112_merge (sp sp' s29 s30 s20 s19 : BitVec 64) (hsp : sp' = sp - 48#64) :
    stackAt sp' 0x40 ∗
      memRegion (sp - 48#64) 16 ∗
      ((sp - 32#64) ↦₆₄ s29) ∗
      ((sp - 24#64) ↦₆₄ s30) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp 0x70 := by
  subst hsp
  rw [stackAt_112_split sp]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro s29) ?_
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s20) ?_
  exact Entails.sepExists_intro s19

attribute [local wp_norm] zeroExtend_16_truncate_32_64

/-- State `(square, out)` after `k` iterations of the `GF16::div_impl` loop.
Keeping this folded during symbolic execution prevents exponential term duplication
across the 15 unrolled `mul2_u16` calls. -/
private def divStep (other self : BitVec 16) : Nat → BitVec 16 × BitVec 16
  | 0 => (unaccelerated.mul other other, self)
  | k + 1 =>
    let p := divStep other self k
    mul2U16 p.1 p.1 p.2

@[local wp_norm]
private theorem divStep_one (other self : BitVec 16) :
    mul2U16 (unaccelerated.mul other other) (unaccelerated.mul other other) self =
      divStep other self 1 := rfl

@[local wp_norm]
private theorem divStep_succ (other self : BitVec 16) (k : Nat) :
    mul2U16 (divStep other self k).1 (divStep other self k).1 (divStep other self k).2 =
      divStep other self (k + 1) := rfl

@[local wp_norm]
private theorem divStep_15_snd (self other : GF16) :
    (divStep other.value self.value 15).2 = (GF16.divImpl self other).value := rfl

/-- Specification of `<spqr::encoding::gf::GF16>::div_impl` (`0x552d0`) under `tokenInitAt b`.
Takes pointers `p_self` in `.x0` (`p_self ↦₁₆ self.value`) and `p_other` in `.x1`
(`p_other ↦₁₆ other.value`), and returns `(GF16.divImpl self other).value` in the low 16 bits
of `.x0`. -/
def divImplSpec (b : BitVec 64) : Spec (BitVec 64 × BitVec 64 × GF16 × GF16) where
  pre := fun (p_self, p_other, self, other) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = p_self ∧
      s.readReg64 .x1 = p_other⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s.sp divImplStack
  post := fun (p_self, p_other, self, other) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
      sf.trace = s0.trace⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s0.sp divImplStack

set_option maxHeartbeats 1600000 in
theorem divImpl_ok (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr divImplName)
      (divImplSpec b) := by
  have hfn : libsignalSessionCode.fnOff divImplName = 0x4fed8 := divImpl_fnOff
  have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr divImplName + BitVec.ofNat 64 59860)
      (unacceleratedMulSpec b) :=
    sub_ok_at_of_fnAddr (unacceleratedMul_ok b ext) divImplName 59860
      (by rw [divImpl_fnOff, unacceleratedMul_fnOff])
  have hmul2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr divImplName + BitVec.ofNat 64 59196)
      (mul2U16Spec b) :=
    sub_ok_at_of_fnAddr (mul2U16_ok b ext) divImplName 59196
      (by rw [divImpl_fnOff, mul2U16_fnOff])
  code_fetches CryptoVerification.libsignalSessionCode divImplBin b
    (Rust.withPanics ext) hfn 0x4fed8 64
  code_fetches_range CryptoVerification.libsignalSessionCode divImplBin b
    (Rust.withPanics ext) hfn 0x4fed8 0xb8 204
  dsimp only [tripleRatchetProgAtExt] at ⊢ hmul hmul2
  clear hfn
  simp only [divImplSpec]
  wp_init args s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr divImplName := by
    rw [Program.fnAddr_rebase, divImpl_fnOff]; exact hpc
  clear hpc
  have hadrp1 := fnAddr_adrp_552e0 (H := Rust.withPanics ext) h_1
  have hadrp2 := fnAddr_adrp_552f8 (H := Rust.withPanics ext) h_1
  have halign := aligned_86bd8 b h_1
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr divImplName = entry
  examples_hide_fetches
  wp_simp_pre [stackAt_112_split, tokenInitAt]
  wp_pull_exists
  wp_steps 7
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
  wp_call hmul
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  refine SepWP.fold
    (stackAt_112_merge s0.sp _
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5))
      ?_)
    (by sep_focus)
    ?_
  · wp_norm_lhs
  wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `331`) -/

/-- Relocatable specification of `<spqr::encoding::gf::GF16>::div_impl` (Block `331`)
under `[LibsignalPlacement]`. -/
def divImplPlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64 × GF16 × GF16) where
  pre := fun (p_self, p_other, self, other) s =>
    ⌜s.readReg64 .x0 = p_self ∧
      s.readReg64 .x1 = p_other⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp divImplStack
  post := fun (p_self, p_other, self, other) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
      sf.trace = s0.trace⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp divImplStack

set_option maxHeartbeats 1600000 in
/-- Relocatable `<spqr::encoding::gf::GF16>::div_impl` (Block `331`) meets
`withLsCodeLoaded lsmpl divImplPlacedSpec` under `[LibsignalPlacement]`. -/
theorem divImpl_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (blkPl_331).base
      (withLsCodeLoaded lsmpl divImplPlacedSpec) := by
  have hmul0 : subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (lsmpl.base 384)
      unacceleratedMulPlacedSpec :=
    unacceleratedMul_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul0
  have hmul20 : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (lsmpl.base 381)
      (withLsCodeLoaded lsmpl mul2U16PlacedSpec) :=
    mul2U16_placed_ok H
  have hmul2 := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul20
  simp only [withLsCl, unacceleratedMulPlacedSpec] at hmul
  simp only [withLsCl, mul2U16PlacedSpec] at hmul2
  simp only [withLsCodeLoaded, divImplPlacedSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_112_split, tokenInitPlacedAt]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_331).base + 184#64)
  wp_steps 7
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact blkPC_331_rebase_fetch_0x1c (blkPl_331).base H
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl1
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  refine SepWP.fold
    (stackAt_112_merge s0.sp _
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5))
      ?_)
    (by sep_focus)
    ?_
  · wp_norm_lhs
  wp_done

end CryptoVerification.SpqrV1.GF.DivImpl
