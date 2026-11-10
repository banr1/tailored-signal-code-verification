/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Proofs.SpqrV1.GF.UnacceleratedMul
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::encoding::gf::mul2_u16`

Proves fixed-offset (`0x63a0c`) and relocatable `[LibsignalPlacement]` (Block `381`) subroutine
contracts for `spqr::encoding::gf::mul2_u16` against `mul2U16`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.GF.Mul2U16

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul

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

abbrev mul2U16Name : String := "spqr::encoding::gf::mul2_u16"

theorem mul2U16_fnOff : libsignalSessionCode.fnOff mul2U16Name = 0x5e614 :=
  ls_lemma% fnOff "spqr::encoding::gf::mul2_u16"

gen_decodes libsignalSessionCode_tree mul2U16Bin [0x5e614 → 0x5e644, 0x5e6f8 → 0x5e72c]

/-- Precondition on `check_accelerated::TOKEN` and `use_accelerated::STORAGE.0` that selects the
unaccelerated path without calling `<Once>::call` or `accelerated::mul2_unreduced`:
- `(b + 0xa5bc8) ↦₈ 0#8`: `InitToken` byte is `0` (initialized, no PMULL acceleration), so
  `cmp w8, #0x1; b.ne 0x63af0` at `+0x02c..+0x030` branches to `0x63af0`;
- `(b + 0xa5bd8) ↦₃₂ 0#32`: `Once` state word is `0` (`COMPLETE`), so `cbnz w8, 0x63a94` at `+0x020`
  is not taken. -/
def tokenInitAt (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_xref% 0x5e638 0x5e63c)) ↦₈ 0#8) ∗
  ((b + bv% (ls_xref% 0x5e628 0x5e62c)) ↦₃₂ 0#32)

theorem tokenInitAt_eq_TokenInit (img : Obj.Image) :
    tokenInitAt img.base = TokenInit img := rfl

theorem tokenInitAt_fold (b : BitVec 64) :
    ((b + bv% (ls_xref% 0x5e638 0x5e63c)) ↦₈ 0#8) ∗
    ((b + bv% (ls_xref% 0x5e628 0x5e62c)) ↦₃₂ 0#32) ⊢
    tokenInitAt b :=
  Entails.refl _

theorem fnAddr_adrp_63a20 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr mul2U16Name + 20#64) &&&
      0xfffffffffffff000#64) = b + 0x5e000#64 := by
  rw [Program.fnAddr_rebase, mul2U16_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_63a30 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr mul2U16Name + 36#64) &&&
      0xfffffffffffff000#64) = b + 0x5e000#64 := by
  rw [Program.fnAddr_rebase, mul2U16_fnOff]
  revert hb; bv_bits

theorem aligned_86bd8 (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    MemWidth.isAligned .W32 (b + bv% (ls_xref% 0x5e628 0x5e62c)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  revert hb; bv_bits

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
theorem step_ldar32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 true rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad32 ea P v)
    (hexec : (s.writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldarStlr .W32 true rn rt) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldarStlr .W32 true rn rt) s = s' := by
    rw [← hexec]
    simp [execInst, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    rfl
  apply hnext R
  rwa [hmem]

theorem stackAt_64_split (sp : BitVec 64) :
    stackAt sp 0x40 =
      memRegion (sp - 64#64) 16 ∗
      (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗
      (∃∗ s21 : BitVec 64, (sp - 32#64) ↦₆₄ s21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x40 = 64#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 16) (k := 48)
        (b' := sp - 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 16#64),
      memRegion_eight (sp - 8#64)]

theorem stackAt_64_merge (sp s29 s30 s21 s20 s19 : BitVec 64) :
    memRegion (sp - 64#64) 16 ∗
      ((sp - 48#64) ↦₆₄ s29) ∗
      ((sp - 40#64) ↦₆₄ s30) ∗
      ((sp - 32#64) ↦₆₄ s21) ∗
      memRegion (sp - 24#64) 8 ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp 0x40 := by
  rw [stackAt_64_split sp]
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s29) ?_)
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s21) ?_
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s20) ?_)
  exact Entails.sepExists_intro s19

@[local wp_norm]
theorem zeroExtend_16_truncate_32_64 (x : BitVec 64) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by
  bv_bits

@[local wp_norm]
private theorem mul2U16_fst (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).1 = unaccelerated.mul a b1 := rfl

@[local wp_norm]
private theorem mul2U16_snd (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).2 = unaccelerated.mul a b2 := rfl

/-- Specification of `spqr::encoding::gf::mul2_u16` (`0x63a0c`) under `tokenInitAt b`.
Multiplies `a` (low 16 bits of `.x0`) by both `b1` (low 16 bits of `.x1`) and `b2`
(low 16 bits of `.x2`), returning `(mul2U16 a b1 b2).1` in the low 16 bits of `.x0`
and `(mul2U16 a b1 b2).2` in the low 16 bits of `.x1`. -/
def mul2U16Spec (b : BitVec 64) : Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝ ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s.sp 0x40
  post := fun (a, b1, b2) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
      BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
      sf.trace = s0.trace⌝ ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s0.sp 0x40

theorem mul2U16_ok (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mul2U16Name)
      (mul2U16Spec b) := by
  have hfn : libsignalSessionCode.fnOff mul2U16Name = 0x5e614 := mul2U16_fnOff
  have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mul2U16Name + BitVec.ofNat 64 664)
      (unacceleratedMulSpec b) :=
    sub_ok_at_of_fnAddr (unacceleratedMul_ok b ext) mul2U16Name 664
      (by rw [mul2U16_fnOff, unacceleratedMul_fnOff])
  code_fetches CryptoVerification.libsignalSessionCode mul2U16Bin b
    (Rust.withPanics ext) hfn 0x5e614 52
  code_fetches_range CryptoVerification.libsignalSessionCode mul2U16Bin b
    (Rust.withPanics ext) hfn 0x5e614 0xe4 56
  dsimp only [tripleRatchetProgAtExt] at ⊢ hmul
  clear hfn
  simp only [mul2U16Spec]
  wp_init args s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr mul2U16Name := by
    rw [Program.fnAddr_rebase, mul2U16_fnOff]; exact hpc
  clear hpc
  have hadrp1 := fnAddr_adrp_63a20 (H := Rust.withPanics ext) h_1
  have hadrp2 := fnAddr_adrp_63a30 (H := Rust.withPanics ext) h_1
  have halign := aligned_86bd8 b h_1
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr mul2U16Name = entry
  examples_hide_fetches
  wp_simp_pre [stackAt_64_split, tokenInitAt]
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
  wp_call hmul
  wp_steps
  wp_call hmul
  wp_steps
  apply SepWP.fold
    (stackAt_64_merge s0.sp
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus)
  apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
  wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `381`) -/

/-- Relocatable precondition on `check_accelerated::TOKEN` (`lsρ tokenName + 8#64`) and
`use_accelerated::STORAGE.0` (`lsρ tokenStorageName`) selecting the unaccelerated GF(2¹⁶) path. -/
def tokenInitPlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ tokenStorageName ↦₈ 0#8) ∗
  ((lsρ tokenName + 8#64) ↦₃₂ 0#32)

theorem tokenInitPlacedAt_fold [LibsignalPlacement] :
    (lsρ tokenStorageName ↦₈ 0#8) ∗
    ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ⊢
    tokenInitPlacedAt :=
  Entails.refl _

private def lsDataAlign8 (sym : String) : Bool :=
  match lsroFind sym with
  | some d => decide (d.align = 8)
  | none => false

private theorem token_align8_mod [LibsignalPlacement] :
    (lsρ tokenName).toNat % 8 = 0 := by
  have hchk : lsDataAlign8 tokenName = true := by decide +kernel
  unfold lsDataAlign8 at hchk
  cases hf : lsroFind tokenName with
  | none => simp [hf] at hchk
  | some d =>
    simp only [hf, decide_eq_true_eq] at hchk
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hf
    have hd := (blkPlaceable_381.data_ok d hmem).2.2.1
    rw [hsym, hchk] at hd
    simpa using hd

private theorem mask3_add8_of_mask7 (x : BitVec 64) (hx : x &&& 7#64 = 0#64) :
    (x + 8#64) &&& 3#64 = 0#64 := by
  revert hx; bv_bits

theorem aligned_tokenOnce_placed [LibsignalPlacement] :
    MemWidth.isAligned .W32 (lsρ tokenName + 8#64) = true := by
  have hmod : (lsρ tokenName &&& 7#64).toNat = 0 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact token_align8_mod
  have hand : lsρ tokenName &&& 7#64 = 0#64 := BitVec.eq_of_toNat_eq hmod
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact mask3_add8_of_mask7 (lsρ tokenName) hand

/-- Relocatable specification of `spqr::encoding::gf::mul2_u16` (Block `381`) under
`tokenInitPlacedAt`. -/
def mul2U16PlacedSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp 0x40
  post := fun (a, b1, b2) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
      BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
      sf.trace = s0.trace⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp 0x40

/-- Relocatable `spqr::encoding::gf::mul2_u16` (Block `381`, calling Block `384`) meets
`withLsCodeLoaded lsmpl mul2U16PlacedSpec` under `[LibsignalPlacement]`. -/
theorem mul2U16_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (blkPl_381).base
      (withLsCodeLoaded lsmpl mul2U16PlacedSpec) := by
  have hmul0 : subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (lsmpl.base 384)
      unacceleratedMulPlacedSpec :=
    unacceleratedMul_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_381).rebase (blkPl_381).base H) hmul0
  simp only [withLsCl, unacceleratedMulPlacedSpec] at hmul
  simp only [withLsCodeLoaded, mul2U16PlacedSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_64_split, tokenInitPlacedAt]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_381).base + 236#64)
  wp_steps 6
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact blkPC_381_rebase_fetch_0x1c (blkPl_381).base H
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
  wp_call hmul
  wp_steps
  wp_call hmul
  wp_steps
  apply SepWP.fold
    (stackAt_64_merge s0.sp
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus)
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_done

end CryptoVerification.SpqrV1.GF.Mul2U16
