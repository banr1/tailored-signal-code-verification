/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.Apply

/-!
# `HookSat`-backed `subtle::black_box::<u8>`, `ct_eq` (Block `213`), and `PublicKey::eq` (Block `212`)

Defines the honest 16-byte stack + `VmPreserved` contract `blackBoxSpecSat` for
`subtle::black_box::<u8>` (`sub sp, sp, #16; strb; ldrb; add sp, sp, #16; ret`), proves that
`LibsignalSession.blackBoxHook` satisfies it (`hookSat_blackBox_of_eq`), and derives relocatable
`[LibsignalPlacement]` contracts for Block `213` (`<[u8] as ConstantTimeEq>::ct_eq`) and
Block `212` (`<PublicKey as PartialEq>::eq`) under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkLib_eq_212 blkLib_eq_213 blkPC_212 blkPC_213 blkPl_212
   blkPl_213 libsignalSessionImage lsBlackBoxU8Sym ls_externAt?_of_mem ls_subroutine_ok_of_block
   lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open LibsignalBinary.Heap (VmPreserved VmPreserved.refl VmPreserved.trans)
open LibsignalBinary.Heap.SpecBudget
  (hookSat_of_withVmPreserved hookSat_withVmPreserved subroutine_ok_of_withVmPreserved
   withVmPreserved)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (ctEqFrame_entails_ext32 ctEqSliceSpecExt ctEq_pre_rearrange_ext32 ct_eq_bool_32_u8_ext32
   extHookStack32 fnFrameBytes_ctEqName_ext32 fnFrameBytes_publicKeyEqName_ext32
   ite_one_zero_and_8_ext32 ite_one_zero_and_one_8_ext32 pointsToBytes32
   pointsToBytes_eq_pointsToBytes32 publicKeyEqSpecExt publicKey_ite_toList_eq
   setWidth32_and_4294967297_ext32 setWidth8_and32_ext32 setWidth8_and64_ext32
   setWidth8_ite_1_0_32_ext32 setWidth8_ite_prop_1_0_ext32 setWidth8_setWidth32_ext32
   setWidth8_zext64_32_ext32 sp_sub48_aligned_ext32 stackFrameFor_ctEq_eq_cells_ext32
   stackFrameFor_ctEq_eq_memRegion_ext32 stackFrameFor_eq_eq_memRegion_ext32)
open CryptoVerification.LibsignalTripleRatchet (blackBoxHook_ok blackBoxSpec withStack)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap.Fine (blackBoxHook_vmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

/-! ## 1. Honest `black_box::<u8>` Contract (`blackBoxSpecSat`) & Bridges -/

/-- 16-byte stack-framed `subtle::black_box::<u8>` contract (`withStack blackBoxSpec 16`). -/
@[expose] def blackBoxSpec16 : Spec (BitVec 64) :=
  withStack blackBoxSpec 16

/-- Honest `subtle::black_box::<u8>` contract (`withVmPreserved (withStack blackBoxSpec 16)`):
owns 16 B below `sp`, sets 64-bit `x0 = (v.setWidth 8).zeroExtend 64`, and preserves `VmPreserved`,
`trace`, `d8..d15` (`calleeSavedVRegs`), and `x19..x29`. -/
@[expose] def blackBoxSpecSat : Spec (BitVec 64) :=
  withVmPreserved blackBoxSpec16

/-- `LibsignalSession.blackBoxHook` meets `blackBoxSpec16`. -/
theorem blackBoxHook_ok_16 : HookOk blackBoxHook blackBoxSpec16 :=
  hookOk_withStack blackBoxHook_ok 16

/-- `LibsignalSession.blackBoxHook` meets `blackBoxSpecSat`. -/
theorem blackBoxHook_ok_sat : HookOk blackBoxHook blackBoxSpecSat := by
  intro v R s0 hrun hpre hsp
  rcases blackBoxHook_ok_16 v R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [blackBoxSpecSat, withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨blackBoxHook_vmPreserved s0, hpost⟩
  · exact Or.inr hrest

/-- Lift an exact `H sym = some blackBoxHook` assumption to `HookSat H sym blackBoxSpecSat`. -/
theorem hookSat_blackBox_of_eq {H : String → Option (State → State)} {sym : String}
    (h : H sym = some blackBoxHook) :
    HookSat H sym blackBoxSpecSat :=
  ⟨blackBoxHook, h, blackBoxHook_ok_sat⟩

/-- Forget `VmPreserved` from `blackBoxSpecSat` to `blackBoxSpec16`. -/
theorem hookSat_blackBox16_of_sat {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym blackBoxSpecSat) :
    HookSat H sym blackBoxSpec16 :=
  hookSat_of_withVmPreserved h

/-- Widen `blackBoxSpecSat` (`16` B stack) to any `withVmPreserved (withStack blackBoxSpec n)`
with `16 ≤ n ≤ 2 ^ 64`. -/
theorem hookSat_blackBox_withStack_vm_of_sat {H : String → Option (State → State)} {sym : String}
    {n : Nat} (h : HookSat H sym blackBoxSpecSat)
    (hle : 16 ≤ n := by decide) (hmax : n ≤ 2 ^ 64 := by decide) :
    HookSat H sym (withVmPreserved (withStack blackBoxSpec n)) := by
  refine ProofLib.HookSat.mono h fun v R s0 hpre => ?_
  have hsplit : stackAt s0.sp n =
      memRegion (s0.sp - BitVec.ofNat 64 n) (n - 16) ∗ stackAt s0.sp 16 := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp 16 (n - 16) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  refine ⟨v, memRegion (s0.sp - BitVec.ofNat 64 n) (n - 16) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withVmPreserved, blackBoxSpecSat, blackBoxSpec16, withStack] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1; sep_ac_rfl
  · dsimp only [withVmPreserved, blackBoxSpecSat, blackBoxSpec16, withStack] at hpost ⊢
    rw [hsplit]
    convert hpost using 1; sep_ac_rfl

/-- Widen `blackBoxSpecSat` (`16` B stack) to `withStack blackBoxSpec n` (`16 ≤ n ≤ 2 ^ 64`). -/
theorem hookSat_blackBox_withStack_of_sat {H : String → Option (State → State)} {sym : String}
    {n : Nat} (h : HookSat H sym blackBoxSpecSat)
    (hle : 16 ≤ n := by decide) (hmax : n ≤ 2 ^ 64 := by decide) :
    HookSat H sym (withStack blackBoxSpec n) :=
  hookSat_of_withVmPreserved (hookSat_blackBox_withStack_vm_of_sat h hle hmax)

/-! ## 2. Tight `+16 B` Specs for Block `213` (`ct_eq`) and Block `212` (`PublicKey::eq`) -/

/-- `ctEqSliceSpec` extended with `16` B below `ct_eq`'s 48-byte frame (`64` B total),
returning full 64-bit `sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64)`. -/
@[expose] noncomputable def ctEqSliceSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
    stackAt (sp - 48#64) 16
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
    stackAt (sp - 48#64) 16

/-- `VmPreserved`-strengthened `ctEqSliceSpec16`. -/
@[expose] noncomputable def ctEqSliceBudgetSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceSpec16

/-- Image-free `ct_eq` contract with `memRegion (sp - 64#64) 64` (`48 + 16` B). -/
@[expose] def ctEqSliceMemSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 64#64) 64
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 64#64) 64

/-- `VmPreserved`-strengthened `ctEqSliceMemSpec16`. -/
@[expose] def ctEqSliceMemBudgetSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceMemSpec16

/-- `publicKeyEqSpec` extended with `16` B below `ct_eq`'s frame (`sp - 64`, `80` B total). -/
@[expose] noncomputable def publicKeyEqSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
    stackAt (sp - 64#64) 16
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
    stackAt (sp - 64#64) 16

/-- `VmPreserved`-strengthened `publicKeyEqSpec16`. -/
@[expose] noncomputable def publicKeyEqBudgetSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqSpec16

/-- Image-free `PublicKey::eq` contract with `memRegion (sp - 80#64) 80` (`16 + 48 + 16` B). -/
@[expose] def publicKeyEqMemSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ memRegion (sp - 80#64) 80
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ memRegion (sp - 80#64) 80

/-- `VmPreserved`-strengthened `publicKeyEqMemSpec16`. -/
@[expose] def publicKeyEqMemBudgetSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqMemSpec16

/-! ## 3. Stepping Helpers & Block `213` (`ct_eq`) Proof under `blackBoxSpecSat` -/

theorem ctEqFrame_sepConj_stackAt_16 (sp : BitVec 64) :
    stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
      stackAt (sp - 48#64) 16 =
    stackAt sp 16 ∗ memRegion (sp - 64#64) 48 := by
  rw [stackFrameFor_ctEq_eq_cells_ext32, sepConj_comm]
  have h1 := (ProofLib.stackAt_split_cells sp 16 6 (by decide)).symm
  have h2 := ProofLib.stackAt_split_bottom sp 16 48 (by decide)
  have h3 : BitVec.ofNat 64 (16 + 48) = 64#64 := rfl
  rw [h3] at h2
  rw [h1, h2, sepConj_comm]

theorem memRegion_64_eq_ctEqFrame_16 (sp : BitVec 64) :
    memRegion (sp - 64#64) 64 =
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
      stackAt (sp - 48#64) 16 := by
  rw [← stackFrameFor_ctEq_eq_memRegion_ext32 sp]
  simp only [stackAt]
  have hsub : sp - 48#64 - BitVec.ofNat 64 16 = sp - 64#64 := by bv_omega
  rw [hsub, ProofLib.memRegion_split' (b := sp - 64#64) (n := 16) (k := 48)
    (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
  sep_ac_rfl

theorem memRegion_80_eq_publicKeyEqFrame_16 (sp : BitVec 64) :
    memRegion (sp - 80#64) 80 =
      stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) ∗
      stackAt (sp - 64#64) 16 := by
  rw [← stackFrameFor_eq_eq_memRegion_ext32 sp,
      ← stackFrameFor_ctEq_eq_memRegion_ext32 (sp - 16#64)]
  simp only [stackAt]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  have h80 : sp - 64#64 - BitVec.ofNat 64 16 = sp - 80#64 := by bv_omega
  rw [h64, h80,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 16) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  sep_ac_rfl

private theorem low8_of_zext64 {w v : BitVec 64}
    (h : w = (v.setWidth 8).zeroExtend 64) :
    w.setWidth 8 = v.setWidth 8 := by
  subst h; bv_bits

private theorem zeroExtend64_ite_prop_1_0_8 (P : Prop) [Decidable P] :
    BitVec.zeroExtend 64 (if P then 1#8 else 0#8) = if P then 1#64 else 0#64 := by
  split <;> rfl

/-- Context-clearing step lemma for calls 1..32 to `subtle::black_box::<u8>` inside `ct_eq`
under `blackBoxSpecSat`. -/
theorem step_blackBox_sat
    {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s0 s : State} {sp_cur x19_v x20_v : BitVec 64}
    {x0_v x19_8_v x21_8_v x22_8_v : BitVec 8}
    {R_rest : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb blackBoxSpecSat)
    (hal_cur : (sp_cur &&& 15#64 == 0#64) = true)
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hlr : s.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x19_v)
    (hx19_8 : (s.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x20_v)
    (hx21_8 : (s.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v)
    (hx22_8 : (s.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = sp_cur)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp_cur →
      (sf.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v →
      sf.readReg64 (Reg.gpr 19#5) = x19_v →
      (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v →
      sf.readReg64 (Reg.gpr 20#5) = x20_v →
      (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v →
      (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v →
      sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) →
      sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) →
      sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) →
      sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) →
      sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) →
      sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sf.readReg64 (Reg.gpr 29#5) = sp_cur →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.trace = s0.trace →
      VmPreserved s0 sf →
      SepWP prog target_pc sf (stackAt sp_cur 16 ∗ R_rest) post) :
    SepWP prog target_pc s (stackAt sp_cur 16 ∗ R_rest) post := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0) (F := R_rest)
    hpc hrun hal hlr
    (fun R hm => by
      rw [sepConj_assoc] at hm
      dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16, withStack, blackBoxSpec]
      simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨trivial, hm⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj hpost)
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  have hcc : CallingConventionPreserved s sf := ⟨hsp_eq, hcs⟩
  dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16, withStack, blackBoxSpec]
  simp only [hsp, sepConj_assoc]
  apply SepWP.pure_elim
  intro hvm_bb
  apply SepWP.pure_elim
  rintro ⟨hx0_sf64, htr_sf⟩
  have hx0_sf : (sf.readReg64 .x0).setWidth 8 = (s.readReg64 .x0).setWidth 8 :=
    low8_of_zext64 hx0_sf64
  have hsp_sf : sf.sp = sp_cur := hcc.1.trans hsp
  have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = x19_v := hcc.2.1.trans hx19
  have hx19_8_sf : (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v := by
    change (sf.readReg64 .x19).setWidth 8 = x19_8_v
    rw [hcc.2.1]; exact hx19_8
  have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = x20_v := hcc.2.2.1.trans hx20
  have hx21_8_sf : (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v := by
    change (sf.readReg64 .x21).setWidth 8 = x21_8_v
    rw [hcc.2.2.2.1]; exact hx21_8
  have hx22_8_sf : (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v := by
    change (sf.readReg64 .x22).setWidth 8 = x22_8_v
    rw [hcc.2.2.2.2.1]; exact hx22_8
  have hx23_sf : sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) := hcc.2.2.2.2.2.1.trans hx23
  have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) := hcc.2.2.2.2.2.2.1.trans hx24
  have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := hcc.2.2.2.2.2.2.2.1.trans hx25
  have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hcc.2.2.2.2.2.2.2.2.1.trans hx26
  have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hcc.2.2.2.2.2.2.2.2.2.1.trans hx27
  have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx28
  have hx29_sf : sf.readReg64 (Reg.gpr 29#5) = sp_cur := hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
  exact hnext sf hret_pc hret_run hsp_sf
    (hx0_sf.trans hx0) hx19_sf hx19_8_sf hx20_sf hx21_8_sf hx22_8_sf
    hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf hvregs_sf
    (htr_sf.trans htr) (hvm.trans hvm_bb)

/-- Tail-call (`b black_box`) step lemma for Call 33 of `ct_eq` at `s.sp = s0.sp`,
returning 64-bit `sf.readReg64 .x0 = x0_target.zeroExtend 64` and `VmPreserved s0 sf`. -/
theorem step_blackBox_tail_sat
    {prog : Program} {entry_bb : BitVec 64}
    {s0 s : State} {x0_v x0_target : BitVec 8}
    {v0 v1 v2 v3 v4 v5 : BitVec 64}
    {R_slices S1 S2 R0 : SepProp}
    (hbb : subroutine_ok prog entry_bb blackBoxSpecSat)
    (hal_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hlr : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
    (hx21 : s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5))
    (hx22 : s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hx0_eq : x0_v = x0_target)
    (h_slices : R_slices = S1 ∗ S2) :
    SepWP prog (s0.readReg64 .lr) s
      (stackAt (s0.sp - 48#64) 16 ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
        ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
        R_slices)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R0 →
          sf.mem ⊨
            (⌜VmPreserved s0 sf⌝ ∗
              ⌜sf.readReg64 .x0 = x0_target.zeroExtend 64 ∧ sf.trace = s0.trace⌝ ∗
              S1 ∗ S2 ∗
              stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s0.sp ∗
              stackAt (s0.sp - 48#64) 16) ∗ R0) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0)
    (F := memRegion (s0.sp - 64#64) 48 ∗ R_slices)
    hpc hrun hal hlr
    (fun R hm => by
      have hm1 : s.mem ⊨
          (stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" s0.sp ∗
            stackAt (s0.sp - 48#64) 16) ∗ (R_slices ∗ R) := by
        have hrearr :
            (stackAt (s0.sp - 48#64) 16 ∗
              ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
              ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
              R_slices) ∗ R =
            (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
              ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
            (stackAt (s0.sp - 48#64) 16 ∗ (R_slices ∗ R)) := by sep_ac_rfl
        rw [hrearr] at hm
        have hm' := Satisfies.mono (sepConj_mono_left (ctEqFrame_entails_ext32 s0.sp v0 v1 v2 v3 v4 v5)) hm
        rwa [← sepConj_assoc] at hm'
      rw [ctEqFrame_sepConj_stackAt_16 s0.sp, sepConj_assoc] at hm1
      dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16, withStack, blackBoxSpec]
      simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨trivial, hm1⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj hpost)
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  have hcc : CallingConventionPreserved s sf := ⟨hsp_eq, hcs⟩
  dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16, withStack, blackBoxSpec]
  simp only [hsp, sepConj_assoc]
  apply SepWP.pure_elim
  intro hvm_bb
  apply SepWP.pure_elim
  rintro ⟨hx0_sf64, htr_sf⟩
  have hsp0 : sf.sp = s0.sp := hcc.1.trans hsp
  have hcs0 : CalleeSavedPreserved s0 sf :=
    ⟨hcc.2.1.trans hx19,
     hcc.2.2.1.trans hx20,
     hcc.2.2.2.1.trans hx21,
     hcc.2.2.2.2.1.trans hx22,
     hcc.2.2.2.2.2.1.trans hx23,
     hcc.2.2.2.2.2.2.1.trans hx24,
     hcc.2.2.2.2.2.2.2.1.trans hx25,
     hcc.2.2.2.2.2.2.2.2.1.trans hx26,
     hcc.2.2.2.2.2.2.2.2.2.1.trans hx27,
     hcc.2.2.2.2.2.2.2.2.2.2.1.trans hx28,
     hcc.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29,
     hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩
  have hx0_64 : sf.readReg64 .x0 = x0_target.zeroExtend 64 := by
    rw [hx0_sf64]
    change ((s.readReg64 (Reg.gpr 0#5)).setWidth 8).zeroExtend 64 = x0_target.zeroExtend 64
    rw [hx0, hx0_eq]
  have htr0 : sf.trace = s0.trace := htr_sf.trans htr
  have hvm0 : VmPreserved s0 sf := hvm.trans hvm_bb
  refine SepWP.done hret_pc hret_run ⟨?_, hsp0, hcs0⟩
  intro hm_post
  have hm_sf' : sf.mem ⊨
      (stackAt s0.sp 16 ∗ memRegion (s0.sp - 64#64) 48) ∗ (R_slices ∗ R0) := by
    simpa only [sepConj_assoc] using hm_post
  rw [← ctEqFrame_sepConj_stackAt_16 s0.sp, sepConj_left_comm, sepConj_assoc, h_slices,
    sepConj_assoc] at hm_sf'
  simp only [satisfies_pure_sepConj]
  exact ⟨hvm0, ⟨hx0_64, htr0⟩, by simpa only [sepConj_assoc] using hm_sf'⟩

/-! ## 4. Placed Contracts for Block `213` (`ct_eq`) and Block `212` (`PublicKey::eq`) -/

section VmStepping

attribute [local irreducible] Program.fnOff VmPreserved

attribute [local simp, local wp_norm, local arm64_norm]
  setWidth8_ite_prop_1_0_ext32 setWidth8_ite_1_0_32_ext32 setWidth8_zext64_32_ext32
  setWidth8_setWidth32_ext32 setWidth8_and64_ext32 setWidth8_and32_ext32
  ite_one_zero_and_8_ext32 setWidth32_and_4294967297_ext32 ite_one_zero_and_one_8_ext32
  fnFrameBytes_ctEqName_ext32 fnFrameBytes_publicKeyEqName_ext32

set_option hygiene false in
local macro "wp_seg_bb_213 " : tactic =>
  `(tactic| (
    apply sepWP_seg_ls_vm (Q := (blkPC_213).rebase (blkPl_213).base (hooksException H))
      blkLib_eq_213 (mid := lsρ lsBlackBoxU8Sym)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_seg : VmPreserved _ _ := _hnsp.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_seg ⊢
    have hvm_cur : VmPreserved s0 _ := hvm_bb.trans hvm_seg
    clear hvm_seg _hnsp _m_strip
  ))

set_option hygiene false in
local macro "wp_black_box_sat " hbb:ident hal:ident : tactic =>
  `(tactic| (
    refine step_blackBox_sat $hbb $hal hvm_cur
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    clear hvm_cur
    try clear _m_real
    try clear hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb hvm_bb s_bb
    intro s_bb hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb hvm_bb
  ))

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `<[u8] as ConstantTimeEq>::ct_eq`
(Block `213`) with `16` B below `ct_eq`'s 48-byte frame (`ctEqSliceBudgetSpec16`). -/
theorem ct_eq_placed_vm_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceBudgetSpec16 := by
  rcases h_bb with ⟨f_bb, hfH, hfOk⟩
  have hbb : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsρ lsBlackBoxU8Sym)
      blackBoxSpecSat :=
    subroutine_ok_of_hookOk ((ls_externAt?_of_mem).trans hfH) hfOk
  simp only [ctEqSliceBudgetSpec16, withVmPreserved, ctEqSliceSpec16]
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  have hal_sub48 : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    sp_sub48_aligned_ext32 hsp_align
  have h_slices :
      pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) k1 ∗
        pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) k2 =
      ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ k1) ∗ ((s0.readReg64 (Reg.gpr 1#5)) ↦ₛ k2) := by
    rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
        pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  rw [ctEq_pre_rearrange_ext32]
  conv =>
    arg 4
    rw [← h_slices]
    unfold pointsToBytes32
    simp only [sepConj_assoc]
  have hvm_bb : VmPreserved s0 s0 := VmPreserved.refl s0
  iterate 32 (wp_seg_bb_213; wp_black_box_sat hbb hal_sub48)
  clear hx19_bb
  wp_seg_bb_213
  conv =>
    arg 5; ext sf P_f
    rw [← zeroExtend64_ite_prop_1_0_8 (k1 = k2)]
  refine step_blackBox_tail_sat hbb hsp_align hvm_cur
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (ct_eq_bool_32_u8_ext32 h_4 h) ?_
  rw [← h_slices]
  unfold pointsToBytes32
  simp only [sepConj_assoc]

/-- Relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`)
on `ctEqSliceSpec16`. -/
theorem ct_eq_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceSpec16 :=
  subroutine_ok_of_withVmPreserved (ct_eq_placed_vm_ok_16_sat h_bb)

/-- Image-free `VmPreserved` contract for `ct_eq` (Block `213`) on `ctEqSliceMemBudgetSpec16`. -/
theorem ct_eq_mem_placed_vm_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceMemBudgetSpec16 := by
  refine subroutine_ok_map (ct_eq_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · simpa only [ctEqSliceMemBudgetSpec16, ctEqSliceBudgetSpec16, withVmPreserved,
      ctEqSliceMemSpec16, ctEqSliceSpec16, memRegion_64_eq_ctEqFrame_16 sp, sepConj_assoc]
      using hpre
  · intro sf hpost
    simpa only [ctEqSliceMemBudgetSpec16, ctEqSliceBudgetSpec16, withVmPreserved,
      ctEqSliceMemSpec16, ctEqSliceSpec16, memRegion_64_eq_ctEqFrame_16 sp, sepConj_assoc]
      using hpost

/-- Image-free contract for `ct_eq` (Block `213`) on `ctEqSliceMemSpec16`. -/
theorem ct_eq_mem_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceMemSpec16 :=
  subroutine_ok_of_withVmPreserved (ct_eq_mem_placed_vm_ok_16_sat h_bb)

private theorem setWidth32_ite_1_0_64 (P : Prop) [Decidable P] :
    BitVec.setWidth 32 (if P then 1#64 else 0#64) = if P then 1#32 else 0#32 := by
  split <;> rfl

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `ct_eq` (Block `213`) on
`withVmPreserved ctEqSliceSpecExt` (`48 + 16384` B). -/
theorem ct_eq_placed_vm_ok_ext_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withVmPreserved ctEqSliceSpecExt) := by
  refine subroutine_ok_map (ct_eq_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  have hstk : stackAt (sp - 48#64) extHookStack32 =
      memRegion ((sp - 48#64) - 16384#64) 16368 ∗ stackAt (sp - 48#64) 16 :=
    ProofLib.stackAt_split_bottom (sp - 48#64) 16 16368 (by decide)
  refine ⟨(p1, k1, p2, k2, sp), memRegion ((sp - 48#64) - 16384#64) 16368 ∗ R, ?_, ?_⟩
  · dsimp only [withVmPreserved, ctEqSliceSpecExt, ctEqSliceBudgetSpec16, ctEqSliceSpec16] at hpre ⊢
    rw [hstk] at hpre
    convert hpre using 1; sep_ac_rfl
  · intro sf hpost
    dsimp only [withVmPreserved, ctEqSliceSpecExt, ctEqSliceBudgetSpec16, ctEqSliceSpec16] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0, htr⟩, hmem⟩
    refine ⟨hvm, ⟨by rw [hx0, setWidth32_ite_1_0_64], htr⟩, ?_⟩
    rw [hstk]
    convert hmem using 1; sep_ac_rfl

/-- Relocatable `[LibsignalPlacement]` contract for `ct_eq` (Block `213`) on `ctEqSliceSpecExt`. -/
theorem ct_eq_placed_ok_ext_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceSpecExt :=
  subroutine_ok_of_withVmPreserved (ct_eq_placed_vm_ok_ext_sat h_bb)

attribute [local simp]
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_bytes_toList_length
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.and64_mask255_ite_1_0
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.csinc_eq_zero32_ite_1_0

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `<PublicKey as PartialEq>::eq`
(Block `212`) on `withLsCodeLoaded lsmpl publicKeyEqBudgetSpec16` (`80` B). -/
theorem publicKey_eq_placed_vm_ok_16_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqBudgetSpec16) := by
  simp only [withLsCodeLoaded, publicKeyEqBudgetSpec16, withVmPreserved, publicKeyEqSpec16]
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      ctEqSliceBudgetSpec16 := ct_eq_placed_vm_ok_16_sat h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, ctEqSliceBudgetSpec16, withVmPreserved, ctEqSliceSpec16] at hct
  wp_init x s0
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  have h64 : s0.sp - 16#64 - 48#64 = s0.sp - 64#64 := by bv_omega
  rw [← h64]
  apply sepWP_seq_lscl h (mid := lsmpl.base 213)
  apply sepWP_seg_ls_vm (Q := (blkPC_212).rebase (blkPl_212).base (hooksException H))
    blkLib_eq_212 (mid := lsmpl.base 213); intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_apply
  rw [publicKey_ite_toList_eq, h64] at *
  apply sepWP_seg_ls_vm (Q := (blkPC_212).rebase (blkPl_212).base (hooksException H))
    blkLib_eq_212 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
  try simp only [sepConj_assoc]
  wp_done

end VmStepping

/-- Relocatable `[LibsignalPlacement]` contract for `<PublicKey as PartialEq>::eq` (Block `212`)
on `withLsCodeLoaded lsmpl publicKeyEqSpec16` (`80` B). -/
theorem publicKey_eq_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqSpec16) := by
  refine subroutine_ok_mono (publicKey_eq_placed_vm_ok_16_sat h_bb)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, publicKeyEqBudgetSpec16, withVmPreserved] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-- Image-free `VmPreserved` contract for `PublicKey::eq` (Block `212`) on
`withLsCodeLoaded lsmpl publicKeyEqMemBudgetSpec16` (`80` B). -/
theorem publicKey_eq_mem_placed_vm_ok_16_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemBudgetSpec16) := by
  refine subroutine_ok_map (publicKey_eq_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, publicKeyEqBudgetSpec16,
      withVmPreserved, publicKeyEqMemSpec16, publicKeyEqSpec16,
      memRegion_80_eq_publicKeyEqFrame_16 sp, sepConj_assoc] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, publicKeyEqBudgetSpec16,
      withVmPreserved, publicKeyEqMemSpec16, publicKeyEqSpec16,
      memRegion_80_eq_publicKeyEqFrame_16 sp, sepConj_assoc] using hpost

/-- Image-free contract for `PublicKey::eq` (Block `212`) on
`withLsCodeLoaded lsmpl publicKeyEqMemSpec16` (`80` B). -/
theorem publicKey_eq_mem_placed_ok_16_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec16) := by
  refine subroutine_ok_mono (publicKey_eq_mem_placed_vm_ok_16_sat h_bb)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, publicKeyEqMemBudgetSpec16, withVmPreserved] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `PublicKey::eq` (Block `212`)
on `withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpecExt)` (`64 + 16384` B). -/
theorem publicKey_eq_placed_vm_ok_ext_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpecExt)) := by
  refine subroutine_ok_map (publicKey_eq_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  have hstk : stackAt (sp - 64#64) extHookStack32 =
      memRegion ((sp - 64#64) - 16384#64) 16368 ∗ stackAt (sp - 64#64) 16 :=
    ProofLib.stackAt_split_bottom (sp - 64#64) 16 16368 (by decide)
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion ((sp - 64#64) - 16384#64) 16368 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved, publicKeyEqSpecExt, publicKeyEqBudgetSpec16,
      publicKeyEqSpec16] at hpre ⊢
    rw [hstk] at hpre
    convert hpre using 1; sep_ac_rfl
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, publicKeyEqSpecExt, publicKeyEqBudgetSpec16,
      publicKeyEqSpec16] at hpost ⊢
    rw [hstk]
    convert hpost using 1; sep_ac_rfl

/-- Relocatable `[LibsignalPlacement]` contract for `PublicKey::eq` (Block `212`)
on `withLsCodeLoaded lsmpl publicKeyEqSpecExt` (`64 + 16384` B). -/
theorem publicKey_eq_placed_ok_ext_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqSpecExt) := by
  refine subroutine_ok_mono (publicKey_eq_placed_vm_ok_ext_sat h_bb)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, withVmPreserved] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
