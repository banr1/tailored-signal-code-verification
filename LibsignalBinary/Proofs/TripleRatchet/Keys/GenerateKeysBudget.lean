/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `<MessageKeyGenerator>::generate_keys`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`generateKeysSpec` and
`generateKeysSpecX`) for `<MessageKeyGenerator>::generate_keys`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HKDF (hkdfExpand hkdfExtract whisperMessageKeys)
open CryptoGames.LibsignalSession (Crypto MessageKeyGenerator ShaCompress)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_69 blkPC_69 blkPl_69 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet
  (ExpandMultiInfoGhost ExtractGhost GenerateKeysGhost expandMultiInfoSpec expandMultiInfoStack
   extHookStack extractSpec generateKeysStack generateKeysStackX hmacCoreAt
   keys_ls_hook_ok_of_mem messageKeysAt mkgAt optSaltAt spqrRecvKeyAt
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv SepWP.done_frozen SepWP.of_sepWP_lscro bv_add_neg64 bv_sub_sub_lit
   deriveMessageKeys_eq exists_unpack64_of_length_80 hkdfExtract_length' hmacCore_entails_cells
   hmacCore_split lsRustDeallocSym lt_32_18 memRegion_out_generateKeys
   messageKeysAt_generateKeys pointsToBytes_memRegion_merge_32 slt_one_eq_false_of_small
   stackAt_alloc_extract stackAt_ext_alloc
   subroutine_ok_withLsCodeRoLoaded_rodata'' vecU8At_split_32 vecU8At_split_nil
   whisperMessageKeys_length)
open CryptoVerification.LibsignalTripleRatchet.Keys.GenerateKeysFacts
  (bv_sub_add_lit' cells_sub208_14_merge cells_sub240_4_merge cells_sub272_4_merge
   cells_sub416_8_merge cells_sub496_10_merge cells_sub96_12_merge hmacCore_merge_sub416
   memRegion_24_merge memRegion_gen_merge readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open scoped CryptoVerification.LibsignalTripleRatchet.Keys
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliDeallocBudgetExternSpecWithStack subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (expandCellsBudgetPlacedAllocStack_ok expandCellsBudgetPlacedStackSpecAt
   expandMultiInfoBudgetSpec extractBudgetSpec extractSomeBudgetPlacedAllocStackSpec
   extractSomeBudgetPlacedAllocStack_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (GenerateKeysEnv generateKeysSpec generateKeysSpecWithStack generateKeysSpecX)

attribute [local simp, local arm64_norm] whisperMessageKeys_length lt_32_18 hkdfExtract_length'
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Stack-frame splits and placed call-site specs -/

theorem fnFrame_split_generateKeysAt_pre (sp : BitVec 64) {callStack : Nat}
    (hbound : 496 + callStack ≤ 2 ^ 64) :
    stackAt sp (496 + callStack) =
      stackAt (sp - 496#64) callStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 4 ∗
        cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
        cells (sp - 96#64) 12 := by
  have hsub : sp - 496#64 - BitVec.ofNat 64 callStack = sp - BitVec.ofNat 64 (496 + callStack) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hb' : sp - BitVec.ofNat 64 (496 + callStack) + BitVec.ofNat 64 callStack = sp - 496#64 := by
    rw [← hsub, BitVec.sub_add_cancel]
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (496 + callStack)) (n := callStack) (k := 496)
      (b' := sp - 496#64) (Nat.add_comm 496 callStack) hb'.symm hbound,
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 32) (k := 384) (b' := sp - 384#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 112) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 176) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 4 (by decide) :
      memRegion (sp - 416#64) 32 = cells (sp - 416#64) 4),
    (memRegion_cells (sp - 384#64) 14 (by decide) :
      memRegion (sp - 384#64) 112 = cells (sp - 384#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12),
    hsub]

theorem fnFrame_split_generateKeysAt_post (sp : BitVec 64) {callStack : Nat}
    (hbound : 496 + callStack ≤ 2 ^ 64) :
    stackAt sp (496 + callStack) =
      stackAt (sp - 496#64) callStack ∗
        cells (sp - 496#64) 10 ∗ cells (sp - 416#64) 8 ∗
        memRegion (sp - 352#64) 80 ∗ cells (sp - 272#64) 4 ∗
        cells (sp - 240#64) 4 ∗ cells (sp - 208#64) 14 ∗
        cells (sp - 96#64) 12 := by
  have hsub : sp - 496#64 - BitVec.ofNat 64 callStack = sp - BitVec.ofNat 64 (496 + callStack) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hb' : sp - BitVec.ofNat 64 (496 + callStack) + BitVec.ofNat 64 callStack = sp - 496#64 := by
    rw [← hsub, BitVec.sub_add_cancel]
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (496 + callStack)) (n := callStack) (k := 496)
      (b' := sp - 496#64) (Nat.add_comm 496 callStack) hb'.symm hbound,
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 64) (k := 352) (b' := sp - 352#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 352#64) (n := 80) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 32) (k := 240) (b' := sp - 240#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 32) (k := 208) (b' := sp - 208#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 112) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = cells (sp - 496#64) 10),
    (memRegion_cells (sp - 416#64) 8 (by decide) :
      memRegion (sp - 416#64) 64 = cells (sp - 416#64) 8),
    (memRegion_cells (sp - 272#64) 4 (by decide) :
      memRegion (sp - 272#64) 32 = cells (sp - 272#64) 4),
    (memRegion_cells (sp - 240#64) 4 (by decide) :
      memRegion (sp - 240#64) 32 = cells (sp - 240#64) 4),
    (memRegion_cells (sp - 208#64) 14 (by decide) :
      memRegion (sp - 208#64) 112 = cells (sp - 208#64) 14),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12),
    hsub]

def extractSomeBudgetPlacedStackSpecAt (F : ShaCompress) (pl : Obj.MultiPlacement)
    (callStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, sv, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack
  post := fun (ret, saltA, sv, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (ret ↦ₛ hkdfExtract F (some sv) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some sv) ikm) [] ∗
      (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack

theorem extractSomeBudgetPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpec C.F))) :
    subroutine_ok prog addr (extractSomeBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractSomeBudgetPlacedAllocStack_ok (C := C) hext) ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomeBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, saltA, sv, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractSomeBudgetPlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractSomeBudgetPlacedAllocStackSpec,
      extractSomeBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

def extractNoneBudgetPlacedStackSpecAt (F : ShaCompress) (pl : Obj.MultiPlacement)
    (callStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack

theorem extractNoneBudgetPlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpec C.F))) :
    subroutine_ok prog addr (extractNoneBudgetPlacedStackSpecAt C.F pl allocHookStack) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, 0#64, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const, true_or,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved, extractSpec,
      ExtractGhost.prk, optSaltAt, extractNoneBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

theorem extractNoneBudgetPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpec C.F))) :
    subroutine_ok prog addr (extractNoneBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractNoneBudgetPlacedAllocStack_ok (C := C) hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractNoneBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractNoneBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

def extractEmptyBudgetPlacedStackSpecAt (F : ShaCompress) (pl : Obj.MultiPlacement)
    (callStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x2 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack

theorem extractEmptyBudgetPlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpec C.F))) :
    subroutine_ok prog addr (extractEmptyBudgetPlacedStackSpecAt C.F pl allocHookStack) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx2, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, s0.readReg64 .x1, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Or.inr hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved, extractSpec,
      ExtractGhost.prk, optSaltAt, extractEmptyBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm⟩, by arm64_sep_close⟩

theorem extractEmptyBudgetPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractBudgetSpec C.F))) :
    subroutine_ok prog addr (extractEmptyBudgetPlacedStackSpecAt C.F pl extHookStack) := by
  refine subroutine_ok_map (extractEmptyBudgetPlacedAllocStack_ok (C := C) hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractEmptyBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractEmptyBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem expandCellsBudgetPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoBudgetSpec C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsBudgetPlacedStackSpecAt C.F pl n extHookStack) := by
  refine subroutine_ok_map (expandCellsBudgetPlacedAllocStack_ok (C := C) hexp n hn) ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsBudgetPlacedStackSpecAt] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [expandCellsBudgetPlacedStackSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandCellsBudgetPlacedStackSpecAt] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

def deallocGenBudgetPlacedStackSpecAt [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (pl : Obj.MultiPlacement) (callStack : Nat) :
    Spec (BitVec 64 × Nat × Nat × BitVec 64 × M.σ) where
  pre := fun (p, size, align, sp, st) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ 0 < size ∧ size < 2 ^ 63 ∧ align = 1 ∧
      s.sp = sp ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.repAlloc.live p size align ∗ memRegion p size ∗ stackAt sp callStack
  post := fun (_, size, align, sp, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt sp callStack

theorem deallocGenBudgetPlacedAllocStack_of_rustCliDealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {addr : BitVec 64}
    (hd : subroutine_ok prog addr (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog addr (deallocGenBudgetPlacedStackSpecAt M A lim pl allocHookStack) := by
  have hd_ext : subroutine_ok prog addr
      (rustCliDeallocBudgetExternSpecWithStack M A lim allocHookStack) :=
    subroutine_ok_rustCliDeallocBudget_externWithStack (stk := allocHookStack)
      (by decide) (by decide) hd
  refine subroutine_ok_map hd_ext ?_
  rintro ⟨p, size, align, sp, st⟩ R s0 hpre
  dsimp only [deallocGenBudgetPlacedStackSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx2, hpos, _hlt, halign, hsp, hlr⟩, hpre⟩
  subst hsp
  have hrl : LibsignalBinary.Heap.RustLayoutOk size align := by
    subst halign
    exact ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  refine ⟨(p, size, align, st), R, ?_, ?_⟩
  · dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hrl, hlr⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      deallocGenBudgetPlacedStackSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, hpost⟩

theorem deallocGenBudgetPlacedExtStack_of_rustCliDeallocExtern [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {addr : BitVec 64}
    (hd : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok prog addr (deallocGenBudgetPlacedStackSpecAt M A lim pl extHookStack) := by
  refine subroutine_ok_map hd ?_
  rintro ⟨p, size, align, sp, st⟩ R s0 hpre
  dsimp only [deallocGenBudgetPlacedStackSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hpos, _hlt, halign, hsp, hlr⟩, hpre⟩
  subst hsp
  have hrl : LibsignalBinary.Heap.RustLayoutOk size align := by
    subst halign
    exact ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  refine ⟨(p, size, align, st), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hrl, hlr⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      deallocGenBudgetPlacedStackSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, hpost⟩

/-! ## Relocatable budget proofs -/

private theorem sepWP_mono_post {prog : Program} {target : BitVec 64} {s : State}
    {P Frame_init : SepProp} {Post₁ Post₂ : State → SepProp}
    {Rest : State → Prop} {oom : State → SepProp}
    (himp : ∀ sf, (sf.mem ⊨ Post₁ sf) → (sf.mem ⊨ Post₂ sf))
    (hwp : SepWP prog target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Frame_init → sf.mem ⊨ Post₁ sf) ∧ Rest sf) oom) :
    SepWP prog target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Frame_init → sf.mem ⊨ Post₂ sf) ∧ Rest sf) oom :=
  SepWP.mono hwp fun sf _ _ _ ⟨hp, hrest⟩ => ⟨fun hm => himp sf (hp hm), hrest⟩

private theorem sepWP_witness_generateKeysPost {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {prog : Program} {target : BitVec 64} {s0 s : State}
    {P Frame_init R : SepProp} {Rest : State → Prop} {oom : State → SepProp}
    {roA : BitVec 64} {roB : List (BitVec 8)}
    {x : GenerateKeysGhost} {st : M.σ} {totalStack : Nat}
    (evs₀ : List AllocEvent) (hEnv : GenerateKeysEnv x evs₀)
    (hwp : SepWP prog target s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Frame_init →
          sf.mem ⊨ ((roA ↦ᵣ roB) ∗
            (⌜sf.trace = s0.trace⌝ ∗ memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
              messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
              A.pool lim (M.stepEvents evs₀ st) sf ∗ stackAt s0.sp totalStack)) ∗ R) ∧
        Rest sf) oom) :
    SepWP prog target s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Frame_init →
          sf.mem ⊨ ((roA ↦ᵣ roB) ∗
            (generateKeysSpecWithStack M A lim F totalStack).post (x, st) s0 sf) ∗ R) ∧
        Rest sf) oom := by
  refine sepWP_mono_post (fun sf h1 => ?_) hwp
  dsimp only [generateKeysSpecWithStack]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at h1 ⊢
  refine ⟨evs₀, ?_⟩
  rw [sepConj_left_comm (roA ↦ᵣ roB), satisfies_pure_sepConj] at h1 ⊢
  exact ⟨⟨h1.1, hEnv⟩, h1.2⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 6000000 in
/-- Relocatable stack-parameterized budget `<MessageKeyGenerator>::generate_keys` (Block `69`). -/
theorem generateKeys_placed_ok_of_hooks_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks} {callStack : Nat}
    (hbound : 496 + callStack ≤ 2 ^ 64)
    (hext_none : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (extractNoneBudgetPlacedStackSpecAt C.F lsmpl callStack))
    (hext_empty : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (extractEmptyBudgetPlacedStackSpecAt C.F lsmpl callStack))
    (hext_some : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (extractSomeBudgetPlacedStackSpecAt C.F lsmpl callStack))
    (hexp_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 53)
      (expandCellsBudgetPlacedStackSpecAt C.F lsmpl 10 callStack))
    (hdealloc : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym)
      (deallocGenBudgetPlacedStackSpecAt M A lim lsmpl callStack)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecWithStack M A lim C.F (496 + callStack))) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.168")
    (roBytes := whisperMessageKeys) (by decide) ?_
  wp_init xst s0
  have hexp' := hexp_raw
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear hexp_raw
  obtain ⟨⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩, st⟩ := xst
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeysAt_pre s0.sp hbound]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A.repAlloc (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_pos : 0 < seed_cap.toNat := by omega
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A.repAlloc (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_lscro hF0
      wp_steps_sync_pool (lsmpl.base 54)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps_sync_pool (lsmpl.base 53)
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      apply SepWP.of_sepWP_lscro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF3
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64, st)
        wp_extract_exists
        wp_steps_sync_pool (s0.readReg64 .lr)
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        have hEnv : GenerateKeysEnv
            ⟨s0.readReg64 (.gpr 0#5), ⟨seed, counter⟩,
              s0.readReg64 (.gpr 1#5), none, s0.readReg64 (.gpr 8#5)⟩
            (rustDeallocEvents seed_cap.toNat 1) :=
          ⟨seed_cap.toNat, hseed_le, hseed_small, Or.inl rfl⟩
        apply sepWP_witness_generateKeysPost (rustDeallocEvents seed_cap.toNat 1) hEnv
        dsimp only
        rw [fnFrame_split_generateKeysAt_post s0.sp hbound,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        have hpqr_pos : 0 < pqr_cap.toNat :=
          Nat.pos_of_ne_zero fun h0 => hpqr_cap0 (BitVec.eq_of_toNat_eq (by simpa using h0))
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        apply SepWP.of_sepWP_lscro hF3
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64, st)
        wp_extract_exists
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
        intro hF4
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64,
          M.stepEvents (rustDeallocEvents seed_cap.toNat 1) st)
        wp_extract_exists
        wp_steps_sync_pool (s0.readReg64 .lr)
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        have hEnv : GenerateKeysEnv
            ⟨s0.readReg64 (.gpr 0#5), ⟨seed, counter⟩,
              s0.readReg64 (.gpr 1#5), none, s0.readReg64 (.gpr 8#5)⟩
            (rustDeallocEvents seed_cap.toNat 1 ++ rustDeallocEvents pqr_cap.toNat 1) :=
          ⟨seed_cap.toNat, hseed_le, hseed_small,
            Or.inr ⟨pqr_cap.toNat, hpqr_pos, hpqr_small, rfl⟩⟩
        apply sepWP_witness_generateKeysPost
          (rustDeallocEvents seed_cap.toNat 1 ++ rustDeallocEvents pqr_cap.toNat 1) hEnv
        dsimp only
        rw [fnFrame_split_generateKeysAt_post s0.sp hbound, M.stepEvents_append,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
        wp_done
    · wp_simp_pre_fast [↓reduceIte, noneCap,
        (memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_lscro hF0
      wp_steps_sync_pool (lsmpl.base 54)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_lscro hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps_sync_pool (lsmpl.base 53)
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      apply SepWP.of_sepWP_lscro hF2
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF3
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64, st)
      wp_extract_exists
      wp_steps_sync_pool (s0.readReg64 .lr)
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      have hEnv : GenerateKeysEnv
          ⟨s0.readReg64 (.gpr 0#5), ⟨seed, counter⟩,
            s0.readReg64 (.gpr 1#5), none, s0.readReg64 (.gpr 8#5)⟩
          (rustDeallocEvents seed_cap.toNat 1) :=
        ⟨seed_cap.toNat, hseed_le, hseed_small, Or.inl rfl⟩
      apply sepWP_witness_generateKeysPost (rustDeallocEvents seed_cap.toNat 1) hEnv
      dsimp only
      rw [fnFrame_split_generateKeysAt_post s0.sp hbound,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
      wp_done
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A.repAlloc (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_pos : 0 < pqr_cap.toNat := by omega
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_lscro hF0
    wp_steps_sync_pool (lsmpl.base 54)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_lscro hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps_sync_pool (lsmpl.base 53)
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    apply SepWP.of_sepWP_lscro hF2
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      lsmpl.ρ "libsignal_protocol:.rodata..Lanon.168", whisperMessageKeys,
      s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF3
    apply SepWP.of_sepWP_lscro hF3
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64, st)
    wp_extract_exists
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF4
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64,
      M.stepEvents (rustDeallocEvents seed_cap.toNat 1) st)
    wp_extract_exists
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    have hEnv : GenerateKeysEnv
        ⟨s0.readReg64 (.gpr 0#5), ⟨seed, counter⟩,
          s0.readReg64 (.gpr 1#5), some sv, s0.readReg64 (.gpr 8#5)⟩
        (rustDeallocEvents seed_cap.toNat 1 ++ rustDeallocEvents pqr_cap.toNat 1) :=
      ⟨seed_cap.toNat, hseed_le, hseed_small,
        pqr_cap.toNat, hpqr_le, hpqr_small, rfl⟩
    apply sepWP_witness_generateKeysPost
      (rustDeallocEvents seed_cap.toNat 1 ++ rustDeallocEvents pqr_cap.toNat 1) hEnv
    dsimp only
    rw [fnFrame_split_generateKeysAt_post s0.sp hbound, M.stepEvents_append,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_none hext_empty hext_some hexp' hdealloc hprk hokm hgood
    wp_done

/-- Contract-backed relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`). -/
theorem generateKeys_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)) :=
  generateKeys_placed_ok_of_hooks_gen (callStack := allocHookStack) (by decide)
    (extractNoneBudgetPlacedAllocStack_ok (C := C) hext)
    (extractEmptyBudgetPlacedAllocStack_ok (C := C) hext)
    (extractSomeBudgetPlacedAllocStack_ok (C := C) hext)
    (expandCellsBudgetPlacedAllocStack_ok (C := C) hexp 10 (by decide))
    (deallocGenBudgetPlacedAllocStack_of_rustCliDealloc (pl := lsmpl) hdealloc_raw)

/-- Relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`) from callee contracts
and `HookSat` hypotheses. -/
theorem generateKeys_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)) :=
  generateKeys_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Contract-backed relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`)
at `generateKeysStackX` (`extHookStack`). -/
theorem generateKeys_placed_ok_of_contracts_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoBudgetSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX M A lim C.F)) :=
  generateKeys_placed_ok_of_hooks_gen (callStack := extHookStack) (by decide)
    (extractNoneBudgetPlacedExtStack_ok (C := C) hext)
    (extractEmptyBudgetPlacedExtStack_ok (C := C) hext)
    (extractSomeBudgetPlacedExtStack_ok (C := C) hext)
    (expandCellsBudgetPlacedExtStack_ok (C := C) hexp 10 (by decide))
    (deallocGenBudgetPlacedExtStack_of_rustCliDeallocExtern hdealloc_raw)

theorem subroutine_ok_generateKeysSpecX_of_generateKeysSpec {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (generateKeysSpec M A lim F))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (generateKeysSpecX M A lim F)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hstk : stackAt s0.sp generateKeysStackX =
      stackAt s0.sp generateKeysStack ∗ memRegion (s0.sp - 16880#64) 12288 := by
    change memRegion (s0.sp - BitVec.ofNat 64 16880) 16880 =
      memRegion (s0.sp - BitVec.ofNat 64 generateKeysStack) generateKeysStack ∗
        memRegion (s0.sp - 16880#64) 12288
    rw [sepConj_comm]
    exact ProofLib.memRegion_split' (b := s0.sp - 16880#64) (n := 12288) (k := generateKeysStack)
      (b' := s0.sp - 4592#64) rfl (by bv_omega) (by decide)
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (generateKeysSpec M A lim F)).pre x s0 ∗
        (memRegion (s0.sp - 16880#64) 12288 ∗ R) := by
    dsimp only [withLsCodeRoLoaded, generateKeysSpecX, generateKeysSpec,
      generateKeysSpecWithStack] at hpre ⊢
    rw [hstk] at hpre
    convert hpre using 1; sep_ac_rfl
  refine h.mono_outcome x (memRegion (s0.sp - 16880#64) 12288 ∗ R) s0 hpc hrun hpre' hsp
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, generateKeysSpecX, generateKeysSpec,
      generateKeysSpecWithStack] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [hstk]
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, generateKeysSpec, generateKeysSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, generateKeysSpec, generateKeysSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, generateKeysSpec, generateKeysSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable budget `<MessageKeyGenerator>::generate_keys` (Block `69`) at `generateKeysStackX`. -/
theorem generateKeys_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hext : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractBudgetSpec C.F)))
    (hexp : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoBudgetSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_69).rebase (blkPl_69).base H) (blkPl_69).base
      (withLsCodeRoLoaded lsmpl (generateKeysSpecX M A lim C.F)) :=
  subroutine_ok_generateKeysSpecX_of_generateKeysSpec
    (generateKeys_placed_ok hext hexp h_dealloc)

end LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
