/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# File-Descriptor-Predicated `<RootKey>::create_chain`

Threads an arbitrary `FsState → Prop` predicate `Pfs` across the `[LibsignalPlacement]`
`RustCliAllocBudget` contracts for `<RootKey>::create_chain`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (hkdfExpand hkdfExtract)
open CryptoGames.LibsignalSession (Crypto PrivateKey PublicKey ShaCompress rootCreateChain)
open CryptoGames.Ratchet (X25519Fn keyToBytesVec32 keysToBytes rootKdf whisperRatchetInfo)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_207 blkPC_40 blkPl_207 blkPl_40
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (CreateChainGhost calculateAgreement
   calculateAgreementResultAt calculateAgreementStack
   createChainResultAt createChainStack createChainStackX diffieHellmanSpec
   expandMultiInfoSpec expandMultiInfoStack extractSpec hmacCoreAt
   keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro optSaltAt
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv SepWP.done_frozen SepWP.of_sepWP_lscro
   and_ff32_hi56_3 and_ff_hi56_3 boxU8At_32_split bv_add_neg64 bv_sub_sub_lit
   calculateAgreementResult_none_cells cells3_memRegion_152_merge createChainResultAt_ok_eq
   exists_unpack64_of_length_64 extractLsb_hi56_3
   fnFrame_split_createChainAt_err fnFrame_split_createChainAt_ok fnFrame_split_createChainAt_pre
   hkdfExtract_length' hmacCore_entails_cells hmacCore_merge hmacCore_split keysToBytes_rootKdf
   lsDhSym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym
   memRegion_out_createChain_err
   pointsToBytes_entails_memRegion_of_eq pointsTo_keyVec_toList
   rootCreateChain_of_calculateAgreement_none rootCreateChain_of_calculateAgreement_some
   stackAt_alloc_expand stackAt_alloc_extract stackAt_calc_alloc_split
   subroutine_ok_withLsCodeRoLoaded_rodata'' whisperRatchet_length
   zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalTripleRatchet.Keys.CreateChainFacts
  (SepWP.exists_left_elim SepWP.pure_left_elim cells14_sub_176 cells14_sub_352_eq cells2_add_eq
   cells3_sub_240 cells4_sub_384_eq cells8_sub_240 cells8_sub_384 cells8_sub_384_eq
   cells8_sub_448 cells8_sub_448_eq cells8_sub_512 cells8_sub_512_eq cells8_sub_64
   cells8_sub_64_eq memRegion_out_createChain_ok_flat pointsTo64_memRegion48_entails)
open scoped CryptoVerification.LibsignalTripleRatchet.Keys
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
   rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliDeallocBudgetSpecWithStack subroutine_ok_rustCliDeallocBudget_withStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
  (calculateAgreement_placed_ok_fsPred withFsPred)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (expandMultiInfoBudgetSpec extractBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CalculateAgreementEnv CreateChainEnv calculateAgreementEvents calculateAgreementSpec
   calculateAgreementSpecWithStack createChainEvents createChainSpec
   createChainSpecWithStack createChainSpecX ctEqSliceROSpec)

attribute [local simp, local arm64_norm] whisperRatchet_length hkdfExtract_length'
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local irreducible] Program.fetch Program.externAt? FitsEvents

/-! ## `Pfs`-threaded placed call-site lifters -/

private theorem fitsEnv_calculateAgreement_of_createChain_fd
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {C : Crypto}
    {x : CreateChainGhost} {ret : BitVec 64}
    (h : FitsEnv M lim st (CreateChainEnv C x)) :
    FitsEnv M lim st (CalculateAgreementEnv C.X ⟨x.ourA, x.our, x.theirA, x.their, ret⟩) := by
  intro evs hevs
  rw [CalculateAgreementEnv] at hevs
  subst hevs
  have hcc := h (createChainEvents C x) rfl
  unfold calculateAgreementEvents
  unfold createChainEvents at hcc
  dsimp only
  cases hdh : calculateAgreement C.X x.their x.our <;> simp only [hdh] at hcc ⊢
  · exact hcc
  · exact ((fitsEvents_append M lim _ _ st).mp hcc).1

private theorem fitsEvents_dealloc_of_createChain_some_fd
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {C : Crypto}
    {x : CreateChainGhost} {ss : List.Vector (BitVec 8) 32}
    (h : FitsEnv M lim st (CreateChainEnv C x))
    (hdh : calculateAgreement C.X x.their x.our = some ss) :
    FitsEvents M lim (M.stepEvents (rustAllocEvents 32 1) st) (rustDeallocEvents 32 1) := by
  have hcc := h (createChainEvents C x) rfl
  unfold createChainEvents at hcc
  rw [hdh] at hcc
  exact ((fitsEvents_append M lim _ _ st).mp hcc).2

def calculateAgreementBudgetCallSpecAtFs (Pfs : FsState → Prop) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (pl : Obj.MultiPlacement)
    (X : X25519Fn) (callStack : Nat) :
    Spec (BitVec 64 × PrivateKey × BitVec 64 × PublicKey × BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (ourA, our, theirA, their, ret, sp, st) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      FitsEnv M lim st (CalculateAgreementEnv X ⟨ourA, our, theirA, their, ret⟩)⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp callStack
  post := fun (ourA, our, theirA, their, ret, sp, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ Pfs sf.fs⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      calculateAgreementResultAt A.repAlloc ret (calculateAgreement X their our) ∗
      A.pool lim (M.stepEvents (calculateAgreementEvents X ⟨ourA, our, theirA, their, ret⟩) st) sf ∗
      stackAt sp callStack

theorem calculateAgreementBudgetCallAt_ok_fsPred {Pfs : FsState → Prop}
    {prog : Program} {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {callStack : Nat} {addr : BitVec 64}
    (hag : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (withFsPred Pfs (calculateAgreementSpecWithStack M A lim X callStack)))) :
    subroutine_ok prog addr
      (calculateAgreementBudgetCallSpecAtFs Pfs M A lim pl X callStack) := by
  refine subroutine_ok_map hag ?_
  rintro ⟨ourA, our, theirA, their, ret, sp, st⟩ R s0 hpre
  dsimp only [calculateAgreementBudgetCallSpecAtFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hpfs0, hx0, hx1, hx8, hsp, hfits⟩, hpre⟩
  subst hsp
  refine ⟨(⟨ourA, our, theirA, their, ret⟩, st), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, withFsPred]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpfs0, ?_⟩
    dsimp only [calculateAgreementSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hfits⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpecWithStack,
      calculateAgreementBudgetCallSpecAtFs] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨evs, hpfs_f, ⟨htr, hevs⟩, hpost⟩
    rw [CalculateAgreementEnv] at hevs
    subst hevs
    exact ⟨⟨htr, hpfs_f⟩, hpost⟩

def extractSomeBudgetPlacedAllocStackSpecFs (Pfs : FsState → Prop) (F : ShaCompress)
    (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, sv, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack
  post := fun (ret, saltA, sv, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      (ret ↦ₛ hkdfExtract F (some sv) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some sv) ikm) [] ∗
      (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack

theorem extractSomeBudgetPlacedAllocStack_ok_fsPred {Pfs : FsState → Prop}
    {prog : Program} {pl : Obj.MultiPlacement} {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (withFsPred Pfs (extractBudgetSpec C.F)))) :
    subroutine_ok prog addr (extractSomeBudgetPlacedAllocStackSpecFs Pfs C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomeBudgetPlacedAllocStackSpecFs] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hpfs0, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  refine ⟨⟨ret, saltA, some sv, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, withFsPred, extractBudgetSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpfs0, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, withFsPred, extractBudgetSpec, withVmPreserved, extractSpec,
      CryptoVerification.LibsignalTripleRatchet.ExtractGhost.prk, optSaltAt,
      extractSomeBudgetPlacedAllocStackSpecFs] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm, hpfs_f⟩, by arm64_sep_close⟩

def extractKey32BudgetPlacedStackSpecAtFs (Pfs : FsState → Prop) (F : ShaCompress)
    (pl : Obj.MultiPlacement) (callStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 256 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, rk, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack
  post := fun (ret, saltA, rk, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      (ret ↦ₛ hkdfExtract F (some (keyToBytesVec32 rk)) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some (keyToBytesVec32 rk)) ikm) [] ∗
      (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack

theorem extractKey32BudgetPlacedAllocStack_ok_fsPred {Pfs : FsState → Prop}
    {prog : Program} {pl : Obj.MultiPlacement} {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (withFsPred Pfs (extractBudgetSpec C.F)))) :
    subroutine_ok prog addr
      (extractKey32BudgetPlacedStackSpecAtFs Pfs C.F pl allocHookStack) := by
  refine subroutine_ok_map (extractSomeBudgetPlacedAllocStack_ok_fsPred (C := C) hext) ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  refine ⟨⟨ret, saltA, keyToBytesVec32 rk, ikmA, ikm, sp⟩, R, ?_, ?_⟩
  · dsimp only [extractSomeBudgetPlacedAllocStackSpecFs,
      extractKey32BudgetPlacedStackSpecAtFs] at hpre ⊢
    rw [pointsTo_keyVec_toList]
    exact hpre
  · intro sf hpost
    dsimp only [extractSomeBudgetPlacedAllocStackSpecFs,
      extractKey32BudgetPlacedStackSpecAtFs] at hpost ⊢
    rw [← pointsTo_keyVec_toList]
    exact hpost

def expandCellsBudgetPlacedStackSpecAtFs (Pfs : FsState → Prop) (F : ShaCompress)
    (pl : Obj.MultiPlacement) (k : Nat) (callStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp callStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp callStack

theorem expandCellsBudgetPlacedAllocStack_ok_fsPred {Pfs : FsState → Prop}
    {prog : Program} {pl : Obj.MultiPlacement} {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (withFsPred Pfs (expandMultiInfoBudgetSpec C.F))))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr
      (expandCellsBudgetPlacedStackSpecAtFs Pfs C.F pl n allocHookStack) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsBudgetPlacedStackSpecAtFs] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA n hn] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hpfs0, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * n⟩,
    memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, withFsPred, expandMultiInfoBudgetSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpfs0, ?_⟩
    dsimp only [expandMultiInfoSpec]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, withFsPred, expandMultiInfoBudgetSpec, withVmPreserved,
      expandMultiInfoSpec, expandCellsBudgetPlacedStackSpecAtFs] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, hvm, htr, hpost⟩
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * n)) ∗
        stackAt s0.sp expandMultiInfoStack ∗ memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA prk)
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨⟨htr, hvm, hpfs_f⟩, by arm64_sep_close⟩

def deallocBudgetPlacedStackSpecAtFs [LibsignalPlacement] (Pfs : FsState → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (pl : Obj.MultiPlacement) (callStack : Nat) :
    Spec (BitVec 64 × Nat × Nat × BitVec 64 × M.σ) where
  pre := fun (p, size, align, sp, st) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ 0 < size ∧ size < 2 ^ 63 ∧ align = 1 ∧
      FitsEvents M lim st (rustDeallocEvents size align) ∧ s.sp = sp ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.repAlloc.live p size align ∗ memRegion p size ∗ stackAt sp callStack
  post := fun (_, size, align, sp, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ Pfs sf.fs⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt sp callStack

theorem deallocBudgetPlacedAllocStack_of_rustCliDealloc_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {addr : BitVec 64}
    (hd : subroutine_ok prog addr (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog addr
      (deallocBudgetPlacedStackSpecAtFs Pfs M A lim pl allocHookStack) := by
  have hd_stk : subroutine_ok prog addr
      (rustCliDeallocBudgetSpecWithStack M A lim allocHookStack) :=
    subroutine_ok_rustCliDeallocBudget_withStack (stk := allocHookStack)
      (by decide) (by decide) hd
  refine subroutine_ok_map hd_stk ?_
  rintro ⟨p, size, align, sp, st⟩ R s0 hpre
  dsimp only [deallocBudgetPlacedStackSpecAtFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hpfs0, hx0, hx1, hx2, _hpos, _hlt, _halign, _hfits, hsp, hlr⟩, hpre⟩
  subst hsp
  refine ⟨(p, size, align, st), R, ?_, ?_⟩
  · dsimp only [rustCliDeallocBudgetSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlr⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustCliDeallocBudgetSpecWithStack, deallocBudgetPlacedStackSpecAtFs] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hpres, _⟩, hpost⟩
    have hpfs_f : Pfs sf.fs := by rw [hpres.1]; exact hpfs0
    exact ⟨⟨hpres.2.1, hpfs_f⟩, hpost⟩

/-! ## `Pfs`-threaded relocatable `<RootKey>::create_chain` -/

private def createChainConcreteSpecAtFs (Pfs : FsState → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (C : Crypto) (callStack : Nat) :
    Spec (CreateChainGhost × M.σ) where
  pre := (withFsPred Pfs (createChainSpecWithStack M A lim C (576 + callStack))).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ Pfs sf.fs⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗
      createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our) ∗
      A.pool lim (M.stepEvents (createChainEvents C x) st) sf ∗ stackAt s0.sp (576 + callStack)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 4000000 in
private theorem createChain_placed_concrete_ok_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks} {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64)
    (hag : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (calculateAgreementBudgetCallSpecAtFs Pfs M A lim lsmpl C.X callStack))
    (hext' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (extractKey32BudgetPlacedStackSpecAtFs Pfs C.F lsmpl callStack))
    (hexp' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (expandCellsBudgetPlacedStackSpecAtFs Pfs C.F lsmpl 8 callStack))
    (hdealloc : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (deallocBudgetPlacedStackSpecAtFs Pfs M A lim lsmpl callStack)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainConcreteSpecAtFs Pfs M A lim C callStack)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.173")
    (roBytes := whisperRatchetInfo) (by decide) ?_
  wpp_init xst s0
  rcases xst with ⟨x, st⟩
  have hpfs0 : Pfs s0.fs := ‹_›
  have hfits : FitsEnv M lim st (CreateChainEnv C x) := ‹_›
  rcases x with ⟨rkA, rk, theirA, their, ourA, our, out⟩
  dsimp only at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = rkA› ‹s0.readReg64 (.gpr 1#5) = theirA›
    ‹s0.readReg64 (.gpr 2#5) = ourA› ‹s0.readReg64 (.gpr 8#5) = out›
  have hfits_ag : FitsEnv M lim st
      (CalculateAgreementEnv C.X ⟨s0.readReg64 (.gpr 2#5), our,
        s0.readReg64 (.gpr 1#5), their, s0.sp - 240#64⟩) :=
    fitsEnv_calculateAgreement_of_createChain_fd hfits
  rw (occs := .pos [1]) [fnFrame_split_createChainAt_pre s0.sp (by omega)]
  apply SepWPp.of_sepWP_ret
  apply SepWP.of_sepWP_lscro hF0
  apply SepWP.replace_pre (hPQ := Entails.of_eq (cells8_sub_64_eq s0.sp)) (by sep_focus)
  repeat' (apply SepWP.exists_left_elim; intro _)
  wp_simp_pre [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 207)
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF1
  refine SepWP.of_sepWP_lscro (mid := (blkPl_40).base + 44#64) hF1 ?_
  apply (SepWP.call_subroutine_frame hag (x := (s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 1#5), their,
    s0.sp - 240#64, s0.sp - 576#64, st)))
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm]
    exact hsp_align
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [calculateAgreementBudgetCallSpecAtFs]
    simp (config := { decide := true }) only [satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
    refine ⟨⟨hF1, hpfs0, hfits_ag⟩, by sep_frame⟩
  · intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp
  · intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he
  intro sf_ag hpc_ag hrun_ag hsp_ag hcs_ag
  dsimp only [calculateAgreementBudgetCallSpecAtFs]
  wp_simp_pre [hsp_ag, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨htr_ag, hpfs_ag⟩
  rcases hcs_ag with ⟨hx19_ag, hx20_ag, hx21_ag, hx22_ag, hx23_ag, hx24_ag, hx25_ag, hx26_ag, hx27_ag, hx28_ag, hx29_ag, hvregs_ag⟩
  simp only [wp_norm, arm64_norm] at hx19_ag hx20_ag hx21_ag hx22_ag hx23_ag hx24_ag hx25_ag hx26_ag hx27_ag hx28_ag hx29_ag hvregs_ag hsp_ag htr_ag
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF_sf
  cases hdh : calculateAgreement C.X their our with
  | none =>
    have hres := rootCreateChain_of_calculateAgreement_none C rk their our hdh
    have hevs_ag_none : calculateAgreementEvents C.X
        ⟨s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 1#5), their, s0.sp - 240#64⟩ = [] := by
      simp [calculateAgreementEvents, hdh]
    have hevs_cc_none : createChainEvents C
        ⟨s0.readReg64 (.gpr 0#5), rk, s0.readReg64 (.gpr 1#5), their,
          s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 8#5)⟩ = [] := by
      simp [createChainEvents, hdh]
    rw [hevs_ag_none, AllocCostModel.stepEvents_nil]
    rw [memRegion_out_createChain_err (s0.readReg64 (.gpr 8#5)), cells2_add_eq]
    wp_simp_pre [hdh, sepConj_assoc]
    apply SepWP.replace_pre
      (hPQ := calculateAgreementResult_none_cells A.repAlloc (s0.sp - 240#64)) (by sep_focus)
    wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    wp_extract_exists
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.replace_pre (hPQ := cells3_sub_240 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_64 s0.sp) (by sep_focus)
    apply SepWP.replace_pre
      (hPQ := pointsTo64_memRegion48_entails (s0.readReg64 (.gpr 8#5))) (by sep_focus)
    clear hag hext' hexp' hdealloc
    rw [fnFrame_split_createChainAt_err s0.sp (by omega), hevs_cc_none, AllocCostModel.stepEvents_nil]
    wp_simp_post [hres, createChainResultAt, sepConj_assoc]
    wp_done
  | some ss =>
    have hres := rootCreateChain_of_calculateAgreement_some C rk their our ss hdh
    have hevs_ag_some : calculateAgreementEvents C.X
        ⟨s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 1#5), their, s0.sp - 240#64⟩ =
        rustAllocEvents 32 1 := by
      simp [calculateAgreementEvents, hdh]
    have hevs_cc_some : createChainEvents C
        ⟨s0.readReg64 (.gpr 0#5), rk, s0.readReg64 (.gpr 1#5), their,
          s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 8#5)⟩ =
        rustAllocEvents 32 1 ++ rustDeallocEvents 32 1 := by
      simp [createChainEvents, hdh]
    have hfits_dealloc :
        FitsEvents M lim (M.stepEvents (rustAllocEvents 32 1) st) (rustDeallocEvents 32 1) :=
      fitsEvents_dealloc_of_createChain_some_fd hfits hdh
    rw [hevs_ag_some]
    obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32
        (hkdfExtract_length' C.F (some (keyToBytesVec32 rk)) ss.toList)
    have hprk_sp := hprk (s0.sp - 240#64)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hprk_sp
    have hsplit := hmacCore_split C.F (s0.sp - 208#64)
      (hkdfExtract C.F (some (keyToBytesVec32 rk)) ss.toList)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hsplit
    have hokm_eq : hkdfExpand C.F (hkdfExtract C.F (some (keyToBytesVec32 rk)) ss.toList)
        whisperRatchetInfo 64 =
        keysToBytes (rootKdf C.F rk ss.toList) :=
      (keysToBytes_rootKdf C.F rk ss.toList).symm
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm⟩ :=
      exists_unpack64_of_length_64
        (bs1 := keyToBytes32 (rootKdf C.F rk ss.toList).1)
        (bs2 := keyToBytes32 (rootKdf C.F rk ss.toList).2)
        (by simp [keyToBytes32]) (by simp [keyToBytes32])
    have hokm_sp := (congrArg ((s0.sp - 512#64) ↦ₛ ·) hokm_eq).trans (hokm (s0.sp - 512#64))
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
    have hokm_out := hokm (s0.readReg64 (.gpr 8#5) + 4#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
    wp_simp_pre [hdh, calculateAgreementResultAt, sepConj_assoc]
    wp_extract_exists
    rename_i ptr
    have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
    apply SepWP.replace_pre
      (hPQ := boxU8At_32_split A.repAlloc (s0.sp - 240#64 + 8#64) ptr ss.toList hss_len)
      (by sep_focus)
    apply SepWP.pure_left_elim; intro hptr_ne
    apply SepWP.replace_pre (hPQ := Entails.of_eq (cells8_sub_512_eq s0.sp)) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    apply SepWP.of_sepWP_lscro hF_sf
    wp_steps_sync_pool (lsmpl.base 54)
    apply SepWP.replace_pre
      (hPQ := cells3_memRegion_152_merge s0.sp 0#64 ptr 32#64)
      (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_512 s0.sp) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_ext
    apply SepWP.of_sepWP_lscro hF_ext
    wp_call hext' (s0.sp - 240#64, s0.readReg64 (.gpr 0#5), rk,
      ptr, ss.toList, s0.sp - 576#64)
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    rw [hprk_sp]
    apply SepWP.replace_pre (hPQ := hsplit) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    apply SepWP.pure_left_elim; intro hgood
    apply SepWP.replace_pre (hPQ := Entails.of_eq (cells4_sub_384_eq s0.sp)) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (cells14_sub_352_eq s0.sp)) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    wp_simp_pre [sepConj_assoc]
    wp_steps_sync_pool (lsmpl.base 53)
    have hmrg := hmacCore_merge C.F (s0.sp - 384#64) _ hgood
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hmrg
    apply SepWP.replace_pre (hPQ := hmrg) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_exp
    apply SepWP.of_sepWP_lscro hF_exp
    wp_call hexp' (s0.sp - 384#64, hkdfExtract C.F (some (keyToBytesVec32 rk)) ss.toList,
      s0.sp - 240#64, lsmpl.ρ "libsignal_protocol:.rodata..Lanon.173", whisperRatchetInfo,
      s0.sp - 512#64, s0.sp - 576#64)
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    rw [hokm_sp]
    apply SepWP.replace_pre
      (hPQ := Entails.of_eq (memRegion_out_createChain_ok_flat (s0.readReg64 (.gpr 8#5))))
      (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (cells8_sub_448_eq s0.sp)) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (cells8_sub_384_eq s0.sp)) (by sep_focus)
    repeat' (apply SepWP.exists_left_elim; intro _)
    wp_simp_pre [sepConj_assoc]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.replace_pre (hPQ := cells14_sub_176 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_512 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_448 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_384 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells8_sub_240 s0.sp) (by sep_focus)
    have hss_mem : (ptr ↦ₛ ss.toList) ⊢ memRegion ptr 32 :=
      pointsToBytes_entails_memRegion_of_eq hss_len
    apply SepWP.replace_pre (hPQ := hss_mem) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_dealloc
    wp_call hdealloc (ptr, 32, 1, s0.sp - 576#64, M.stepEvents (rustAllocEvents 32 1) st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    apply SepWP.replace_pre (hPQ := cells8_sub_64 s0.sp) (by sep_focus)
    rw [fnFrame_split_createChainAt_ok s0.sp (by omega), hevs_cc_some, M.stepEvents_append]
    wp_simp_post [hres,
      createChainResultAt_ok_eq (s0.readReg64 (.gpr 8#5)) (rootKdf C.F rk ss.toList),
      keysToBytes, hokm_out, sepConj_assoc]
    clear hag hext' hexp' hdealloc hprk hprk_sp hsplit hokm hokm_sp hokm_out hmrg hgood
    wp_done

/-- Relocatable stack-parameterized `Pfs`-threaded `<RootKey>::create_chain` (Block `40`, 460 B). -/
theorem createChain_placed_ok_of_hooks_gen_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks} {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64)
    (hag : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (calculateAgreementBudgetCallSpecAtFs Pfs M A lim lsmpl C.X callStack))
    (hext' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (extractKey32BudgetPlacedStackSpecAtFs Pfs C.F lsmpl callStack))
    (hexp' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (expandCellsBudgetPlacedStackSpecAtFs Pfs C.F lsmpl 8 callStack))
    (hdealloc : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (deallocBudgetPlacedStackSpecAtFs Pfs M A lim lsmpl callStack)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl
        (withFsPred Pfs (createChainSpecWithStack M A lim C (576 + callStack)))) := by
  refine subroutine_ok_mono
    (createChain_placed_concrete_ok_fsPred hbound hag hext' hexp' hdealloc)
    (fun _ _ _ hp => hp) ?_
  rintro ⟨x, st⟩ R s0 sf hq
  dsimp only [withLsCodeRoLoaded, withFsPred, createChainConcreteSpecAtFs,
    createChainSpecWithStack] at hq ⊢
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨⟨htr, hpfs⟩, hrest⟩
  exact ⟨createChainEvents C x, hpfs, ⟨htr, rfl⟩, hrest⟩

/-- Contract-backed relocatable `Pfs`-threaded `<RootKey>::create_chain` (Block `40`). -/
theorem createChain_placed_ok_of_contracts_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (calculateAgreementSpec M A lim C.X))))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (extractBudgetSpec C.F))))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (expandMultiInfoBudgetSpec C.F))))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (createChainSpec M A lim C))) := by
  have hag := calculateAgreementBudgetCallAt_ok_fsPred hag_ok
  have hext0 := extractKey32BudgetPlacedAllocStack_ok_fsPred (C := C) hext
  have hext_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (extractKey32BudgetPlacedStackSpecAtFs Pfs C.F lsmpl calculateAgreementStack) := by
    refine subroutine_ok_map hext0 ?_
    rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
    dsimp only [extractKey32BudgetPlacedStackSpecAtFs] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [extractKey32BudgetPlacedStackSpecAtFs]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [extractKey32BudgetPlacedStackSpecAtFs] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, by arm64_sep_close⟩
  have hexp0 := expandCellsBudgetPlacedAllocStack_ok_fsPred (C := C) hexp 8 (by decide)
  have hexp_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (expandCellsBudgetPlacedStackSpecAtFs Pfs C.F lsmpl 8 calculateAgreementStack) := by
    refine subroutine_ok_map hexp0 ?_
    rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
    dsimp only [expandCellsBudgetPlacedStackSpecAtFs] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [expandCellsBudgetPlacedStackSpecAtFs]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [expandCellsBudgetPlacedStackSpecAtFs] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, by arm64_sep_close⟩
  have hdealloc0 := deallocBudgetPlacedAllocStack_of_rustCliDealloc_fsPred
    (Pfs := Pfs) (pl := lsmpl) hdealloc_raw
  have hdealloc_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (deallocBudgetPlacedStackSpecAtFs Pfs M A lim lsmpl calculateAgreementStack) := by
    refine subroutine_ok_map hdealloc0 ?_
    rintro ⟨p, size, align, sp, st⟩ R s0 hpre
    dsimp only [deallocBudgetPlacedStackSpecAtFs] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨p, size, align, sp, st⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [deallocBudgetPlacedStackSpecAtFs]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [deallocBudgetPlacedStackSpecAtFs] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, by arm64_sep_close⟩
  exact createChain_placed_ok_of_hooks_gen_fsPred (callStack := calculateAgreementStack) (by decide)
    hag hext_c hexp_c hdealloc_c

/-- Relocatable `Pfs`-threaded `<RootKey>::create_chain` (Block `40`) from `HookSat`. -/
theorem createChain_placed_ok_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec C.X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (withFsPred Pfs (extractBudgetSpec C.F))))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (withFsPred Pfs (expandMultiInfoBudgetSpec C.F))))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (createChainSpec M A lim C))) :=
  createChain_placed_ok_of_contracts_fsPred
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok_fsPred h_dh h_shdrop hct h_shim h_alloc h_stdrop))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

theorem subroutine_ok_createChainSpecX_of_createChainSpec_fsPred {Pfs : FsState → Prop}
    {prog : Program} {entry : BitVec 64} {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withFsPred Pfs (createChainSpec M A lim C)))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withFsPred Pfs (createChainSpecX M A lim C))) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hstk : stackAt s0.sp createChainStackX =
      stackAt s0.sp createChainStack ∗ memRegion (s0.sp - 17120#64) 12288 := by
    change memRegion (s0.sp - BitVec.ofNat 64 17120) 17120 =
      memRegion (s0.sp - BitVec.ofNat 64 4832) 4832 ∗ memRegion (s0.sp - 17120#64) 12288
    rw [sepConj_comm]
    exact ProofLib.memRegion_split' (b := s0.sp - 17120#64) (n := 12288) (k := 4832)
      (b' := s0.sp - 4832#64) rfl (by bv_omega) (by decide)
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (withFsPred Pfs (createChainSpec M A lim C))).pre x s0 ∗
        (memRegion (s0.sp - 17120#64) 12288 ∗ R) := by
    dsimp only [withLsCodeRoLoaded, withFsPred, createChainSpecX, createChainSpec,
      createChainSpecWithStack] at hpre ⊢
    rw [hstk] at hpre
    convert hpre using 1; sep_ac_rfl
  refine h.mono_outcome x (memRegion (s0.sp - 17120#64) 12288 ∗ R) s0 hpc hrun hpre' hsp
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withFsPred, createChainSpecX, createChainSpec,
      createChainSpecWithStack] at hq ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [hstk]
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, withFsPred, createChainSpec, createChainSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFsPred, createChainSpec, createChainSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFsPred, createChainSpec, createChainSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable `Pfs`-threaded `<RootKey>::create_chain` (Block `40`) at `createChainStackX`. -/
theorem createChain_placed_ok_x_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec C.X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (withFsPred Pfs (extractBudgetSpec C.F))))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (withFsPred Pfs (expandMultiInfoBudgetSpec C.F))))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (createChainSpecX M A lim C))) :=
  subroutine_ok_createChainSpecX_of_createChainSpec_fsPred
    (createChain_placed_ok_fsPred h_dh h_shdrop hct h_shim h_alloc h_stdrop hext hexp h_dealloc)

end LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudgetFd
