/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# File-Descriptor-Predicated `<PrivateKey>::calculate_agreement`

Threads an arbitrary `FsState → Prop` predicate `Pfs` across the `[LibsignalPlacement]`
`RustCliAllocBudget` contracts for `<PrivateKey>::calculate_agreement`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

open Arm64 Arm64.Obj ProofLib
open CryptoGames.Ratchet (X25519Fn clampScalar)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_207 blkPC_207 blkPC_207_pairStep_0x68 blkPl_207 lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (CalculateAgreementGhost calculateAgreement calculateAgreementResultAt
   calculateAgreementStack calculateAgreementStackX diffieHellmanSpec
   keys_ls_hook_ok_of_mem withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv SepWP.done_frozen SepWP.of_sepWP_lscro SepWPp.of_sepWP_lscro SepWPp.rw_pre
   calculateAgreementResultAt_some_intro calculateAgreement_eq_none calculateAgreement_eq_some
   clampScalar_view2_sp ctEqROAllocStackSpec ctEqROAllocStackSpec_post_eq
   ctEqROAllocStackSpec_pre_eq
   lsDhSym lsRodataCst32Sym lsRustAllocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym
   memRegion_24_err memRegion_24_ok memRegion_32_cells memRegion_32_view1_sp
   pointsToBytes_entails_memRegion_of_eq rejoin_stack_calculateAgreementAt
   stackAt_calculateAgreementAt_split stackAt_calculateAgreementExt_split
   stur_q0_reframe_sp subroutine_ok_withLsCodeRoLoaded_rodata''
   vec32_view1 vec32_view1_to_view2 vec32_view2)
open scoped CryptoVerification.LibsignalTripleRatchet.Keys
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents PoolPreserved
   RustCliAllocBudget VmPreserved rustAllocEvents rustCliAllocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CalculateAgreementEnv calculateAgreementEvents calculateAgreementSpec
   calculateAgreementSpecWithStack calculateAgreementSpecX ctEqSliceROSpec)

/-- Thread a unary `FsState` predicate `Pfs` (such as `FdsGe3Closed`) from `pre` to `post`,
preserving `onPanic`, `onExit`, and `onOom` verbatim. -/
def withFsPred {α : Type} (Pfs : FsState → Prop) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜Pfs s.fs⌝ ∗ spec.pre x s
    post := fun x s0 sf => ⌜Pfs sf.fs⌝ ∗ spec.post x s0 sf }

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

/-! ## Pool synchronization and `Pfs`-threaded call-site specifications -/

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

def dhPlacedCallSpecFs (Pfs : FsState → Prop) (pl : Obj.MultiPlacement)
    (X : X25519Fn) (subStack : Nat) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64 × BitVec 64) where
  pre := fun (secA, sec, pubA, pub, ret, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = secA ∧ s.readReg64 .x1 = pubA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ memRegion ret 32 ∗ stackAt sp subStack
  post := fun (secA, sec, pubA, pub, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ (ret ↦ₛ (X sec pub).toList) ∗
      stackAt sp subStack

def zeroizePlacedCallSpecFs (Pfs : FsState → Prop) (pl : Obj.MultiPlacement) (subStack : Nat) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (a, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = a ∧ s.sp = sp⌝ ∗
      memRegion a 32 ∗ stackAt sp subStack
  post := fun (a, sp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      (a ↦ₛ List.replicate 32 0#8) ∗ stackAt sp subStack

def ctEqPlacedCallSpecFs (Pfs : FsState → Prop) (pl : Obj.MultiPlacement) (subStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack

def shimPlacedCallSpecFs (Pfs : FsState → Prop) (pl : Obj.MultiPlacement) (subStack : Nat) :
    Spec (BitVec 64) where
  pre := fun sp s => ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ s.sp = sp⌝ ∗ stackAt sp subStack
  post := fun sp s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ Pfs sf.fs⌝ ∗ stackAt sp subStack

def allocPlacedCallSpecFs [LibsignalPlacement] (Pfs : FsState → Prop) (pl : Obj.MultiPlacement)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (subStack : Nat) :
    Spec (Nat × Nat × M.σ × BitVec 64) where
  pre := fun (size, align, st, sp) s =>
    ⌜LsFrozenInv pl s ∧ Pfs s.fs ∧ (s.readReg64 .x0).toNat = size ∧
      (s.readReg64 .x1).toNat = align ∧ LayoutOk size align ∧ align ≤ 2 ^ 31 ∧
      FitsEvents M lim st (rustAllocEvents size align) ∧ s.sp = sp ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt sp subStack
  post := fun (size, align, st, sp) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ (sf.readReg64 .x0).toNat % align = 0 ∧
      sf.trace = s0.trace ∧ Pfs sf.fs⌝ ∗
      A.repAlloc.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size ∗
      A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗ stackAt sp subStack

private theorem dhPlacedCallAt_of_raw_fsPred {Pfs : FsState → Prop}
    {pl : Obj.MultiPlacement} {X : X25519Fn}
    {subStack : Nat} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withFsPred Pfs (withVmPreserved (diffieHellmanSpec X)))) :
    subroutine_ok prog entry (dhPlacedCallSpecFs Pfs pl X subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhPlacedCallSpecFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hpfs, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(secA, sec, pubA, pub, ret), stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [withFsPred, withVmPreserved, diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpfs, ⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withFsPred, withVmPreserved, diffieHellmanSpec, dhPlacedCallSpecFs] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm, hpfs_f⟩, by arm64_sep_close⟩

private theorem zeroizePlacedCallAt_of_raw_fsPred {Pfs : FsState → Prop}
    {pl : Obj.MultiPlacement} {subStack : Nat} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :
    subroutine_ok prog entry (zeroizePlacedCallSpecFs Pfs pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizePlacedCallSpecFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hpfs, hx0, hsp⟩, hpre⟩
  subst hsp
  refine ⟨a, stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [withFsPred, withVmPreserved, zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpfs, hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withFsPred, withVmPreserved, zeroizeSecretSpec, zeroizePlacedCallSpecFs] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, hvm, htr, hpost⟩
    exact ⟨⟨htr, hvm, hpfs_f⟩, by arm64_sep_close⟩

private theorem ctEqPlacedCallAt_of_withLsCodeLoaded_fsPred {Pfs : FsState → Prop}
    {pl : Obj.MultiPlacement} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (withFsPred Pfs ctEqSliceROSpec))) :
    subroutine_ok prog entry (ctEqPlacedCallSpecFs Pfs pl allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqPlacedCallSpecFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfr, hpfs, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded, withFsPred, ctEqSliceROSpec, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr.1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpfs, ?_⟩
    rw [← ctEqROAllocStackSpec_pre_eq]
    dsimp only [ctEqROAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withFsPred, ctEqSliceROSpec, withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hpfs_f, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hpost⟩
    rw [ctEqROAllocStackSpec_post_eq] at hpost
    dsimp only [ctEqROAllocStackSpec, ctEqPlacedCallSpecFs] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr, hvm, hpfs_f⟩, hpost⟩
    rw [hres]; split <;> rfl

private theorem shimPlacedCallAt_of_raw_fsPred {Pfs : FsState → Prop}
    {pl : Obj.MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withFsPred Pfs noAllocShimBudgetSpec)) :
    subroutine_ok prog entry (shimPlacedCallSpecFs Pfs pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimPlacedCallSpecFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hpfs, hsp⟩, hpre⟩
  refine ⟨(), stackAt sp subStack ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (⌜Pfs s0.fs⌝ ∗ emp) ∗ (stackAt sp subStack ∗ R)
    simp only [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj]
    exact ⟨hpfs, hpre⟩
  · intro sf hpost
    change sf.mem ⊨
      (⌜Pfs sf.fs⌝ ∗ ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝) ∗
        (stackAt sp subStack ∗ R) at hpost
    dsimp only [shimPlacedCallSpecFs]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, ⟨htr, hvm⟩, hpost⟩
    exact ⟨⟨htr, hvm, hpfs_f⟩, hpost⟩

private theorem allocPlacedCallAt_of_allocStack_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog entry (allocPlacedCallSpecFs Pfs pl M A lim allocHookStack) := by
  have hno : subroutine_ok prog entry
      (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget h)
  refine subroutine_ok_map hno ?_
  rintro ⟨size, align, st, sp⟩ R s0 hpre
  dsimp only [allocPlacedCallSpecFs] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hpfs, hx0, hx1, hlay, hal_le, hfits, hsp, hlr_ls⟩, hpre⟩
  subst hsp
  refine ⟨(size, align, st), R, ?_, ?_⟩
  · dsimp only [rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.RustLayoutOk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, ⟨hlay, hal_le⟩, hfits, hlr_ls⟩, by convert hpre using 1⟩
  · intro sf hpost
    dsimp only [rustCliAllocNoOomSpecWithStack, allocPlacedCallSpecFs] at hpost ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hpres, hne0, hmod⟩, hpost⟩
    have hpfs_f : Pfs sf.fs := by rw [hpres.1]; exact hpfs
    refine ⟨⟨hne0, hmod, hpres.2.1, hpfs_f⟩, ?_⟩
    change sf.mem ⊨
      A.live (sf.readReg64 .x0) size align ∗
        (memRegion (sf.readReg64 .x0) size ∗
          (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            (stackAt s0.sp allocHookStack ∗ R)))
    convert hpost using 1; sep_ac_rfl

/-! ## `Pfs`-threaded relocatable `<PrivateKey>::calculate_agreement` -/

private def calculateAgreementConcreteSpecWithStackFs (Pfs : FsState → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : X25519Fn) (totalStack : Nat) :
    Spec (CalculateAgreementGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜Pfs s.fs ∧ s.readReg64 .x0 = x.ourA ∧ s.readReg64 .x1 = x.theirA ∧
      s.readReg64 .x8 = x.ret ∧ FitsEnv M lim st (CalculateAgreementEnv X x)⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ Pfs sf.fs⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      calculateAgreementResultAt A.repAlloc x.ret (calculateAgreement X x.their x.our) ∗
      A.pool lim (M.stepEvents (calculateAgreementEvents X x) st) sf ∗ stackAt s0.sp totalStack

attribute [local irreducible] FitsEvents

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
private theorem calculateAgreement_placed_concrete_ok_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : String → Option (State → State)} {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64)
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (dhPlacedCallSpecFs Pfs lsmpl X subStack))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      (zeroizePlacedCallSpecFs Pfs lsmpl subStack))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (ctEqPlacedCallSpecFs Pfs lsmpl subStack))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      (shimPlacedCallSpecFs Pfs lsmpl subStack))
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (allocPlacedCallSpecFs Pfs lsmpl M A lim subStack))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      (zeroizePlacedCallSpecFs Pfs lsmpl subStack)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl
        (calculateAgreementConcreteSpecWithStackFs Pfs M A lim X (160 + subStack))) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata'' (roSym := lsRodataCst32Sym)
    (roBytes := List.replicate 32 0#8) (by decide) ?_
  wpp_init xst s0
  rcases xst with ⟨x, st⟩
  have hpfs0 : Pfs s0.fs := ‹_›
  have hfits : FitsEnv M lim st (CalculateAgreementEnv X x) := ‹_›
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = ourA› ‹s0.readReg64 (.gpr 1#5) = theirA›
    ‹s0.readReg64 (.gpr 8#5) = ret›
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := X (clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length (clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreementAt_split s0.sp (by omega),
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_207).base + 120#64) hF0 ?_
  apply SepWP.of_sepWP_lscro hF0
  apply sepWP_seg_ls_vm (Q := (blkPC_207).rebase (blkPl_207).base (hooksException H)) blkLib_eq_207
    (mid := lsρ lsDhSym)
  intro _m_strip
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by simp [wp_norm, arm64_norm])) (hnext := ?_)
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF1
  apply SepWP.of_sepWP_lscro hF1
  wp_call h_dh (s0.sp - 160#64, clampScalar our.bytes, s0.sp - 64#64, their.bytes,
    s0.sp - 96#64, s0.sp - 160#64)
  refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps_sync_pool (lsρ lsSharedDropSym)
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF2
  apply SepWP.of_sepWP_lscro hF2
  wp_call h_shdrop (s0.sp - 96#64, s0.sp - 160#64)
  refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
  apply sepWP_seg_ls_vm (Q := (blkPC_207).rebase (blkPl_207).base (hooksException H)) blkLib_eq_207
    (mid := lsmpl.base 213)
  intro _m_strip2
  apply blkPC_207_pairStep_0x68 (blkPl_207).base (hooksException H) rfl (by wp_norm_lhs) (by wp_norm_lhs)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool (_hnsp2.toVmPreserved (by simp [wp_norm, arm64_norm])) (hnext := ?_)
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF3
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq (s0.sp - 128#64, ss.toList,
    lsρ lsRodataCst32Sym,
    List.replicate 32 0#8, s0.sp - 160#64)
  refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF4
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement X their our = none := calculateAgreement_eq_none hzero
    have hevs_none : calculateAgreementEvents X ⟨s0.readReg64 (.gpr 0#5), our,
        s0.readReg64 (.gpr 1#5), their, s0.readReg64 (.gpr 8#5)⟩ = [] := by
      simp [calculateAgreementEvents, hres]
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    apply SepWP.of_sepWP_lscro hF4
    wp_steps_sync_pool (lsρ lsStaticDropSym)
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
    refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
    wp_steps_sync_pool (s0.readReg64 .lr)
    refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hevs_none, AllocCostModel.stepEvents, hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement X their our = some ss := calculateAgreement_eq_some hzero
    have hevs_some : calculateAgreementEvents X ⟨s0.readReg64 (.gpr 0#5), our,
        s0.readReg64 (.gpr 1#5), their, s0.readReg64 (.gpr 8#5)⟩ = rustAllocEvents 32 1 := by
      simp [calculateAgreementEvents, hres]
    have hfits32 : FitsEvents M lim st (rustAllocEvents 32 1) :=
      hfits (rustAllocEvents 32 1) (by simp [CalculateAgreementEnv, hevs_some])
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_207).base + 160#64) hF4 ?_
    apply SepWP.of_sepWP_lscro hF4
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    apply SepWP.of_sepWP_lscro hF5
    wp_call h_shim (s0.sp - 160#64)
    refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF6
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
    wp_call h_alloc (32, 1, st, s0.sp - 160#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF7
    have halloc_ne0 : sf_4.readReg64 (.gpr 0#5) ≠ 0#64 := ‹_›
    have halloc_beq : (sf_4.readReg64 (.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr halloc_ne0
    refine SepWPp.rw_pre (by
      rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
        memRegion_32_cells,
        ← hss_sp128]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    apply SepWP.of_sepWP_lscro hF7
    wp_steps_sync_pool (lsρ lsStaticDropSym)
    refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF8
    wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
    refine SepWP.sync_pool (hvm := ‹VmPreserved _ _›) (hk := ?_)
    wp_steps_sync_pool (s0.readReg64 .lr)
    refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hss_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    have h_res_intro := calculateAgreementResultAt_some_intro A.repAlloc (s0.readReg64 (.gpr 8#5))
      _ ss halloc_ne0
    rw [show A.repAlloc.live = A.live from rfl] at h_res_intro
    refine SepWP.fold h_res_intro (by sep_focus) ?_
    rw [hevs_some, hres]
    wp_done

/-- Relocatable stack-parameterized `Pfs`-threaded `<PrivateKey>::calculate_agreement` (Block `207`). -/
theorem calculateAgreement_placed_ok_of_hooks_gen_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : String → Option (State → State)} {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64)
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (dhPlacedCallSpecFs Pfs lsmpl X subStack))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      (zeroizePlacedCallSpecFs Pfs lsmpl subStack))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (ctEqPlacedCallSpecFs Pfs lsmpl subStack))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      (shimPlacedCallSpecFs Pfs lsmpl subStack))
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (allocPlacedCallSpecFs Pfs lsmpl M A lim subStack))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      (zeroizePlacedCallSpecFs Pfs lsmpl subStack)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl
        (withFsPred Pfs (calculateAgreementSpecWithStack M A lim X (160 + subStack)))) := by
  refine subroutine_ok_mono
    (calculateAgreement_placed_concrete_ok_fsPred hbound h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop)
    ?_ ?_
  · rintro ⟨x, st⟩ R s0 hp
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpecWithStack,
      calculateAgreementConcreteSpecWithStackFs] at hp ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨hpfs, hregs, hrest⟩
    exact ⟨⟨hpfs, hregs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩
  · rintro ⟨x, st⟩ R s0 sf hq
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementConcreteSpecWithStackFs,
      calculateAgreementSpecWithStack] at hq ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hpfs⟩, hrest⟩
    exact ⟨calculateAgreementEvents X x, hpfs, ⟨htr, rfl⟩, hrest⟩

/-- Contract-backed relocatable `Pfs`-threaded `<PrivateKey>::calculate_agreement` (Block `207`). -/
theorem calculateAgreement_placed_ok_of_contracts_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : String → Option (State → State)}
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (withFsPred Pfs (withVmPreserved (diffieHellmanSpec X))))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (calculateAgreementSpec M A lim X))) :=
  calculateAgreement_placed_ok_of_hooks_gen_fsPred (subStack := allocHookStack) (by decide)
    (dhPlacedCallAt_of_raw_fsPred h_dh)
    (zeroizePlacedCallAt_of_raw_fsPred h_shdrop)
    (ctEqPlacedCallAt_of_withLsCodeLoaded_fsPred hct)
    (shimPlacedCallAt_of_raw_fsPred h_shim)
    (allocPlacedCallAt_of_allocStack_fsPred h_alloc)
    (zeroizePlacedCallAt_of_raw_fsPred h_stdrop)

/-- Relocatable `Pfs`-threaded `<PrivateKey>::calculate_agreement` (Block `207`) from `HookSat`. -/
theorem calculateAgreement_placed_ok_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (calculateAgreementSpec M A lim X))) :=
  calculateAgreement_placed_ok_of_contracts_fsPred
    (M := M) (A := A) (lim := lim) (X := X) (H := H)
    (keys_ls_hook_ok_of_mem (prog := (blkPC_207).rebase (blkPl_207).base H) (i := 207) h_dh)
    (keys_ls_hook_ok_of_mem (prog := (blkPC_207).rebase (blkPl_207).base H) (i := 207) h_shdrop)
    hct
    (keys_ls_hook_ok_of_mem (prog := (blkPC_207).rebase (blkPl_207).base H) (i := 207) h_shim)
    (keys_ls_hook_ok_of_mem (prog := (blkPC_207).rebase (blkPl_207).base H) (i := 207) h_alloc)
    (keys_ls_hook_ok_of_mem (prog := (blkPC_207).rebase (blkPl_207).base H) (i := 207) h_stdrop)

theorem subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec_fsPred
    {Pfs : FsState → Prop} {pl : Obj.MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {X : X25519Fn}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withFsPred Pfs (calculateAgreementSpec M A lim X)))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withFsPred Pfs (calculateAgreementSpecX M A lim X))) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (withFsPred Pfs (calculateAgreementSpec M A lim X))).pre x s0 ∗
        (stackAt (s0.sp - 4256#64) 12288 ∗ R) := by
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec, calculateAgreementSpecX,
      calculateAgreementSpecWithStack, calculateAgreementStackX] at hpre ⊢
    rw [stackAt_calculateAgreementExt_split s0.sp] at hpre
    convert hpre using 1; sep_ac_rfl
  refine h.mono_outcome x (stackAt (s0.sp - 4256#64) 12288 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec, calculateAgreementSpecX,
      calculateAgreementSpecWithStack, calculateAgreementStackX] at hq ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_calculateAgreementExt_split s0.sp]
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec,
      calculateAgreementSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec,
      calculateAgreementSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec,
      calculateAgreementSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable `Pfs`-threaded `<PrivateKey>::calculate_agreement` (Block `207`) at
`calculateAgreementStackX`. -/
theorem calculateAgreement_placed_ok_x_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : X25519Fn} {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (withFsPred Pfs (calculateAgreementSpecX M A lim X))) :=
  subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec_fsPred
    (calculateAgreement_placed_ok_fsPred h_dh h_shdrop hct h_shim h_alloc h_stdrop)

end LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
