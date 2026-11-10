/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded 2-Slice Concatenation and `memcpy` Helpers (Block 386)

Provides `AllocCallPreserved ∧ VmPreserved` `shim`/`memcpy` contracts and 2-slice
`Concat<u8>::concat [local#2]` proofs for block 386.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_386 blkPl_386 lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.SpqrV1.ChainProofs (SliceConcat2Ghost bytesAt bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.Alloc (
  concatStack concatStackXA
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved allocMemcpyVmSpec
  rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack
  subroutine_ok_allocNoOom_withStack_of_hookSat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  hookOk_withVmPreserved vmPreserved_hookMemcpy
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (memRegion_24)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and `vecU8At` Helpers -/

theorem stackAt_concat_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 96) = stackAt (sp - 96#64) hookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp hookStack 12 hhook
  change stackAt sp (hookStack + 96) =
    stackAt (sp - 96#64) hookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

theorem stackAt_extHookStack_eq_concatStack (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp (allocHookStack + 96) ∗ memRegion (sp - 16384#64) 12192 :=
  (ProofLib.stackAt_split_bottom sp (allocHookStack + 96) 12192 (by decide)).trans
    (sepConj_comm _ _)

theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := ofNat_getLsbD_63_false h

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne; intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht; omega

theorem ofNat_ult_of_le {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]; omega

theorem pointsToBytes_append3 (p : BitVec 64) (bs0 bs1 bs2 : List (BitVec 8)) :
    (p ↦ₛ (bs0 ++ bs1 ++ bs2)) = (p ↦ₛ bs0) ∗ ((p + BitVec.ofNat 64 bs0.length) ↦ₛ bs1) ∗
      ((p + BitVec.ofNat 64 (bs0.length + bs1.length)) ↦ₛ bs2) := by
  rw [pointsToBytes_append p (bs0 ++ bs1) bs2, List.length_append, pointsToBytes_append p bs0 bs1,
    sepConj_assoc]

theorem vecU8At_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptr : BitVec 64, vecU8At A v 0#64 ptr [] := by
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  unfold vecU8At vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by sep_ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem vecU8At_of_pos {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      ∃∗ ptr : BitVec 64, vecU8At A.repAlloc v (BitVec.ofNat 64 bs.length) ptr bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  unfold vecU8At vecHeader
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc, RustCliAllocBudget.repAlloc_live]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by sep_ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

theorem vecU8At_of_append_pos {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      ∃∗ ptr : BitVec 64,
        vecU8At A.repAlloc v (BitVec.ofNat 64 (bs0.length + bs1.length)) ptr (bs0 ++ bs1) := by
  have hlen : (bs0 ++ bs1).length = bs0.length + bs1.length := List.length_append
  rw [← hlen]
  exact vecU8At_of_pos A v p' (bs0 ++ bs1) (by rw [hlen]; exact hpos) (by rw [hlen]; exact hlt) hp'

theorem vecU8At_of_append3_pos {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs0 bs1 bs2 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length + bs2.length)
    (hlt : bs0.length + bs1.length + bs2.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)) ∗
      A.live p' (bs0.length + bs1.length + bs2.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1 ++ bs2)) ⊢
      ∃∗ ptr : BitVec 64,
        vecU8At A.repAlloc v (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)) ptr
          (bs0 ++ bs1 ++ bs2) := by
  have hlen : (bs0 ++ bs1 ++ bs2).length = bs0.length + bs1.length + bs2.length := by
    simp only [List.length_append]
  rw [← hlen]
  exact vecU8At_of_pos A v p' (bs0 ++ bs1 ++ bs2) (by rw [hlen]; exact hpos)
    (by rw [hlen]; exact hlt) hp'

theorem vecU8_of_exists_vecU8At (A : RustAlloc) (v cap : BitVec 64) (bs : List (BitVec 8)) :
    (∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs) ⊢ vecU8 A v bs :=
  Entails.sepExists_intro (P := fun c => ∃∗ ptr, vecU8At A v c ptr bs) cap

/-! ## `AllocCallPreserved ∧ VmPreserved` Shim and `memcpy` Specs -/

theorem hookNoop_rustAllocShimVm_ok : HookOk hookNoop rustAllocShimVmSpec := by
  intro _ R s0 hrun hpre _hsp
  dsimp only [rustAllocShimVmSpec] at hpre
  rw [emp_sepConj] at hpre
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · dsimp only [hookNoop, retHook, id]
    rw [CalleeSavedPreserved_setPC]
    unfold CalleeSavedPreserved
    simp [calleeSavedVRegs]
  · dsimp only [rustAllocShimVmSpec, hookNoop]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨⟨rfl, rfl, rfl⟩, by cases s0; rfl, fun _ => by cases s0; rfl,
       fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩

/-- Stack-equipped `AllocCallPreserved ∧ VmPreserved` no-op shim specification. -/
def session2ShimAcpSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp hookStack

theorem session2ShimAcpWithStack_of_rustAllocShimVm {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr rustAllocShimVmSpec) :
    subroutine_ok prog addr (session2ShimAcpSpecWithStack hookStack) := by
  have h' := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack rustAllocShimVmSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, rustAllocShimVmSpec, session2ShimAcpSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

/-- Frameless `AllocCallPreserved ∧ VmPreserved` `memcpy` specification. -/
def framelessMemcpyAcpSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

theorem hookMemcpy_framelessMemcpyAcp_ok : HookOk hookMemcpy framelessMemcpyAcpSpec := by
  have h := hookOk_withVmPreserved
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpy_hookOk vmPreserved_hookMemcpy
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec).pre x s0 ∗ R :=
    hpre
  rcases h x R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyAcpSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpost.2.1.1, ?_, hpost.1⟩, hpost.2.2⟩
    dsimp only [hookMemcpy, retHook]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr hrest

theorem framelessMemcpyAcp_of_allocMemcpyVm {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr allocMemcpyVmSpec) :
    subroutine_ok prog addr framelessMemcpyAcpSpec := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [framelessMemcpyAcpSpec, allocMemcpyVmSpec] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, by rwa [sepConj_assoc]⟩
  · rintro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hq ⊢
    simpa only [sepConj_assoc] using hq

def session2MemcpyAcpSpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

theorem session2MemcpyAcpWithStack_of_frameless {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr framelessMemcpyAcpSpec) :
    subroutine_ok prog addr (session2MemcpyAcpSpecWithStack hookStack) := by
  have h' := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpyAcpSpec hookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, framelessMemcpyAcpSpec, session2MemcpyAcpSpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h'.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpyAcpSpec, session2MemcpyAcpSpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Read-only `AllocCallPreserved ∧ VmPreserved` `memcpy` region contract. -/
def sessionMemcpyRegionROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)

theorem hookMemcpy_region_ro_trace_ok : HookOk hookMemcpy sessionMemcpyRegionROSpec := by
  have h := hookOk_withVmPreserved CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok
    vmPreserved_hookMemcpy
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec).pre x s0 ∗ R :=
    hpre
  rcases h x R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      sessionMemcpyRegionROSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpost.2.1.1, ?_, hpost.1⟩, hpost.2.2⟩
    dsimp only [hookMemcpy, retHook]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr hrest

def sessionMemcpyRegionROSpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

def sessionMemcpyRegionROSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  sessionMemcpyRegionROSpecWithStack extHookStack

/-- `AllocCallPreserved ∧ VmPreserved` `ChainProofs.bytesAt` `memcpy` specification. -/
def sessionMemcpyBytesAtSpec (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ bytesAt ro src bs
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ bytesAt ro src bs

def sessionMemcpyBytesAtSpecWithStack (hookStack : Nat) (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ bytesAt ro src bs ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ bytesAt ro src bs ∗ stackAt s0.sp hookStack

theorem sessionMemcpyRegionROWithStack_of_ro {prog : Program} {addr : BitVec 64}
    (hro : subroutine_ok prog addr sessionMemcpyRegionROSpec) (hookStack : Nat) :
    subroutine_ok prog addr (sessionMemcpyRegionROSpecWithStack hookStack) := by
  have h := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok
    hro hookStack
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionMemcpyRegionROSpec hookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem session_memcpy_bytesAt_ok_at {hookStack : Nat} {prog : Program} {addr : BitVec 64}
    (hmc : subroutine_ok prog addr (session2MemcpyAcpSpecWithStack hookStack))
    (hmc_ro : subroutine_ok prog addr (sessionMemcpyRegionROSpecWithStack hookStack))
    (ro : Bool) :
    subroutine_ok prog addr (sessionMemcpyBytesAtSpecWithStack hookStack ro) := by
  cases ro
  · refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [sessionMemcpyBytesAtSpecWithStack, bytesAt_false] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hpre' : s0.mem ⊨ (session2MemcpyAcpSpecWithStack hookStack).pre (dst, src, bs) s0 ∗ R := by
      dsimp only [session2MemcpyAcpSpecWithStack]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
    exact hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun _ hout => hout
  · exact hmc_ro

theorem acp_chain_acp {s0 sm sf : State} (h1 : AllocCallPreserved sm sf)
    (h0 : AllocCallPreserved s0 sm) : AllocCallPreserved s0 sf :=
  h0.trans h1

/-! ## 2-Slice Concatenation (Block 386) -/

abbrev sliceConcat2Events := LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events
abbrev SliceConcat2Env := LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.SliceConcat2Env
abbrev sliceConcat2Spec := LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Spec

theorem fitsEnv_sliceConcat2_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : SliceConcat2Ghost} :
    FitsEnv M lim st (SliceConcat2Env x) ↔
      FitsEvents M lim st (sliceConcat2Events (x.bs0.length + x.bs1.length)) := by
  constructor
  · intro h
    exact h _ rfl
  · rintro h evs rfl
    exact h

/-- Budget-threaded 2-slice concatenation specification parameterized by callee `hookStack`. -/
def sliceConcat2SpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hookStack : Nat) : Spec (SliceConcat2Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63 ∧
      FitsEnv M lim st (SliceConcat2Env x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 96)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ SliceConcat2Env x evs⌝ ∗
      (∃∗ ptr : BitVec 64,
        vecU8At A.repAlloc x.outVec (BitVec.ofNat 64 (x.bs0.length + x.bs1.length))
          ptr (x.bs0 ++ x.bs1)) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (hookStack + 96)

abbrev sliceConcat2SpecXA (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SliceConcat2Ghost × M.σ) :=
  sliceConcat2SpecWithStack M A lim extHookStack

theorem sliceConcat2Spec_of_withStack {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sliceConcat2SpecWithStack M A lim allocHookStack)) :
    subroutine_ok P addr (sliceConcat2Spec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let btm := memRegion (s0.sp - 16384#64) 12192
  have hpre' : s0.mem ⊨
      (sliceConcat2SpecWithStack M A lim allocHookStack).pre (x, st) s0 ∗ (btm ∗ R) := by
    simpa only [sliceConcat2Spec, LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Spec,
      sliceConcat2SpecWithStack, stackAt_extHookStack_eq_concatStack, btm, sepConj_assoc] using hpre
  refine h.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [sliceConcat2SpecWithStack, sliceConcat2Spec,
      LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Spec,
      stackAt_extHookStack_eq_concatStack, btm, sepExists_sepConj_left, sepConj_assoc] using hq
  · rw [show (sliceConcat2SpecWithStack M A lim allocHookStack).onPanic (x, st) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1
  · rw [show (sliceConcat2SpecWithStack M A lim allocHookStack).onExit (x, st) code s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1
  · rw [show (sliceConcat2SpecWithStack M A lim allocHookStack).onOom (x, st) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1

set_option maxHeartbeats 1600000 in
/-- Block 386 meets `sliceConcat2SpecWithStack M A lim hookStack` given callee hook contracts. -/
theorem slice_concat_2_withStack_placed_ok_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimAcpSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false hookStack))
    (hmc_any : ∀ ro, subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrMemcpySym) (sessionMemcpyBytesAtSpecWithStack hookStack ro)) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecWithStack M A lim hookStack) := by
  unfold sliceConcat2SpecWithStack
  simp only [memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩, st⟩
  dsimp only at *
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hfits_env : FitsEnv M lim st
      (SliceConcat2Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩) := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have htot_lt63 : bs1.length + bs0.length < 2 ^ 63 := by omega
  have htot_lt64 : bs1.length + bs0.length < 2 ^ 64 := by omega
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1
  ·
    simp only [List.length_nil, Nat.add_zero, List.nil_append] at *
    have henv : SliceConcat2Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, []⟩ [] := rfl
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists ([] : List AllocEvent)
    simp only [M.stepEvents_nil]
    apply SepWP.fold (vecU8At_of_zero A.repAlloc outVec) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h1_len_ne : bs1.length ≠ 0 := Nat.ne_of_gt hpos1
    have henv : SliceConcat2Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, bs1⟩
        (rustAllocEvents bs1.length 1) := by
      simp only [SliceConcat2Env, LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.SliceConcat2Env,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.zero_add, h1_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents bs1.length 1) := hfits_env _ henv
    have hlay : RustLayoutOk bs1.length 1 := ⟨⟨hpos1, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs1.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5), p1, bs1)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rcases hacp2 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents bs1.length 1)
    apply SepWP.fold (vecU8At_of_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs1
      hpos1 hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h0_len_ne : bs0.length ≠ 0 := Nat.ne_of_gt hpos0
    have henv : SliceConcat2Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, []⟩
        (rustAllocEvents bs0.length 1) := by
      simp only [SliceConcat2Env, LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.SliceConcat2Env,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, h0_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents bs0.length 1) := hfits_env _ henv
    have hlay : RustLayoutOk bs0.length 1 := ⟨⟨hpos0, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rcases hacp2 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents bs0.length 1)
    apply SepWP.fold (vecU8At_of_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0
      hpos0 hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have htot_pos : 0 < bs0.length + bs1.length := by omega
    have htot_len_ne : bs0.length + bs1.length ≠ 0 := Nat.ne_of_gt htot_pos
    have henv : SliceConcat2Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩
        (rustAllocEvents (bs0.length + bs1.length) 1) := by
      simp only [SliceConcat2Env, LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.SliceConcat2Env,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        htot_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents (bs0.length + bs1.length) 1) :=
      hfits_env _ henv
    have hlay : RustLayoutOk (bs0.length + bs1.length) 1 := ⟨⟨htot_pos, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length + bs1.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    rw [ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) bs0.length bs1.length (by omega)]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 bs0.length, p1, bs1)
    have hacp3 : AllocCallPreserved s0 sf_3 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp2])
    rcases hacp3 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents (bs0.length + bs1.length) 1)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8At_of_append_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1
      htot_pos hmax hptr_ne) (by sep_focus)
    wp_done

theorem slice_concat_2_withStack_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack) (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecWithStack M A lim hookStack) :=
  slice_concat_2_withStack_placed_ok_of_hooks hhook
    (session2ShimAcpWithStack_of_rustAllocShimVm hookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_withStack_of_hookSat halloc spqr_externAt?_of_mem hge (by omega))
    (session_memcpy_bytesAt_ok_at
      (session2MemcpyAcpWithStack_of_frameless hookStack (spqr_hook_ok_of_mem hmemcpy))
      (sessionMemcpyRegionROWithStack_of_ro (spqr_hook_ok_of_mem hRO) hookStack))

/-- Block 386 meets `Chain.DefsBudget.sliceConcat2Spec` under `HookSat`. -/
theorem slice_concat_2_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2Spec M A lim) :=
  sliceConcat2Spec_of_withStack (slice_concat_2_withStack_placed_ok (hookStack := allocHookStack)
    (by decide) (by decide) hshim halloc hmemcpy hRO)

/-- Block 386 meets `sliceConcat2SpecXA` under `HookSat`. -/
theorem slice_concat_2_placed_ok_xa [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecXA M A lim) :=
  slice_concat_2_withStack_placed_ok (hookStack := extHookStack) (by decide) (by decide)
    hshim halloc hmemcpy hRO

end LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
