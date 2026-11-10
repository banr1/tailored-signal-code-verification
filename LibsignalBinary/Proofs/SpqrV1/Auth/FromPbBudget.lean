/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<spqr::authenticator::Authenticator>::from_pb` (Block 330)

Proves `RustCliAllocBudget M` / `AllocCallPreserved` `[LibsignalPlacement]` contracts
for `<spqr::authenticator::Authenticator>::from_pb` (block 330) with deterministic
allocation envelope `AuthFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_330 blkPl_330 lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (Authenticator ProtoAuthenticator)
open CryptoVerification.SpqrV1.ProtoRepr (
  authenticatorPBAt authenticatorPBAt_eq_exists_pinned authenticatorPBPinnedAt
)
open CryptoVerification.SpqrV1.Auth (
  AuthFromPbGhost AuthFromPbPinnedGhost authFromPbStack authenticatorAt vecBufAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack subroutine_ok_rustCliAllocBudget_withStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec rustAllocShimVmSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Allocation Envelope -/

/-- Deterministic `AllocEvent` list for cloning a key byte slice (`[]` if empty, else `rustAllocEvents bs.length 1`). -/
def authKeyCloneEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.isEmpty then [] else rustAllocEvents bs.length 1

/-- Deterministic `AllocEvent` sequence of `Authenticator::from_pb` (`pb.rootKey` then `pb.macKey`). -/
def authFromPbEvents (pb : ProtoAuthenticator) : List AllocEvent :=
  authKeyCloneEvents pb.rootKey ++ authKeyCloneEvents pb.macKey

def AuthFromPbEnv (pb : ProtoAuthenticator) (evs : List AllocEvent) : Prop :=
  evs = authFromPbEvents pb

theorem fitsEvents_of_fitsEnv_authFromPbEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {pb : ProtoAuthenticator} (h : FitsEnv M lim st (AuthFromPbEnv pb)) :
    FitsEvents M lim st (authFromPbEvents pb) :=
  h (authFromPbEvents pb) rfl

/-! ## Budget-Threaded Specifications -/

/-- Budget-threaded pinned specification of `Authenticator::from_pb`. -/
def authFromPbPinnedSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthFromPbPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (AuthFromPbEnv x.pb)⌝ ∗
      memRegion x.out 48 ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp authFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthFromPbEnv x.pb evs⌝ ∗
      authenticatorAt A.repAlloc x.out (Authenticator.fromPb x.pb) ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.pbA x.pb ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authFromPbStack

/-- Budget-threaded unpinned specification of `Authenticator::from_pb`. -/
def authFromPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (AuthFromPbEnv x.pb)⌝ ∗
      memRegion x.out 48 ∗
      authenticatorPBAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp authFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AuthFromPbEnv x.pb evs⌝ ∗
      authenticatorAt A.repAlloc x.out (Authenticator.fromPb x.pb) ∗
      authenticatorPBAt A.repAlloc x.pbA x.pb ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authFromPbStack

/-! ## Zeroed Allocator and IKM Deallocation Helpers -/

abbrev rustAllocZeroedSpecWithStack [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpecWithStack M A lim true hookStack

theorem rustAllocZeroedWithStack_of_rustAllocZeroed [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (hstack : allocHookStack ≤ hookStack) (hbound : hookStack ≤ 2 ^ 64)
    (h : subroutine_ok P addr (rustCliAllocBudgetSpec M A lim true)) :
    subroutine_ok P addr (rustAllocZeroedSpecWithStack M A lim hookStack) :=
  subroutine_ok_rustCliAllocBudget_withStack hstack hbound h

/-- Local resource bundle for the `Vec<u8>` IKM deallocation tail (`+488..+544`). -/
def ikmDeallocLocal {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (_hlen : bs.length ≤ cap.toNat) (_hptr : ptr ≠ 0) (st : M.σ) (s : State) (sp : BitVec 64) :
    SepProp :=
  vecBufAt A.repAlloc cap ptr bs ∗ A.pool lim st s ∗ stackAt sp extHookStack

/-! ## Frame Layout and Return Helpers -/

private theorem stackAt_authFromPb (sp : BitVec 64) :
    stackAt sp authFromPbStack =
      stackAt (sp - 64#64) allocHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4096 8 (by decide)
  change stackAt sp authFromPbStack =
    stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (a ↦₆₄ w5) ∗ ((a + 8#64) ↦₆₄ w4) ∗ ((a + 16#64) ↦₆₄ w3) ∗
        ((a + 24#64) ↦₆₄ w2) ∗ ((a + 32#64) ↦₆₄ w1) ∗ ((a + 40#64) ↦₆₄ w0)) := by
  rw [ProofLib.memRegion_split a 24 24 (by decide), memRegion_24, memRegion_24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem cap_ne_zero_of_pos {cap : BitVec 64} {n : Nat} (hpos : 0 < n) (hle : n ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h
  subst h
  change n ≤ 0 at hle
  omega

private theorem vecU8_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

private theorem vecU8_of_pos (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

private theorem out_add24_add8 (out : BitVec 64) :
    (out + 24#64) + 8#64 = out + 32#64 := by bv_omega

private theorem out_add24_add16 (out : BitVec 64) :
    (out + 24#64) + 16#64 = out + 40#64 := by bv_omega

private theorem sepExists_eq_singleton {P : Prop} (evs0 : List AllocEvent)
    (Q : List AllocEvent → SepProp) :
    (∃∗ evs : List AllocEvent, ⌜P ∧ evs = evs0⌝ ∗ Q evs) = (⌜P⌝ ∗ Q evs0) := by
  apply Entails.antisymm
  · apply Entails.sepExists_elim
    intro evs
    apply Entails.pure_left
    rintro ⟨hp, rfl⟩
    exact Entails.pure_right hp (Entails.refl _)
  · apply Entails.pure_left
    intro hp
    exact Entails.sepExists_right evs0 (Entails.pure_right ⟨hp, rfl⟩ (Entails.refl _))

/-! ## Relocatable Contracts (Block 330) -/

set_option maxHeartbeats 1600000 in
/-- Block 330 (`Authenticator::from_pb`) meets `authFromPbPinnedSpec M A lim`. -/
theorem auth_from_pb_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "memcpy") allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base H) (blkPl_330).base
      (authFromPbPinnedSpec M A lim) := by
  have hallocNoOom : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  dsimp only [rustAllocShimVmSpec] at hshim
  dsimp only [rustCliAllocNoOomSpec, RustCliAllocBudget.live, ↓reduceIte] at hallocNoOom
  dsimp only [allocMemcpyVmSpec] at hmc
  simp only [authFromPbPinnedSpec, AuthFromPbEnv, sepExists_eq_singleton]
  simp only [authenticatorPBPinnedAt, authenticatorAt,
    Authenticator.fromPb, vecU8At, vecHeader, memRegion_48_cells, stackAt_authFromPb,
    out_add24_add8, out_add24_add16, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_init g s0
  obtain ⟨⟨out, pbA, ⟨⟨cap0, ptr0⟩, ⟨cap1, ptr1⟩⟩, ⟨rootKey, macKey⟩⟩, st⟩ := g
  dsimp only at *
  have hfit_all : FitsEvents M lim st (authFromPbEvents ⟨rootKey, macKey⟩) :=
    fitsEvents_of_fitsEnv_authFromPbEnv ‹FitsEnv M lim st _›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hr_le : rootKey.length ≤ cap0.toNat := ‹_›
  have hr_cap : cap0.toNat < 2 ^ 63 := ‹_›
  have hm_le : macKey.length ≤ cap1.toNat := ‹_›
  have hm_cap : cap1.toNat < 2 ^ 63 := ‹_›
  have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
  have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
  have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
  have hm_lt64 : macKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hr_cases with rfl | hr_pos <;>
    rcases hm_cases with rfl | hm_pos
  · -- Case 1: rootKey = [] ∧ macKey = []
    have hevs : authFromPbEvents ⟨[], []⟩ = [] := rfl
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hevs, M.stepEvents_nil] at *
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply SepWP.fold (vecU8_of_zero A.repAlloc out) (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
        vecU8 A.repAlloc (out + 24#64) [] := by
      simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A.repAlloc (out + 24#64)
    apply SepWP.fold h2 (by sep_focus)
    wp_done
  · -- Case 2: rootKey = [] ∧ 0 < macKey.length
    have hne_nil1 : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authFromPbEvents ⟨[], macKey⟩ = rustAllocEvents macKey.length 1 := by
      simp [authFromPbEvents, authKeyCloneEvents, hne_nil1]
    rw [hevs] at hfit_all
    have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hrlay1 : RustLayoutOk macKey.length 1 := ⟨⟨hm_pos, hpow1, by omega⟩, by decide⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap1_ne, hevs, ↓reduceIte, sepConj_assoc] at *
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s0 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_shim : sf.trace = s0.trace := hacp_shim.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    simp only [State.setMem_setMem]
    wp_call hallocNoOom (macKey.length, 1, st)
    have hne1 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hbeq1 : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hne1
    have hacp_alloc : AllocCallPreserved s0 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_pool (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, ptr1, macKey)
    have hacp_mc : AllocCallPreserved s0 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have htr_mc : sf_2.trace = s0.trace := hacp_mc.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply SepWP.fold (vecU8_of_zero A.repAlloc out) (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        ((out + 32#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        A.live (sf_1.readReg64 .x0) macKey.length 1 ∗
        (sf_1.readReg64 .x0 ↦ₛ macKey) ⊢
        vecU8 A.repAlloc (out + 24#64) macKey := by
      simpa only [out_add24_add8, out_add24_add16, RustCliAllocBudget.repAlloc] using
        vecU8_of_pos A.repAlloc (out + 24#64) (sf_1.readReg64 .x0) macKey hm_pos hm_lt63 hne1
    apply SepWP.fold h2 (by sep_focus)
    wp_done
  · -- Case 3: 0 < rootKey.length ∧ macKey = []
    have hne_nil0 : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authFromPbEvents ⟨rootKey, []⟩ = rustAllocEvents rootKey.length 1 := by
      simp [authFromPbEvents, authKeyCloneEvents, hne_nil0]
    rw [hevs] at hfit_all
    have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hrlay0 : RustLayoutOk rootKey.length 1 := ⟨⟨hr_pos, hpow1, by omega⟩, by decide⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap0_ne, hevs, ↓reduceIte, sepConj_assoc] at *
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s0 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    simp only [State.setMem_setMem]
    wp_call hallocNoOom (rootKey.length, 1, st)
    have hne0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hbeq0 : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hne0
    have hacp_alloc : AllocCallPreserved s0 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_pool (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, ptr0, rootKey)
    have hacp_mc : AllocCallPreserved s0 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have htr_mc : sf_2.trace = s0.trace := hacp_mc.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have h1 : (out ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        ((out + 8#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        ((out + 16#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        A.live (sf_1.readReg64 .x0) rootKey.length 1 ∗
        (sf_1.readReg64 .x0 ↦ₛ rootKey) ⊢
        vecU8 A.repAlloc out rootKey := by
      simpa only [RustCliAllocBudget.repAlloc] using
        vecU8_of_pos A.repAlloc out (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hne0
    apply SepWP.fold h1 (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
        vecU8 A.repAlloc (out + 24#64) [] := by
      simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A.repAlloc (out + 24#64)
    apply SepWP.fold h2 (by sep_focus)
    wp_done
  · -- Case 4: 0 < rootKey.length ∧ 0 < macKey.length
    have hne_nil0 : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hne_nil1 : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authFromPbEvents ⟨rootKey, macKey⟩ =
        rustAllocEvents rootKey.length 1 ++ rustAllocEvents macKey.length 1 := by
      simp [authFromPbEvents, authKeyCloneEvents, hne_nil0, hne_nil1]
    rw [hevs] at hfit_all
    rcases (fitsEvents_append M lim
      (rustAllocEvents rootKey.length 1) (rustAllocEvents macKey.length 1) st).mp hfit_all
      with ⟨hfit0, hfit1⟩
    have hstep_append :
        M.stepEvents (rustAllocEvents rootKey.length 1 ++ rustAllocEvents macKey.length 1) st =
          M.stepEvents (rustAllocEvents macKey.length 1)
            (M.stepEvents (rustAllocEvents rootKey.length 1) st) :=
      M.stepEvents_append _ _ st
    have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hrlay0 : RustLayoutOk rootKey.length 1 := ⟨⟨hr_pos, hpow1, by omega⟩, by decide⟩
    have hrlay1 : RustLayoutOk macKey.length 1 := ⟨⟨hm_pos, hpow1, by omega⟩, by decide⟩
    simp only [hcap0_ne, hcap1_ne, hevs, hstep_append, ↓reduceIte, sepConj_assoc] at *
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_0 : AllocCallPreserved s0 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    simp only [State.setMem_setMem]
    wp_call hallocNoOom (rootKey.length, 1, st)
    have hne0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hbeq0 : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hne0
    have hacp_1 : AllocCallPreserved s0 sf_1 :=
      hacp_0.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_pool (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, ptr0, rootKey)
    have hacp_2 : AllocCallPreserved s0 sf_2 :=
      hacp_1.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_3 : AllocCallPreserved s0 sf_3 :=
      hacp_2.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_3›)
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    simp only [State.setMem_setMem]
    wp_call hallocNoOom (macKey.length, 1, M.stepEvents (rustAllocEvents rootKey.length 1) st)
    have hne1 : sf_4.readReg64 .x0 ≠ 0#64 := ‹_›
    have hbeq1 : (sf_4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hne1
    have hacp_4 : AllocCallPreserved s0 sf_4 :=
      hacp_3.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_4›)
    wp_steps_sync_pool (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_4.readReg64 .x0, ptr1, macKey)
    have hacp_5 : AllocCallPreserved s0 sf_5 :=
      hacp_4.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_5›)
    have htr_5 : sf_5.trace = s0.trace := hacp_5.2.1
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have h1 : (out ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        ((out + 8#64) ↦₆₄ sf_1.readReg64 .x0) ∗
        ((out + 16#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        A.live (sf_1.readReg64 .x0) rootKey.length 1 ∗
        (sf_1.readReg64 .x0 ↦ₛ rootKey) ⊢
        vecU8 A.repAlloc out rootKey := by
      simpa only [RustCliAllocBudget.repAlloc] using
        vecU8_of_pos A.repAlloc out (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hne0
    apply SepWP.fold h1 (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        ((out + 32#64) ↦₆₄ sf_4.readReg64 .x0) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        A.live (sf_4.readReg64 .x0) macKey.length 1 ∗
        (sf_4.readReg64 .x0 ↦ₛ macKey) ⊢
        vecU8 A.repAlloc (out + 24#64) macKey := by
      simpa only [out_add24_add8, out_add24_add16, RustCliAllocBudget.repAlloc] using
        vecU8_of_pos A.repAlloc (out + 24#64) (sf_4.readReg64 .x0) macKey hm_pos hm_lt63 hne1
    apply SepWP.fold h2 (by sep_focus)
    wp_done

/-- Block 330 (`Authenticator::from_pb`) meets `authFromPbSpec M A lim`. -/
theorem auth_from_pb_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "memcpy") allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base H) (blkPl_330).base
      (authFromPbSpec M A lim) := by
  have hpinned := auth_from_pb_pinned_placed_ok hshim halloc hmc
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp => ?_
  simp only [authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.out, x.pbA, g, x.pb⟩, st) R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [authFromPbPinnedSpec, authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    exact ⟨evs, g, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

end LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
