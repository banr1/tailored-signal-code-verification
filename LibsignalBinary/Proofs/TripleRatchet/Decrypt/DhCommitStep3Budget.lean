/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvictBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPackBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded DH Step Commit Sub-Segment 3 (`+0xa84 → +0xaf0`)

Defines the Step 3 allocator event lists (`dhCommitStep3aEvents`, `dhCommitStep3Events`), the
stack-parametric `growOneSpecWithStack`, `VmPreserved` basic-block `SepWP` bundles for blocks `130`
and `433`, and relocatable `dhCommit_step3` theorems over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open scoped CryptoVerification.RustHeap
open CryptoGames.LibsignalSession (ChainKey PublicKey ReceiverChain)
open CryptoVerification (LibsignalPlacement lsRustDeallocSym lsmpl)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_131 blkPC_434 blkPl_131 blkPl_434 growOneChainStackX)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (add_assoc_const cells_4_to_memRegion_32 chainAt_newChain_of_cells chainHeaps elim_memRegion_104 growOneStack newChainGhost newReceiverChain optChainKeyHeap optChainKeyTailBytes optChainKeyTailBytes_length pointsToBytes_32_eq_pointsTo64 publicKey_serialize_length saturating_sub_one_u32 stackAt_split_from vecBuf_chainAt_expose_bytes vecBuf_chainAt_of_bytes vecBuf_chainAt_push_reassemble vecBuf_expose_for_grow vecBuf_expose_for_push)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecBuf)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved fitsEvents_append fitsEvents_nil rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceSimp (ReachesOrPanicOom)

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  growOne104Events GrowOne104Env fitsEnv_growOne104_iff
)

abbrev growOneChainSpecXB :=
  LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX

/-! ## 1. Allocator Event Lists, Envelopes, and Stack-Parametric `grow_one` Spec -/

/-- Deterministic `AllocEvent` list for Step 3a (`+0xa84 → +0xa9c`): emits
`growOne104Events chainsCap` iff `rcLen = chainsCap`, else `[]`. -/
def dhCommitStep3aEvents (chainsCap rcLen : BitVec 64) : List AllocEvent :=
  if rcLen = chainsCap then growOne104Events chainsCap else []

/-- Deterministic `AllocEvent` list for full Step 3 (`+0xa84 → +0xaf0`): Step 3a followed by
`__rust_dealloc(boxPtr, 33, 1)`. -/
def dhCommitStep3Events (chainsCap rcLen : BitVec 64) : List AllocEvent :=
  dhCommitStep3aEvents chainsCap rcLen ++ rustDeallocEvents 33 1

/-- Allocation envelope for Step 3 (`+0xa84 → +0xaf0`). -/
def DhCommitStep3Env (chainsCap rcLen : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = dhCommitStep3Events chainsCap rcLen

theorem fitsEnv_dhCommitStep3_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {chainsCap rcLen : BitVec 64} :
    FitsEnv M lim st (DhCommitStep3Env chainsCap rcLen) ↔
      FitsEvents M lim st (dhCommitStep3Events chainsCap rcLen) :=
  ⟨fun h => h _ rfl, fun h _ he => he ▸ h⟩

theorem fitsEvents_dhCommitStep3a_of_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {chainsCap rcLen : BitVec 64}
    (h : FitsEvents M lim st (dhCommitStep3Events chainsCap rcLen)) :
    FitsEvents M lim st (dhCommitStep3aEvents chainsCap rcLen) := by
  unfold dhCommitStep3Events at h
  rw [fitsEvents_append] at h
  exact h.1

theorem fitsEvents_dhCommitStep3a_of_imp {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {chainsCap rcLen : BitVec 64}
    (h : rcLen = chainsCap → FitsEvents M lim st (growOne104Events chainsCap)) :
    FitsEvents M lim st (dhCommitStep3aEvents chainsCap rcLen) := by
  unfold dhCommitStep3aEvents
  by_cases heq : rcLen = chainsCap
  · simp only [heq, ↓reduceIte]
    exact h heq
  · simp only [heq, ↓reduceIte, fitsEvents_nil]

/-- Stack-parametric budget-threaded `<RawVec<Chain>>::grow_one` contract (`stride = 104`,
`align = 8`). Definitionally equal to `GrowOneXBudget.growOneChainSpecX` at `growOneChainStackX`. -/
def growOneSpecWithStack (stk : Nat) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp stk
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool lim (M.stepEvents (growOne104Events cap) st) sf ∗
      stackAt s0.sp stk

/-- Standard-stack (`growOneStack = 4608`) budget-threaded `<RawVec<Chain>>::grow_one` contract. -/
abbrev growOneSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) :=
  growOneSpecWithStack growOneStack M A lim

theorem growOneSpecWithStack_eq_growOneChainSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    growOneSpecWithStack growOneChainStackX M A lim =
      LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX M A lim :=
  rfl

/-- Bridge `FromRecordCallees.GrowSpeBudget.growOne104SpecX` to
`GrowOneXBudget.growOneChainSpecX` (`= growOneSpecWithStack growOneChainStackX`). -/
theorem subroutine_ok_growOneChainSpecX_of_growSpe {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget.growOne104SpecX M A lim)) :
    subroutine_ok prog entry
      (LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX M A lim) := by
  have hevs_eq : ∀ (cap : BitVec 64) (evs : List AllocEvent),
      LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget.GrowOne104Env cap evs →
      evs = growOne104Events cap := by
    intro cap evs henv
    unfold growOne104Events LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents
    rcases henv with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
    · rfl
    · have hc0 : cap.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
      simp only [hc0, ↓reduceIte]
  refine subroutine_ok_outcome_intro (fun ((v, cap, ptr, bs), st) R s0 hpc0 hrun0 hpre0 hsp0 => ?_)
  have hpre_spe : s0.mem ⊨
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget.growOne104SpecX M A lim).pre
        ((v, cap, ptr, bs), st) s0 ∗ R := by
    dsimp only [LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX,
      LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOne104SpecX,
      LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget.growOne104SpecX] at hpre0 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hlen, hptr, hmax, hfits⟩, hmem0⟩
    refine ⟨⟨hx0, hlen, hptr, hmax, fun evs henv => ?_⟩, hmem0⟩
    rw [hevs_eq cap evs henv]
    exact (fitsEnv_growOne104_iff.mp hfits)
  refine h.mono_outcome ((v, cap, ptr, bs), st) R s0 hpc0 hrun0 hpre_spe hsp0 (fun sf hout => ?_)
  rcases hout with ⟨hret, hpres, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hpres, ?_⟩
    dsimp only [LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX,
      LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOne104SpecX,
      LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget.growOne104SpecX] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, henv⟩, hpost⟩
    rw [hevs_eq cap evs henv] at hpost
    rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hp', _halign⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hp', by refine Satisfies.mono (Entails.of_eq ?_) hpost; sep_ac_rfl⟩
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

/-! ## 2. `VmPreserved`-Carrying Basic-Block `SepWP` Predicates & Block `130` / `433` Instances -/

/-- Step 3a (`+0xa84 → +0xa9c`) when `rcLen ≠ chainsCap`, carrying `VmPreserved`. -/
abbrev CommitStep3aNogrowVmWp (prog : Program) (entry : BitVec 64) : Prop :=
  ∀ (sp chainsCap rcLen : BitVec 64) (s : State),
    s.pc = entry + 0xa84#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    rcLen ≠ chainsCap →
    SepWP prog (entry + 0xa9c#64) s
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ rcLen)))

/-- Step 3a (`+0xa84 → growEntry`) when `rcLen = chainsCap`, carrying `VmPreserved`. -/
abbrev CommitStep3aGrowVmWp (prog : Program) (entry growEntry : BitVec 64) : Prop :=
  ∀ (sp rcLen : BitVec 64) (s : State),
    s.pc = entry + 0xa84#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    SepWP prog growEntry s
      (((sp + 0x38#64) ↦₆₄ rcLen) ∗ ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xa9c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x38#64) ↦₆₄ rcLen) ∗ ((sp + 0x48#64) ↦₆₄ rcLen)))

/-- Step 3b (`+0xa9c → deallocEntry`), carrying `VmPreserved`. -/
abbrev CommitStep3bVmWp (prog : Program) (entry deallocEntry : BitVec 64) : Prop :=
  ∀ (sp chainsPtr1 rcLen boxPtr srkPtr : BitVec 64)
    (ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) (s : State),
    s.pc = entry + 0xa9c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
    s.readReg64 .x24 = rcLen → s.readReg64 .x25 = sp + 0x190#64 →
    s.readReg64 .x26 = 33#64 → s.readReg64 .x27 = boxPtr → s.readReg64 .x28 = srkPtr →
    SepWP prog deallocEntry s
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = boxPtr ∧ sf.readReg64 .x1 = 33#64 ∧ sf.readReg64 .x2 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = rcLen + 1#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xaf0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ (rcLen + 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
          ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
          ((chainsPtr1 + rcLen * 104#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ srkPtr) ∗
          ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ 1#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ 8#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ ck0) ∗
          ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ ck1) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ ck2) ∗
          ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ ck3)))

/-- Bundle of `VmPreserved`-carrying `SepWP` obligations for Step 3 (`+0xa84 → +0xaf0`). -/
structure DhCommitStep3BlockWp (prog : Program) (entry growEntry deallocEntry : BitVec 64) : Prop where
  step3a_nogrow : CommitStep3aNogrowVmWp prog entry
  step3a_grow : CommitStep3aGrowVmWp prog entry growEntry
  step3b : CommitStep3bVmWp prog entry deallocEntry

section BlockWpInstances

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.writeReg64_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.writeReg32_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setPC_trace,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setPState_trace, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.setMem_trace, State.trace_writeVReg128,
    *])

local macro "wp_done_vm_reg" hsp_al:ident : tactic =>
  `(tactic|
    by_vm_steps (
      wp_steps
      refine SepWP.done (by rfl) (by wp_reg) ?_
      refine And.intro (by wp_reg) ?_
      refine And.intro (by wp_reg)
        (And.intro (CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts.spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
      repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
      try rw [← saturating_sub_one_u32 _]
      exact Entails.refl _))

set_option maxHeartbeats 800000 in
theorem dhCommitStep3BlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep3BlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym) where
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_vm_reg hsp_align
  step3a_grow := by
    intro _ _ s hpc hrun hsp hsp_align
    wp_done_vm_reg hsp_align
  step3b := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28
    wp_done_vm_reg hsp_align

set_option maxHeartbeats 800000 in
theorem dhCommitStep3BlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitStep3BlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym) where
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_vm_reg hsp_align
  step3a_grow := by
    intro _ _ s hpc hrun hsp hsp_align
    wp_done_vm_reg hsp_align
  step3b := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28
    wp_done_vm_reg hsp_align

end BlockWpInstances

/-! ## 3. Total-Correctness `Steps` Continuation Combinators -/

private theorem steps_of_sepWP {prog : Program} {s : State}
    {target : BitVec 64} {Pre Rest : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ Rest) →
      PostWP s1 P_out →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 P_out hpc1 hrun1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hm1 hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem steps_of_call_no_panic {α : Type} {prog : Program} {s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Rest : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ Rest) →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg Rest s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

/-! ## 4. Budget-Threaded Sub-Segment 3 Composition (`+0xa84 → +0xa9c → +0xaf0`) -/

/-- Stack-parametric budget-threaded Step 3a (`+0xa84 → +0xa9c`): checks `rcLen = chainsCap`,
calling `<RawVec<Chain>>::grow_one` if equal and preserving `A.pool` via `VmPreserved` otherwise. -/
theorem dhCommit_step3a_of_wp {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry (growOneSpecWithStack stk M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R)) :
    let st1 := M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
           A.pool lim st1 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro st1
  have hexp0 : s.mem ⊨
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       A.pool lim st0 s ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  by_cases hgrow : BitVec.ofNat 64 gcs.length = chainsCap
  · have hst1_eq : st1 = M.stepEvents (growOne104Events chainsCap) st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]
    have hfits_grow : FitsEnv M lim st0 (GrowOne104Env chainsCap) := by
      rw [fitsEnv_growOne104_iff]
      dsimp only [dhCommitStep3aEvents] at hfits3a
      simpa only [hgrow, ↓reduceIte] using hfits3a
    have hexp := Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_expose_bytes A.repAlloc chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A.repAlloc chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
      rw [hgrow]
    have hm_grow_wp : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
          chainHeaps A.repAlloc gcs ∗ A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      rw [h38_grow] at hexp
      change _ at hexp
      refine Satisfies.mono (Entails.of_eq ?_) hexp; sep_ac_rfl
    refine steps_of_sepWP
      (hwp.step3a_grow sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align)
      hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1] at hm1'
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨
        (growOneSpecWithStack stk M A lim).pre ((sp + 0x38#64, chainsCap, chainsPtr, bs), st0) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          chainHeaps A.repAlloc gcs ∗ Frame) ∗ R) := by
      dsimp only [growOneSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by omega, hptr, hmax_lt, hfits_grow⟩, ?_⟩
      have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
      rw [h38_8]
      rw [← h38_grow] at hm1'
      refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    refine steps_of_call_no_panic hGrow hpc1 hrun1 hsp_align1 hx30_1 hm_call hL1
      (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hL2 hm2
    dsimp only [growOneSpecWithStack] at hm2
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
    rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨hp', hm2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < cap1.toNat := by omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
    rw [h38_8, ← hst1_eq] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.repAlloc.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]; rfl
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
      rw [hlen_bs, hcap1_toNat, ← hlen_eq_cap]
    have hpull2 : s2.mem ⊨
        (A.repAlloc.live p' (cap1.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
         memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) ∗
         chainHeaps A.repAlloc gcs) ∗
        (((sp + 0x38#64) ↦₆₄ cap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         A.pool lim st1 s2 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
      rw [hlive_eq, hmr_eq] at hm2
      refine Satisfies.mono (Entails.of_eq ?_) hm2; sep_ac_rfl
    have hreasm := vecBuf_chainAt_of_bytes A.repAlloc cap1 p' hcap1_ne hbs (by omega) (by omega) hp'
    have hm2_vec := Satisfies.mono (sepConj_mono_left hreasm) hpull2
    have hm2_final : s2.mem ⊨
        (((sp + 0x38#64) ↦₆₄ cap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) cap1 p' gcs ∗
         A.pool lim st1 s2 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm2_vec; sep_ac_rfl
    exact ⟨s2, .refl s2, cap1, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      htr2.trans (htr1.trans htrace), by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, hL2, hm2_final⟩
  · have hst1_eq : st1 = st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]; exact M.stepEvents_nil st0
    have hle_cap : gcs.length ≤ chainsCap.toNat := by
      unfold vecBuf at hexp0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hexp0
      exact hexp0.1.1
    have hlt_cap : gcs.length < chainsCap.toNat := by
      rcases Nat.lt_or_eq_of_le hle_cap with hlt | heq
      · exact hlt
      · exfalso; apply hgrow; rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hm_nogrow : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
    refine steps_of_sepWP
      (hwp.step3a_nogrow sp chainsCap (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hgrow)
      hm_nogrow hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1, ← hst1_eq] at hm1'
    have hm1_final : s1.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
         A.pool lim st1 s1 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    exact ⟨s1, .refl s1, chainsCap, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

/-- Stack-parametric budget-threaded Step 3b (`+0xa9c → +0xaf0`): writes the new `ReceiverChain`
into slot `rcLen`, increments `rcLen`, and calls `__rust_dealloc(boxPtr, 33, 1)`. -/
theorem dhCommit_step3b_of_wp [LibsignalPlacement] {prog : Program} {entry deallocEntry : BitVec 64}
    (hwp3b : CommitStep3bVmWp prog entry deallocEntry)
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 : M.σ)
    (hDealloc : subroutine_ok prog deallocEntry (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s s1 : State)
    (sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlt_cap1 : gcs.length < chainsCap1.toNat)
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hpc1 : s1.pc = entry + 0xa9c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp) (hsp_align1 : s1.spAligned = true) (htr1 : s1.trace = s0.trace)
    (hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19)
    (hx20_1 : s1.readReg64 .x20 = s.readReg64 .x20)
    (hx21_1 : s1.readReg64 .x21 = s.readReg64 .x21)
    (hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22)
    (hx23_1 : s1.readReg64 .x23 = s.readReg64 .x23)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 gcs.length)
    (hx25_1 : s1.readReg64 .x25 = s.readReg64 .x25)
    (hx26_1 : s1.readReg64 .x26 = s.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s.readReg64 .x27)
    (hx28_1 : s1.readReg64 .x28 = s.readReg64 .x28)
    (hx29_1 : s1.readReg64 .x29 = s.readReg64 .x29)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL1 : prog.CodeLoaded s1.mem)
    (hm1 : s1.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
       A.pool lim st1 s1 ∗ stackAt sp stk) ∗
      ((((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
        memRegion (sp + 0x1b0#64) 72 ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
        Frame) ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (rustDeallocEvents 33 1) st1
    ∃ sf, Steps prog s1 sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro newGC st2
  have hm1_push : s1.mem ⊨
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st1 s1 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1; sep_ac_rfl
  have hm1_exp := Satisfies.mono
    (sepConj_mono_left (vecBuf_expose_for_push A.repAlloc chainsCap1 chainsPtr1 gcs hlt_cap1)) hm1_push
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_exp
  rcases hm1_exp with ⟨⟨hcap1_lt, hptr1_ne⟩, hm1_exp⟩
  set rcLen := BitVec.ofNat 64 gcs.length
  set slot := chainsPtr1 + rcLen * 104#64
  have hm1_slot : s1.mem ⊨
      memRegion slot 104 ∗
      (A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
       ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st1 s1 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1_exp; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, hm1_w⟩ :=
    elim_memRegion_104 hm1_slot
  set tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
  have htail_len : tail.length = 32 := optChainKeyTailBytes_length ⟨32#64, ckPtr⟩ (some rck) hpad
  have h190_cells : ((sp + 0x190#64) ↦ₛ tail) =
      ((sp + 0x190#64) ↦₆₄ CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (tail.take 8)) ∗
      ((sp + 0x198#64) ↦₆₄ CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((tail.drop 8).take 8)) ∗
      ((sp + 0x1a0#64) ↦₆₄ CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((tail.drop 16).take 8)) ∗
      ((sp + 0x1a8#64) ↦₆₄ CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (tail.drop 24)) := by
    rw [pointsToBytes_32_eq_pointsTo64 (sp + 0x190#64) htail_len,
      add_assoc_const sp 0x190#64 8#64 0x198#64,
      add_assoc_const sp 0x190#64 16#64 0x1a0#64,
      add_assoc_const sp 0x190#64 24#64 0x1a8#64]
  set ck0 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (tail.take 8)
  set ck1 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((tail.drop 8).take 8)
  set ck2 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 ((tail.drop 16).take 8)
  set ck3 := CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.pack64 (tail.drop 24)
  have hm_step3b : s1.mem ⊨
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12)) ∗
      ((A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
        arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
        memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ memRegion (sp + 0x1b0#64) 72 ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
        A.pool lim st1 s1 ∗ stackAt sp stk ∗ Frame) ∗ R) := by
    rw [h190_cells] at hm1_w
    dsimp only [slot] at hm1_w
    refine Satisfies.mono (Entails.of_eq ?_) hm1_w; sep_ac_rfl
  refine steps_of_sepWP
    (hwp3b sp chainsPtr1 rcLen boxPtr srkPtr
      ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      s1 hpc1 hrun1 hsp1 hsp_align1 hx24_1
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain))
    hm_step3b hL1 ?_
  intro s2 P2 hpc2 hrun2 hL2 hm2 hpost2
  rcases hpost2 with ⟨hvm2, hsp2, hsp_align2, htr2, hx0_2, hx1_2, hx2_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _hx24_2, hx25_2, _hx26_2, _hx27_2, _hx28_2,
    hx29_2, hx30_2, hvregs_2, hP2⟩
  have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
  rw [← A.pool_transport lim st1 s1 s2 hvm2] at hm2'
  have h190_reg :
      (((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗
      memRegion (sp + 0x1b0#64) 72 ⊢ memRegion (sp + 0x190#64) 104 := by
    have hsplit104 := memRegion_split (sp + 0x190#64) 32 72 (by decide)
    rw [show (32 + 72 : Nat) = 104 from rfl] at hsplit104
    rw [hsplit104, add_assoc_const sp 0x190#64 (BitVec.ofNat 64 32) 0x1b0#64]
    have h32 := cells_4_to_memRegion_32 (sp + 0x190#64) ck0 ck1 ck2 ck3
    rw [add_assoc_const sp 0x190#64 8#64 0x198#64,
      add_assoc_const sp 0x190#64 16#64 0x1a0#64,
      add_assoc_const sp 0x190#64 24#64 0x1a8#64] at h32
    exact sepConj_mono_left h32
  have hslot_eq : chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104) = slot := by
    dsimp only [slot, rcLen]; rw [BitVec.ofNat_mul]
  have hnew_chain :
      (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
        ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
        ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
        ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
        ((slot + 96#64) ↦₆₄ ck3) ∗
        (A.repAlloc.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck))) ⊢
      chainAt A.repAlloc newGC (chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104)) := by
    rw [hslot_eq]
    exact chainAt_newChain_of_cells A.repAlloc slot srkPtr ckPtr srk rck hpad hsrk_ne
  have hpush_vec := vecBuf_chainAt_push_reassemble A.repAlloc chainsCap1 chainsPtr1 gcs newGC
    hlt_cap1 hcap1_lt hptr1_ne
  have hlen_append : rcLen + 1#64 = BitVec.ofNat 64 (gcs ++ [newGC]).length := by
    dsimp only [rcLen]; rw [List.length_append, List.length_singleton, BitVec.ofNat_add]
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  have hm2_grouped : s2.mem ⊨
      (A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
       (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
         ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
         ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
         ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
         ((slot + 96#64) ↦₆₄ ck3) ∗
         (A.repAlloc.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
         optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck))) ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104)) ∗
      ((((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
        ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗
       memRegion (sp + 0x1b0#64) 72) ∗
      ((boxPtr ↦ₛ srk.serialize) ∗
       (A.live boxPtr 33 1 ∗ A.pool lim st1 s2 ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        stackAt sp stk ∗ Frame ∗ R)) := by
    rw [← hlen_append]
    dsimp only [slot]
    refine Satisfies.mono (Entails.of_eq ?_) hm2'; sep_ac_rfl
  have hm2_chain := Satisfies.mono
    (sepConj_mono
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hnew_chain)))
        hpush_vec)
      (sepConj_mono_left h190_reg))
    hm2_grouped
  have hbox_reg : (boxPtr ↦ₛ srk.serialize) ⊢ memRegion boxPtr 33 := by
    have h := pointsToBytes_entails_memRegion boxPtr srk.serialize
    rwa [hser_len] at h
  have hm2_box := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hbox_reg)))
    hm2_chain
  have hstk_dealloc := stackAt_split_from sp stk allocHookStack hstk_lo hstk_hi
  have hm_dealloc : s2.mem ⊨
      (rustCliDeallocBudgetSpec M A lim).pre (boxPtr, 33, 1, st1) s2 ∗
      ((((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
        memRegion (sp + 0x190#64) 104 ∗
        memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        Frame) ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec]
    rw [hstk_dealloc] at hm2_box
    rw [hsp2, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_2, by rw [hx1_2]; rfl, by rw [hx2_2]; rfl, hx30_2.symm ▸ hlr_dealloc⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm2_box; sep_ac_rfl
  refine steps_of_call_no_panic hDealloc
    hpc2 hrun2 hsp_align2 hx30_2 hm_dealloc hL2
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s3 hpc3 hrun3 hsp3 hsp_align3 hcs3 hL3 hm3
  dsimp only [rustCliDeallocBudgetSpec] at hm3
  rw [hsp2, sepConj_assoc, satisfies_pure_sepConj] at hm3
  rcases hm3 with ⟨⟨hacp3, _hlive3⟩, hm3⟩
  have htr3 : s3.trace = s2.trace := hacp3.2.1
  have hm3_final : s3.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
       memRegion (sp + 0x190#64) 104 ∗
       A.pool lim st2 s3 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
    rw [hstk_dealloc]
    refine Satisfies.mono (Entails.of_eq ?_) hm3; sep_ac_rfl
  exact ⟨s3, .refl s3, chainsCap1, chainsPtr1, hpc3, hrun3, by reg_chain, hsp_align3,
    htr3.trans (htr2.trans htr1), by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL3, hm3_final⟩

/-- Stack-parametric budget-threaded full Step 3 (`+0xa84 → +0xaf0`). -/
theorem dhCommit_step3_of_wp [LibsignalPlacement] {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry (growOneSpecWithStack stk M A lim))
    (hDealloc : subroutine_ok prog deallocEntry (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro newGC st2
  set Step3Rest : SepProp :=
    ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
    memRegion (sp + 0x1b0#64) 72 ∗
    (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
    (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
    optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
    Frame
  have hm3a : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Step3Rest ∗ R) := by
    dsimp only [Step3Rest]
    refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  obtain ⟨s1, hsteps3a, chainsCap1, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step3a_of_wp hwp A lim st0 hGrow R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hfits3a hpc hrun hsp hsp_align htrace hL hm3a
  obtain ⟨sf, hsteps3b, hpost⟩ :=
    dhCommit_step3b_of_wp (hlr_dealloc := hlr_dealloc) hwp.step3b hstk_lo hstk_hi A lim
      (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0)
      hDealloc R Frame s0 s s1 sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr gcs srk rck pad
      hlt_cap1 hpad hsrk_ne hpc1 hrun1 hsp1 hsp_align1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
      hx25 hx26 hx27 hx28 hL1 hm1
  have hst2_eq :
      M.stepEvents (rustDeallocEvents 33 1)
        (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0) = st2 := by
    dsimp only [st2, dhCommitStep3Events]
    exact (M.stepEvents_append (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length))
      (rustDeallocEvents 33 1) st0).symm
  rw [hst2_eq] at hpost
  exact ⟨sf, hsteps3a.trans hsteps3b, hpost⟩

/-! ## 5. Relocatable `[LibsignalPlacement]` Specializations (`growOneStack` & `growOneChainStackX`) -/

/-- Relocatable Step 3a (`+0xa84 → +0xa9c`) at `growOneStack` (`4608`). -/
theorem dhCommit_step3a_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym))
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    let st1 := M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
           A.pool lim st1 sf ∗ stackAt sp growOneStack) ∗ (Frame ∗ R)) :=
  dhCommit_step3a_of_wp hwp A lim st0 hGrow R Frame s0 s sp chainsCap chainsPtr gcs
    hlen_lt hfits3a hpc hrun hsp hsp_align htrace hL hmem

/-- Relocatable Step 3a (`+0xa84 → +0xa9c`) at `growOneChainStackX` (`464 + finishGrowStackX`). -/
theorem dhCommit_step3a_x_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym))
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog (lsmpl.base 43)
      (LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp growOneChainStackX) ∗ (Frame ∗ R)) :
    let st1 := M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
           A.pool lim st1 sf ∗ stackAt sp growOneChainStackX) ∗ (Frame ∗ R)) :=
  dhCommit_step3a_of_wp hwp A lim st0 hGrow R Frame s0 s sp chainsCap chainsPtr gcs
    hlen_lt hfits3a hpc hrun hsp hsp_align htrace hL hmem

/-- Relocatable full Step 3 (`+0xa84 → +0xaf0`) at `growOneStack` (`4608`). -/
theorem dhCommit_step3_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym))
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp growOneStack) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool lim st2 sf ∗ stackAt sp growOneStack) ∗ (Frame ∗ R)) :=
  dhCommit_step3_of_wp (hlr_dealloc := hlr_dealloc) hwp (by decide) (by decide) A lim st0 hGrow hDealloc R Frame s0 s
    sp chainsCap chainsPtr boxPtr srkPtr ckPtr gcs srk rck pad
    hlen_lt hpad hsrk_ne hfits3a hpc hrun hsp hsp_align htrace hx25 hx26 hx27 hx28 hL hmem

/-- Relocatable full Step 3 (`+0xa84 → +0xaf0`) at `growOneChainStackX` (`464 + finishGrowStackX`). -/
theorem dhCommit_step3_x_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym))
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog (lsmpl.base 43)
      (LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.growOneChainSpecX M A lim))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp growOneChainStackX) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ∃ sf, Steps prog s sf ∧
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool lim st2 sf ∗ stackAt sp growOneChainStackX) ∗ (Frame ∗ R)) :=
  dhCommit_step3_of_wp (hlr_dealloc := hlr_dealloc) hwp (by decide) (by decide) A lim st0 hGrow hDealloc R Frame s0 s
    sp chainsCap chainsPtr boxPtr srkPtr ckPtr gcs srk rck pad
    hlen_lt hpad hsrk_ne hfits3a hpc hrun hsp hsp_align htrace hx25 hx26 hx27 hx28 hL hmem

/-- `ReachesOrPanicOom` corollary of `dhCommit_step3_of_wp` for downstream `DhCommit` composition. -/
theorem dhCommit_step3_withStack_placed_oom [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym))
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (growOneSpecWithStack stk M A lim))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (Pan : State → State → SepProp) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    ReachesOrPanicOom prog Pan R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R))) := by
  intro newGC st2
  obtain ⟨sf, hsteps, hpost⟩ :=
    dhCommit_step3_of_wp (hlr_dealloc := hlr_dealloc) hwp hstk_lo hstk_hi A lim st0 hGrow hDealloc R Frame s0 s
      sp chainsCap chainsPtr boxPtr srkPtr ckPtr gcs srk rck pad
      hlen_lt hpad hsrk_ne hfits3a hpc hrun hsp hsp_align htrace hx25 hx26 hx27 hx28 hL hmem
  exact ⟨sf, hsteps, Or.inl hpost⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
