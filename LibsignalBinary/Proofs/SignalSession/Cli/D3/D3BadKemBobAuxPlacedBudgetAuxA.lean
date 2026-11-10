/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.SharedCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Bad-KEM Error Ownership (`Pqxdh::accept` Block `79`, `opk = none`)

Deterministic allocator event trace `acceptBadKemEvents`, envelope `AcceptBadKemEnv`,
Block-`79` Bad-KEM specifications, and the `opk = none` branch proof for `Pqxdh::accept`
when `pkVecTag? 8#8 1568 ctBytes = none`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement blkLib_eq_79 blkPC_79
  blkPl_79 libsignalSessionLib lsLogFilterAddr lsMemcpySym lsProg_79 lsmpl lsroCheck lsρ
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  withLsCodeRoLoaded withLsFrozen withRoSlice
)
open CryptoVerification.LibsignalTripleRatchet.Keys (lsRustAllocSym lsRustNoAllocShimSym)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalPublicApi.StoreKit (speWordsAt)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput F_X25519 Primitives StructuralPrims WellSizedAcceptKeysInput
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit bytesToBv8
  incomingBaseKeyInvalidBytes pollReadyOkWord pqxdhEntryStack readReg_setMem_setPC_pre
  readReg_setPC_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  AcceptCanonTrue LsFullFrozenInv acceptRustDeallocSym alloc_to_alloc_stack_of_eq
  alloc_to_calc_stack alloc_to_calc_stack_of_eq and_ff_hi56_3 and_ff32_hi56_3
  calc_to_alloc_stack calc_to_vecAppend_stack cells_sub4944_4_merge cells_sub80_10_merge
  cells10_sub80_eq cells3_sub4912_to_memRegion24 cells4_sub4944_eq emp_entails_anyHeap
  extractLsb_hi56_3
  hook_ok_79_of_mem incoming_alloc_split incoming_overlap_prep memRegion_192_init_split
  outPtr_err104_split pointsTo64_4_allOnes_eq_F_X25519 pointsToBytes_append_at
  pqsk_region_phaseA_cells_merge pqsk_region_phaseA_merge pqsk_region_phaseA_split
  rodata_incoming_1_to_2 rodata_incoming_split1 rodata_incoming_split2
  stackAt_pqxdh_accept_top subStack_to_alloc subStack_to_alloc_of_eq
  subroutine_ok_withLsFrozen_of_withRoSlice subroutine_ok_withMemEq_of_withCodeLoaded
  vec_err_dh1_merge vec_err_dh2_merge vec_err_dh3_merge vec_err_dh4_merge vec_ok_160_merge
  vecAppend_to_alloc_stack_of_eq zext64_trunc32_hi56_3_and_ff
)
open CryptoVerification.E2E.Pqxdh.ResponderCore.SepWPp (of_sepWP_lsfull)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  AcceptBadKemGhost PlainSpeTag pkVecTag? pkVecTag?_8_1568_eq_none_cases
  pqxdhAcceptBadKemErrOwnedAt pqxdhAcceptBadKemFieldsAt pqxdhBadKemErrPayloadAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  RustCliAllocBudget coarseCostModel coarseStep coarseStepReserve fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  SepWPp_call_hag_placed acceptCalculateAgreementPlacedBaseSpec calculateAgreementEvents
  ecPubKeyIsCanonicalCallSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec noAllocShimSpec)

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 1. Allocator Event Envelope, Non-Vacuity Witness, and Block-`79` Bad-KEM Specs -/

/-- Exact deterministic `AllocEvent` list emitted by `Pqxdh::accept` (Block `79`) when
`pkVecTag? 8#8 1568 ctBytes = none` (exiting before ML-KEM decapsulation). -/
def acceptBadKemEvents (P : Primitives) (inp : AcceptKeysInput) : List AllocEvent :=
  if !P.isCanonical inp.hdr.ekAPk then
    rustAllocEvents 28 1
  else
    let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
    if P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ rustDeallocEvents 192 1
    else if P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1
    else if P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0 then
      rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
    else
      match inp.opkBSk? with
      | none =>
        rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
      | some opkSk =>
        if P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 then
          rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
        else
          rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ dhCycle ++
            rustDeallocEvents 192 1

/-- Allocator event envelope for `Pqxdh::accept` (Block `79`) on Bad-KEM inputs. -/
def AcceptBadKemEnv (P : Primitives) (inp : AcceptKeysInput) (evs : List AllocEvent) : Prop :=
  evs = acceptBadKemEvents P inp

@[simp]
theorem fitsEnv_acceptBadKemEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (P : Primitives) (inp : AcceptKeysInput) :
    FitsEnv M lim st (AcceptBadKemEnv P inp) ↔
      FitsEvents M lim st (acceptBadKemEvents P inp) := by
  unfold AcceptBadKemEnv; exact FitsEnv.eq_iff

example (P : Primitives) (inp : AcceptKeysInput) :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init (AcceptBadKemEnv P inp) := by
  rw [fitsEnv_acceptBadKemEnv_iff]
  have hcases :
      acceptBadKemEvents P inp = [.alloc 28] ∨
      acceptBadKemEvents P inp = [.alloc 192, .free 1 192] ∨
      acceptBadKemEvents P inp = [.alloc 192, .alloc 32, .free 1 32, .free 1 192] ∨
      acceptBadKemEvents P inp =
        [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .free 1 192] ∨
      acceptBadKemEvents P inp =
        [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
         .free 1 192] ∨
      acceptBadKemEvents P inp =
        [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
         .alloc 32, .free 1 32, .free 1 192] := by
    unfold acceptBadKemEvents; dsimp only
    cases hcanon : P.isCanonical inp.hdr.ekAPk
    · simp only [Bool.not_false, ↓reduceIte]; exact Or.inl rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · simp only [hd1, ↓reduceIte]; exact Or.inr (Or.inl rfl)
      · simp only [hd1, ↓reduceIte]
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd2, ↓reduceIte]; exact Or.inr (Or.inr (Or.inl rfl))
        · simp only [hd2, ↓reduceIte]
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · simp only [hd3, ↓reduceIte]
            cases inp.opkBSk? <;> dsimp only
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · rename_i opkSk
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0
              · simp only [hd4, ↓reduceIte]
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · simp only [hd4, ↓reduceIte]
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hcases with h | h | h | h | h | h <;> (
    rw [h]
    dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
      AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
    decide)

attribute [local irreducible] FitsEvents

/-- Budget-threaded relocatable inner specification of `Pqxdh::accept` (Block `79`) when
`pkVecTag? 8#8 1568 g.ctBytes = none` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (AcceptErrEnv g.inp)`). -/
def pqxdhAcceptBadKemErrOwnedInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptBadKemGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ctBytes.length < 2 ^ 63 ∧
      pkVecTag? 8#8 1568 g.ctBytes = none ∧
      FitsEnv M lim st (AcceptErrEnv g.inp)⌝ ∗
    pqxdhAcceptBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp g.ctBytes ∗
    memRegion g.outPtr 104 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp pqxdhEntryStack ∗
    A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptErrEnv g.inp evs⌝ ∗
      pqxdhAcceptBadKemFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp g.ctBytes ∗
      (pqxdhAcceptBadKemErrOwnedAt A.repAlloc g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp pqxdhEntryStack ∗
      A.pool lim (M.stepEvents evs st) sf

def pqxdhAcceptBadKemErrOwnedPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptBadKemGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv)

def pqxdhAcceptBadKemErrOwnedFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptBadKemGhost × M.σ) :=
  withLsFrozen lsmpl (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv)

def pqxdhAcceptBadKemErrOwnedOpkNoneInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptBadKemGhost × M.σ) :=
  { pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv with
    pre := fun (g, st) s =>
      ⌜g.inp.opkBSk? = none⌝ ∗
        (pqxdhAcceptBadKemErrOwnedInnerPlacedSpec A lim AcceptErrEnv).pre (g, st) s }

/-! ## 2. Separation-Logic, Condition-Code, and Budget-Event Helpers -/

private theorem outPtr_tail64_to_spe_tail_placed (outPtr : BitVec 64) (b40 : BitVec 8) :
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗ memRegion (outPtr + 56#64) 48 := by
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hb40) ?_
  have hm64 :
      memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63 =
        (∃∗ w5 : BitVec 64, (outPtr + 40#64) ↦₆₄ w5) ∗
        (∃∗ w6 : BitVec 64, (outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 48 := by
    rw [← ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 1) (k := 63)
          (b' := outPtr + 41#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 8) (k := 56)
          (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 48)
          (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (outPtr + 40#64), ProofLib.memRegion_eight (outPtr + 48#64)]
  rw [hm64]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))

theorem outPtr_badKem_err104_owned_merge_placed (A : RustAlloc)
    (outPtr errTag w2 w3 w4 : BitVec 64) (b40 : BitVec 8)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ -3#64 ∧ errTag ≠ -2#64) :
    pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗ (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptBadKemErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhBadKemErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))))))) =
      (outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗
        ((((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) ∗
          (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
            ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
            pqxdhBadKemErrPayloadAt A errTag w2 w3 w4))) := by sep_ac_rfl
  rw [hrearr]; unfold pqxdhAcceptBadKemErrOwnedAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (outPtr_tail64_to_spe_tail_placed outPtr b40)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem pqxdhBadKemErrPayloadAt_plain_intro_placed (A : RustAlloc) (i : Nat)
    (hi : PlainSpeTag i) (w2 w3 w4 : BitVec 64) :
    emp ⊢ pqxdhBadKemErrPayloadAt A (speWord i) w2 w3 w4 := by
  unfold pqxdhBadKemErrPayloadAt; refine Entails.sepExists_right false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]; refine Entails.sepExists_right i ?_
  rw [← sepConj_emp ⌜PlainSpeTag i ∧ speWord i = speWord i⌝, pure_sepConj_of_true ⟨hi, rfl⟩ emp]
  exact Entails.refl _

theorem outPtr_badKem_err104_plain_merge_placed (A : RustAlloc) (i : Nat)
    (hi : PlainSpeTag i)
    (hw1 : speWord i ≠ pollReadyOkWord ∧ speWord i ≠ -3#64 ∧ speWord i ≠ -2#64)
    (outPtr w2 w3 w4 : BitVec 64) (b40 : BitVec 8) :
    (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ speWord i) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptBadKemErrOwnedAt A outPtr := by
  rw [← emp_sepConj ((outPtr ↦₃₂ 1#32) ∗ _)]
  exact Entails.trans
    (sepConj_mono_left (pqxdhBadKemErrPayloadAt_plain_intro_placed A i hi w2 w3 w4))
    (outPtr_badKem_err104_owned_merge_placed A outPtr (speWord i) w2 w3 w4 b40 hw1)

theorem err28_badKem_payload_intro_placed (A : RustAlloc) (ptr u2 u3 : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    memRegion ptr 12 ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) ∗ A.live ptr 28 1 ⊢
      pqxdhBadKemErrPayloadAt A (speWord 24) 28#64 ptr 28#64 := by
  have hm12 : memRegion ptr 12 =
      (∃∗ q0 : BitVec 64, ptr ↦₆₄ q0) ∗ (∃∗ q1 : BitVec 32, (ptr + 8#64) ↦₃₂ q1) := by
    rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 4)
          (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight ptr, memRegion_four (ptr + 8#64)]
  rw [hm12, sepConj_assoc, sepExists_sepConj_left]; refine Entails.sepExists_elim fun q0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_elim fun q1 => ?_
  unfold pqxdhBadKemErrPayloadAt; refine Entails.sepExists_right true ?_
  simp only [↓reduceIte]; rw [pure_sepConj_of_true trivial]
  let bs : List (BitVec 8) := unpack64 q0 ++ (unpack32 q1 ++ (unpack64 u2 ++ unpack64 u3))
  refine Entails.sepExists_right bs ?_
  have hbs_len : bs.length = 28 := by simp [bs, unpack64_length, unpack32_length]
  have hpure : BitVec.ofNat 64 bs.length = 28#64 ∧ bs.length ≤ (28#64 : BitVec 64).toNat ∧
      (28#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := by
    rw [hbs_len]; exact ⟨rfl, by decide, by decide, hptr⟩
  rw [pure_sepConj_of_true hpure]
  have h28_ne : (28#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [h28_ne, ↓reduceIte, hbs_len]
  have h28_nat : (28#64 : BitVec 64).toNat = 28 := rfl
  rw [h28_nat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦₆₄ q0) ∗ ((ptr + 8#64) ↦₃₂ q1) ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) := by
    dsimp only [bs]
    rw [pointsToBytes_append, unpack64_length, pointsToBytes_append, unpack32_length,
        pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hpts]; exact Entails.of_eq (by sep_ac_rfl)

theorem bv64_ofNat_ne_zero_of_pos_placed {n : Nat} (hpos : 0 < n) (hbd : n < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h; have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; change n = 0 at hnat; omega

theorem bv64_ofNat_ne_1569_placed {n : Nat} (hne : n ≠ 1569) (hbd : n < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 1569#64 := by
  intro h; have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; change n = 1569 at hnat; omega

theorem cond_ne_tag8_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.zeroExtend 64 tag) 8#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_bits

theorem cond_ne_tag8_concat_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState64 (0#56 ++ tag) 8#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_bits

theorem cond_ne_tag8_32_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState32 (BitVec.zeroExtend 32 tag) 8#32) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState32]; bv_bits

theorem cond_ne_tag8_32_concat_placed {tag : BitVec 8} (htag : tag ≠ 8#8) :
    ConditionHolds CondCode.NE (subsPState32 (0#24 ++ tag) 8#32) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState32]; bv_bits

theorem cond_ne_ctLen1569_placed {ctLen : BitVec 64} (hlen : ctLen ≠ 1569#64) :
    ConditionHolds CondCode.NE (subsPState64 ctLen 1569#64) = true := by
  rw [ProofLib.conditionHolds_ne_subsPState64]; bv_arith

theorem fitsEvents_pfx {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {pfx sfx evs : List AllocEvent} (h : FitsEvents M lim st evs) (heq : evs = pfx ++ sfx) :
    FitsEvents M lim st pfx := by
  rw [heq] at h; exact ((fitsEvents_append M lim pfx sfx st).mp h).1

theorem fitsEvents_mid {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {pfx mid sfx evs : List AllocEvent}
    (h : FitsEvents M lim st evs) (heq : evs = pfx ++ (mid ++ sfx)) :
    FitsEvents M lim (M.stepEvents pfx st) mid := by
  rw [heq] at h
  exact ((fitsEvents_append M lim mid sfx _).mp
    ((fitsEvents_append M lim pfx (mid ++ sfx) st).mp h).2).1

theorem sepWPp_alloc_post {M : AllocCostModel} {prog : Program} {ret : BitVec 64}
    {s_pre s : State} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sp sp' : BitVec 64} {size align : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hsp : sp = sp')
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 →
      s.trace = s_pre.trace →
      SepWPp prog ret s
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
          stackAt sp' allocHookStack ∗ A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp)
    (hne : s.readReg64 (.gpr 0#5) ≠ 0#64 := by assumption)
    (hal : (s.readReg64 (.gpr 0#5)).toNat % align = 0 := by omega)
    (hacp : AllocCallPreserved s_pre s := by assumption) :
    SepWPp prog ret s
      (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
        stackAt sp allocHookStack ∗ A.live (s.readReg64 (.gpr 0#5)) size align ∗
        memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp := by
  subst hsp; exact hok hne hal hacp.2.1

private theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList; simp [List.utf8Encode]

private theorem incomingBaseKeyInvalidBytes_eq_list :
    incomingBaseKeyInvalidBytes =
      bytesToBv8 ("incoming base key is invalid".toList.flatMap String.utf8EncodeChar) := by
  unfold incomingBaseKeyInvalidBytes; rw [toUTF8_data_toList]

theorem lsroCheck_incomingBaseKeyInvalid :
    lsroCheck "libsignal_protocol:.rodata..Lanon.393" incomingBaseKeyInvalidBytes = true := by
  rw [incomingBaseKeyInvalidBytes_eq_list]; exact eagerReduce (Eq.refl true)

theorem sepWP_instantiate_ro1_post_exists {α : Type _} {prog : Program}
    {target_pc : BitVec 64} {s : State} {P L₁ R : SepProp} {Q : State → α → SepProp}
    {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (L₁ ∗ Q sf w) ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (L₁ ∗ (∃∗ a, Q sf a)) ∗ R) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_intro w)))
      (h1 hm), h2⟩

/-! ## 3. Budget-Threaded Rejecting `Pqxdh::accept` Proof on Bad-KEM (Block `79`) -/

local macro "badkem_ct_exit_placed" s0:ident A:ident ctBufPtr:ident
    hbadKem:ident hct_bd:ident
    h_canon:ident h_agree:ident hshim:ident
    halloc:ident hdealloc:ident hmemcpy:ident
    st_cur:ident evs_out:ident hst_fin:ident henv_out:ident : tactic =>
  `(tactic| (
    rcases pkVecTag?_8_1568_eq_none_cases $hbadKem with
      hct_eq | ⟨b0, rest, hct_eq, hb0⟩ | ⟨rest, hct_eq, hlen_ne⟩
    · subst hct_eq
      wp_simp_pre_fast [List.length_nil]
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 7 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [List.length_nil, sepConj_assoc, *]; wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hc_tag64 := cond_ne_tag8_placed hb0; have hc_tag64' := cond_ne_tag8_concat_placed hb0
      have hc_tag32 := cond_ne_tag8_32_placed hb0; have hc_tag32' := cond_ne_tag8_32_concat_placed hb0
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr b0 rest).symm) (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 31 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [sepConj_assoc, *]; wp_done
    · subst hct_eq
      have hne0 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 0#64 :=
        bv64_ofNat_ne_zero_of_pos_placed (by simp) $hct_bd
      have hbeq0 : (BitVec.ofNat 64 (8#8 :: rest).length == 0#64) = false := beq_false_of_ne hne0
      have hne1569 : BitVec.ofNat 64 (8#8 :: rest).length ≠ 1569#64 :=
        bv64_ofNat_ne_1569_placed hlen_ne $hct_bd
      have hc_len := cond_ne_ctLen1569_placed hne1569
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call $hdealloc (_, 192, 1, $st_cur)
      wp_steps_sync_pool (($s0).readReg64 Reg.lr)
      refine SepWP.fold (Entails.of_eq (pointsToBytes_cons $ctBufPtr 8#8 rest).symm) (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed ($A).repAlloc 34 (by decide) (by decide)
          (($s0).readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge ($s0).sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge ($s0).sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq ($s0).sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top ($s0).sp).symm) (by sep_focus) ?_
      have hst_rw := $hst_fin; rw [hst_rw]; have _ := $henv_out
      clear $h_canon $h_agree $hshim $halloc $hdealloc $hmemcpy
      refine sepWP_instantiate_ro1_post_exists $evs_out ?_
      simp only [sepConj_assoc, *]; wp_done))

set_option maxHeartbeats 10000000 in
/-- Budget-threaded owned-error rejecting contract for `Pqxdh::accept` (Block `79`) on the
`g.inp.opkBSk? = none` branch when `pkVecTag? 8#8 1568 g.ctBytes = none`. -/
theorem pqxdhAccept_badKem_err_owned_opk_none_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (h_canon : subroutine_ok (lsProg_79 H) (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)))
    (h_agree : subroutine_ok (lsProg_79 H) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H acceptRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_79 H) (blkPl_79).base
      (withLsFrozen lsmpl
        (pqxdhAcceptBadKemErrOwnedOpkNoneInnerPlacedSpec A lim (AcceptBadKemEnv P))) := by
  refine subroutine_ok_withLsFrozen_of_withRoSlice
    (roSym := "libsignal_protocol:.rodata..Lanon.393")
    (roBytes := incomingBaseKeyInvalidBytes) lsroCheck_incomingBaseKeyInvalid ?_
  have hshim := hook_ok_79_of_mem h_shim (by decide)
  have halloc := subroutine_ok_allocNoOom_of_budget (hook_ok_79_of_mem h_alloc (by decide))
  have hdealloc := hook_ok_79_of_mem h_dealloc (by decide)
  have hmemcpy := hook_ok_79_of_mem h_memcpy (by decide)
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved] at hdealloc
  clear h_shim h_alloc h_dealloc h_memcpy
  unfold withLsFrozen withRoSlice pqxdhAcceptBadKemErrOwnedOpkNoneInnerPlacedSpec
    pqxdhAcceptBadKemErrOwnedInnerPlacedSpec
  wpp_init x s0
  rcases x with ⟨⟨inp, ctBytes, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩, st⟩
  dsimp only at *
  have hfr0 : LibsignalFrozen lsmpl s0.mem := ‹_›
  have hF0 : LsFullFrozenInv lsmpl s0 := LsFullFrozenInv.of_frozen hfr0
  have hopk_none_in : inp.opkBSk? = none := ‹_›
  have hct_bd : ctBytes.length < 2 ^ 63 := ‹ctBytes.length < 2 ^ 63›
  have hbadKem : pkVecTag? 8#8 1568 ctBytes = none := ‹pkVecTag? 8#8 1568 ctBytes = none›
  have hfits_env : FitsEnv M lim st (AcceptBadKemEnv P inp) := ‹_›
  have hfits_all : FitsEvents M lim st (acceptBadKemEvents P inp) :=
    (fitsEnv_acceptBadKemEnv_iff P inp).mp hfits_env
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, _hpqSk, _hpqPk, hikAPk, hekAPk,
    _hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'; unfold pqxdhAcceptBadKemFieldsAt
  refine of_sepWP_lsfull hF0 (mid := lsmpl.base 202) ?_
  wp_steps_sync_pool (lsmpl.base 202); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF0_1; try simp only [arm64_norm] at hF0_1
  refine of_sepWP_lsfull hF0_1 (mid := (blkPl_79).base + 52#64) ?_
  have hcanon0 := subroutine_ok_withMemEq_of_withCodeLoaded
    (spec := ecPubKeyIsCanonicalCallSpec P) h_canon hF0_1.code
  simp only [ecPubKeyIsCanonicalCallSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec] at hcanon0
  wp_call hcanon0 ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hevs_eq : acceptBadKemEvents P inp = rustAllocEvents 28 1 := by
      simp [acceptBadKemEvents, hcanon_b]
    have hfits28 : FitsEvents M lim st (rustAllocEvents 28 1) := hevs_eq ▸ hfits_all
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *; rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := (blkPl_79).base + 216#64) ?_
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym); wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl28 : LibsignalBinary.Heap.RustLayoutOk 28 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (28, 1, st); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc0 halign0 htr0 => ?_
    refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
      (by sep_focus) ?_; sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_; sep_elim_exists'
    refine SepWPp.fold
      (Entails.of_eq (rodata_incoming_split1 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_79).rebase (blkPl_79).base (hooksException H))
      blkLib_eq_79 (mid := s0.readReg64 Reg.lr)
    intro _m_strip; wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_1_to_2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")))
      (by sep_focus) ?_; wp_steps
    refine SepWP.fold
      (Entails.of_eq (rodata_incoming_split2 (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.393")).symm)
      (by sep_focus) ?_
    refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_; sep_elim_exists'; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)
    refine SepWP.fold (err28_badKem_payload_intro_placed A.repAlloc _ _ _ halloc0)
      (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus) ?_
    refine SepWP.fold
      (outPtr_badKem_err104_owned_merge_placed A.repAlloc (s0.readReg64 (.gpr 8#5))
        (speWord 24) 28#64 _ 28#64 _ (by decide)) (by sep_focus) ?_
    refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
    refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
    refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
    · simp only [arm64_norm, *]
    refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
    have henv_out : AcceptBadKemEnv P inp (rustAllocEvents 28 1) := hevs_eq.symm
    clear h_canon h_agree hshim halloc hdealloc hmemcpy
    refine sepWP_instantiate_ro1_post_exists (rustAllocEvents 28 1) ?_
    simp only [sepConj_assoc, *]; wp_done
  · have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    have hcanon_keep : AcceptCanonTrue P inp := ⟨hcanon_b⟩
    simp only [hcanon_ec, ↓reduceIte] at *; clear hcanon_b hcanon_ec
    have hcanon_b : P.isCanonical inp.hdr.ekAPk = true := hcanon_keep.out; clear hcanon_keep
    have hfits192 : FitsEvents M lim st (rustAllocEvents 192 1) := by
      unfold acceptBadKemEvents at hfits_all; dsimp only at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · simp only [hd1, ↓reduceIte] at hfits_all; exact fitsEvents_pfx hfits_all rfl
      · simp only [hd1, ↓reduceIte] at hfits_all
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd2, ↓reduceIte] at hfits_all
          exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
        · simp only [hd2, ↓reduceIte] at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
            · rename_i opkSk_c
              by_cases hd4 : P.x25519 opkSk_c inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_pfx hfits_all (by simp only [List.append_assoc]; rfl)
    rw [subStack_to_alloc s0.sp]
    refine of_sepWP_lsfull hF1 (mid := (blkPl_79).base + 72#64) ?_
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym); wp_call hshim ()
    refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrl192 : LibsignalBinary.Heap.RustLayoutOk 192 1 :=
      ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
    wp_call halloc (192, 1, st); apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine sepWPp_alloc_post (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      fun halloc192 halign192 htr192 => ?_
    let st_192 := M.stepEvents (rustAllocEvents 192 1) st
    have hfits_ag1 :
        FitsEvents M lim st_192 (calculateAgreementEvents P inp.spkBSk inp.hdr.ikAPk) := by
      unfold acceptBadKemEvents at hfits_all; dsimp only at hfits_all
      simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfits_all
      by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
      · exact of_eq_true (by
          simp only [calculateAgreementEvents, hd1, ↓reduceIte]
          exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
      · simp only [calculateAgreementEvents, hd1, ↓reduceIte] at hfits_all ⊢
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd2, ↓reduceIte] at hfits_all
          exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
        · simp only [hd2, ↓reduceIte] at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
            · rename_i opkSk_c
              by_cases hd4 : P.x25519 opkSk_c inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [List.append_assoc]; rfl)
    refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
    sep_elim_exists'
    refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
    refine of_sepWP_lsfull hF2 (mid := lsmpl.base 207) ?_
    wp_steps_sync_pool (lsmpl.base 207)
    refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF3; try simp only [arm64_norm] at hF3
    refine SepWPp_call_hag_placed hWF h_agree hF3.to_frozen
      (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
      (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs) hsp_align
      (by wp_norm_lhs) (ret_pc := (blkPl_79).base + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk, hfits_ag1⟩
      (by sep_focus)
      (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 _hfr1 => ?_)
      (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hfr4 => ?_)
    · have hevs_eq :
          acceptBadKemEvents P inp = rustAllocEvents 192 1 ++ rustDeallocEvents 192 1 := by
        simp [acceptBadKemEvents, hcanon_b, hdh1]
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_; sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_192)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
          (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_192 =
          M.stepEvents (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) st := by
        dsimp only [st_192]; rw [← M.stepEvents_append]
      rw [hst_eq]
      have henv_out : AcceptBadKemEnv P inp (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) :=
        hevs_eq.symm
      clear h_canon h_agree hshim halloc hdealloc hmemcpy
      refine sepWP_instantiate_ro1_post_exists (rustAllocEvents 192 1 ++ rustDeallocEvents 192 1) ?_
      simp only [sepConj_assoc, *]; wp_done
    · have hF4 : LsFullFrozenInv lsmpl sf1 := LsFullFrozenInv.of_frozen hfr4
      have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
      have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
        simp [bytesToBv8, hdh1_len]
      have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
        simp [F_X25519, hdh1_len]
      let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
      let st_dh1_a := M.stepEvents (rustAllocEvents 32 1) st_192
      let st_dh1 := M.stepEvents (rustDeallocEvents 32 1) st_dh1_a
      have hst_dh1_eq : st_dh1 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle) st := by
        dsimp only [st_dh1, st_dh1_a, st_192, dhCycle]
        rw [← M.stepEvents_append, ← M.stepEvents_append]
      have hfits_ag2 :
          FitsEvents M lim st_dh1 (calculateAgreementEvents P inp.ikBSk inp.hdr.ekAPk) := by
        unfold acceptBadKemEvents at hfits_all
        simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, ↓reduceIte] at hfits_all
        by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
        · exact of_eq_true (by
            simp only [calculateAgreementEvents, hd2, ↓reduceIte]
            exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
        · simp only [calculateAgreementEvents, hd2, ↓reduceIte] at hfits_all ⊢
          rw [hst_dh1_eq]
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · simp only [hd3, ↓reduceIte] at hfits_all
            exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
          · simp only [hd3, ↓reduceIte] at hfits_all
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
            · rename_i opkSk
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
      rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
        hcs29, hvregs1⟩
      simp only [arm64_norm]
        at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hvregs1
      refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
      refine of_sepWP_lsfull hF4 (mid := lsmpl.base 207) ?_
      wp_steps_sync_pool (lsρ lsMemcpySym)
      wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
      refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
      wp_steps_sync_pool (lsρ acceptRustDeallocSym)
      refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _) (by sep_focus) ?_
      wp_call hdealloc (dh1_ptr, 32, 1, st_dh1_a); wp_steps_sync_pool (lsmpl.base 207)
      refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ F_X25519 (P.x25519 inp.spkBSk
        inp.hdr.ikAPk) 32 (by decide))) (by sep_focus) ?_
      refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF5; try simp only [arm64_norm] at hF5
      refine SepWPp_call_hag_placed hWF h_agree hF5.to_frozen
        (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
        (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
        (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
        (ret_pc := (blkPl_79).base + 304#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk, hfits_ag2⟩
        (by sep_focus)
        (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 _hfr2 => ?_)
        (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hfr6 => ?_)
      · have hevs_eq : acceptBadKemEvents P inp =
            rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1 := by
          simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2,
            ↓reduceIte, dhCycle]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_; sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
        wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_dh1)
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
        refine SepWP.fold
          (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
            (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_dh1 =
            M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) st := by
          rw [hst_dh1_eq, ← M.stepEvents_append]
        rw [hst_eq]
        have henv_out :
            AcceptBadKemEnv P inp (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) :=
          hevs_eq.symm
        clear h_canon h_agree hshim halloc hdealloc hmemcpy
        refine sepWP_instantiate_ro1_post_exists
          (rustAllocEvents 192 1 ++ dhCycle ++ rustDeallocEvents 192 1) ?_
        simp only [sepConj_assoc, *]; wp_done
      · have hF6 : LsFullFrozenInv lsmpl sf2 := LsFullFrozenInv.of_frozen hfr6
        have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
        have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
          simp [bytesToBv8, hdh2_len]
        have hpfx2_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
          P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by simp [F_X25519, hdh1_len, hdh2_len]
        let st_dh2_a := M.stepEvents (rustAllocEvents 32 1) st_dh1
        let st_dh2 := M.stepEvents (rustDeallocEvents 32 1) st_dh2_a
        have hst_dh2_eq :
            st_dh2 = M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle) st := by
          dsimp only [st_dh2, st_dh2_a]; rw [hst_dh1_eq, ← M.stepEvents_append, ← M.stepEvents_append]
        have hfits_ag3 :
            FitsEvents M lim st_dh2 (calculateAgreementEvents P inp.spkBSk inp.hdr.ekAPk) := by
          unfold acceptBadKemEvents at hfits_all
          simp only [hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1, hdh2, ↓reduceIte]
            at hfits_all
          by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
          · exact of_eq_true (by
              simp only [calculateAgreementEvents, hd3, ↓reduceIte]
              exact LibsignalBinary.Heap.fitsEvents_nil M lim _)
          · simp only [calculateAgreementEvents, hd3, ↓reduceIte] at hfits_all ⊢
            rw [hst_dh2_eq]
            cases hopk_c : inp.opkBSk? <;> simp only [hopk_c] at hfits_all
            · exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
            · rename_i opkSk
              by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0 <;>
                simp only [hd4, ↓reduceIte] at hfits_all <;>
                exact fitsEvents_mid hfits_all (by simp only [dhCycle, List.append_assoc]; rfl)
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
        rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
          hcs2_27, hcs2_28, hcs2_29, hvregs2⟩
        simp only [arm64_norm]
          at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
             hcs2_29 hvregs2
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine of_sepWP_lsfull hF6 (mid := lsmpl.base 207) ?_
        wp_steps_sync_pool (lsρ lsMemcpySym)
        wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
        refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
        wp_steps_sync_pool (lsρ acceptRustDeallocSym)
        refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
          (by sep_focus) ?_
        wp_call hdealloc (dh2_ptr, 32, 1, st_dh2_a); wp_steps_sync_pool (lsmpl.base 207)
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _ (F_X25519 ++
          P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
          (by simp only [bytesToBv8, List.length_map, hpfx1_len]))) (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF7; try simp only [arm64_norm] at hF7
        refine SepWPp_call_hag_placed hWF h_agree hF7.to_frozen
          (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs)
          (ret_pc := (blkPl_79).base + 404#64) (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk,
            hfits_ag3⟩ (by sep_focus)
          (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 _hfr3 => ?_)
          (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hfr8 => ?_)
        · have hevs_eq : acceptBadKemEvents P inp =
              rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1 := by
            simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true, hdh1,
              hdh2, hdh3, ↓reduceIte, dhCycle]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
          rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
            hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
          simp only [arm64_norm]
            at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
               hcs3_29 hvregs3
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_; sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_; apply SepWPp.of_sepWP_ret
          wp_steps_sync_pool (lsρ acceptRustDeallocSym); wp_call hdealloc (_, 192, 1, st_dh2)
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
          refine SepWP.fold
            (outPtr_badKem_err104_plain_merge_placed A.repAlloc 10 (by decide) (by decide)
              (s0.readReg64 (.gpr 8#5)) _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          have hst_eq : M.stepEvents (rustDeallocEvents 192 1) st_dh2 =
              M.stepEvents
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) st := by
            rw [hst_dh2_eq, ← M.stepEvents_append]
          rw [hst_eq]
          have henv_out : AcceptBadKemEnv P inp
              (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) :=
            hevs_eq.symm
          clear h_canon h_agree hshim halloc hdealloc hmemcpy
          refine sepWP_instantiate_ro1_post_exists
            (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1) ?_
          simp only [sepConj_assoc, *]; wp_done
        · have hF8 : LsFullFrozenInv lsmpl sf3 := LsFullFrozenInv.of_frozen hfr8
          have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh3_len]
          have hpfx3_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
            P.x25519 inp.ikBSk inp.hdr.ekAPk ++ P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 :=
            by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
          let st_dh3_a := M.stepEvents (rustAllocEvents 32 1) st_dh2
          let st_dh3 := M.stepEvents (rustDeallocEvents 32 1) st_dh3_a
          have hst_dh3_eq : st_dh3 =
              M.stepEvents (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle) st := by
            dsimp only [st_dh3, st_dh3_a]
            rw [hst_dh2_eq, ← M.stepEvents_append, ← M.stepEvents_append]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
          rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
            hcs3_26, hcs3_27, hcs3_28, hcs3_29, hvregs3⟩
          simp only [arm64_norm]
            at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
               hcs3_29 hvregs3
          cases hopk_eq : inp.opkBSk? with
          | none =>
            have hevs_eq : acceptBadKemEvents P inp =
                rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                  rustDeallocEvents 192 1 := by
              simp only [acceptBadKemEvents, hcanon_b, Bool.not_true, Bool.false_eq_true,
                hdh1, hdh2, hdh3, hopk_eq, ↓reduceIte, dhCycle]
            have hst_fin3 : M.stepEvents (rustDeallocEvents 192 1) st_dh3 =
                M.stepEvents
                  (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                    rustDeallocEvents 192 1) st := by
              rw [hst_dh3_eq, ← M.stepEvents_append]
            have henv_out3 : AcceptBadKemEnv P inp
                (rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++
                  rustDeallocEvents 192 1) := hevs_eq.symm
            simp only [Bool.false_eq_true, ↓reduceIte, emp_sepConj]
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_; sep_elim_exists'; apply SepWPp.of_sepWP_ret
            wp_steps_sync_pool (lsρ lsMemcpySym)
            wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
            refine SepWP.transport_budgetPool ‹_› (hnext := ?_)
            wp_steps_sync_pool (lsρ acceptRustDeallocSym)
            refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
              (by sep_focus) ?_; wp_call hdealloc (dh3_ptr, 32, 1, st_dh3_a)
            refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (pointsToBytes_append_at _
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++ P.x25519 inp.ikBSk inp.hdr.ekAPk)
              (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
              (by simp only [bytesToBv8, List.length_map, hpfx2_len]))) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp 0#64 dh3_ptr 32#64 0#64)
              (by sep_focus) ?_
            refine SepWP.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
            let evs_out3 :=
              rustAllocEvents 192 1 ++ dhCycle ++ dhCycle ++ dhCycle ++ rustDeallocEvents 192 1
            badkem_ct_exit_placed s0 A ctBufPtr hbadKem hct_bd
              h_canon h_agree hshim halloc hdealloc hmemcpy st_dh3
              evs_out3 hst_fin3 henv_out3
          | some _ => simp [hopk_eq] at hopk_none_in

end LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA
