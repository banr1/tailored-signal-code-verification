/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.HooksE.Common

/-!
# Shared-pool (`mallocng`) budget hook discharge helpers

Provides placed `malloc`, `calloc`, and `free` `HookOk` bridges (`malloc_budget_hookOk`,
`calloc_budget_hookOk`, `free_budget_hookOk`), non-OOM CPS stepping rules
(`stepRustAlloc1_budget_cps`, `stepRustDealloc1_budget_cps`), and `vecU8` / `Err` result writers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers

open Arm64 Arm64.CType ProofLib.SepLogic
open ProofLib hiding MallocngAddrs MallocngIface
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open CryptoVerification.E2E (
  aesInput aesIv aesKey
  restoreCallerRegs stepRustAlloc1 stepRustDealloc1 writeVecHeader
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits
  FitsEvent FitsEvents
  MallocngCostModelIface MallocngCostModelSound
  MallocngModelBlock MallocngModelEnv MallocngModelFreeableBlock
  MallocngModelPostEnv MallocngModelZeroedBlock
  RustLayoutOk VmPreserved
  allocMallocng_svcValid
  mallocngModelCallocSpec mallocngModelFreeSpec mallocngModelMallocSpec
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  allocCallPreserved_of_mallocngProcPreserved allocCallPreserved_trans
  callocHookBridgeSpec freeHookBridgeSpec hook_oom_false
  mallocHookBridgeSpec mallocngHook mallocngHookBudgetPool mallocngHookBudgetPool_transport
  mallocngHookRustCliAllocBudget oomCond_to_oomPreserved_hookExit
  packHookPostEnv perm_writeVecHeader procPreserved_hookExit runPlacedAllocHook
  spAligned_sub_16 stackAt_split_frame unpackHookBudgetPool
  vmPreserved_restoreCallerRegs vmPreserved_writeReg64
)
open VerifiedLibraries.Mallocng (
  MallocngMaxAllocSize mallocngAddrsOfPlacement mallocngStackBytes
)

/-! ## `MultiCodeROHook` budget bridges (`malloc`, `calloc`, `free`) -/

private theorem pure_sepConj_of_true {P : Prop} {Q : SepProp} (h : P) : (⌜P⌝ ∗ Q) = Q := by
  simp [h]

theorem malloc_budget_hookOk {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (mallocngHook mpl "malloc")
      (mallocHookBridgeSpec M I γ mpl tp brkStart lim) := by
  have hEntries := hS.entries_ok mpl allocMallocng hPl allocMallocng_svcValid
  refine runPlacedAllocHook hPl (hEntries.malloc_ok γ) ?_
  rintro ⟨req, sp, st⟩ R s0 i hpre
  set entry := VerifiedLibraries.mallocngLib.fnAddr mpl "malloc"
  set s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  dsimp only [mallocHookBridgeSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hsp⟩, hpre⟩ := hpre
  obtain ⟨staticIvs, ivs0, hrx0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackHookBudgetPool hS hpre
  refine ⟨(req, sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
  · dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec]
    have hx0' : s0'.readReg64 .x0 = req := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0] using hx0
    have hsp' : s0'.sp = sp := by simpa [s0', multiCodeROHookEntry_sp] using hsp
    have henv' :
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' =
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 := by
      simp [MallocngModelEnv, s0',
        multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_brk]
    simp only [ctype_simp, henv', sepConj_assoc]
    rw [sepConj_left_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      pure_sepConj_of_true (by simp [hx0', hsp'])]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
  · intro sf' _hLf hpprw' hkf' _hoom hoomSat
    dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec] at hoomSat
    rw [satisfies_pure_sepConj] at hoomSat
    obtain ⟨hOomCond, hCodeRest⟩ := hoomSat
    have hR_exit :
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨ R := by
      have hs0_codeR : s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        have h1 : s0.mem ⊨
            MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 ∗
              stackFrameAt sp mallocngStackBytes ∗
              (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
        exact Satisfies.of_sep_right (Satisfies.of_sep_right h1)
      have hsf_codeR :
          (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        simpa only [multiCodeROHookExit_mem] using
          satisfies_restoreMultiCodeMem hPl hkf' hs0_codeR hCodeRest
      exact Satisfies.of_sep_right hsf_codeR
    have hOomPres := oomCond_to_oomPreserved_hookExit hOomCond
    have hNotFit : ¬ FitsEvent M lim st (.alloc req.toNat) := by
      rintro ⟨hMax, hFitStep⟩
      have hok : decide (req.toNat ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
      simp only [hok, ↓reduceIte] at hOomCond
      exact hook_oom_false hFitStep hrx0 hInv0 hIvsLen hIvsSum hpprw' hOomCond
    dsimp only [mallocHookBridgeSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotFit, hOomPres⟩, hR_exit⟩
  · intro sf' hLf hpprw' _hkf' _hret _hcc hpost
    dsimp only [mallocngModelMallocSpec, ToBaseSpec.toSpec] at hpost
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    have hx0_exit : sf'.readReg64 (.gpr 0#5) = sf.readReg64 .x0 :=
      (multiCodeROHookExit_readReg64 VerifiedLibraries.mallocngLib mpl i s0 sf' .x0).symm
    cases hok : decide (req.toNat ≤ MallocngMaxAllocSize) with
    | true =>
      have hPack := packHookPostEnv I γ mpl tp brkStart
        (st' := M.step (.alloc req.toNat) st) hrx0 hInv0 hLf hpprw'
      simp only [hok, ↓reduceIte, ctype_simp, MallocngModelBlock, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨_, hne, hal16, hfit64⟩, hacc⟩, hpost⟩ := hpost
      rw [hx0_exit] at hne hal16 hfit64 hpost
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart
              (M.step (.alloc req.toNat) st) ivs0 s0' sf') ∗
            (I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
              memRegion (sf.readReg64 .x0) req.toNat ∗
              stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [mallocHookBridgeSpec]
      simp only [hok, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc req.toNat) st) sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
              memRegion (sf.readReg64 .x0) req.toNat)) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + req.toNat < 2 ^ 64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc req.toNat) st) sf ∗
                (I.BlockM γ (sf.readReg64 .x0) req.toNat 16 ∗
                  memRegion (sf.readReg64 .x0) req.toNat ∗
                  stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hne, hal16, hfit64⟩, hpost1⟩
    | false =>
      have hPack := packHookPostEnv I γ mpl tp brkStart (st' := st) hrx0 hInv0 hLf hpprw'
      simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨hnull, hpost⟩ := hpost
      rw [hx0_exit] at hnull
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' sf') ∗
            (stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [mallocHookBridgeSpec]
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
                (stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hnull, hpost1⟩

theorem calloc_budget_hookOk {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (mallocngHook mpl "calloc")
      (callocHookBridgeSpec M I γ mpl tp brkStart lim) := by
  have hEntries := hS.entries_ok mpl allocMallocng hPl allocMallocng_svcValid
  refine runPlacedAllocHook hPl (hEntries.calloc_ok γ) ?_
  rintro ⟨nmemb, size, sp, st⟩ R s0 i hpre
  set entry := VerifiedLibraries.mallocngLib.fnAddr mpl "calloc"
  set s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  dsimp only [callocHookBridgeSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hsp⟩, hpre⟩ := hpre
  obtain ⟨staticIvs, ivs0, hrx0, hInv0, hIvsLen, hIvsSum, hpreEnv⟩ := unpackHookBudgetPool hS hpre
  refine ⟨(nmemb, size, sp, tp, brkStart, st, ivs0), R, ?_, ?_, ?_⟩
  · dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec]
    have hx0' : s0'.readReg64 .x0 = nmemb := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0] using hx0
    have hx1' : s0'.readReg64 .x1 = size := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x1] using hx1
    have hsp' : s0'.sp = sp := by simpa [s0', multiCodeROHookEntry_sp] using hsp
    have henv' :
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' =
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 := by
      simp [MallocngModelEnv, s0',
        multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_brk]
    simp only [ctype_simp, henv', sepConj_assoc]
    rw [sepConj_left_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      pure_sepConj_of_true (by simp [hx0', hx1', hsp'])]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
  · intro sf' _hLf hpprw' hkf' _hoom hoomSat
    dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec] at hoomSat
    rw [satisfies_pure_sepConj] at hoomSat
    obtain ⟨hOomCond, hCodeRest⟩ := hoomSat
    have hR_exit :
        (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨ R := by
      have hs0_codeR : s0.mem ⊨ VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        have h1 : s0.mem ⊨
            MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 ∗
              stackFrameAt sp mallocngStackBytes ∗
              (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
        exact Satisfies.of_sep_right (Satisfies.of_sep_right h1)
      have hsf_codeR :
          (multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf').mem ⊨
            VerifiedLibraries.mallocngLib.codeRO mpl ∗ R := by
        simpa only [multiCodeROHookExit_mem] using
          satisfies_restoreMultiCodeMem hPl hkf' hs0_codeR hCodeRest
      exact Satisfies.of_sep_right hsf_codeR
    have hOomPres := oomCond_to_oomPreserved_hookExit hOomCond
    have hNotFit : ¬ FitsEvent M lim st (.alloc (nmemb.toNat * size.toNat)) := by
      rintro ⟨hMax, hFitStep⟩
      have hok : decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) = true :=
        decide_eq_true hMax
      simp only [hok, ↓reduceIte] at hOomCond
      exact hook_oom_false hFitStep hrx0 hInv0 hIvsLen hIvsSum hpprw' hOomCond
    dsimp only [callocHookBridgeSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotFit, hOomPres⟩, hR_exit⟩
  · intro sf' hLf hpprw' _hkf' _hret _hcc hpost
    dsimp only [mallocngModelCallocSpec, ToBaseSpec.toSpec] at hpost
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    let total := nmemb.toNat * size.toNat
    have hx0_exit : sf'.readReg64 (.gpr 0#5) = sf.readReg64 .x0 :=
      (multiCodeROHookExit_readReg64 VerifiedLibraries.mallocngLib mpl i s0 sf' .x0).symm
    cases hok : decide (nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize) with
    | true =>
      have hPack := packHookPostEnv I γ mpl tp brkStart
        (st' := M.step (.alloc total) st) hrx0 hInv0 hLf hpprw'
      simp only [hok, ↓reduceIte, ctype_simp, MallocngModelZeroedBlock, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨_, hne, hal16, hfit64⟩, hacc⟩, hpost⟩ := hpost
      rw [hx0_exit] at hne hal16 hfit64 hpost
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart
              (M.step (.alloc total) st) ivs0 s0' sf') ∗
            (I.BlockM γ (sf.readReg64 .x0) total 16 ∗
              (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8) ∗
              stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [callocHookBridgeSpec]
      simp only [hok, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc total) st) sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) total 16 ∗
              (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + total < 2 ^ 64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc total) st) sf ∗
                (I.BlockM γ (sf.readReg64 .x0) total 16 ∗
                  (sf.readReg64 .x0 ↦ₛ List.replicate total 0#8) ∗
                  stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hne, hal16, hfit64⟩, hpost1⟩
    | false =>
      have hPack := packHookPostEnv I γ mpl tp brkStart (st' := st) hrx0 hInv0 hLf hpprw'
      simp only [hok, Bool.false_eq_true, ↓reduceIte, ctype_simp, sepConj_assoc] at hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨_, hacc⟩, hpost⟩ := hpost
      rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
        sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨hnull, hpost⟩ := hpost
      rw [hx0_exit] at hnull
      have hacp : AllocCallPreserved s0 sf :=
        allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
      have hpostReord : sf.mem ⊨
          (VerifiedLibraries.mallocngLib.codeRO mpl ∗
            MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' sf') ∗
            (stackFrameAt sp mallocngStackBytes ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
      dsimp only [callocHookBridgeSpec]
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
            stackFrameAt sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngHookBudgetPool M I γ mpl tp brkStart lim st sf ∗
                (stackFrameAt sp mallocngStackBytes ∗ R))) := by sep_ac_rfl
      rw [hGoalEq, satisfies_pure_sepConj]
      refine ⟨hacp, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hnull, hpost1⟩

theorem free_budget_hookOk {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {mpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) :
    HookOk (mallocngHook mpl "free")
      (freeHookBridgeSpec M I γ mpl tp brkStart lim) := by
  have hEntries := hS.entries_ok mpl allocMallocng hPl allocMallocng_svcValid
  refine runPlacedAllocHook hPl (hEntries.free_ok γ) ?_
  rintro ⟨p, n, align, sp, st⟩ R s0 i hpre
  set entry := VerifiedLibraries.mallocngLib.fnAddr mpl "free"
  set s0' := multiCodeROHookEntry VerifiedLibraries.mallocngLib mpl i entry s0
  dsimp only [freeHookBridgeSpec] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ s0.sp = sp ∧
          (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
        (if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
        stackFrameAt sp mallocngStackBytes) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ s0.sp = sp ∧
          (if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64)⌝ ∗
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s0 ∗
          ((if p = 0#64 then emp else I.BlockM γ p n (max align 16) ∗ memRegion p n) ∗
            stackFrameAt sp mallocngStackBytes ∗ R)) := by sep_ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hsp, hpWf⟩, hpre⟩ := hpre
  obtain ⟨staticIvs, ivs0, hrx0, hInv0, _hIvsLen, _hIvsSum, hpreEnv⟩ := unpackHookBudgetPool hS hpre
  refine ⟨(p, sp, n, align, tp, brkStart, st, ivs0), R, ?_,
    (fun _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho)), ?_⟩
  · dsimp only [mallocngModelFreeSpec, ToBaseSpec.toSpec, MallocngModelFreeableBlock]
    have hx0' : s0'.readReg64 .x0 = p := by
      simpa [s0', multiCodeROHookEntry_readReg64 _ _ _ _ _ .x0] using hx0
    have hsp' : s0'.sp = sp := by simpa [s0', multiCodeROHookEntry_sp] using hsp
    have henv' :
        MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0' =
          MallocngModelEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st ivs0 s0 := by
      simp [MallocngModelEnv, s0',
        multiCodeROHookEntry_tpidrEl0, multiCodeROHookEntry_brkStart, multiCodeROHookEntry_brk]
    simp only [ctype_simp, henv', sepConj_assoc]
    rw [sepConj_left_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      pure_sepConj_of_true ⟨hx0', hsp', hpWf⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpreEnv
  · intro sf' hLf hpprw' _hkf' _hret _hcc hpost
    dsimp only [mallocngModelFreeSpec, ToBaseSpec.toSpec] at hpost
    let sf := multiCodeROHookExit VerifiedLibraries.mallocngLib mpl i s0 sf'
    let st' := if p == 0#64 then st else M.step (.free align n) st
    have hPack := packHookPostEnv I γ mpl tp brkStart (st' := st') hrx0 hInv0 hLf hpprw'
    simp only [ctype_simp, sepConj_assoc] at hpost
    rw [← sepConj_assoc, sepConj_comm (VerifiedLibraries.mallocngLib.codeRO mpl),
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hacc, hpost⟩ := hpost
    have hacp : AllocCallPreserved s0 sf :=
      allocCallPreserved_of_mallocngProcPreserved (procPreserved_hookExit hacc.1)
    have hpostReord : sf.mem ⊨
        (VerifiedLibraries.mallocngLib.codeRO mpl ∗
          MallocngModelPostEnv M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st' ivs0 s0' sf') ∗
          (stackFrameAt sp mallocngStackBytes ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    have hpost1 := Satisfies.mono (sepConj_mono_left hPack) hpostReord
    dsimp only [freeHookBridgeSpec]
    have hGoalEq :
        (⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
          stackFrameAt sp mallocngStackBytes) ∗ R =
        ⌜AllocCallPreserved s0 sf⌝ ∗
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim st' sf ∗
            (stackFrameAt sp mallocngStackBytes ∗ R)) := by sep_ac_rfl
    rw [hGoalEq, satisfies_pure_sepConj]
    exact ⟨hacp, hpost1⟩

/-! ## Non-OOM CPS rules (`stepRustAlloc1`, `stepRustDealloc1`) and `vecU8` / `Err` writers -/

theorem rustAllocEvents_one {size : Nat} (hpos : 1 ≤ size) :
    rustAllocEvents size 1 = [.alloc size] := by
  unfold rustAllocEvents
  simp [hpos]

@[simp] theorem rustDeallocEvents_one (size : Nat) :
    rustDeallocEvents size 1 = [.free 1 size] := rfl

theorem fitsEvent_of_fitsAlloc1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {size : Nat}
    (hpos : 1 ≤ size) (h : FitsEvents M lim st (rustAllocEvents size 1)) :
    FitsEvent M lim st (.alloc size) := by
  rw [rustAllocEvents_one hpos] at h
  exact h.1

/-- Non-OOM CPS proof rule for `stepRustAlloc1` under `FitsEvent M lim st (.alloc size)`:
    rules out both `.OutOfMemory` and `0#64` (`NULL`) return, advances `st` to
    `M.step (.alloc size) st`, and passes `I.BlockM γ p size 16` + alignment/bounds metadata to `k`. -/
theorem stepRustAlloc1_budget_cps {α : Type} {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    {spec : Spec α} {x : α} {R Rest : SepProp} {s0 s : State}
    (zeroed : Bool) (frameBytes size : Nat) (hfb16 : frameBytes % 16 = 0)
    (hfb_le : frameBytes + mallocngStackBytes ≤ extHookStack)
    (hFit : FitsEvent M lim st (.alloc size))
    (hrun : s.status = .Running) (hsp_eq : s.sp = s0.sp) (hregs_eq : s.regs = s0.regs)
    (hvregs_eq : s.vregs = s0.vregs) (hsp_al : s0.spAligned = true)
    (hkf0 : s0.mem.KeepsFrozen s.mem) (hsym0 : s.symtab = s0.symtab)
    (hpres0 : AllocCallPreserved s0 s)
    (hmem : s.mem ⊨
      (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗
        stackAt s0.sp extHookStack ∗ Rest) ∗ R)
    (k : State → BitVec 64 → State)
    (hk : ∀ (s1 : State) (p : BitVec 64),
      p ≠ 0#64 → 16 ∣ p.toNat → p.toNat + size < 2 ^ 64 →
      s1.status = .Running → s1.sp = s0.sp → s1.regs = s0.regs → s1.vregs = s0.vregs →
      s0.mem.KeepsFrozen s1.mem → s1.symtab = s0.symtab → AllocCallPreserved s0 s1 →
      (s1.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
          stackAt s0.sp extHookStack ∗
          I.BlockM γ p size 16 ∗
          (if zeroed then (p ↦ₛ List.replicate size 0#8) else memRegion p size) ∗
          Rest) ∗ R) →
      s0.mem.KeepsFrozen (k s1 p).mem ∧ (k s1 p).symtab = s0.symtab ∧
        SubroutineOutcome spec x R s0 (k s1 p)) :
    s0.mem.KeepsFrozen (stepRustAlloc1 mpl zeroed frameBytes size k s).mem ∧
      (stepRustAlloc1 mpl zeroed frameBytes size k s).symtab = s0.symtab ∧
      SubroutineOutcome spec x R s0 (stepRustAlloc1 mpl zeroed frameBytes size k s) := by
  have hsz_le : size ≤ MallocngMaxAllocSize := hFit.1
  have hmax : MallocngMaxAllocSize < 2 ^ 64 := by decide
  have hsz_bv : (BitVec.ofNat 64 size).toNat = size := Nat.mod_eq_of_lt (by omega)
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  have hsCall_run : sCall.status = .Running := by cases zeroed <;> exact hrun
  have hsCall_mem : sCall.mem = s.mem := by cases zeroed <;> rfl
  have hsCall_sym : sCall.symtab = s.symtab := by cases zeroed <;> rfl
  have hsCall_sp : sCall.sp = spCall := by cases zeroed <;> rfl
  have hsCall_x0 : sCall.readReg64 .x0 = BitVec.ofNat 64 size := by
    cases zeroed <;> simp [sCall, sCall0, State.writeReg64, State.readReg64, RegFile.read, RegFile.write]
  have hsCall_pres : AllocCallPreserved s0 sCall := by cases zeroed <;> exact hpres0
  have hsCall_al : sCall.spAligned = true := by
    simp only [State.spAligned, hsCall_sp, spCall, hsp_eq]; exact spAligned_sub_16 hsp_al hfb16
  have hsCall_vm : VmPreserved s sCall := by
    have hvm0 : VmPreserved s sCall0 :=
      (vmPreserved_writeReg64 s .sp spCall).trans
        (vmPreserved_writeReg64 (s.writeReg64 .sp spCall) .x0 (BitVec.ofNat 64 size))
    cases zeroed with
    | false => exact hvm0
    | true => exact hvm0.trans (vmPreserved_writeReg64 sCall0 .x1 1#64)
  let Slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - frameBytes - mallocngStackBytes) ∗
    memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes
  have hstk_eq : stackAt s0.sp extHookStack = stackFrameAt spCall mallocngStackBytes ∗ Slack := by
    dsimp only [spCall, Slack]; rw [hsp_eq]; exact stackAt_split_frame s0.sp frameBytes hfb_le
  have hpool_call :
      mallocngHookBudgetPool M I γ mpl tp brkStart lim st sCall =
        mallocngHookBudgetPool M I γ mpl tp brkStart lim st s :=
    mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hsCall_vm
  cases zeroed with
  | false =>
    let s1 := mallocngHook mpl "malloc" sCall
    have hstep_eq : stepRustAlloc1 mpl false frameBytes size k s =
        (if s1.status != .Running then s1 else let p := s1.readReg64 .x0
          let sKeep := restoreCallerRegs s s1
          if p == 0#64 then Rust.panicked sKeep else k sKeep p) := rfl
    rw [hstep_eq]
    have hpre_m : sCall.mem ⊨
        (mallocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (BitVec.ofNat 64 size, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
      dsimp only [mallocHookBridgeSpec]
      rw [hsCall_mem, hpool_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hsCall_x0, hsCall_sp⟩, ?_⟩
      rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨hkf1, hsym1, hout1⟩ := malloc_budget_hookOk hS γ tp brkStart lim hPl
      (BitVec.ofNat 64 size, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hsCall_run hpre_m hsCall_al
    have hkf01 : s0.mem.KeepsFrozen s1.mem := hkf0.trans (hsCall_mem ▸ hkf1)
    have hsym01 : s1.symtab = s0.symtab := hsym1.trans (hsCall_sym.trans hsym0)
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom1⟩
    · have hs1_run : s1.status = .Running := hret1.2.2
      rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [mallocHookBridgeSpec] at hpost1
      change s1.mem ⊨ _ at hpost1
      have hok : decide (size ≤ MallocngMaxAllocSize) = true := decide_eq_true hsz_le
      simp only [hsz_bv, hok, ↓reduceIte, sepConj_assoc] at hpost1
      rw [satisfies_pure_sepConj] at hpost1
      obtain ⟨hpres1', hpost1⟩ := hpost1
      have hpull :
          mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
            (stackFrameAt spCall mallocngStackBytes ∗
              (⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
                  (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
                (I.BlockM γ (s1.readReg64 .x0) size 16 ∗
                  (memRegion (s1.readReg64 .x0) size ∗ (Slack ∗ (Rest ∗ R)))))) =
          ⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
              (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
              (stackFrameAt spCall mallocngStackBytes ∗ Slack) ∗
              I.BlockM γ (s1.readReg64 .x0) size 16 ∗
              memRegion (s1.readReg64 .x0) size ∗ Rest ∗ R) := by sep_ac_rfl
      rw [hpull, satisfies_pure_sepConj] at hpost1
      obtain ⟨⟨hp_ne, hp_al16, hp_fit64⟩, hpost1⟩ := hpost1
      rw [beq_eq_false_iff_ne.mpr hp_ne]; simp only [Bool.false_eq_true, ↓reduceIte]
      let sKeep := restoreCallerRegs s s1
      have hpres1 := allocCallPreserved_trans hsCall_pres hpres1'
      have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
        (M.step (.alloc size) st) (vmPreserved_restoreCallerRegs s s1)
      have hmem_keep : sKeep.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) sKeep ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ (s1.readReg64 .x0) size 16 ∗
            memRegion (s1.readReg64 .x0) size ∗ Rest) ∗ R := by
        change s1.mem ⊨ _
        rw [hpool_keep, hstk_eq]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
      exact hk sKeep (s1.readReg64 .x0) hp_ne hp_al16 hp_fit64
        hs1_run hsp_eq hregs_eq hvregs_eq hkf01 hsym01 hpres1 hmem_keep
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [mallocHookBridgeSpec] at hoom1
      rw [satisfies_pure_sepConj] at hoom1
      rw [hsz_bv] at hoom1
      exact False.elim (hoom1.1.1 hFit)
  | true =>
    let s1 := mallocngHook mpl "calloc" sCall
    have hstep_eq : stepRustAlloc1 mpl true frameBytes size k s =
        (if s1.status != .Running then s1 else let p := s1.readReg64 .x0
          let sKeep := restoreCallerRegs s s1
          if p == 0#64 then Rust.panicked sKeep else k sKeep p) := rfl
    rw [hstep_eq]
    have hsCall_x1 : sCall.readReg64 .x1 = 1#64 := by
      simp [sCall, sCall0, State.writeReg64, State.readReg64, RegFile.read, RegFile.write]
    have hpre_c : sCall.mem ⊨
        (callocHookBridgeSpec M I γ mpl tp brkStart lim).pre
          (BitVec.ofNat 64 size, 1#64, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
      dsimp only [callocHookBridgeSpec]
      rw [hsCall_mem, hpool_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hsCall_x0, hsCall_x1, hsCall_sp⟩, ?_⟩
      rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    obtain ⟨hkf1, hsym1, hout1⟩ := calloc_budget_hookOk hS γ tp brkStart lim hPl
      (BitVec.ofNat 64 size, 1#64, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hsCall_run hpre_c hsCall_al
    have hkf01 : s0.mem.KeepsFrozen s1.mem := hkf0.trans (hsCall_mem ▸ hkf1)
    have hsym01 : s1.symtab = s0.symtab := hsym1.trans (hsCall_sym.trans hsym0)
    have htot : (BitVec.ofNat 64 size).toNat * (1#64).toNat = size := by
      change (BitVec.ofNat 64 size).toNat * 1 = size; rw [Nat.mul_one, hsz_bv]
    rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom1⟩
    · have hs1_run : s1.status = .Running := hret1.2.2
      rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [callocHookBridgeSpec] at hpost1
      change s1.mem ⊨ _ at hpost1
      have hok : decide (size ≤ MallocngMaxAllocSize) = true := decide_eq_true hsz_le
      simp only [htot, hok, ↓reduceIte, sepConj_assoc] at hpost1
      rw [satisfies_pure_sepConj] at hpost1
      obtain ⟨hpres1', hpost1⟩ := hpost1
      have hpull :
          mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
            (stackFrameAt spCall mallocngStackBytes ∗
              (⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
                  (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
                (I.BlockM γ (s1.readReg64 .x0) size 16 ∗
                  ((s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ (Slack ∗ (Rest ∗ R)))))) =
          ⌜s1.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (s1.readReg64 .x0).toNat ∧
              (s1.readReg64 .x0).toNat + size < 2 ^ 64⌝ ∗
            (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) s1 ∗
              (stackFrameAt spCall mallocngStackBytes ∗ Slack) ∗
              I.BlockM γ (s1.readReg64 .x0) size 16 ∗
              (s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ Rest ∗ R) := by sep_ac_rfl
      rw [hpull, satisfies_pure_sepConj] at hpost1
      obtain ⟨⟨hp_ne, hp_al16, hp_fit64⟩, hpost1⟩ := hpost1
      rw [beq_eq_false_iff_ne.mpr hp_ne]; simp only [Bool.false_eq_true, ↓reduceIte]
      let sKeep := restoreCallerRegs s s1
      have hpres1 := allocCallPreserved_trans hsCall_pres hpres1'
      have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
        (M.step (.alloc size) st) (vmPreserved_restoreCallerRegs s s1)
      have hmem_keep : sKeep.mem ⊨
          (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.alloc size) st) sKeep ∗
            stackAt s0.sp extHookStack ∗
            I.BlockM γ (s1.readReg64 .x0) size 16 ∗
            (s1.readReg64 .x0 ↦ₛ List.replicate size 0#8) ∗ Rest) ∗ R := by
        change s1.mem ⊨ _
        rw [hpool_keep, hstk_eq]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
      exact hk sKeep (s1.readReg64 .x0) hp_ne hp_al16 hp_fit64
        hs1_run hsp_eq hregs_eq hvregs_eq hkf01 hsym01 hpres1 hmem_keep
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [callocHookBridgeSpec] at hoom1
      rw [satisfies_pure_sepConj] at hoom1
      rw [htot] at hoom1
      exact False.elim (hoom1.1.1 hFit)

/-- CPS proof rule for `stepRustDealloc1` (`align = 1`): consumes
    `I.BlockM γ ptr size 16 ∗ memRegion ptr size` and advances `st` to `M.step (.free 1 size) st`. -/
theorem stepRustDealloc1_budget_cps {α : Type} {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    {spec : Spec α} {x : α} {R Rest : SepProp} {s0 s : State}
    (frameBytes size : Nat) (ptr : BitVec 64)
    (hptr_ne : ptr ≠ 0#64) (hptr_al16 : 16 ∣ ptr.toNat) (hptr_fit64 : ptr.toNat + size < 2 ^ 64)
    (hfb16 : frameBytes % 16 = 0)
    (hfb_le : frameBytes + mallocngStackBytes ≤ extHookStack) (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp) (hregs_eq : s.regs = s0.regs) (hvregs_eq : s.vregs = s0.vregs)
    (hsp_al : s0.spAligned = true) (hkf0 : s0.mem.KeepsFrozen s.mem) (hsym0 : s.symtab = s0.symtab)
    (hpres0 : AllocCallPreserved s0 s)
    (hmem : s.mem ⊨
      (mallocngHookBudgetPool M I γ mpl tp brkStart lim st s ∗
        stackAt s0.sp extHookStack ∗
        I.BlockM γ ptr size 16 ∗ memRegion ptr size ∗ Rest) ∗ R)
    (k : State → State)
    (hk : ∀ (s1 : State), s1.status = .Running → s1.sp = s0.sp → s1.regs = s0.regs →
      s1.vregs = s0.vregs → s0.mem.KeepsFrozen s1.mem → s1.symtab = s0.symtab →
      AllocCallPreserved s0 s1 →
      (s1.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free 1 size) st) s1 ∗
          stackAt s0.sp extHookStack ∗ Rest) ∗ R) →
      s0.mem.KeepsFrozen (k s1).mem ∧ (k s1).symtab = s0.symtab ∧
        SubroutineOutcome spec x R s0 (k s1)) :
    s0.mem.KeepsFrozen (stepRustDealloc1 mpl frameBytes ptr k s).mem ∧
      (stepRustDealloc1 mpl frameBytes ptr k s).symtab = s0.symtab ∧
      SubroutineOutcome spec x R s0 (stepRustDealloc1 mpl frameBytes ptr k s) := by
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  have hsCall_al : sCall.spAligned = true := by
    simp only [State.spAligned, sCall, State.writeReg64, spCall, hsp_eq]
    exact spAligned_sub_16 hsp_al hfb16
  have hsCall_vm : VmPreserved s sCall :=
    (vmPreserved_writeReg64 s .sp spCall).trans
      (vmPreserved_writeReg64 (s.writeReg64 .sp spCall) .x0 ptr)
  let Slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - frameBytes - mallocngStackBytes) ∗
    memRegion (s0.sp - BitVec.ofNat 64 frameBytes) frameBytes
  have hstk_eq : stackAt s0.sp extHookStack = stackFrameAt spCall mallocngStackBytes ∗ Slack := by
    dsimp only [spCall, Slack]; rw [hsp_eq]; exact stackAt_split_frame s0.sp frameBytes hfb_le
  have hpool_call :=
    mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hsCall_vm
  let s1 := mallocngHook mpl "free" sCall
  have hstep_eq : stepRustDealloc1 mpl frameBytes ptr k s =
      (if s1.status != .Running then s1 else k (restoreCallerRegs s s1)) := rfl
  rw [hstep_eq]
  have hmax1 : max 1 16 = 16 := rfl
  have hpre_f : sCall.mem ⊨
      (freeHookBridgeSpec M I γ mpl tp brkStart lim).pre
        (ptr, size, 1, spCall, st) sCall ∗ ((Slack ∗ Rest) ∗ R) := by
    dsimp only [freeHookBridgeSpec]
    simp only [hptr_ne, ↓reduceIte, hmax1]
    change s.mem ⊨ _
    rw [hpool_call, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [sCall, State.writeReg64, State.readReg64, RegFile.read, RegFile.write],
      rfl, hptr_al16, hptr_fit64⟩, ?_⟩
    rw [hstk_eq] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨hkf1, hsym1, hout1⟩ := free_budget_hookOk hS γ tp brkStart lim hPl
    (ptr, size, 1, spCall, st) ((Slack ∗ Rest) ∗ R) sCall hrun hpre_f hsCall_al
  have hkf01 : s0.mem.KeepsFrozen s1.mem := hkf0.trans hkf1
  have hsym01 : s1.symtab = s0.symtab := hsym1.trans hsym0
  rcases hout1 with ⟨hret1, _, hpost1⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hs1_run : s1.status = .Running := hret1.2.2
    rw [show (s1.status != .Running) = false by rw [hs1_run]; rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [freeHookBridgeSpec] at hpost1
    change s1.mem ⊨ _ at hpost1
    rw [beq_eq_false_iff_ne.mpr hptr_ne] at hpost1
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost1
    rw [satisfies_pure_sepConj] at hpost1
    obtain ⟨hpres1', hpost1⟩ := hpost1
    let sKeep := restoreCallerRegs s s1
    have hpres1 := allocCallPreserved_trans hpres0 hpres1'
    have hpool_keep := mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim
      (M.step (.free 1 size) st) (vmPreserved_restoreCallerRegs s s1)
    have hmem_keep : sKeep.mem ⊨
        (mallocngHookBudgetPool M I γ mpl tp brkStart lim (M.step (.free 1 size) st) sKeep ∗
          stackAt s0.sp extHookStack ∗ Rest) ∗ R := by
      change s1.mem ⊨ _
      rw [hpool_keep, hstk_eq]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
    exact hk sKeep hs1_run hsp_eq hregs_eq hvregs_eq hkf01 hsym01 hpres1 hmem_keep
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem rustLayoutOk_one {cap : Nat} (hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    RustLayoutOk cap 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩

theorem pointsTo_replicate_to_memRegion (p : BitVec 64) (n : Nat) :
    (p ↦ₛ List.replicate n 0#8) ⊢ memRegion p n := by
  simpa only [List.length_replicate] using pointsToBytes_entails_memRegion p (List.replicate n 0#8)

private theorem keepsFrozen_write64_of_pointsTo64 {m : Memory} {a old : BitVec 64} {F : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ old) ∗ F) :
    m.KeepsFrozen (m.write64 a v) := by
  have hm : m ⊨ memRegion a 8 ∗ F :=
    Satisfies.mono (sepConj_mono_left (pointsTo64_entails_memRegion a old)) h
  exact Memory.keepsFrozen_write64 ((IsBlock.memRegion a 8).canWrite (by decide) hm) v

private theorem satisfies_write64_of_pointsTo64 {m : Memory} {a old : BitVec 64} {F : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ old) ∗ F) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ F := by
  have hm : m ⊨ memRegion a 8 ∗ F :=
    Satisfies.mono (sepConj_mono_left (pointsTo64_entails_memRegion a old)) h
  exact (IsBlock.memRegion a 8).write64 hm v

private theorem writeVecHeader_of_memRegion_aux {m : Memory} {r : BitVec 64} {F : SepProp}
    (v0 v1 v2 : BitVec 64) (h : m ⊨ memRegion r 24 ∗ F) :
    m.KeepsFrozen (writeVecHeader m r v0 v1 v2) ∧
      (writeVecHeader m r v0 v1 v2 ⊨ vecHeader r v0 v1 v2 ∗ F) := by
  unfold writeVecHeader vecHeader
  have h16 : r + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = r + 16#64 := by
    rw [BitVec.add_assoc]; rfl
  have hsplit : memRegion r 24 =
      memRegion r 8 ∗ memRegion (r + 8#64) 8 ∗ memRegion (r + 16#64) 8 := by
    have hs := memRegion_split_three r 8 8 8 (by decide)
    simpa [h16] using hs
  rw [hsplit] at h
  have h1 : m ⊨ memRegion r 8 ∗ (memRegion (r + 8#64) 8 ∗ memRegion (r + 16#64) 8 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h
  have hkf1 := Memory.keepsFrozen_write64 ((IsBlock.memRegion r 8).canWrite (by decide) h1) v0
  have hw1 := (IsBlock.memRegion r 8).write64 h1 v0
  have h2 : m.write64 r v0 ⊨
      memRegion (r + 8#64) 8 ∗ ((r ↦₆₄ v0) ∗ memRegion (r + 16#64) 8 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw1
  have hkf2 := Memory.keepsFrozen_write64
    ((IsBlock.memRegion (r + 8#64) 8).canWrite (by decide) h2) v1
  have hw2 := (IsBlock.memRegion (r + 8#64) 8).write64 h2 v1
  have h3 : (m.write64 r v0).write64 (r + 8#64) v1 ⊨
      memRegion (r + 16#64) 8 ∗ ((r ↦₆₄ v0) ∗ ((r + 8#64) ↦₆₄ v1) ∗ F) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw2
  have hkf3 := Memory.keepsFrozen_write64
    ((IsBlock.memRegion (r + 16#64) 8).canWrite (by decide) h3) v2
  have hw3 := (IsBlock.memRegion (r + 16#64) 8).write64 h3 v2
  exact ⟨hkf1.trans (hkf2.trans hkf3),
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw3⟩

private theorem keepsFrozen_writeVecHeader_of_memRegion {m : Memory} {r : BitVec 64} {F : SepProp}
    (v0 v1 v2 : BitVec 64) (h : m ⊨ memRegion r 24 ∗ F) :
    m.KeepsFrozen (writeVecHeader m r v0 v1 v2) :=
  (writeVecHeader_of_memRegion_aux v0 v1 v2 h).1

private theorem satisfies_writeVecHeader_of_memRegion {m : Memory} {r : BitVec 64} {F : SepProp}
    (v0 v1 v2 : BitVec 64) (h : m ⊨ memRegion r 24 ∗ F) :
    writeVecHeader m r v0 v1 v2 ⊨ vecHeader r v0 v1 v2 ∗ F :=
  (writeVecHeader_of_memRegion_aux v0 v1 v2 h).2

theorem write_vecU8_from_alloc {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName}
    {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {m : Memory} {ret p : BitVec 64} {cap : Nat} {bs : List (BitVec 8)} {Frame : SepProp}
    (hp_ne : p ≠ 0#64) (hp_al16 : 16 ∣ p.toNat) (hp_fit64 : p.toNat + cap < 2 ^ 64)
    (hcap_pos : 0 < cap) (hcap_lt : cap < 2 ^ 63) (hbs_le : bs.length ≤ cap)
    (hmem : m ⊨ I.BlockM γ p cap 16 ∗ memRegion p cap ∗ memRegion ret 24 ∗ Frame) :
    let mf := writeVecHeader (m.writeBytes p bs) ret (BitVec.ofNat 64 cap) p (BitVec.ofNat 64 bs.length)
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧
      (mf ⊨ vecU8 (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc ret bs ∗ Frame) := by
  have hsplit_cap : memRegion p cap =
      memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (cap - bs.length) :=
    (SepFrameInfer.memRegion_merge p (p + BitVec.ofNat 64 bs.length)
      bs.length (cap - bs.length) cap rfl (by omega) (by omega)).symm
  have hm0 : m ⊨ memRegion p bs.length ∗ (memRegion ret 24 ∗ (I.BlockM γ p cap 16 ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (cap - bs.length) ∗ Frame)) := by
    rw [hsplit_cap] at hmem; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf1 := keepsFrozen_writeBytes_of_memRegion bs (by omega) hm0
  have hm1 : m.writeBytes p bs ⊨ memRegion ret 24 ∗ ((p ↦ₛ bs) ∗ I.BlockM γ p cap 16 ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (cap - bs.length) ∗ Frame) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (satisfies_writeBytes bs (by omega) hm0)
  let capW := BitVec.ofNat 64 cap
  let lenW := BitVec.ofNat 64 bs.length
  have hperm :
      (writeVecHeader (m.writeBytes p bs) ret capW p lenW).perm = m.perm := by
    rw [perm_writeVecHeader, Memory.perm_writeBytes]
  refine ⟨hkf1.trans (keepsFrozen_writeVecHeader_of_memRegion capW p lenW hm1), hperm, ?_⟩
  have hw2 := satisfies_writeVecHeader_of_memRegion capW p lenW hm1
  have hcapW_toNat : capW.toNat = cap := Nat.mod_eq_of_lt (by omega)
  have hcapW_ne : capW ≠ 0 := by
    intro h0; have : capW.toNat = 0 := by rw [h0]; rfl
    omega
  unfold vecU8
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨capW, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨p, ?_⟩
  unfold vecU8At; simp only [hcapW_ne, ↓reduceIte, hcapW_toNat]
  have hlive : I.BlockM γ p cap 16 ⊢
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc.live p cap 1 := by
    change I.BlockM γ p cap 16 ⊢
      I.BlockM γ p cap (max 1 16) ∗
        ⌜p ≠ 0#64 ∧ 1 ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + cap < 2 ^ 64 ∧ RustLayoutOk cap 1⌝
    have hmax1 : max 1 16 = 16 := rfl
    rw [hmax1, sepConj_comm]
    exact Entails.pure_right
      ⟨hp_ne, Nat.one_dvd p.toNat, hp_al16, hp_fit64, rustLayoutOk_one hcap_pos hcap_lt⟩
      (Entails.refl _)
  refine Satisfies.mono (Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hlive))) ?_) hw2
  have heq1 : vecHeader ret capW p lenW ∗ ((p ↦ₛ bs) ∗
      ((mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc.live p cap 1 ∗
        memRegion (p + lenW) (cap - bs.length) ∗ Frame)) =
      (vecHeader ret capW p lenW ∗
        ((mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc.live p cap 1 ∗
          (p ↦ₛ bs) ∗ memRegion (p + lenW) (cap - bs.length))) ∗ Frame := by sep_ac_rfl
  rw [heq1]
  exact sepConj_mono_left (sepConj_mono_right
    (Entails.pure_right ⟨hbs_le, hcap_lt, hp_ne⟩ (Entails.refl _)))

theorem write_empty_vecU8 {A : RustAlloc} {m : Memory} {ret : BitVec 64} {Frame : SepProp}
    (hmem : m ⊨ memRegion ret 24 ∗ Frame) :
    let mf := writeVecHeader m ret 0#64 1#64 0#64
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧ (mf ⊨ vecU8 A ret [] ∗ Frame) := by
  refine ⟨keepsFrozen_writeVecHeader_of_memRegion 0#64 1#64 0#64 hmem,
    perm_writeVecHeader m ret 0#64 1#64 0#64, ?_⟩
  have hw := satisfies_writeVecHeader_of_memRegion 0#64 1#64 0#64 hmem
  unfold vecU8
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨0#64, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨1#64, ?_⟩
  unfold vecU8At
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  refine Satisfies.mono (sepConj_mono_left ?_) hw
  rw [sepConj_comm]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem write_aesErr_at_ret {m : Memory} {ret : BitVec 64} {Frame : SepProp}
    (hmem : m ⊨ memRegion ret 24 ∗ Frame) :
    let mf := (m.write64 ret errTag).write64 (ret + 8#64) 1#64
    m.KeepsFrozen mf ∧ (mf.perm = m.perm) ∧
      (mf ⊨ ((ret ↦₆₄ errTag) ∗ (∃∗ q : BitVec 64, ⌜q ≠ 0#64⌝ ∗ ((ret + 8#64) ↦₆₄ q)) ∗
        memRegion (ret + 16#64) 8) ∗ Frame) := by
  have hsplit : memRegion ret 24 = (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      ((∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗ memRegion (ret + 16#64) 8) := by
    rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide), memRegion_eight ret,
      memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
        rfl (by bv_omega) (by decide), memRegion_eight (ret + 8#64)]
  rw [hsplit] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists] at hmem
  rcases hmem with ⟨w1, w0, hmem0⟩
  have hmem1 : m.write64 ret errTag ⊨
      ((ret + 8#64) ↦₆₄ w1) ∗ ((ret ↦₆₄ errTag) ∗ memRegion (ret + 16#64) 8 ∗ Frame) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) (satisfies_write64_of_pointsTo64 errTag hmem0)
  have hperm : ((m.write64 ret errTag).write64 (ret + 8#64) 1#64).perm = m.perm := by
    simp [Memory.perm_write64]
  refine ⟨(keepsFrozen_write64_of_pointsTo64 errTag hmem0).trans
    (keepsFrozen_write64_of_pointsTo64 1#64 hmem1), hperm, ?_⟩
  have hex : ((ret + 8#64) ↦₆₄ 1#64) ⊢ ∃∗ q : BitVec 64, ⌜q ≠ 0#64⌝ ∗ ((ret + 8#64) ↦₆₄ q) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  exact Satisfies.mono (Entails.trans (sepConj_mono_left hex) (Entails.of_eq (by sep_ac_rfl)))
    (satisfies_write64_of_pointsTo64 1#64 hmem1)

theorem aes_post_calloc_inputs {x : AesCall} {s0 s1 : State} {Extra : SepProp}
    (hx0 : s0.readReg64 .x0 = x.inA) (hx1 : (s0.readReg64 .x1).toNat = x.input.length)
    (hx2 : s0.readReg64 .x2 = x.keyA) (hx4 : s0.readReg64 .x4 = x.ivA)
    (hx8 : s0.readReg64 .x8 = x.ret) (hkey_len : x.key.length = 32) (hiv_len : x.iv.length = 16)
    (hs1_regs : s1.regs = s0.regs) (hmem1 : s1.mem ⊨ x.frame ∗ Extra) :
    s1.readReg64 .x8 = x.ret ∧ aesInput s1 = x.input ∧ aesKey s1 = x.key ∧ aesIv s1 = x.iv := by
  have hm_in : s1.mem ⊨ (x.inA ↦ₛ x.input) ∗ ((x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ Extra) := by
    unfold AesCall.frame at hmem1; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
  have hm_k : s1.mem ⊨ (x.keyA ↦ₛ x.key) ∗ ((x.inA ↦ₛ x.input) ∗ (x.ivA ↦ₛ x.iv) ∗ Extra) := by
    unfold AesCall.frame at hmem1; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
  have hm_iv : s1.mem ⊨ (x.ivA ↦ₛ x.iv) ∗ ((x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ Extra) := by
    unfold AesCall.frame at hmem1; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
  refine ⟨by simp [State.readReg64, hs1_regs] at hx8 ⊢; exact hx8, ?_, ?_, ?_⟩
  · have h0 : s1.readReg64 .x0 = x.inA := by simp [State.readReg64, hs1_regs] at hx0 ⊢; exact hx0
    have h1 : (s1.readReg64 .x1).toNat = x.input.length := by simp [State.readReg64, hs1_regs] at hx1 ⊢; exact hx1
    simp only [aesInput, h0, h1]; exact ((IsBlock.pointsToBytes x.inA x.input).read hm_in).2
  · have h2 : s1.readReg64 .x2 = x.keyA := by simp [State.readReg64, hs1_regs] at hx2 ⊢; exact hx2
    simp only [aesKey, h2, ← hkey_len]; exact ((IsBlock.pointsToBytes x.keyA x.key).read hm_k).2
  · have h4 : s1.readReg64 .x4 = x.ivA := by simp [State.readReg64, hs1_regs] at hx4 ⊢; exact hx4
    simp only [aesIv, h4, ← hiv_len]; exact ((IsBlock.pointsToBytes x.ivA x.iv).read hm_iv).2

end LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetHelpers
