/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# Budget-Threaded Relocatable Contracts for `KeyPairCallees`

Allocator-budget-threaded (`RustCliAllocBudget M`) and `VmPreserved` relocatable `[LibsignalPlacement]`
contracts for the curve and ML-KEM key-pair constructors, `KeySerde::serialize` implementations
(Blocks `107`, `109`, `87`), and `PreKeyRecord::new` (Block `66`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl withLsCodeLoaded
   blkPC_66 blkPl_66 blkLib_eq_66
   blkPC_67 blkPl_67
   blkPC_70 blkPl_70
   blkPC_87 blkPl_87 blkLib_eq_87
   blkPC_107 blkPl_107
   blkPC_109 blkPl_109 blkLib_eq_109
   blkPC_112 blkPl_112
   blkPC_113 blkPl_113
   blkPC_209 blkPl_209
   lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsMemcpySym
   ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack publicKeySerializeStack
   sessionShimSpec sessionMemcpyRegionSpec SepWP.instantiate_post_exists)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply
  (boxU8Buf_pk_expose pk_buf_to_memRegion priv_buf_to_memRegion)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   AllocCallPreserved PoolPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents publicKeySerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
  (PrivSerializeEnv privSerializeEvents privSerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget
  (privSerialize_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (pointsToBytes_cons_fold stackAt_publicKeySerialize_sub48 stackAt_publicKeySerialize_sub48_assoc
   memRegion_1569_cons memRegion_3169_cons
   stackAt_112_ext_to SepWP_fold_stack_112_to_ext stack_24_to_memRegion_104
   vecU8_priv_expose_104 sepWP_pure_focus public_key_serialize_placed_ok_of_sessionShim
   rustDeallocTail48BudgetSpec dealloc_tail48_of_dealloc
   rustDeallocTail64BudgetSpec dealloc_tail64_of_dealloc)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Base Contract Re-Exports -/

abbrev curveKeyPairFromPubPrivBudgetSpec :=
  KeyPairCalleesAuxBudget.curveKeyPairFromPubPrivBudgetSpec

theorem curveKeyPairFromPubPriv_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_209).rebase (blkPl_209).base H) (blkPl_209).base
      curveKeyPairFromPubPrivBudgetSpec :=
  KeyPairCalleesAuxBudget.curveKeyPairFromPubPriv_placed_ok H

abbrev curveKeyPairSerdeBudgetSpec :=
  KeyPairCalleesAuxBudget.curveKeyPairSerdeBudgetSpec

theorem curveKeyPairSerde_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_112).rebase (blkPl_112).base H) (blkPl_112).base
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec) :=
  KeyPairCalleesAuxBudget.curveKeyPairSerde_placed_ok H

abbrev preKeyRecordKeyPairBudgetSpec :=
  KeyPairCalleesAuxBudget.preKeyRecordKeyPairBudgetSpec

theorem preKeyRecordKeyPair_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_67).rebase (blkPl_67).base H) (blkPl_67).base
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec) :=
  KeyPairCalleesAuxBudget.preKeyRecordKeyPair_placed_ok H

theorem privKeySerdeSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_107).rebase (blkPl_107).base H) (blkPl_107).base
      (withLsCodeLoaded lsmpl (privSerializeSpec M A lim)) :=
  KeyPairCalleesAuxBudget.privKeySerdeSerialize_placed_ok hshim halloc

abbrev kemKeyPairFromPubPrivEvents := KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivEvents
abbrev KemKeyPairFromPubPrivEnv := KeyPairCalleesAuxBudget.KemKeyPairFromPubPrivEnv
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

abbrev kemKeyPairFromPubPrivOkSpecBase :=
  KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpecBase

abbrev kemKeyPairFromPubPrivOkSpec [LibsignalPlacement] :=
  KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec

theorem kemKeyPairFromPubPriv_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base H) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec M A lim) :=
  KeyPairCalleesAuxBudget.kemKeyPairFromPubPriv_placed_ok hshim halloc hmemcpy

theorem kemKeyPairSerde_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)) :=
  KeyPairCalleesAuxBudget.kemKeyPairSerde_placed_ok hshim halloc hmemcpy

/-! ## `kemPubKeySerdeSerialize_placed_ok` and `kemSecretKeySerdeSerialize_placed_ok` (Block `109`) -/

def kemPubKeySerdeSerializeEvents : List AllocEvent :=
  rustAllocEvents 1569 1 ++ rustAllocEvents 1569 1 ++ rustDeallocEvents 1569 1

def KemPubKeySerdeSerializeEnv (evs : List AllocEvent) : Prop :=
  evs = kemPubKeySerdeSerializeEvents

def kemPubKeySerdeSerializeOkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st KemPubKeySerdeSerializeEnv ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.kemPubKeySerdeSerializeOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    (CryptoVerification.E2E.Pqxdh.ResponderStore.kemPubKeySerdeSerializeOkSpec
      (A.atState lim (M.stepEvents kemPubKeySerdeSerializeEvents st) sf)).post x s0 sf

set_option maxHeartbeats 1200000 in
theorem kemPubKeySerdeSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_109).rebase (blkPl_109).base H) (blkPl_109).base
      (kemPubKeySerdeSerializeOkSpec M A lim) := by
  simp only [kemPubKeySerdeSerializeOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.kemPubKeySerdeSerializeOkSpec,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hdealloc_ok := dealloc_tail64_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_109).rebase (blkPl_109).base H) hdealloc)
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy_ok
  simp only [rustDeallocTail64BudgetSpec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wp_init xst s0
  obtain ⟨⟨self, boxPtr, pk, outPtr⟩, st⟩ := xst
  dsimp only at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = self := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  have hpk_len : pk.length = 1568 := by assumption
  subst hx0_eq hx8_eq
  have hfit_all : FitsEvents M lim st kemPubKeySerdeSerializeEvents :=
    ‹FitsEnv M lim st KemPubKeySerdeSerializeEnv› _ rfl
  rw [kemPubKeySerdeSerializeEvents, fitsEvents_append, fitsEvents_append] at hfit_all
  rcases hfit_all with ⟨⟨hfit1, hfit2⟩, _⟩
  have hfe1 : FitsEvents M lim st [.alloc 1569] := by simpa [rustAllocEvents] using hfit1
  rcases hfe1 with ⟨⟨hwma1, henf, hram1, hva1⟩, -⟩
  have hfe2 : FitsEvents M lim (M.stepEvents (rustAllocEvents 1569 1) st) [.alloc 1569] := by
    simpa [rustAllocEvents] using hfit2
  rcases hfe2 with ⟨⟨hwma2, _, hram2, hva2⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk 1569 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hcons_len : (8#8 :: pk).length = 1569 := by simp [hpk_len]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (1569, 1, st)
  simp only [memRegion_1569_cons, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hpk_len]
  wp_apply
  simp only [hpk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (1569, 1, M.stepEvents (rustAllocEvents 1569 1) st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  refine SepWP.fold (pointsToBytes_cons_fold _ 8#8 pk) (by sep_focus) ?_
  rw [show memRegion _ 1569 = memRegion _ (8#8 :: pk).length by rw [hcons_len]]
  wp_call hmemcpy_ok (_, _, 8#8 :: pk)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_simp_pre [wp_norm]
  refine SepWP.fold (pointsToBytes_cons_fold _ 8#8 pk) (by sep_focus) ?_
  rw [show A.live _ 1569 1 = A.live _ (8#8 :: pk).length 1 by rw [hcons_len]]
  wp_call hdealloc_ok (_, 8#8 :: pk, 1,
    s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5),
    M.stepEvents (rustAllocEvents 1569 1) (M.stepEvents (rustAllocEvents 1569 1) st))
  simp only [hcons_len, kemPubKeySerdeSerializeEvents, AllocCostModel.stepEvents_append]
  wp_done

def kemSecretKeySerdeSerializeEvents : List AllocEvent :=
  rustAllocEvents 3169 1 ++ rustAllocEvents 3169 1 ++ rustDeallocEvents 3169 1

def KemSecretKeySerdeSerializeEnv (evs : List AllocEvent) : Prop :=
  evs = kemSecretKeySerdeSerializeEvents

def kemSecretKeySerdeSerializeOkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st KemSecretKeySerdeSerializeEnv ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.kemSecretKeySerdeSerializeOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    (CryptoVerification.E2E.Pqxdh.ResponderStore.kemSecretKeySerdeSerializeOkSpec
      (A.atState lim (M.stepEvents kemSecretKeySerdeSerializeEvents st) sf)).post x s0 sf

set_option maxHeartbeats 1200000 in
theorem kemSecretKeySerdeSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_109).rebase (blkPl_109).base H) (blkPl_109).base
      (kemSecretKeySerdeSerializeOkSpec M A lim) := by
  simp only [kemSecretKeySerdeSerializeOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.kemSecretKeySerdeSerializeOkSpec,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hdealloc_ok := dealloc_tail64_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_109).rebase (blkPl_109).base H) hdealloc)
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy_ok
  simp only [rustDeallocTail64BudgetSpec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wp_init xst s0
  obtain ⟨⟨self, boxPtr, sk, outPtr⟩, st⟩ := xst
  dsimp only at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = self := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  have hsk_len : sk.length = 3168 := by assumption
  subst hx0_eq hx8_eq
  have hfit_all : FitsEvents M lim st kemSecretKeySerdeSerializeEvents :=
    ‹FitsEnv M lim st KemSecretKeySerdeSerializeEnv› _ rfl
  rw [kemSecretKeySerdeSerializeEvents, fitsEvents_append, fitsEvents_append] at hfit_all
  rcases hfit_all with ⟨⟨hfit1, hfit2⟩, _⟩
  have hfe1 : FitsEvents M lim st [.alloc 3169] := by simpa [rustAllocEvents] using hfit1
  rcases hfe1 with ⟨⟨hwma1, henf, hram1, hva1⟩, -⟩
  have hfe2 : FitsEvents M lim (M.stepEvents (rustAllocEvents 3169 1) st) [.alloc 3169] := by
    simpa [rustAllocEvents] using hfit2
  rcases hfe2 with ⟨⟨hwma2, _, hram2, hva2⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk 3169 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hcons_len : (8#8 :: sk).length = 3169 := by simp [hsk_len]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (3169, 1, st)
  simp only [memRegion_3169_cons, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hsk_len]
  wp_apply
  simp only [hsk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (3169, 1, M.stepEvents (rustAllocEvents 3169 1) st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  refine SepWP.fold (pointsToBytes_cons_fold _ 8#8 sk) (by sep_focus) ?_
  rw [show memRegion _ 3169 = memRegion _ (8#8 :: sk).length by rw [hcons_len]]
  wp_call hmemcpy_ok (_, _, 8#8 :: sk)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_simp_pre [wp_norm]
  refine SepWP.fold (pointsToBytes_cons_fold _ 8#8 sk) (by sep_focus) ?_
  rw [show A.live _ 3169 1 = A.live _ (8#8 :: sk).length 1 by rw [hcons_len]]
  wp_call hdealloc_ok (_, 8#8 :: sk, 1,
    s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5),
    M.stepEvents (rustAllocEvents 3169 1) (M.stepEvents (rustAllocEvents 3169 1) st))
  simp only [hcons_len, kemSecretKeySerdeSerializeEvents, AllocCostModel.stepEvents_append]
  wp_done

/-! ## `pubKeySerdeSerialize_placed_ok` (Block `87`) and `preKeyRecordNew_placed_ok` (Block `66`) -/

def pubKeySerdeSerializeEvents : List AllocEvent :=
  publicKeySerializeEvents ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1

def PubKeySerdeSerializeEnv (evs : List AllocEvent) : Prop :=
  evs = pubKeySerdeSerializeEvents

def pubKeySerdeSerializeOkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × PublicKey × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st PubKeySerdeSerializeEnv ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.pubKeySerdeSerializeOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    (CryptoVerification.E2E.Pqxdh.ResponderStore.pubKeySerdeSerializeOkSpec
      (A.atState lim (M.stepEvents pubKeySerdeSerializeEvents st) sf)).post x s0 sf

set_option maxHeartbeats 1200000 in
theorem pubKeySerdeSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_87).rebase (blkPl_87).base H) (blkPl_87).base
      (withLsCodeLoaded lsmpl (pubKeySerdeSerializeOkSpec M A lim)) := by
  simp only [pubKeySerdeSerializeOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.pubKeySerdeSerializeOkSpec,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hpubser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_87).rebase (blkPl_87).base H) (entry := lsmpl.base 205)
    (public_key_serialize_placed_ok_of_sessionShim hshim halloc)
  have hshim_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hdealloc_ok := dealloc_tail48_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_87).rebase (blkPl_87).base H) hdealloc)
  simp only [withLsCl, publicKeySerializeSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf] at hpubser
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy_ok
  simp only [rustDeallocTail48BudgetSpec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wp_init xst s0
  obtain ⟨⟨self, pk, outPtr⟩, st⟩ := xst
  dsimp only [withLsCodeLoaded] at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = self := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  subst hx0_eq hx8_eq
  have hfit_all : FitsEvents M lim st pubKeySerdeSerializeEvents :=
    ‹FitsEnv M lim st PubKeySerdeSerializeEnv› _ rfl
  rw [pubKeySerdeSerializeEvents, fitsEvents_append, fitsEvents_append] at hfit_all
  rcases hfit_all with ⟨⟨hfit_pk, hfit_alloc⟩, _⟩
  have hfe : FitsEvents M lim (M.stepEvents publicKeySerializeEvents st) [.alloc 33] := by
    simpa [rustAllocEvents] using hfit_alloc
  rcases hfe with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hfit_pk_env : FitsEnv M lim st PublicKeySerializeEnv := by
    rintro _ rfl; exact hfit_pk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk 33 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  rw [stackAt_publicKeySerialize_sub48_assoc s0.sp]
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk)
    ‹LibsignalCodeLoaded lsmpl s0.mem› (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_simp_pre [wp_norm]
  wp_call hpubser (⟨s0.readReg64 (Reg.gpr 0#5), pk⟩, st)
  refine SepWP.fold (boxU8Buf_pk_expose A.repAlloc _ pk) (by sep_focus) ?_
  dsimp only [RustCliAllocBudget.repAlloc]
  rw [← stackAt_publicKeySerialize_sub48 s0.sp]
  refine sepWP_pure_focus (φ := _ ≠ 0#64) (by sep_focus) fun _hbox_ne => ?_
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (33, 1, M.stepEvents publicKeySerializeEvents st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [show memRegion _ 33 = memRegion _ pk.serialize.length by rw [hser_len]]
  wp_call hmemcpy_ok (_, _, pk.serialize)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_simp_pre [wp_norm]
  rw [show A.live _ 33 1 = A.live _ pk.serialize.length 1 by rw [hser_len]]
  wp_call hdealloc_ok (_, pk.serialize, 1,
    s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5),
    M.stepEvents (rustAllocEvents 33 1) (M.stepEvents publicKeySerializeEvents st))
  simp only [hser_len, pubKeySerdeSerializeEvents, AllocCostModel.stepEvents_append]
  wp_done

def preKeyRecordNewEvents (cap : Nat) : List AllocEvent :=
  publicKeySerializeEvents ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
    privSerializeEvents ++ rustAllocEvents 32 1 ++ rustDeallocEvents cap 1

def PreKeyRecordNewEnv (evs : List AllocEvent) : Prop :=
  ∃ cap : Nat, 32 ≤ cap ∧ cap < 2 ^ 63 ∧ evs = preKeyRecordNewEvents cap

def preKeyRecordNewOkSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × PublicKey × List.Vector (BitVec 8) 32 × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st PreKeyRecordNewEnv⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.preKeyRecordNewOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PreKeyRecordNewEnv evs⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.preKeyRecordNewOkSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

private theorem sepWP_sync_stackAt {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {sp1 : BitVec 64} {sz : Nat}
    (hf : P = stackAt sp1 sz ∗ F) (hsp : sp1 = s.sp)
    (hnext : SepWP prog pc s (stackAt s.sp sz ∗ F) post) :
    SepWP prog pc s P post :=
  SepWP.fold (Entails.of_eq (congrArg (stackAt · sz) hsp)) hf hnext

private theorem sepWP_instantiate_post_exists_outer {α : Type} {prog : Program} {pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w) ∧ rest sf)) :
    SepWP prog pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ∃∗ x, Q sf x) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (Entails.sepExists_right w (Entails.refl _)) (h1 hm), h2⟩

set_option maxHeartbeats 1600000 in
theorem preKeyRecordNew_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_66).rebase (blkPl_66).base H) (blkPl_66).base
      (withLsCodeLoaded lsmpl (preKeyRecordNewOkSpec M A lim)) := by
  simp only [preKeyRecordNewOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.preKeyRecordNewOkSpec,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hpubser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_66).rebase (blkPl_66).base H) (entry := lsmpl.base 205)
    (public_key_serialize_placed_ok_of_sessionShim hshim halloc)
  have hprivser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_66).rebase (blkPl_66).base H) (entry := lsmpl.base 208)
    (privSerialize_placed_ok hshim halloc)
  have hshim_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hdealloc_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_of_mem hdealloc
  have hmemcpy_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  simp only [withLsCl, publicKeySerializeSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf] at hpubser
  simp only [withLsCl, privSerializeSpec,
    LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget.privSerializeSpecWithStack] at hprivser
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [rustCliDeallocBudgetSpec, AllocCallPreserved] at hdealloc_ok
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy_ok
  wp_init xst s0
  obtain ⟨⟨id, kpPtr, pk, priv, outPtr⟩, st⟩ := xst
  dsimp only [withLsCodeLoaded] at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = id := by assumption
  have hx1_eq : s0.readReg64 .x1 = kpPtr := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  subst hx0_eq hx1_eq hx8_eq
  have hfit32 : FitsEvents M lim st (preKeyRecordNewEvents 32) :=
    ‹FitsEnv M lim st PreKeyRecordNewEnv› (preKeyRecordNewEvents 32) ⟨32, by decide, by decide, rfl⟩
  rw [preKeyRecordNewEvents, fitsEvents_append, fitsEvents_append, fitsEvents_append,
    fitsEvents_append, fitsEvents_append] at hfit32
  rcases hfit32 with ⟨⟨⟨⟨⟨hfit_pk, hfit_a1⟩, _⟩, hfit_priv⟩, hfit_a2⟩, _⟩
  simp only [AllocCostModel.stepEvents_append] at hfit_a1 hfit_priv hfit_a2
  have hfit_pk_env : FitsEnv M lim st PublicKeySerializeEnv := by
    rintro _ rfl; exact hfit_pk
  let st1 := M.stepEvents publicKeySerializeEvents st
  have hfe1 : FitsEvents M lim st1 [.alloc 33] := by simpa [rustAllocEvents, st1] using hfit_a1
  rcases hfe1 with ⟨⟨hwma1, henf, hram1, hva1⟩, -⟩
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustDeallocEvents 33 1) st2
  have hfit_priv_env : FitsEnv M lim st3 PrivSerializeEnv := by
    rintro _ rfl; exact hfit_priv
  let st4 := M.stepEvents privSerializeEvents st3
  have hfe2 : FitsEvents M lim st4 [.alloc 32] := by simpa [rustAllocEvents, st4, st3, st2, st1] using hfit_a2
  rcases hfe2 with ⟨⟨hwma2, _, hram2, hva2⟩, -⟩
  let st5 := M.stepEvents (rustAllocEvents 32 1) st4
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay33 : RustLayoutOk 33 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hpriv_len : priv.toList.length = 32 := priv.toList_length
  refine SepWP.fold (stackAt_112_ext_to s0.sp publicKeySerializeStack) (by sep_focus) ?_
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk)
    ‹LibsignalCodeLoaded lsmpl s0.mem› (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call1 => ?_
  wp_simp_pre [wp_norm]
  wp_call hpubser (⟨s0.readReg64 (Reg.gpr 1#5), pk⟩, st)
  refine SepWP.fold (boxU8Buf_pk_expose A.repAlloc _ pk) (by sep_focus) ?_
  dsimp only [RustCliAllocBudget.repAlloc]
  refine sepWP_pure_focus (φ := _ ≠ 0#64) (by sep_focus) fun _hbox_ne => ?_
  let pkBoxPtr : BitVec 64 := (fun {p : BitVec 64} (_ : p ≠ 0#64) => p) _hbox_ne
  refine SepWP_fold_stack_112_to_ext s0.sp publicKeySerializeStack
    (by decide) (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine SepWP.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
  apply SepWP.seq_frozen (fun _ _ (hc : LibsignalCodeLoaded lsmpl _) hk => hc.of_keepsFrozen hk)
    (by assumption) (mid := lsmpl.base 208)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (33, 1, st1)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [show memRegion _ 33 = memRegion _ pk.serialize.length by rw [hser_len]]
  wp_call hmemcpy_ok (_, pkBoxPtr, pk.serialize)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  refine SepWP.fold (pk_buf_to_memRegion pkBoxPtr pk) (by sep_focus) ?_
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_simp_pre [wp_norm]
  refine sepWP_sync_stackAt (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  wp_call hdealloc_ok (pkBoxPtr, 33, 1, st2)
  wp_steps_sync_pool (lsmpl.base 208)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call2 => ?_
  refine SepWP_fold_stack_112_to_ext s0.sp allocHookStack
    (by decide) (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine SepWP.fold (stack_24_to_memRegion_104 s0.sp _ _ _) (by sep_focus) ?_
  wp_simp_pre [wp_norm]
  wp_call hprivser (s0.readReg64 (Reg.gpr 1#5) + 32#64, priv.toList, s0.sp - 104#64, st3)
  refine SepWP.fold (vecU8_priv_expose_104 A.repAlloc s0.sp priv) (by sep_focus) ?_
  dsimp only [RustCliAllocBudget.repAlloc]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  wp_pull_exists
  rename_i privTempCap privTempPtr
  refine sepWP_pure_focus
    (φ := 32 ≤ privTempCap.toNat ∧ privTempCap.toNat < 2 ^ 63 ∧
      (privTempCap == 0#64) = false ∧ privTempPtr ≠ 0)
    (by sep_focus) fun ⟨hpt_le, hpt_lt, hpt_c0, hpt_ptr⟩ => ?_
  have hlay_pt : RustLayoutOk privTempCap.toNat 1 := ⟨⟨by omega, hpow2, by omega⟩, by omega⟩
  apply sepWP_instantiate_post_exists_outer (preKeyRecordNewEvents privTempCap.toNat)
  have h_env : PreKeyRecordNewEnv (preKeyRecordNewEvents privTempCap.toNat) :=
    ⟨privTempCap.toNat, hpt_le, hpt_lt, rfl⟩
  refine SepWP.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (32, 1, st4)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [show memRegion _ 32 = memRegion _ priv.toList.length by rw [hpriv_len]]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  refine SepWP.fold (priv_buf_to_memRegion privTempPtr privTempCap priv hpt_le hpt_lt)
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  wp_simp_pre [wp_norm]
  refine sepWP_sync_stackAt (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  wp_call hdealloc_ok (privTempPtr, privTempCap.toNat, 1, st5)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  refine SepWP_fold_stack_112_to_ext s0.sp allocHookStack
    (by decide) (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  have hst_end : M.stepEvents (rustDeallocEvents privTempCap.toNat 1) st5 =
      M.stepEvents (preKeyRecordNewEvents privTempCap.toNat) st := by
    simp only [st1, st2, st3, st4, st5, preKeyRecordNewEvents, AllocCostModel.stepEvents_append]
  rw [hst_end]
  wp_done

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
