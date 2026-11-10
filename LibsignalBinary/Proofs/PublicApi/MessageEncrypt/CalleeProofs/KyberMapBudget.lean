/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMap
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# Budget-Threaded `kyberMap`

Proves `subroutine_ok (lsProg_127 H) (blkPl_127).base (CalleesBudget.kyberMapSpec M A lim)` under
`[LibsignalPlacement]` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMapBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   AllocCallPreserved PoolPreserved VmPreserved FitsEnv FitsEvents rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
   ls_hook_ok_of_mem lsρ)
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (boxU8At)
open CryptoVerification.LibsignalTripleRatchet
  (sessionShimSpec sessionMemcpyRegionSpec SepWP.instantiate_post_exists)
open CryptoVerification.LibsignalPublicApiRepr (optKyberAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_127 blkPC_127 blkPl_127 blkLib_eq_127)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (KyberMapCall kyberArgAt)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (KyberOptEnv kyberMapSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_kyberMap (sp : BitVec 64) :
    stackAt sp (allocHookStack + 0x40) =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)

private theorem memRegion_24_none (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u0 : BitVec 64, (p ↦₆₄ u0) ∗ memRegion (p + 8#64) 16) := by
  rw [memRegion_split p 8 16 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left]

private theorem memRegion_24_some (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₃₂ u2) ∗ memRegion (p + 20#64) 4) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 4 4 (by decide),
    memRegion_four, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem optKyberAt_none_exists (A : RustAlloc) (out : BitVec 64) :
    (∃∗ bp : BitVec 64, optKyberAt A out bp none) =
      (out ↦₆₄ 0#64) ∗ memRegion (out + 8#64) 16 := by
  apply ProofLib.sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => by simp only [optKyberAt]; exact Entails.refl _
  · exact Entails.sepExists_right 0#64 (by simp only [optKyberAt]; exact Entails.refl _)

private theorem fitsEvents_of_kyberOptEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)}
    (hfit : FitsEnv M lim st (KyberOptEnv (some bs)))
    (hpos : 0 < bs.length) :
    FitsEvents M lim st (rustAllocEvents bs.length 1) :=
  hfit (rustAllocEvents bs.length 1) (Or.inr ⟨hpos, rfl⟩)

private theorem sepWP_pure_focus {prog : Program} {tgt : BitVec 64} {s : State}
    {P B : SepProp} {φ : Prop} {Q : State → SepProp → Prop}
    (hf : P = ⌜φ⌝ ∗ B) (h : φ → SepWP prog tgt s B Q) :
    SepWP prog tgt s P Q :=
  hf ▸ SepWP.pure_elim h

set_option maxHeartbeats 1200000 in
theorem kyberMap_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_127 H) (blkPl_127).base (kyberMapSpec M A lim) := by
  simp only [kyberMapSpec, CryptoVerification.LibsignalPublicApi.MessageEncrypt.kyberMapSpec,
    stackAt_kyberMap]
  cells_unfold
  have h_shim : subroutine_ok (lsProg_127 H) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have h_alloc : subroutine_ok (lsProg_127 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have h_memcpy : subroutine_ok (lsProg_127 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at h_shim
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at h_alloc
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at h_memcpy
  wp_init xst s0
  obtain ⟨⟨out, arg, ptr, kp⟩, st⟩ := xst
  dsimp only at *
  cases kp with
  | none =>
    apply SepWP.instantiate_post_exists ([] : List AllocEvent)
    dsimp only [Option.map, AllocCostModel.stepEvents]
    have hky_ev : KyberOptEnv none [] := rfl
    simp only [kyberArgAt, optKyberAt_none_exists, memRegion_24_none,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      RustCliAllocBudget.atState_pool]
    wp_pull_exists
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done
  | some k =>
    by_cases hbs : k.ciphertext = []
    · apply SepWP.instantiate_post_exists ([] : List AllocEvent)
      dsimp only [Option.map, AllocCostModel.stepEvents]
      have hky_ev : KyberOptEnv (some []) [] := Or.inl ⟨rfl, rfl⟩
      simp only [kyberArgAt, optKyberAt, boxU8At, memRegion_24_some,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        hbs, List.length_nil, ite_true, sepConj_emp, emp_sepConj,
        RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      wp_pull_exists
      refine sepWP_pure_focus (φ := ptr ≠ 0#64 ∧ 0 < 2 ^ 32)
        (by sep_focus) fun ⟨hptr_ne, _⟩ => ?_
      have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      wp_done
    · apply SepWP.instantiate_post_exists (rustAllocEvents k.ciphertext.length 1)
      dsimp only [Option.map]
      have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hky_ev : KyberOptEnv (some k.ciphertext) (rustAllocEvents k.ciphertext.length 1) :=
        Or.inr ⟨hpos, rfl⟩
      have hfit_ev : FitsEvents M lim st (rustAllocEvents k.ciphertext.length 1) :=
        fitsEvents_of_kyberOptEnv (by assumption) hpos
      simp only [kyberArgAt, optKyberAt, boxU8At, memRegion_24_some,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        hbs, ite_false, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      wp_pull_exists
      refine sepWP_pure_focus (φ := ptr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 32)
        (by sep_focus) fun ⟨hptr_ne, hlen_lt32⟩ => ?_
      have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
      have hlen_lt63 : k.ciphertext.length < 2 ^ 63 := by omega
      have hlen_ne0 : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hpow2 : ∃ m, 1 = 2 ^ m := ⟨0, rfl⟩
      have hbound : k.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : RustLayoutOk k.ciphertext.length 1 := ⟨⟨hpos, hpow2, hbound⟩, by decide⟩
      wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
      wp_simp_pre [wp_norm]
      wp_apply
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      wp_steps_sync_pool (lsρ lsRustAllocSym)
      wp_simp_pre [wp_norm]
      wp_apply with (k.ciphertext.length, 1, st)
      wp_steps_sync_pool (lsρ lsMemcpySym)
      wp_simp_pre [wp_norm]
      wp_apply
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      wp_done

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMapBudget
