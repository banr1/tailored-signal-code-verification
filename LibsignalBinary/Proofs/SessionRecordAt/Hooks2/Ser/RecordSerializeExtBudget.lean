/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExt
public import LibsignalBinary.Proofs.E2E.Bin.RecordBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded Bridge from `serializeSpecX` to `recordSerializeSpecX` (Block `52`)

Bridges the budget-threaded `SessionRecord::serialize` body contract (`serializeSpecX M A lim`) to
`serializeCanonSpecX M A lim`, parametric-envelope `recordSerializeEnvSpecX`, and canonical-envelope
`recordSerializeSpecX M A lim` (`Env := SerializeEnvX`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open CryptoVerification.E2E.Record.Serialization (encRecordMem_eq_of_canon SerializeGhost)
open CryptoVerification.E2E.Bin (RecordSerializeGhost recordSerializeStack)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX serializeStackX_le_recordSerializeStack
  SerializeEnvX serializeSpecX serializeCanonSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SerializePlacedOkX SerializeCanonPlacedOkX
)

abbrev canonRecord_to_serializationCanonX :=
  @Proofs.libsignal.Hooks2.canonRecord_to_serializationCanonX

private theorem stackAt_sub_split (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

private theorem stackAt_recordSerialize_split (sp : BitVec 64) :
    stackAt sp recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - serializeStackX) ∗
      stackAt sp serializeStackX :=
  stackAt_sub_split sp serializeStackX recordSerializeStack
    serializeStackX_le_recordSerializeStack (by decide)

private theorem memRegion_48_split_32_16 (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

private theorem sessionRecordAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (self : BitVec 64) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    sessionRecordAt (A.atState lim st s) self g r = sessionRecordAt A.repAlloc self g r := by
  rcases g with ⟨_, _, _ | G⟩ <;> rcases r with ⟨_ | sess⟩ <;> rfl

private theorem vecU8_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (addr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 (A.atState lim st s) addr bs = vecU8 A.repAlloc addr bs :=
  rfl

/-! ## `serializeSpecX` to `serializeCanonSpecX` bridges -/

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSpecX M A lim` to
`serializeCanonSpecX M A lim`. -/
theorem serializeCanonX_of_serialize_placedX {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpecX M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (serializeCanonSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' h fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [serializeCanonSpecX] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨h0, h8, hcanon, hlen, hfit⟩, hrest⟩
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  refine ⟨(x, st), R, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializeSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen, hfit⟩, hrest⟩
  · intro sf hq
    have hpost_eq :
        (serializeSpecX M A lim).post (x, st) s0 sf =
          (serializeCanonSpecX M A lim).post (x, st) s0 sf := by
      dsimp only [serializeSpecX, serializeCanonSpecX]
      rw [henc]
    rwa [hpost_eq] at hq

theorem serializeCanonX_placed_ok_of_serializeX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : SerializePlacedOkX M A lim H) :
    SerializeCanonPlacedOkX M A lim H :=
  serializeCanonX_of_serialize_placedX h

theorem serializeCanonX_placed_cl_of_serializeX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSpecX M A lim))) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeCanonSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serializeCanonX_of_serialize_placedX h)

/-! ## Parametric-envelope and canonical-envelope `recordSerialize` contracts -/

/-- Parametric-envelope budget-threaded `SessionRecord::serialize` contract (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`). -/
def recordSerializeEnvSpecX
    (Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordSerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (Env x.g x.r)⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x.g x.r evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Canonical-envelope (`SerializeEnvX`) budget-threaded `SessionRecord::serialize` contract. -/
abbrev recordSerializeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordSerializeGhost × M.σ) :=
  recordSerializeEnvSpecX SerializeEnvX M A lim

theorem recordSerializeSpecX_eq_recordBudget (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    recordSerializeSpecX M A lim =
      LibsignalBinary.Proofs.E2E.Bin.RecordBudget.recordSerializeSpec M A lim :=
  rfl

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSpecX M A lim` to
`recordSerializeEnvSpecX Env M A lim` for any envelope `Env` containing `SerializeEnvX`. -/
theorem recordSerializeEnv_placed_ok_ext_of_serializeX {pl : Obj.MultiPlacement}
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpecX M A lim)))
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok prog entry (withLsCodeLoaded pl (recordSerializeEnvSpecX Env M A lim)) := by
  have hser := serializeCanonX_of_serialize_placedX h
  refine subroutine_ok_withLsCodeLoaded_map_oom' hser fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [recordSerializeEnvSpecX, CryptoVerification.E2E.Bin.recordSerializeSpec] at hpre
  rw [RustCliAllocBudget.atState_pool, sessionRecordAt_atState,
      memRegion_48_split_32_16 x.out, stackAt_recordSerialize_split s0.sp] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hFitEnv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have hFitX : FitsEnv M lim st (SerializeEnvX x.g x.r) :=
    fun evs hevs => hFitEnv evs (hsub x.g x.r evs hevs)
  let x_ser : SerializeGhost := ⟨x.self, x.out, x.g, x.r⟩
  let R_ser : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
      memRegion (s0.sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - serializeStackX) ∗ R
  refine ⟨(x_ser, st), R_ser, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializeCanonSpecX, x_ser, R_ser]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, canonRecord_to_serializationCanonX hcanon, hlen, hFitX⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  · intro sf hq
    dsimp only [serializeCanonSpecX, x_ser, R_ser] at hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq_mem⟩
    dsimp only [recordSerializeEnvSpecX, CryptoVerification.E2E.Bin.recordSerializeSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [RustCliAllocBudget.atState_pool, sessionRecordAt_atState, vecU8_atState,
        stackAt_recordSerialize_split s0.sp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hsub x.g x.r evs hevs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq_mem

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSpecX M A lim` to
`recordSerializeSpecX M A lim` (`Env := SerializeEnvX`). -/
theorem recordSerialize_placed_ok_ext_of_serializeX {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSpecX M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (recordSerializeSpecX M A lim)) :=
  recordSerializeEnv_placed_ok_ext_of_serializeX h (fun _ _ _ hev => hev)

theorem recordSerializeEnv_placed_cl_of_serializeX [LibsignalPlacement]
    {Env : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSpecX M A lim)))
    (hsub : ∀ g r evs, SerializeEnvX g r evs → Env g r evs) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeEnvSpecX Env M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (recordSerializeEnv_placed_ok_ext_of_serializeX h hsub)

theorem recordSerialize_placed_cl_of_serializeX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSpecX M A lim))) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (recordSerializeSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (recordSerialize_placed_ok_ext_of_serializeX h)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
