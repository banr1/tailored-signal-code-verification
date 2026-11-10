/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget

/-!
# Budget-Threaded Relocatable `SessionRecord::serialize` with One Previous Session

Relocatable `[LibsignalPlacement]` budget-threaded statements `SerializePrev1PlacedOkWithEnvStmt`
and `SerializePrev1PlacedOkStmt` for `<SessionRecord>::serialize` (Block `52`) on a record with
one archived previous session, together with envelope-monotonicity lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env serializePrev1SpecWithEnv serializePrev1Spec
)

/-- Envelope-parameterized `[LibsignalPlacement]` budget contract for `<SessionRecord>::serialize`
(Block `52`) on a record with one previous session. -/
def SerializePrev1PlacedOkWithEnvStmt [LibsignalPlacement] (prog : Program)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) :
    Prop :=
  subroutine_ok prog (lsmpl.base 52) (withLsCl lsmpl (serializePrev1SpecWithEnv M A lim Env))

def SerializePrev1PlacedOkStmt [LibsignalPlacement] (prog : Program)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  subroutine_ok prog (lsmpl.base 52) (withLsCl lsmpl (serializePrev1Spec M A lim))

theorem serializePrev1PlacedOkWithEnvStmt_mono [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ :
      SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (himp : ∀ G sess enc evs, Env₁ G sess enc evs → Env₂ G sess enc evs)
    (h : SerializePrev1PlacedOkWithEnvStmt prog M A lim Env₁) :
    SerializePrev1PlacedOkWithEnvStmt prog M A lim Env₂ := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [withLsCl, serializePrev1SpecWithEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.mono (himp x.G x.sess x.enc), hp.2⟩
  · dsimp only [withLsCl, serializePrev1SpecWithEnv] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq2 := hq.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq2 ⊢
    rcases hq2 with ⟨evs, hq2⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq2 ⊢
    exact ⟨himp x.G x.sess x.enc evs hq2.1, hq2.2⟩

theorem serializePrev1PlacedOkStmt_of_withEnv [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (himp : ∀ G sess enc evs, Env G sess enc evs → SerializePrev1Env G sess enc evs)
    (h : SerializePrev1PlacedOkWithEnvStmt prog M A lim Env) :
    SerializePrev1PlacedOkStmt prog M A lim := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [withLsCl, serializePrev1Spec, serializePrev1SpecWithEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.mono (himp x.G x.sess x.enc), hp.2⟩
  · dsimp only [withLsCl, serializePrev1Spec, serializePrev1SpecWithEnv] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq2 := hq.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq2 ⊢
    rcases hq2 with ⟨evs, hq2⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq2 ⊢
    exact ⟨himp x.G x.sess x.enc evs hq2.1, hq2.2⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
