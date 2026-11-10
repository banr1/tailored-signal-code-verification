/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# File-Descriptor-Preserving Placed Stage P2 Over-Path Callee Contracts

Defines `FdsGe3Closed`-preserving `[LibsignalPlacement]` contracts for `SessionRecord::promote_state`
(block 47) and bridges them to `AllocWithFds.withFds A` when `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPending clearPendingGhost)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteOverEnv p2PromoteOverAtSpecWithEnv p2PromoteOverGenSpecWithEnv
  PromoteOverAtPlacedWithEnvProp PromoteOverGenPlacedWithEnvProp
  promoteOverAt_placed_of_gen_withEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  withFds_pool_eq_of_fdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_pool_enforced withFds_repAlloc
)

/-- `FdsGe3Closed`-preserving `[LibsignalPlacement]` envelope-parameterized contract for
`SessionRecord::promote_state` at block 47 (`lsmpl.base 47`). -/
def PromoteOverAtPlacedWithEnvPropFd [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl
      (withFdsGe3Closed (p2PromoteOverAtSpecWithEnv M A lim Env coroPtr g recG sess)))

abbrev PromoteOverAtPlacedPropFd [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  PromoteOverAtPlacedWithEnvPropFd M A lim PromoteOverEnv ext coroPtr g recG sess

def PromoteOverGenPlacedWithEnvPropFd [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl (withFdsGe3Closed (p2PromoteOverGenSpecWithEnv M A lim Env)))

abbrev PromoteOverGenPlacedPropFd [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PromoteOverGenPlacedWithEnvPropFd M A lim PromoteOverEnv ext

theorem PromoteOverAtPlacedWithEnvPropFd.toWithFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))}
    (h : PromoteOverAtPlacedWithEnvPropFd M A lim Env ext coroPtr g recG sess) :
    PromoteOverAtPlacedWithEnvProp M (withFds A) lim Env ext coroPtr g recG sess := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ _ s hpre => ?_) (fun ⟨x, st⟩ _ s0 sf hpost => ?_)
  · dsimp only [withLsCl, withFdsGe3Closed, p2PromoteOverAtSpecWithEnv, withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    exact Satisfies.of_eq hpre (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withLsCl, withFdsGe3Closed]
    refine sepConj_mono_right (Entails.pure_left fun hfdsf => ?_)
    dsimp only [p2PromoteOverAtSpecWithEnv, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfdsf]
    exact Entails.refl _

theorem PromoteOverGenPlacedWithEnvPropFd.toWithFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : PromoteOverGenPlacedWithEnvPropFd M A lim Env ext) :
    PromoteOverGenPlacedWithEnvProp M (withFds A) lim Env ext := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ _ s hpre => ?_) (fun ⟨x, st⟩ _ s0 sf hpost => ?_)
  · dsimp only [withLsCl, withFdsGe3Closed, p2PromoteOverGenSpecWithEnv, withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    exact Satisfies.of_eq hpre (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withLsCl, withFdsGe3Closed]
    refine sepConj_mono_right (Entails.pure_left fun hfdsf => ?_)
    dsimp only [p2PromoteOverGenSpecWithEnv, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfdsf]
    exact Entails.refl _

theorem PromoteOverGenPlacedWithEnvPropFd.toAtWithFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedWithEnvPropFd M A lim Env ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedWithEnvProp M (withFds A) lim Env ext coroPtr g recG sess :=
  promoteOverAt_placed_of_gen_withEnv (hGen.toWithFds henf) coroPtr g recG sess hlen

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudgetFd
