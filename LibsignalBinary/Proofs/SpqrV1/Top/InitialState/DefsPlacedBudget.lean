/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlaced

/-!
# Budget-Threaded Relocatable Specifications for `spqr::initial_state` (`Block 327`)

Defines the bounded allocation envelope `InitialStateEnv` and relocatable `[LibsignalPlacement]`
budget specifications (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) for `spqr::initial_state`
(`Block 327`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Top.InitInner (statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState
  (InitialStateGhost initialStatePlacedEntry initialStatePlacedProg initialStateResultAt
   initialStateStack initialStateValue paramsAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Default allocation envelope of `spqr::initial_state` (`Block 327`): `evs = []` on `.v0`, and
    linearly bounded in `x.p.authKey.length` on `.v1` (`SpqrBoundedEvs` absorbs trailing
    `FreeOnlyEvs` drops at zero allocation count). -/
def InitialStateEnv (_F : ShaCompress) (x : InitialStateGhost) (evs : List AllocEvent) : Prop :=
  match x.p.version with
  | .v0 => evs = []
  | .v1 => SpqrBoundedEvs 128 (4 * x.p.authKey.length + 4096) evs

/-- Envelope-parametric relocatable specification of `spqr::initial_state` (`Block 327`) with
    `.rodata` jump tables (`statesIntoPbJumpTablePlacedAt` and `optProtoInnerStateJumpTablePlacedAt`)
    carried explicitly. -/
def initialStatePlacedRoSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitialStateGhost → List AllocEvent → Prop) :
    Spec (InitialStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      statesIntoPbJumpTablePlacedAt ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st s ∗ stackAt s.sp initialStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      statesIntoPbJumpTablePlacedAt ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initialStateStack

abbrev initialStatePlacedRoSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitialStateGhost × M.σ) :=
  initialStatePlacedRoSpecOfEnv M A lim F (InitialStateEnv F)

/-- Envelope-parametric core relocatable specification of `spqr::initial_state` (`Block 327`)
    where `.rodata` jump tables are discharged from `LibsignalRoLoaded lsmpl s.mem`. -/
def initialStatePlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitialStateGhost → List AllocEvent → Prop) :
    Spec (InitialStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st s ∗ stackAt s.sp initialStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initialStateStack

abbrev initialStatePlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitialStateGhost × M.σ) :=
  initialStatePlacedSpecOfEnv M A lim F (InitialStateEnv F)

abbrev initialStatePlacedSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitialStateGhost → List AllocEvent → Prop) :
    Spec (InitialStateGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initialStatePlacedSpecOfEnv M A lim F Env)

abbrev initialStatePlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitialStateGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (initialStatePlacedSpec M A lim F)

/-- `spqr::initial_state` (`Block 327`) meets `withLsCodeLoaded lsmpl (initialStatePlacedRoSpec M A lim F)`
    on `initialStatePlacedProg ext`. -/
def InitialStatePlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
    (withLsCodeLoaded lsmpl (initialStatePlacedRoSpec M A lim F))

/-- `spqr::initial_state` (`Block 327`) meets `initialStatePlacedSpecX M A lim F`
    on `initialStatePlacedProg ext`. -/
def InitialStatePlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
    (initialStatePlacedSpecX M A lim F)

/-- `spqr::initial_state` (`Block 327`) meets `initialStatePlacedSpecX M A lim F` on
    `libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext)` at `lsmpl.base 327`. -/
def InitialStatePlacedOkBlockProgram [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext))
    (lsmpl.base 327)
    (initialStatePlacedSpecX M A lim F)

end LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
