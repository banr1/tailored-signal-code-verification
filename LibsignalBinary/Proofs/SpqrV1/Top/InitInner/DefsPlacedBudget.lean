/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlaced

/-!
# Budget-Threaded Relocatable Specifications for `spqr::init_inner` (`Block 324`)

Defines bounded allocation envelopes (`SpqrBoundedEvs`, `StatesIntoPbEnv`, `InitInnerEnv`) and
relocatable `[LibsignalPlacement]` budget specifications for `<States>::into_pb` (`Block 334`)
and `spqr::init_inner` (`Block 324`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.IntoPb
  (StatesIntoPbGhost statesIntoPbStack statesIntoPbStackX)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initInnerResultAt initInnerStack initInnerStackX statesIntoPbJumpTablePlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Allocation-Count / Request-Size Bounded Event Envelopes (`SpqrBoundedEvs`) -/

/-- Number of non-`free` (`alloc`, `aligned`, `realloc`) events in an `AllocEvent` list. -/
def nonFreeCount : List AllocEvent → Nat
  | [] => 0
  | .free _ _ :: evs => nonFreeCount evs
  | _ :: evs => nonFreeCount evs + 1

theorem nonFreeCount_nil : nonFreeCount [] = 0 := rfl

theorem nonFreeCount_append : ∀ evs₁ evs₂ : List AllocEvent,
    nonFreeCount (evs₁ ++ evs₂) = nonFreeCount evs₁ + nonFreeCount evs₂
  | [], _ => by simp [nonFreeCount]
  | .free _ _ :: evs₁, evs₂ => by simp [nonFreeCount, nonFreeCount_append evs₁ evs₂]
  | .alloc _ :: evs₁, evs₂ => by simp [nonFreeCount, nonFreeCount_append evs₁ evs₂]; omega
  | .aligned _ _ :: evs₁, evs₂ => by simp [nonFreeCount, nonFreeCount_append evs₁ evs₂]; omega
  | .realloc _ _ _ :: evs₁, evs₂ => by simp [nonFreeCount, nonFreeCount_append evs₁ evs₂]; omega

theorem nonFreeCount_eq_zero_of_freeOnly {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    nonFreeCount evs = 0 := by
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    have ⟨al, sz, hev⟩ := h ev List.mem_cons_self
    subst hev
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- Bounded `AllocEvent` envelope with at most `maxAllocs` non-`free` events, per-event request
    size `≤ maxReq`, and alignment `≤ 16` (preserving `0` cost for arbitrary `FreeOnlyEvs` drops
    and avoiding `MaxAlignedAllocAlign` overcharge under Tier T2 `FineCostModel`). -/
def SpqrBoundedEvs (maxAllocs maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxAllocs ∧
  ∀ ev ∈ evs,
    ev.withinMaxAlloc ∧
    ev.reqBytes ≤ maxReq ∧
    (∀ al r, ev = .aligned al r → al ≤ 16) ∧
    (∀ al o n, ev = .realloc al o n → al ≤ 16)

theorem SpqrBoundedEvs.nil (maxAllocs maxReq : Nat) :
    SpqrBoundedEvs maxAllocs maxReq [] :=
  ⟨Nat.zero_le _, fun _ h => nomatch h⟩

theorem SpqrBoundedEvs.of_freeOnly {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    SpqrBoundedEvs 0 0 evs := by
  refine ⟨Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly h), fun ev hev => ?_⟩
  obtain ⟨al, sz, rfl⟩ := h ev hev
  exact ⟨trivial, Nat.le_refl 0, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem SpqrBoundedEvs.append {c₁ c₂ r₁ r₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : SpqrBoundedEvs c₁ r₁ evs₁) (h2 : SpqrBoundedEvs c₂ r₂ evs₂) :
    SpqrBoundedEvs (c₁ + c₂) (max r₁ r₂) (evs₁ ++ evs₂) := by
  refine ⟨by rw [nonFreeCount_append]; exact Nat.add_le_add h1.1 h2.1, ?_⟩
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · obtain ⟨hw, hr, ha, hre⟩ := h1.2 ev hm1
    exact ⟨hw, Nat.le_trans hr (Nat.le_max_left _ _), ha, hre⟩
  · obtain ⟨hw, hr, ha, hre⟩ := h2.2 ev hm2
    exact ⟨hw, Nat.le_trans hr (Nat.le_max_right _ _), ha, hre⟩

theorem SpqrBoundedEvs.mono {c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (hc : c₁ ≤ c₂) (hr : r₁ ≤ r₂) (h : SpqrBoundedEvs c₁ r₁ evs) :
    SpqrBoundedEvs c₂ r₂ evs :=
  ⟨Nat.le_trans h.1 hc, fun ev hev =>
    let ⟨hw, hreq, ha, hre⟩ := h.2 ev hev
    ⟨hw, Nat.le_trans hreq hr, ha, hre⟩⟩

/-- Default allocation envelope of `<spqr::v1::chunked::states::States>::into_pb` (`Block 334`),
    bounded linearly in the serialized `V1State` length. -/
def StatesIntoPbEnv {F : ShaCompress} (x : StatesIntoPbGhost F) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 64 (2 * (V1State.encodeRaw x.st.into_pb).length + 1024) evs

/-- Default allocation envelope of `spqr::init_inner` (`Block 324`): `evs = []` on `.v0`, and
    linearly bounded in `x.authKey.length` on `.v1`. -/
def InitInnerEnv (_F : ShaCompress) (x : InitInnerGhost) (evs : List AllocEvent) : Prop :=
  match x.v with
  | .v0 => evs = []
  | .v1 => SpqrBoundedEvs 96 (2 * x.authKey.length + 2048) evs

/-! ## 2. Relocatable Budget Callee Specifications for `<States>::into_pb` (`Block 334`) -/

/-- Envelope-parametric relocatable specification of `<States>::into_pb` (`Block 334`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def statesIntoPbPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

abbrev statesIntoPbPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedSpecOfEnv M A lim F StatesIntoPbEnv

/-- Envelope-parametric per-variant relocatable specification of `<States>::into_pb` (`Block 334`). -/
def statesIntoPbVariantPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, stA⟩, st) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = stA ∧
      FitsEnv M lim st Env⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA stateVal ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStack
  post := fun (⟨out, stA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

abbrev statesIntoPbVariantPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal
    (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024))

/-- Envelope-parametric extended-stack relocatable specification of `<States>::into_pb` (`Block 334`). -/
def statesIntoPbPlacedSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc x.stA x.st ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStackX

abbrev statesIntoPbPlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedSpecXOfEnv M A lim F StatesIntoPbEnv

/-- `<States>::into_pb` (`Block 334`) meets `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F)`
    on `libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext)` at `lsmpl.base 334`. -/
def StatesIntoPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
    (lsmpl.base 334)
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F))

/-! ## 3. Relocatable Budget Specifications for `spqr::init_inner` (`Block 324`) -/

/-- Envelope-parametric relocatable Hoare specification of `spqr::init_inner` (`Block 324`)
    carrying `statesIntoPbJumpTablePlacedAt` explicitly. -/
def initInnerPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStack

abbrev initInnerPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerPlacedSpecOfEnv M A lim F (InitInnerEnv F)

/-- Envelope-parametric extended-stack relocatable specification of `spqr::init_inner` (`Block 324`). -/
def initInnerPlacedSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStackX

abbrev initInnerPlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerPlacedSpecXOfEnv M A lim F (InitInnerEnv F)

/-- Envelope-parametric extended-stack relocatable specification of `spqr::init_inner` (`Block 324`)
    where `.rodata` is discharged from `LibsignalRoLoaded lsmpl s.mem`. -/
def initInnerPlacedRoSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStackX

abbrev initInnerPlacedRoSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerPlacedRoSpecXOfEnv M A lim F (InitInnerEnv F)

/-- `spqr::init_inner` (`Block 324`) meets `withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)`
    on `libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext)` at `lsmpl.base 324`. -/
def InitInnerPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
    (lsmpl.base 324)
    (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F))

/-- `initInnerPlacedSpecOfEnv M A lim F Env` entails `initInnerPlacedSpecXOfEnv M A lim F Env`. -/
theorem initInnerPlacedSpecXOfEnv_of_initInnerPlacedSpecOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    (h : subroutine_ok P addr (initInnerPlacedSpecOfEnv M A lim F Env)) :
    subroutine_ok P addr (initInnerPlacedSpecXOfEnv M A lim F Env) :=
  h

/-- `initInnerPlacedSpec M A lim F` entails `initInnerPlacedSpecX M A lim F`. -/
theorem initInnerPlacedSpecX_of_initInnerPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (initInnerPlacedSpec M A lim F)) :
    subroutine_ok P addr (initInnerPlacedSpecX M A lim F) :=
  h

/-- `withLsCodeLoaded lsmpl (initInnerPlacedSpec M A lim F)` entails
    `withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)`. -/
theorem withLsCodeLoaded_initInnerPlacedSpecX_of_initInnerPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpec M A lim F))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)) :=
  h

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
