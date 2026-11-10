/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed

/-!
# `spqr::initial_state` (`Block 327`): Relocatable `[LibsignalPlacement]` Definitions and Specifications

Defines the relocatable `[LibsignalPlacement]` specifications `initialStatePlacedSpec`,
`initialStatePlacedRoSpec`, `initialStatePlacedSpecX`, `InitialStatePlacedOkExt`, and
`InitialStatePlacedOkX` on `Block 327`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Rebased Program, Entry Address, and `.rodata` Jump Table Helper -/

/-- Rebased program for Block `327` (`spqr::initial_state`). -/
noncomputable abbrev initialStatePlacedProg [LibsignalPlacement]
    (ext : String → Option (State → State)) : Program :=
  (blkPC_327).rebase (blkPl_327).base (Rust.withPanics ext)

/-- Placed entry address of Block `327` (`spqr::initial_state`). -/
abbrev initialStatePlacedEntry [LibsignalPlacement] : BitVec 64 :=
  (blkPl_327).base

/-- Discharge `optProtoInnerStateJumpTablePlacedAt` from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_optProtoInnerStateJumpTablePlacedAt [LibsignalPlacement] {s : State}
    (hro : LibsignalRoLoaded lsmpl s.mem) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ optProtoInnerStateJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

/-! ## 2. Relocatable `[LibsignalPlacement]` Specifications for `spqr::initial_state` (`Block 327`) -/

/-- Relocatable specification of `spqr::initial_state` (`Block 327`) with `.rodata` jump tables
    (`statesIntoPbJumpTablePlacedAt` and `optProtoInnerStateJumpTablePlacedAt`) carried explicitly. -/
def initialStatePlacedRoSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      statesIntoPbJumpTablePlacedAt ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp initialStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      statesIntoPbJumpTablePlacedAt ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp initialStateStack
  onPanic := fun _ s0 sf => initialStateOnPanic s0 sf

/-- Core relocatable specification of `spqr::initial_state` (`Block 327`) where `.rodata`
    jump tables are discharged from `LibsignalRoLoaded lsmpl s.mem`. -/
def initialStatePlacedSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp initialStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp initialStateStack
  onPanic := fun _ s0 sf => initialStateOnPanic s0 sf

abbrev initialStatePlacedSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec InitialStateGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (initialStatePlacedSpec A F)

/-- `spqr::initial_state` (`Block 327`) meets `withLsCodeLoaded lsmpl (initialStatePlacedRoSpec A F)`
    on `initialStatePlacedProg ext`. -/
def InitialStatePlacedOkExt [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
    (withLsCodeLoaded lsmpl (initialStatePlacedRoSpec A F))

/-- `spqr::initial_state` (`Block 327`) meets `initialStatePlacedSpecX A F`
    on `initialStatePlacedProg ext`. -/
def InitialStatePlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
    (initialStatePlacedSpecX A F)

/-- `spqr::initial_state` (`Block 327`) meets `initialStatePlacedSpecX A F` on
    `libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext)` at `lsmpl.base 327`. -/
def InitialStatePlacedOkBlockProgram [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext))
    (lsmpl.base 327)
    (initialStatePlacedSpecX A F)

end CryptoVerification.SpqrV1.Top.InitialState
