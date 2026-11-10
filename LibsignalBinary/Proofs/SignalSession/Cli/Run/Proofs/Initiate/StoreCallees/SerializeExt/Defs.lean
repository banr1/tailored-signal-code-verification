/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs

/-!
# `extHookStack`-Scaled Stack Budgets and Specifications for `SessionRecord::serialize`

Stack-budget constants (`*StackX`) and `Spec` definitions (`dropSessionStructureLocal1SpecX`,
`encodeChainSpecX`, `encodeRawSpecX`, `sessionCloneSpecX`, `vecVecCloneEmptySpecX`,
`serializeSpecX`, `serializeCanonSpecX`) parameterized over arbitrary extern tables.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization

/-! ## `extHookStack`-Scaled Stack Budgets & `.inImage img` Contracts for `SessionRecord::serialize` -/

abbrev dropSessionStructureLocal1StackX : Nat :=
  32 + Getters.dropVecChainStackX

abbrev encodeChainStackX : Nat :=
  0x60 + Prost.encodeVarintStackX + doReserveStackX + chainLenStack

abbrev encodeRawStackX : Nat :=
  0x50 + Prost.encodeVarintStackX + doReserveStackX + encodeChainStackX

abbrev chainCloneStackX : Nat :=
  0xd0 + extHookStack

abbrev sessionCloneStackX : Nat :=
  0x1d0 + 0xd0 + 0x400 + extHookStack

abbrev vecVecCloneStackX : Nat :=
  0x60 + extHookStack

/-- Full `SessionRecord::serialize` stack budget under `AllocContractsX` (`167,840` bytes). -/
abbrev serializeStackX : Nat :=
  0x360 + sessionCloneStackX + vecVecCloneStackX + sessionLenStack + extHookStack +
    Prost.encodeVarintStackX + encodeRawStackX + doReserveStackX +
    dropSessionStructureLocal1StackX

def dropSessionStructureLocal1SpecX (A : RustAlloc) :
    Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp dropSessionStructureLocal1StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal1StackX

def encodeChainSpecX (A : RustAlloc) : Spec EncodeChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧ x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ protoChainAt A x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool ∗ stackAt s0.sp encodeChainStackX
  onPanic := allocPanic

def encodeRawSpecX (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp encodeRawStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool ∗ stackAt s0.sp encodeRawStackX
  onPanic := allocPanic

def sessionCloneSpecX (A : RustAlloc) : Spec SessionCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      sessionStateReprAt A x.src x.G x.s ∗ memRegion x.dst 344 ∗ A.pool ∗ stackAt s.sp sessionCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s) ∗
      A.pool ∗ stackAt s0.sp sessionCloneStackX
  onPanic := allocPanic

def vecVecCloneEmptySpecX : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp vecVecCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp vecVecCloneStackX

/-- `SessionRecord::serialize`, memory-level, at `serializeStackX`. -/
def serializeSpecX (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ (encRecordMem x.g x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := allocPanic

/-- `SessionRecord::serialize` on a canonical record, at `serializeStackX`. -/
def serializeCanonSpecX (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := allocPanic

/-- Pure subroutine contract at image base `b` under arbitrary extern table `ext`. -/
abbrev OkAtExt {α : Type} (b : BitVec 64) (ext : String → Option (State → State))
    (fn : String) (spec : Spec α) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr fn) spec

/-- Image-invariant subroutine contract at `img` under arbitrary extern table `ext`. -/
abbrev OkAtX {α : Type} (img : Obj.Image) (ext : String → Option (State → State))
    (fn : String) (spec : Spec α) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr fn) (spec.inImage img)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
