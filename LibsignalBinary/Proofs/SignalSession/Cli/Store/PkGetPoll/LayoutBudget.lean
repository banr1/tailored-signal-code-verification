/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Layout

/-!
# Budget-Threaded Cell and Inner Specifications for `PkGetPoll`

`RustCliAllocBudget`-threaded cell-level callee specs (`deallocBufCellsSpec`, `decimalCellsSpec`,
`dirGetCellsSpec`, `pkDecCellsSpec`, `dropSpeWordCellsSpec`) and inner poll spec
`pkGetPollInnerSpec` with composed `AllocEvent` envelope `CliPkGetPollEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv SeqEnv FreeOnlyEvs
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule PkPollGhost PkNameOk PkSizeOk PkAns pkAnsOf pkGetAnsAt dirAt pathOf keyName)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (vecU8BufRest DeallocCellsGhost DecimalCellsGhost DirGetCellsGhost PkDecCellsGhost
   DropSpeCellsGhost dirGetPayload pkDecPayload)

/-- Optional `PreKeyRecord::deserialize` event envelope on a `Dir::get` result (`len > 0` only). -/
def OptPkDecodeEnv (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (gr : Except Unit (List (BitVec 8))) : List AllocEvent → Prop :=
  match gr with
  | .ok (b :: bs) => PkDecEnv (b :: bs)
  | _ => (· = [])

/-- Composed `AllocEvent` envelope for `get_pre_key::{closure#0}`. -/
def CliPkGetPollEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (x : PkPollGhost) : List AllocEvent → Prop :=
  SeqEnv (DecEnv x.id)
    (SeqEnv (GetEnv x.dir (keyName x.id))
      (SeqEnv (OptPkDecodeEnv PkDecEnv (x.dir.get rd F0 (keyName x.id))) FreeOnlyEvs))

def deallocBufCellsSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec (DeallocCellsGhost × M.σ) where
  pre := fun ((ptr, cap, bs, fsp), st) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (ptr ↦ₛ bs) ∗ vecU8BufRest A.repAlloc cap ptr bs ∗ A.pool lim st s ∗ stackAt fsp calleeStk
  post := fun ((_ptr, cap, _bs, fsp), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf ∗ stackAt fsp calleeStk

def decimalCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DecimalCellsGhost × M.σ) where
  pre := fun ((n, ret, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = n ∧ s.sp = fsp ∧
      FitsEnv M lim st (DecEnv n)⌝ ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((n, ret, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.fs.files = s0.fs.files ∧ DecEnv n evs⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName n).length) ∗
      (nPtr ↦ₛ keyName n) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName n) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def dirGetCellsSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name) ∧
      FitsEnv M lim st (GetEnv dir name)⌝ ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      ((ret + 24#64) ↦₆₄ o3) ∗ ((ret + 32#64) ↦₆₄ o4) ∗ ((ret + 40#64) ↦₆₄ o5) ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, nameA, name, _o0, _o1, _o2, _o3, _o4, _o5, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ r : Except Unit (List (BitVec 8)),
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace ∧ GetEnv dir name evs⌝ ∗
      (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ∗
      dirGetPayload A.repAlloc r w0 w1 w2 w3 w4 w5 ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗ stackAt fsp calleeStk ∗
      A.pool lim (M.stepEvents evs st) sf

def pkDecCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PkDecCellsGhost × M.σ) where
  pre := fun ((bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp), st) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = ret ∧ s.sp = fsp ∧
      FitsEnv M lim st (PkDecEnv bytes)⌝ ∗
      (bytesA ↦ₛ bytes) ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      ((ret + 24#64) ↦₆₄ o3) ∗ ((ret + 32#64) ↦₆₄ o4) ∗ ((ret + 40#64) ↦₆₄ o5) ∗
      ((ret + 48#64) ↦₆₄ o6) ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((bytesA, bytes, ret, _o0, _o1, _o2, _o3, _o4, _o5, _o6, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
    ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
      ⌜sf.trace = s0.trace ∧ PkDecEnv bytes evs⌝ ∗
      (ret ↦₆₄ d0) ∗ ((ret + 8#64) ↦₆₄ d1) ∗ ((ret + 16#64) ↦₆₄ d2) ∗
      ((ret + 24#64) ↦₆₄ d3) ∗ ((ret + 32#64) ↦₆₄ d4) ∗ ((ret + 40#64) ↦₆₄ d5) ∗
      ((ret + 48#64) ↦₆₄ d6) ∗
      pkDecPayload A.repAlloc (PreKeyRecord.deserialize bytes) d0 d1 d2 d3 d4 d5 d6 ∗
      (bytesA ↦ₛ bytes) ∗ stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def dropSpeWordCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (calleeStk : Nat) : Spec (DropSpeCellsGhost × M.σ) where
  pre := fun ((a, c1, c2, c3, c4, c5, fsp), st) s =>
    ⌜s.readReg64 .x0 = a ∧ s.sp = fsp⌝ ∗
      (a ↦₆₄ speWord 13) ∗
      ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗ ((a + 24#64) ↦₆₄ c3) ∗
      ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
      A.pool lim st s ∗ stackAt fsp calleeStk
  post := fun ((a, _c1, _c2, _c3, _c4, _c5, fsp), st) s0 sf =>
    ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64,
    ∃∗ m3 : BitVec 64, ∃∗ m4 : BitVec 64, ∃∗ m5 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      (a ↦₆₄ m0) ∗ ((a + 8#64) ↦₆₄ m1) ∗ ((a + 16#64) ↦₆₄ m2) ∗
      ((a + 24#64) ↦₆₄ m3) ∗ ((a + 32#64) ↦₆₄ m4) ∗ ((a + 40#64) ↦₆₄ m5) ∗
      A.pool lim st sf ∗ stackAt fsp calleeStk

def pkGetPollInnerSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PkPollGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s.fs.files x.dir x.id ∧
      FitsEnv M lim st (CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s.fs.files x)⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 56 ∗
      A.pool lim st s ∗ stackAt (s.sp - 256#64) calleeStk ∗ cells (s.sp - 256#64) 32
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ ans : PkAns PreKeyRecord,
        ⌜ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace ∧
            CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x evs⌝ ∗
        pkGetAnsAt A.repAlloc x.out ans) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
