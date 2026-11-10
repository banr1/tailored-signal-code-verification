/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Callees

/-!
# Budget-Threaded Cell and Inner Specifications for `SpkGetPoll`

`RustCliAllocBudget`-threaded cell-level callee specs (`decimalCellsSpec`, `dirGetCellsSpec`,
`decodeSpkCellsSpec`, `deallocBufCellsSpec`, `dropSpeWordCellsSpec`) and inner poll spec
`spkGetPollInnerSpec` with composed `AllocEvent` envelope `CliSpkGetPollEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv SeqEnv FreeOnlyEvs
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.RecordCodecs (SignedPreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule PkPollGhost PkNameOk PkSizeOk PkAns pkAnsOf spkAnsAt dirAt keyName)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (words6At words11At DecimalCellsGhost DirGetCellsGhost DecodeCellsGhost DeallocBufGhost
   DropSpeCellsGhost dirGetDetached decodeSpkDetached)

/-- Deterministic `AllocEvent` list emitted by conditional `Vec` buffer deallocation (`cap = 0` vs `cap ≠ 0`). -/
def optDeallocBufEvents (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

/-- Optional `decode_kyber_pre_key` (`decodeSignedPreKeySpec`) event envelope (`len > 0` only). -/
def OptSpkDecodeEnv (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (gr : Except Unit (List (BitVec 8))) : List AllocEvent → Prop :=
  match gr with
  | .ok (b :: bs) => DecodeEnv (b :: bs)
  | _ => (· = [])

/-- Composed `AllocEvent` envelope for `get_signed_pre_key::{closure#0}`. -/
def CliSpkGetPollEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (x : PkPollGhost) : List AllocEvent → Prop :=
  SeqEnv (DecEnv x.id)
    (SeqEnv (GetEnv x.dir x.id)
      (SeqEnv (OptSpkDecodeEnv DecodeEnv (x.dir.get rd F0 (keyName x.id))) FreeOnlyEvs))

def decimalCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DecimalCellsGhost × M.σ) where
  pre := fun ((id, ret, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = id ∧ s.sp = fsp ∧
      FitsEnv M lim st (DecEnv id)⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((id, ret, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.fs.files = s0.fs.files ∧ DecEnv id evs⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName id).length) ∗
      vecU8Buf A.repAlloc nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def dirGetCellsSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (F0 : FsFiles) (calleeStk : Nat) : Spec (DirGetCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName id).length ∧
      s.sp = fsp ∧ s.fs.files = F0 ∧ PkNameOk pathOk dir id ∧
      FitsEnv M lim st (GetEnv dir id)⌝ ∗
    dirAt A.repAlloc self dir ∗ vecU8Buf A.repAlloc nCap nPtr (keyName id) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗ stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, nCap, nPtr, id, _o0, _o1, _o2, _o3, _o4, _o5, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ gr : Except Unit (List (BitVec 8)),
    ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
    ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
      ⌜gr = dir.get rd F0 (keyName id) ∧ sf.trace = s0.trace ∧ GetEnv dir id evs⌝ ∗
      words6At ret g0 g1 g2 g3 g4 g5 ∗
      dirGetDetached A.repAlloc gr g0 g1 g2 g3 g4 g5 ∗
      dirAt A.repAlloc self dir ∗ vecU8Buf A.repAlloc nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def decodeSpkCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DecodeCellsGhost × M.σ) where
  pre := fun ((ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧
      s.sp = fsp ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (DecodeEnv bytes)⌝ ∗
    vecU8Buf A.repAlloc bCap bPtr bytes ∗
    words11At ret c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, bCap, bPtr, bytes,
      _c0, _c1, _c2, _c3, _c4, _c5, _c6, _c7, _c8, _c9, _c10, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
      ⌜sf.trace = s0.trace ∧ DecodeEnv bytes evs⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      decodeSpkDetached A.repAlloc
        (SignedPreKeyRecord.deserialize bytes) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      vecU8Buf A.repAlloc bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def deallocBufCellsSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec (DeallocBufGhost × M.σ) where
  pre := fun ((cap, ptr, bytes, fsp), st) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    vecU8Buf A.repAlloc cap ptr bytes ∗ stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((cap, _ptr, _bytes, fsp), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf

def dropSpeWordCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (calleeStk : Nat) : Spec (DropSpeCellsGhost × M.σ) where
  pre := fun ((a, d1, d2, d3, d4, d5, fsp), st) s =>
    ⌜s.readReg64 .x0 = a ∧ s.sp = fsp⌝ ∗
    words6At a (speWord 14) d1 d2 d3 d4 d5 ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((a, _d1, _d2, _d3, _d4, _d5, fsp), st) s0 sf =>
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
    ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      words6At a c0 c1 c2 c3 c4 c5 ∗
      stackAt fsp calleeStk ∗ A.pool lim st sf

def spkGetPollInnerSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PkPollGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s.fs.files x.dir x.id ∧
      FitsEnv M lim st (CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd s.fs.files x)⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗
      A.pool lim st s ∗ stackAt (s.sp - 384#64) calleeStk ∗ cells (s.sp - 384#64) 48
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ ans : PkAns SignedPreKeyRecord,
        ⌜ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace ∧
            CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs⌝ ∗
        spkAnsAt A.repAlloc x.out ans) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.dir ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ cells (s0.sp - 384#64) 48

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
