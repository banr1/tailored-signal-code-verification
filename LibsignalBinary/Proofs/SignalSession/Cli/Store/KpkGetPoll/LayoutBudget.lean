/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.Layout

/-!
# Budget-Threaded Cell & Inner Specifications for `KpkGetPoll`

Defines the composite allocation envelopes (`OptKpkDecodeEnv`, `KpkPassEnv`, `CliKpkGetPollEnv`)
and budget-threaded cell and inner `Spec` definitions (`deallocVecBufCellsSpec`,
`decimalFsCellsSpec`, `dirGetFsCellsSpec`, `decodeFsCellsSpec`, `cliKpkGetPollInnerSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv SeqEnv FreeOnlyEvs
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles FsInv)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule KpkPollGhost PkNameOk PkSizeOk PkAns pkAnsOf kpkAnsOf kpkAnsAt dirAt keyName)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (words6At words11At DeallocBufGhost DecimalCellsGhost DirGetCellsGhost DecodeCellsGhost
   dirGetPostProp decodePostProp)

/-- Optional `decode_kyber_pre_key` event envelope on a `Dir::get` result (`len > 0` only). -/
def OptKpkDecodeEnv (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (gr : Except Unit (List (BitVec 8))) : List AllocEvent → Prop :=
  match gr with
  | .ok (b :: bs) => DecodeEnv (b :: bs)
  | _ => (· = [])

/-- Single-directory (`oneTime` or `lastResort`) `AllocEvent` envelope for `KpkGetPoll`. -/
def KpkPassEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (id : BitVec 32) :
    List AllocEvent → Prop :=
  SeqEnv (DecEnv id)
    (SeqEnv (GetEnv dir id)
      (SeqEnv (OptKpkDecodeEnv DecodeEnv (dir.get rd F0 (keyName id))) FreeOnlyEvs))

/-- Composed `AllocEvent` envelope for `get_kyber_pre_key::{closure#0}` (`oneTime`, plus
`lastResort` when `oneTime` is `.missing`). -/
def CliKpkGetPollEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (x : KpkPollGhost) : List AllocEvent → Prop :=
  match pkAnsOf KyberPreKeyRecord.deserialize (x.kg.oneTime.get rd F0 (keyName x.id)) with
  | .missing =>
    SeqEnv (KpkPassEnv DecEnv GetEnv DecodeEnv rd F0 x.kg.oneTime x.id)
      (KpkPassEnv DecEnv GetEnv DecodeEnv rd F0 x.kg.lastResort x.id)
  | _ => KpkPassEnv DecEnv GetEnv DecodeEnv rd F0 x.kg.oneTime x.id

def deallocVecBufCellsSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DeallocBufGhost × M.σ) where
  pre := fun ((cap, ptr, bs, fsp), st) s =>
    ⌜FsInv F0 T0 s ∧ cap ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    vecU8Buf A.repAlloc cap ptr bs ∗ stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((cap, _ptr, _bs, fsp), st) s0 sf =>
    ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace⌝ ∗
    stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf

def decimalFsCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DecimalCellsGhost × M.σ) where
  pre := fun ((n, ret, o0, o1, o2, fsp), st) s =>
    ⌜FsInv F0 T0 s ∧ s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = n ∧ s.sp = fsp ∧
      FitsEnv M lim st (DecEnv n)⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((n, ret, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace ∧ DecEnv n evs⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName n).length) ∗
      vecU8Buf A.repAlloc nCap nPtr (keyName n) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def dirGetFsCellsSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DirGetCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp), st) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ PkNameOk pathOk dir keyId ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName keyId).length ∧ s.sp = fsp ∧
      FitsEnv M lim st (GetEnv dir keyId)⌝ ∗
    dirAt A.repAlloc self dir ∗ vecU8Buf A.repAlloc nCap nPtr (keyName keyId) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, keyId, nCap, nPtr, _o0, _o1, _o2, _o3, _o4, _o5, fsp), st)
      _s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ r : Except Unit (List (BitVec 8)),
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ H : SepProp,
      ⌜dirGetPostProp rd A.repAlloc F0 T0 dir keyId sf r w0 w1 w2 w3 w4 w5 H ∧
        GetEnv dir keyId evs⌝ ∗
      words6At ret w0 w1 w2 w3 w4 w5 ∗ H ∗
      dirAt A.repAlloc self dir ∗ vecU8Buf A.repAlloc nCap nPtr (keyName keyId) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def decodeFsCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DecodeCellsGhost × M.σ) where
  pre := fun ((ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp), st) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32 ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧ s.sp = fsp ∧
      FitsEnv M lim st (DecodeEnv bytes)⌝ ∗
    vecU8Buf A.repAlloc bCap bPtr bytes ∗
    words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, bCap, bPtr, bytes,
      _o0, _o1, _o2, _o3, _o4, _o5, _o6, _o7, _o8, _o9, _o10, fsp), st) _s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ H : SepProp,
      ⌜decodePostProp A.repAlloc F0 T0 bytes sf w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 H ∧
        DecodeEnv bytes evs⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗ H ∗
      vecU8Buf A.repAlloc bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def cliKpkGetPollInnerSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (KpkPollGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FsInv s.fs.files s.trace s ∧
      s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
      PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id ∧
      FitsEnv M lim st (CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s.fs.files x)⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗ dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      memRegion x.out 88 ∗
      A.pool lim st s ∗ stackAt (s.sp - 432#64) calleeStk ∗ cells (s.sp - 432#64) 54
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ ans : PkAns KyberPreKeyRecord,
        ⌜ans = kpkAnsOf
              (pkAnsOf KyberPreKeyRecord.deserialize
                (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
              (pkAnsOf KyberPreKeyRecord.deserialize
                (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
            sf.trace = s0.trace ∧
            CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs⌝ ∗
        kpkAnsAt A.repAlloc x.out ans) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 432#64) calleeStk ∗ cells (s0.sp - 432#64) 54

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
