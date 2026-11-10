/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Layout

/-!
# Budget-Threaded Cell Wrappers for `StorePoll`

`RustCliAllocBudget`-threaded cell and inner specifications (`addrTextCellsSpec`,
`serializeCellsSpec`, `dirPutCellsSpec`, `cliStorePollInnerSpec`) and composed `AllocEvent`
envelope `CliStorePollEnv` for `store_session::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv SeqEnv)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.SignalSession.Cli
  (DirGhost SessStorePollGhost addressText dirAt)
open CryptoVerification.E2E.Record (RecordGhost encodeRecord sessionRecordAt)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.E2E.InMem.SessionStoreImpl (toRecordGhost)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (AddrCellsGhost SerCellsGhost PutCellsGhost)

/-- Composed `AllocEvent` envelope for `store_session::{closure#0}`: `address_text` followed by
`SessionRecord::serialize` followed by `Dir::put`. -/
def CliStorePollEnv
    (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (SerEnv : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : SessStorePollGhost) : List AllocEvent → Prop :=
  SeqEnv (AddrEnv x.call.call.addr)
    (SeqEnv (SerEnv (toRecordGhost x.call.call.g) x.call.call.record)
      (PutEnv x.dir (addressText x.call.call.addr.val) (encodeRecord x.call.call.record)))

def addrTextCellsSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (AddrEnv : AddrGhost → List AllocEvent → Prop) (calleeStk : Nat) :
    Spec (AddrCellsGhost × M.σ) where
  pre := fun ((addrA, g, ret, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = addrA ∧ s.sp = fsp ∧
      g.name.bytes.length < 2 ^ 32 ∧ FitsEnv M lim st (AddrEnv g) ∧
      LsRetAddr624 (s.readReg64 .x30)⌝ ∗
    protocolAddressAt A.repAlloc g addrA ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((addrA, g, ret, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AddrEnv g evs⌝ ∗
      vecU8 A.repAlloc ret (addressText g.val) ∗
      protocolAddressAt A.repAlloc g addrA ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def serializeCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SerEnv : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (SerCellsGhost × M.σ) where
  pre := fun ((recA, out, g, r, o0, o1, o2, o3, fsp), st) s =>
    ⌜s.readReg64 .x0 = recA ∧ s.readReg64 .x8 = out ∧ s.sp = fsp ∧
      CanonRecord g r ∧ (encodeRecord r).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerEnv g r)⌝ ∗
    sessionRecordAt A.repAlloc recA g r ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗
    A.pool lim st s ∗ stackAt fsp calleeStk
  post := fun ((recA, out, g, r, _o0, _o1, _o2, _o3, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ SerEnv g r evs⌝ ∗
      sessionRecordAt A.repAlloc recA g r ∗
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ bCap) ∗ ((out + 16#64) ↦₆₄ bPtr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (encodeRecord r).length) ∗
      vecU8Buf A.repAlloc bCap bPtr (encodeRecord r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt fsp calleeStk

def dirPutCellsSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PutCellsGhost × M.σ) where
  pre := fun ((self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp), st) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = nameV ∧ s.readReg64 .x2 = bytesV ∧
      s.sp = fsp ∧ dir.changed.length < 2 ^ 32 ∧
      FitsEnv M lim st (PutEnv dir name bytes) ∧
      LsRetAddr624 (s.readReg64 .x30)⌝ ∗
    dirAt A.repAlloc self dir ∗ vecU8 A.repAlloc nameV name ∗
    (bytesV ↦₆₄ bCap) ∗ ((bytesV + 8#64) ↦₆₄ bPtr) ∗
    ((bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 bytes.length) ∗
    vecU8Buf A.repAlloc bCap bPtr bytes ∗
    stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((self, dir, nameV, name, bytesV, _bCap, _bPtr, bytes, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
    ∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 64, ∃∗ n2 : BitVec 64,
    ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64,
      ⌜sf.trace = s0.trace ∧ PutEnv dir name bytes evs⌝ ∗
      dirAt A.repAlloc self (dir.put name bytes) ∗
      (nameV ↦₆₄ n0) ∗ ((nameV + 8#64) ↦₆₄ n1) ∗ ((nameV + 16#64) ↦₆₄ n2) ∗
      (bytesV ↦₆₄ m0) ∗ ((bytesV + 8#64) ↦₆₄ m1) ∗ ((bytesV + 16#64) ↦₆₄ m2) ∗
      stackAt fsp calleeStk ∗ A.pool lim (M.stepEvents evs st) sf

def cliStorePollInnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (SerEnv : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (SessStorePollGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧
      (encodeRecord x.call.call.record).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32 ∧
      CanonRecord (toRecordGhost x.call.call.g) x.call.call.record ∧
      FitsEnv M lim st (CliStorePollEnv AddrEnv SerEnv PutEnv x)⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
      protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
      sessionRecordAt A.repAlloc x.call.call.recA
        (toRecordGhost x.call.call.g) x.call.call.record ∗
      A.pool lim st s ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ CliStorePollEnv AddrEnv SerEnv PutEnv x evs⌝ ∗
        (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self (x.dir.put (addressText x.call.call.addr.val)
          (encodeRecord x.call.call.record)) ∗
        (x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.call.out + 8#64) 40 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        sessionRecordAt A.repAlloc x.call.call.recA
          (toRecordGhost x.call.call.g) x.call.call.record ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
