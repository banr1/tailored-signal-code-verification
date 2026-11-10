/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1

/-!
# Budget-Threaded Cell and Inner Specifications for `StoreSessionPrev1`

`RustCliAllocBudget`-threaded cell and inner specifications (`serializePrev1CellsSpec`,
`cliStorePollPrev1InnerSpec`) and composed `AllocEvent` envelope `CliStorePollPrev1Env` for
`store_session::{closure#0}` on a `Prev1` record.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv SeqEnv)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost protocolAddressAt)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession.Cli (DirGhost addressText dirAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (prevVecAt encodeRecordPrev1Mem)
open CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
  (SessStorePollPrev1Ghost SerPrev1CellsGhost)

/-- Composed `AllocEvent` envelope for `store_session::{closure#0}` on a `Prev1` record:
`address_text` followed by `SessionRecord::serialize` (`Prev1`) followed by `Dir::put`. -/
def CliStorePollPrev1Env
    (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : SessStorePollPrev1Ghost) : List AllocEvent → Prop :=
  SeqEnv (AddrEnv x.addr)
    (SeqEnv (SerPrev1Env x.G x.sess x.enc)
      (PutEnv x.dir (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)))

def serializePrev1CellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (SerPrev1CellsGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.recA ∧ s.readReg64 .x8 = g.out ∧ s.sp = g.fsp ∧
      (encodeRecordPrev1Mem g.G g.sess g.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerPrev1Env g.G g.sess g.enc)⌝ ∗
    prevVecAt A.repAlloc g.recA g.prevCap g.prevPtr [g.enc] ∗
    sessionStateReprAt A.repAlloc (g.recA + 24#64) g.G g.sess ∗
    (g.out ↦₆₄ g.o0) ∗ ((g.out + 8#64) ↦₆₄ g.o1) ∗
    ((g.out + 16#64) ↦₆₄ g.o2) ∗ ((g.out + 24#64) ↦₆₄ g.o3) ∗
    A.pool lim st s ∗ stackAt g.fsp calleeStk
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ SerPrev1Env g.G g.sess g.enc evs⌝ ∗
      prevVecAt A.repAlloc g.recA g.prevCap g.prevPtr [g.enc] ∗
      sessionStateReprAt A.repAlloc (g.recA + 24#64) g.G g.sess ∗
      (g.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((g.out + 8#64) ↦₆₄ bCap) ∗ ((g.out + 16#64) ↦₆₄ bPtr) ∗
      ((g.out + 24#64) ↦₆₄ BitVec.ofNat 64 (encodeRecordPrev1Mem g.G g.sess g.enc).length) ∗
      vecU8Buf A.repAlloc bCap bPtr (encodeRecordPrev1Mem g.G g.sess g.enc) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt g.fsp calleeStk

def cliStorePollPrev1InnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AddrEnv : AddrGhost → List AllocEvent → Prop)
    (SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (SessStorePollPrev1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.addr.name.bytes.length < 2 ^ 32 ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      x.dir.changed.length < 2 ^ 32 ∧
      FitsEnv M lim st (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv x)⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
      ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      prevVecAt A.repAlloc x.recA x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A.repAlloc (x.recA + 24#64) x.G x.sess ∗
      A.pool lim st s ∗ stackAt (s.sp - 208#64) calleeStk ∗ cells (s.sp - 208#64) 26
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv x evs⌝ ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₆₄ x.addrA) ∗
        ((x.fut + 16#64) ↦₆₄ x.recA) ∗ ((x.fut + 24#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self
          (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
        (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
        protocolAddressAt A.repAlloc x.addr x.addrA ∗
        prevVecAt A.repAlloc x.recA x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A.repAlloc (x.recA + 24#64) x.G x.sess ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 208#64) calleeStk ∗ cells (s0.sp - 208#64) 26

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget
