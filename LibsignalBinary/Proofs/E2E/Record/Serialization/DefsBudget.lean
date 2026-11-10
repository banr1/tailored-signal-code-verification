/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs

/-!
# Allocation-budget specifications for `SessionRecord::serialize`

Defines `VmPreserved` and `RustCliAllocBudget M` specifications for `SessionRecord::serialize` and
its callees:
- Zero-allocation `VmPreserved` specs (`msgKeyLenSpec`, `chainLenSpec`, `sessionLenSpec`,
  `vecVecCloneEmptySpec`).
- Input-bounded allocation event envelopes (`BoundedRustEvs`, `EncodeChainEnv`, `EncodeRawEnv`,
  `SessionCloneEnv`, `SerializeEnv`) and total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`)
  budget specs (`encodeChainSpec`, `encodeRawSpec`, `sessionCloneSpec`, `serializeSpec`,
  `serializeCanonSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsRustDeallocSym
  lsHandleErrorSym
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At vecU8)
open CryptoVerification.LibsignalSessionRepr (messageKeyAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost sessionStateReprAt sessionRecordAt
)
open CryptoVerification.E2E.Record (lenField encMessageKey encodeRecord)
open CryptoVerification.E2E.Record.Serialization (
  msgKeyLenStack chainLenStack sessionLenStack
  encodeChainStack encodeRawStack sessionCloneStack vecVecCloneStack serializeStack
  encChainMem encSessionMem encRecordMem CanonRecord protoChainAt
  MsgKeyLenGhost ChainLenGhost SessionLenGhost
  EncodeChainGhost EncodeRawGhost SessionCloneGhost VecVecCloneGhost SerializeGhost
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec allocMemcpyVmSpec)

/-! ## Zero-allocation `VmPreserved` leaf specifications -/

/-- VM-preserving specification of `<chain::MessageKey as Message>::encoded_len`. -/
def msgKeyLenSpec (A : RustAlloc) : Spec MsgKeyLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ messageKeyAt A x.gk x.a ∗ stackAt s.sp msgKeyLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey x.gk.2).length ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      messageKeyAt A x.gk x.a ∗ stackAt s0.sp msgKeyLenStack

/-- VM-preserving specification of `<Chain as Message>::encoded_len`. -/
def chainLenSpec (A : RustAlloc) : Spec ChainLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ (encChainMem x.gc).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗ stackAt s.sp chainLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      protoChainAt A x.gc x.a ∗ stackAt s0.sp chainLenStack

/-- VM-preserving specification of `<SessionStructure as Message>::encoded_len`. -/
def sessionLenSpec (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp sessionLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧
      sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp sessionLenStack

/-- VM-preserving specification of `<Vec<Vec<u8>> as Clone>::clone` on `len = 0` (`0` allocations). -/
def vecVecCloneEmptySpec : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp vecVecCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp vecVecCloneStack

/-! ## Input-bounded allocation envelopes -/

/-- Alignment-bounded (`align ≤ 16`) `AllocEvent` list predicate bounded by `maxCount` events and
per-event request size `maxReq`, closed under append. -/
def BoundedRustEvs (maxCount maxReq : Nat) (evs : List AllocEvent) : Prop :=
  evs.length ≤ maxCount ∧
  ∀ ev ∈ evs,
    ev.withinMaxAlloc ∧
    ev.reqBytes ≤ maxReq ∧
    (∀ al r, ev = .aligned al r → al ≤ 16) ∧
    (∀ al o n, ev = .realloc al o n → al ≤ 16)

theorem BoundedRustEvs.nil (maxCount maxReq : Nat) :
    BoundedRustEvs maxCount maxReq [] :=
  ⟨Nat.zero_le _, fun _ h => nomatch h⟩

theorem BoundedRustEvs.append {c₁ c₂ r₁ r₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : BoundedRustEvs c₁ r₁ evs₁) (h2 : BoundedRustEvs c₂ r₂ evs₂) :
    BoundedRustEvs (c₁ + c₂) (max r₁ r₂) (evs₁ ++ evs₂) := by
  refine ⟨by rw [List.length_append]; exact Nat.add_le_add h1.1 h2.1, ?_⟩
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · obtain ⟨hw, hr, ha, hre⟩ := h1.2 ev hm1
    exact ⟨hw, Nat.le_trans hr (Nat.le_max_left _ _), ha, hre⟩
  · obtain ⟨hw, hr, ha, hre⟩ := h2.2 ev hm2
    exact ⟨hw, Nat.le_trans hr (Nat.le_max_right _ _), ha, hre⟩

theorem BoundedRustEvs.mono {c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (hc : c₁ ≤ c₂) (hr : r₁ ≤ r₂) (h : BoundedRustEvs c₁ r₁ evs) :
    BoundedRustEvs c₂ r₂ evs :=
  ⟨Nat.le_trans h.1 hc, fun ev hev =>
    let ⟨hw, hreq, ha, hre⟩ := h.2 ev hev
    ⟨hw, Nat.le_trans hreq hr, ha, hre⟩⟩

/-- Allocation event envelope for `prost::encoding::message::encode::<Chain, Vec<u8>>`. -/
def EncodeChainEnv (x : EncodeChainGhost) (evs : List AllocEvent) : Prop :=
  let outLen := x.bs.length + (lenField x.tag (encChainMem x.gc)).length
  BoundedRustEvs (4 * outLen + 16) (max (2 * x.cap.toNat) (2 * outLen + 16)) evs

/-- Allocation envelope for `<SessionStructure as Message>::encode_raw::<Vec<u8>>`. -/
def EncodeRawEnv (x : EncodeRawGhost) (evs : List AllocEvent) : Prop :=
  let outLen := x.bs.length + (encSessionMem x.G x.s).length
  BoundedRustEvs (4 * outLen + 32) (max (2 * x.cap.toNat) (2 * outLen + 16)) evs

/-- Allocation event envelope for `<SessionStructure as Clone>::clone`. -/
def SessionCloneEnv (G : SessionGhost) (s : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  let encLen := (encSessionMem G s).length
  BoundedRustEvs (4 * encLen + 64) (256 * (encLen + 16)) evs

/-- Allocation envelope for `<SessionRecord>::serialize`. -/
def SerializeEnv (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  let encLen := (encRecordMem g r).length
  BoundedRustEvs (8 * encLen + 128) (256 * (encLen + 16)) evs

/-! ## Budget-threaded allocating specifications -/

/-- Budget-threaded specification of `prost::encoding::message::encode::<Chain, Vec<u8>>`. -/
def encodeChainSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeChainEnv x)⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeChainStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeChainEnv x evs⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encodeChainStack

/-- Budget-threaded specification of `<SessionStructure as Message>::encode_raw::<Vec<u8>>`. -/
def encodeRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeRawGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32 ∧
      FitsEnv M lim st (EncodeRawEnv x)⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeRawStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ EncodeRawEnv x evs⌝ ∗
      sessionStateReprAt A.repAlloc x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encodeRawStack

/-- Budget-threaded specification of `<SessionStructure as Clone>::clone`. -/
def sessionCloneSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SessionCloneEnv x.G x.s)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp sessionCloneStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SessionCloneEnv x.G x.s evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sessionCloneStack

/-- Budget-threaded memory-level specification of `<SessionRecord>::serialize`. -/
def serializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encRecordMem x.g x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeEnv x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializeEnv x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStack

/-- Budget-threaded canonical specification of `<SessionRecord>::serialize`. -/
def serializeCanonSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeEnv x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializeEnv x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStack

/-! ## External hook bundle -/

/-- Budget-threaded external hook contracts required by `SessionRecord::serialize` and its callees. -/
structure PlacedSerializeHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (H : String → Option (State → State)) : Prop where
  shim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec
  alloc : ∀ lim : BudgetLimits, HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  realloc : ∀ lim : BudgetLimits, HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  dealloc : ∀ lim : BudgetLimits, HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat H "memcpy" allocMemcpyVmSpec
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked

end LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
