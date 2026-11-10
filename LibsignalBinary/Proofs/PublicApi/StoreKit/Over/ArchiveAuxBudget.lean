/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAux
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Helpers for `archive_current_state_inner` and `promote_state`

`RustCliAllocBudget M` helpers for Blocks `51` and `47` under `[LibsignalPlacement]`:
* `A.atState lim st s` ↔ `A.repAlloc` bridges across session/record separation-logic predicates and
  unfoldings for `ArchiveDefsBudget` specifications;
* `ArchiveCoreEnv` decomposition and `FitsEvents` / `FitsEnv` projections across pending-key
  deallocations, `Vec::with_capacity(encLen)`, and `RawVec<Vec<u8>>::grow_one`;
* Relocatable callee sub-specifications at `serializeSubStackX`, including pre-reserved 0-allocation
  `encodeRawPreallocSubSpecX`, `rustDeallocSubSpecX`, and `growOneSubSpecX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (
  ChainKey MessageKeyGenerator ReceiverChain SenderChain SessionState
)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsMemcpySym
  blkPl_6 lsProg_47 blkPl_47 lsProg_51 blkPl_51
)
open CryptoVerification.RustHeap (
  RustAlloc vecBuf vecAt vecOf vecU8At vecU8 arrayAt_congr vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (
  VecPin VecGhost MessageKeyGhost ChainGhost
  vecGhostAt messageKeyAt optChainKeyAt chainAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost TailVecGhost SessionGhost
  noneCap optSenderChainAt optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost sessionStateReprAt sessionRecordAt
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  vecGhostHeap optChainKeyHeap protoChainAt protoChainHeap chainHeap
  optSenderChainHeap optTailVecHeap sessionHeap
)
open CryptoVerification.E2E.Record.Placed (lsProg_14 blkPl_14 blkPl_86)
open CryptoVerification.E2E.Record.Serialization (encSessionMem EncodeRawGhost)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  sessionAtHeap
  subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX stackAt_serializeSub_splitX
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall newCapVecU8)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP prevElem prevVecAt Prev1 recCurAt sessionRecordPrevAt
  clearPendingGhost clearPending archiveStackX promoteStackX
  ArchiveOverGenGhost PromoteOverGenGhost ArchiveOverGhost PromoteOverGhost
  tailPinDealloc
)
open LibsignalBinary.Heap (
  VmPreserved AllocCallPreserved OomPreserved
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk NullAllowed FitsEvents FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceLemmas (satisfies_drop_mid_entails)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rawVecNewCap rawVecGrowEvents RawVecGrowEnv
  rawVecGrowEnv_events rawVecGrowEvents_eq_of_env
  rawVecGrowBudgetCondSpec rawVecGrowNoOomSpec rawVecGrowBudgetSpec
  growOneVecU8Events GrowOneVecU8Env
  growOneVecU8BudgetCondSpec growOneVecU8NoOomSpec growOneVecU8BudgetSpec
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCl_map_oom' subroutine_ok_withLsCl_map_panic_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeRawStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (
  ArchiveCoreEnv ArchiveOverGenEnv PromoteOverGenEnv ArchiveOverEnvX PromoteOverEnvX
)

/-! ## `A.atState` ↔ `A.repAlloc` Bridges and `*PlacedOk*` Abbreviations -/

theorem vecU8Buf_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A₁ cap ptr bs = vecU8Buf A₂ cap ptr bs := by
  unfold vecU8Buf
  rw [h]

theorem vecU8At_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A₁ v cap ptr bs = vecU8At A₂ v cap ptr bs := by
  unfold vecU8At
  rw [h]

theorem vecU8_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A₁ v bs = vecU8 A₂ v bs := by
  unfold vecU8
  simp only [vecU8At_congr_live h]

theorem vecBuf_congr_live {α : Type} {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (stride align : Nat) {elem₁ elem₂ : α → BitVec 64 → SepProp}
    (cap ptr : BitVec 64) (xs : List α)
    (helem : ∀ x ∈ xs, ∀ a, elem₁ x a = elem₂ x a) :
    vecBuf A₁ stride align elem₁ cap ptr xs = vecBuf A₂ stride align elem₂ cap ptr xs := by
  unfold vecBuf
  rw [h, arrayAt_congr stride ptr helem]

theorem vecAt_congr_live {α : Type} {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (stride align : Nat) {elem₁ elem₂ : α → BitVec 64 → SepProp}
    (v cap ptr : BitVec 64) (xs : List α)
    (helem : ∀ x ∈ xs, ∀ a, elem₁ x a = elem₂ x a) :
    vecAt A₁ stride align elem₁ v cap ptr xs = vecAt A₂ stride align elem₂ v cap ptr xs := by
  unfold vecAt
  rw [vecBuf_congr_live h stride align cap ptr xs helem]

theorem vecOf_congr_live {α : Type} {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (stride align : Nat) {elem₁ elem₂ : α → BitVec 64 → SepProp}
    (v : BitVec 64) (xs : List α)
    (helem : ∀ x ∈ xs, ∀ a, elem₁ x a = elem₂ x a) :
    vecOf A₁ stride align elem₁ v xs = vecOf A₂ stride align elem₂ v xs := by
  unfold vecOf
  have heq : ∀ cap ptr : BitVec 64,
      vecAt A₁ stride align elem₁ v cap ptr xs = vecAt A₂ stride align elem₂ v cap ptr xs :=
    fun cap ptr => vecAt_congr_live h stride align v cap ptr xs helem
  simp only [heq]

theorem vecGhostAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A₁ g v = vecGhostAt A₂ g v :=
  vecU8At_congr_live h v g.cap g.ptr g.bytes

theorem vecGhostHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (g : VecGhost) :
    vecGhostHeap A₁ g = vecGhostHeap A₂ g :=
  vecU8Buf_congr_live h g.cap g.ptr g.bytes

theorem messageKeyAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A₁ gk a = messageKeyAt A₂ gk a := by
  unfold messageKeyAt
  simp only [vecU8At_congr_live h]

theorem optChainKeyAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (pin : VecPin) (o : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A₁ pin o a = optChainKeyAt A₂ pin o a := by
  cases o <;> simp only [optChainKeyAt, vecU8At_congr_live h]

theorem optChainKeyHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (pin : VecPin) (o : Option ChainKey) :
    optChainKeyHeap A₁ pin o = optChainKeyHeap A₂ pin o := by
  cases o <;> simp only [optChainKeyHeap, vecU8Buf_congr_live h]

theorem chainAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A₁ gc a = chainAt A₂ gc a := by
  unfold chainAt
  rw [vecGhostAt_congr_live h, vecGhostAt_congr_live h,
    vecAt_congr_live h _ _ _ _ _ _ (fun x _ b => messageKeyAt_congr_live h x b),
    optChainKeyAt_congr_live h]

theorem protoChainAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A₁ gc a = protoChainAt A₂ gc a := by
  unfold protoChainAt
  rw [vecGhostAt_congr_live h, vecGhostAt_congr_live h,
    vecAt_congr_live h _ _ _ _ _ _ (fun x _ b => messageKeyAt_congr_live h x b),
    optChainKeyAt_congr_live h]

theorem protoChainHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gc : ChainGhost × ReceiverChain) :
    protoChainHeap A₁ gc = protoChainHeap A₂ gc := by
  unfold protoChainHeap
  rw [vecGhostHeap_congr_live h, vecGhostHeap_congr_live h,
    vecBuf_congr_live h _ _ _ _ _ (fun x _ b => messageKeyAt_congr_live h x b),
    optChainKeyHeap_congr_live h]

theorem chainHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (gc : ChainGhost × ReceiverChain) :
    chainHeap A₁ gc = chainHeap A₂ gc := by
  unfold chainHeap
  rw [vecGhostHeap_congr_live h, vecGhostHeap_congr_live h,
    vecBuf_congr_live h _ _ _ _ _ (fun x _ b => messageKeyAt_congr_live h x b),
    optChainKeyHeap_congr_live h]

theorem optSenderChainAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (a : BitVec 64) (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A₁ a g sc = optSenderChainAt A₂ a g sc := by
  cases g <;> cases sc <;>
    simp only [optSenderChainAt, vecGhostAt_congr_live h, optChainKeyAt_congr_live h,
      vecAt_congr_live h _ _ _ _ _ _ (fun x _ b => messageKeyAt_congr_live h x b)]

theorem optSenderChainHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainHeap A₁ g sc = optSenderChainHeap A₂ g sc := by
  cases g <;> cases sc <;> simp only [optSenderChainHeap, protoChainHeap_congr_live h]

theorem optTailVecAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (size : Nat) (a : BitVec 64) (o : Option TailVecGhost) :
    optTailVecAt A₁ size a o = optTailVecAt A₂ size a o := by
  cases o <;> simp only [optTailVecAt, vecGhostAt_congr_live h]

theorem optTailVecHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (o : Option TailVecGhost) :
    optTailVecHeap A₁ o = optTailVecHeap A₂ o := by
  cases o <;> simp only [optTailVecHeap, vecGhostHeap_congr_live h]

theorem sessionStateAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A₁ ss G st = sessionStateAt A₂ ss G st := by
  unfold sessionStateAt
  rw [vecGhostAt_congr_live h, vecGhostAt_congr_live h, vecU8At_congr_live h,
    vecAt_congr_live h _ _ _ _ _ _ (fun x _ b => chainAt_congr_live h x b),
    vecGhostAt_congr_live h, vecU8At_congr_live h, optSenderChainAt_congr_live h,
    optTailVecAt_congr_live h, optTailVecAt_congr_live h]

theorem sessionHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionHeap A₁ G st = sessionHeap A₂ G st := by
  unfold sessionHeap
  rw [vecGhostHeap_congr_live h, vecGhostHeap_congr_live h, vecU8Buf_congr_live h,
    vecBuf_congr_live h _ _ _ _ _ (fun x _ b => chainAt_congr_live h x b),
    vecGhostHeap_congr_live h, vecU8Buf_congr_live h, optSenderChainHeap_congr_live h,
    optTailVecHeap_congr_live h, optTailVecHeap_congr_live h]

theorem sessionStateReprAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (ss : BitVec 64) (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionStateReprAt A₁ ss G s = sessionStateReprAt A₂ ss G s := by
  unfold sessionStateReprAt
  rw [sessionStateAt_congr_live h]

theorem sessionAtHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionAtHeap A₁ G s = sessionAtHeap A₂ G s := by
  unfold sessionAtHeap
  rw [sessionHeap_congr_live h]

theorem sessionRecordAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (r : BitVec 64) (g : RecordGhost) (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt A₁ r g rec = sessionRecordAt A₂ r g rec := by
  unfold sessionRecordAt
  rw [vecAt_congr_live h 24 8 r g.prevCap g.prevPtr [] (fun _ _ _ => rfl)]
  cases g.cur <;> cases rec.currentSession <;> simp only [sessionStateReprAt_congr_live h]

theorem prevElem_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live) :
    prevElem A₁ = prevElem A₂ := by
  funext bs a
  exact vecU8_congr_live h a bs

theorem prevVecAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) :
    prevVecAt A₁ r cap ptr ps = prevVecAt A₂ r cap ptr ps :=
  vecAt_congr_live h 24 8 r cap ptr ps (fun bs _ a => vecU8_congr_live h a bs)

theorem prev1_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (q : BitVec 64) (enc : List (BitVec 8)) :
    Prev1 A₁ q enc = Prev1 A₂ q enc := by
  unfold Prev1
  exact vecBuf_congr_live h 24 8 4#64 q [enc] (fun bs _ a => vecU8_congr_live h a bs)

theorem recCurAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (r : BitVec 64) (cur : Option SessionGhost) (rec : SessionRecord (List (BitVec 8))) :
    recCurAt A₁ r cur rec = recCurAt A₂ r cur rec := by
  cases cur <;> cases rec.currentSession <;> simp only [recCurAt, sessionStateReprAt_congr_live h]

theorem sessionRecordPrevAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (r : BitVec 64) (g : RecordGhost) (ps : List (List (BitVec 8)))
    (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordPrevAt A₁ r g ps rec = sessionRecordPrevAt A₂ r g ps rec := by
  unfold sessionRecordPrevAt
  rw [prevVecAt_congr_live h, recCurAt_congr_live h]

theorem tailPinDealloc_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (cap ptr : BitVec 64) :
    tailPinDealloc A₁ cap ptr = tailPinDealloc A₂ cap ptr := by
  unfold tailPinDealloc
  rw [h]

/-! ### `A.atState lim st s` ↔ `A.repAlloc` Specializations -/

theorem vecAt_empty_unit_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v cap ptr : BitVec 64) :
    vecAt (A.atState lim st s) 24 8 (fun (_ : Unit) _ => emp) v cap ptr [] =
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) v cap ptr [] :=
  vecAt_congr_live (A.atState_live_eq_repAlloc lim st s) 24 8 v cap ptr [] (fun _ _ _ => rfl)

theorem vecU8Buf_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf (A.atState lim st s) cap ptr bs = vecU8Buf A.repAlloc cap ptr bs :=
  vecU8Buf_congr_live (A.atState_live_eq_repAlloc lim st s) cap ptr bs

theorem vecU8At_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At (A.atState lim st s) v cap ptr bs = vecU8At A.repAlloc v cap ptr bs :=
  vecU8At_congr_live (A.atState_live_eq_repAlloc lim st s) v cap ptr bs

theorem vecU8_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 (A.atState lim st s) v bs = vecU8 A.repAlloc v bs :=
  vecU8_congr_live (A.atState_live_eq_repAlloc lim st s) v bs

theorem sessionStateAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (ss : BitVec 64) (G : SessionGhost) (sessSt : SessionState (List (BitVec 8))) :
    sessionStateAt (A.atState lim st s) ss G sessSt = sessionStateAt A.repAlloc ss G sessSt :=
  sessionStateAt_congr_live (A.atState_live_eq_repAlloc lim st s) ss G sessSt

theorem sessionStateReprAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (ss : BitVec 64) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionStateReprAt (A.atState lim st s) ss G sess =
      sessionStateReprAt A.repAlloc ss G sess :=
  sessionStateReprAt_congr_live (A.atState_live_eq_repAlloc lim st s) ss G sess

theorem sessionAtHeap_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionAtHeap (A.atState lim st s) G sess = sessionAtHeap A.repAlloc G sess :=
  sessionAtHeap_congr_live (A.atState_live_eq_repAlloc lim st s) G sess

theorem sessionRecordAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (g : RecordGhost) (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt (A.atState lim st s) r g rec = sessionRecordAt A.repAlloc r g rec :=
  sessionRecordAt_congr_live (A.atState_live_eq_repAlloc lim st s) r g rec

theorem prevVecAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (r cap ptr : BitVec 64) (ps : List (List (BitVec 8))) :
    prevVecAt (A.atState lim st s) r cap ptr ps = prevVecAt A.repAlloc r cap ptr ps :=
  prevVecAt_congr_live (A.atState_live_eq_repAlloc lim st s) r cap ptr ps

theorem prev1_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (q : BitVec 64) (enc : List (BitVec 8)) :
    Prev1 (A.atState lim st s) q enc = Prev1 A.repAlloc q enc :=
  prev1_congr_live (A.atState_live_eq_repAlloc lim st s) q enc

theorem recCurAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (cur : Option SessionGhost) (rec : SessionRecord (List (BitVec 8))) :
    recCurAt (A.atState lim st s) r cur rec = recCurAt A.repAlloc r cur rec :=
  recCurAt_congr_live (A.atState_live_eq_repAlloc lim st s) r cur rec

theorem sessionRecordPrevAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (g : RecordGhost) (ps : List (List (BitVec 8)))
    (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordPrevAt (A.atState lim st s) r g ps rec =
      sessionRecordPrevAt A.repAlloc r g ps rec :=
  sessionRecordPrevAt_congr_live (A.atState_live_eq_repAlloc lim st s) r g ps rec

theorem tailPinDealloc_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) :
    tailPinDealloc (A.atState lim st s) cap ptr = tailPinDealloc A.repAlloc cap ptr :=
  tailPinDealloc_congr_live (A.atState_live_eq_repAlloc lim st s) cap ptr

/-! ### `ArchiveDefsBudget` Unfoldings and `*PlacedOk*` Abbreviations -/

theorem archiveOverGenSpec_pre_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : ArchiveOverGenGhost) (st : M.σ) (s : State) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).pre (x, st) s =
      (⌜FitsEnv M lim st (ArchiveOverGenEnv x)⌝ ∗
        ⌜s.readReg64 .x0 = x.recPtr ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
        sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
        A.pool lim st s ∗ stackAt s.sp archiveStackX) := by
  dsimp only [ArchiveDefsBudget.archiveOverGenSpec,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec]
  rw [vecAt_empty_unit_atState, sessionStateReprAt_atState, RustCliAllocBudget.atState_pool]

theorem archiveOverGenSpec_post_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : ArchiveOverGenGhost) (st : M.σ) (s0 sf : State) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).post (x, st) s0 sf =
      (∃∗ evs : List AllocEvent,
        ⌜ArchiveOverGenEnv x evs⌝ ∗
        ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
          ⌜prevCap' ≠ 0#64⌝ ∗
          prevVecAt A.repAlloc x.recPtr prevCap' prevPtr'
            [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
        ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX) := by
  dsimp only [ArchiveDefsBudget.archiveOverGenSpec,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec]
  simp only [prevVecAt_atState, RustCliAllocBudget.atState_pool]

theorem promoteOverGenSpec_pre_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PromoteOverGenGhost) (st : M.σ) (s : State) :
    (ArchiveDefsBudget.promoteOverGenSpec M A lim).pre (x, st) s =
      (⌜FitsEnv M lim st (PromoteOverGenEnv x)⌝ ∗
        ⌜s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
        sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
        A.pool lim st s ∗ (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX) := by
  dsimp only [ArchiveDefsBudget.promoteOverGenSpec,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec]
  rw [vecAt_empty_unit_atState, sessionStateReprAt_atState, RustCliAllocBudget.atState_pool]

theorem promoteOverGenSpec_post_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PromoteOverGenGhost) (st : M.σ) (s0 sf : State) :
    (ArchiveDefsBudget.promoteOverGenSpec M A lim).post (x, st) s0 sf =
      (∃∗ evs : List AllocEvent,
        ⌜PromoteOverGenEnv x evs⌝ ∗
        ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
          ⌜prevCap' ≠ 0#64⌝ ∗
          prevVecAt A.repAlloc x.recPtr prevCap' prevPtr'
            [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
        ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp promoteStackX) := by
  dsimp only [ArchiveDefsBudget.promoteOverGenSpec,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec]
  simp only [prevVecAt_atState, RustCliAllocBudget.atState_pool]

theorem archiveOverSpecX_pre_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : ArchiveOverGhost) (st : M.σ) (s : State) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).pre (x, st) s =
      (⌜FitsEnv M lim st (ArchiveOverEnvX x)⌝ ∗
        ⌜s.readReg64 .x0 = x.recPtr ∧ x.prevPtr ≠ 0#64 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
        HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗
        sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
        A.pool lim st s ∗ stackAt s.sp archiveStackX) := by
  dsimp only [ArchiveDefsBudget.archiveOverSpecX,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX]
  rw [sessionStateReprAt_atState, RustCliAllocBudget.atState_pool]

theorem archiveOverSpecX_post_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : ArchiveOverGhost) (st : M.σ) (s0 sf : State) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).post (x, st) s0 sf =
      (∃∗ evs : List AllocEvent,
        ⌜ArchiveOverEnvX x evs⌝ ∗
        ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ q : BitVec 64,
          HdrP x.recPtr 4#64 q 1#64 ∗
            Prev1 A.repAlloc q (encSessionMem (clearPendingGhost x.G) (clearPending x.sess))) ∗
        ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX) := by
  dsimp only [ArchiveDefsBudget.archiveOverSpecX,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX]
  simp only [prev1_atState, RustCliAllocBudget.atState_pool]

theorem promoteOverSpecX_pre_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PromoteOverGhost) (st : M.σ) (s : State) :
    (ArchiveDefsBudget.promoteOverSpecX M A lim).pre (x, st) s =
      (⌜FitsEnv M lim st (PromoteOverEnvX x)⌝ ∗
        ⌜s.readReg64 .x0 = x.recPtr ∧ s.readReg64 .x1 = x.src ∧ x.newBs.length = 344 ∧
          x.prevPtr ≠ 0#64 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
        HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗
        sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
        A.pool lim st s ∗ (x.src ↦ₛ x.newBs) ∗ stackAt s.sp promoteStackX) := by
  dsimp only [ArchiveDefsBudget.promoteOverSpecX,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX]
  rw [sessionStateReprAt_atState, RustCliAllocBudget.atState_pool]

theorem promoteOverSpecX_post_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (x : PromoteOverGhost) (st : M.σ) (s0 sf : State) :
    (ArchiveDefsBudget.promoteOverSpecX M A lim).post (x, st) s0 sf =
      (∃∗ evs : List AllocEvent,
        ⌜PromoteOverEnvX x evs⌝ ∗
        ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ q : BitVec 64,
          HdrP x.recPtr 4#64 q 1#64 ∗
            Prev1 A.repAlloc q (encSessionMem (clearPendingGhost x.G) (clearPending x.sess))) ∗
        ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗ (x.src ↦ₛ x.newBs) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp promoteStackX) := by
  dsimp only [ArchiveDefsBudget.promoteOverSpecX,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX]
  simp only [prev1_atState, RustCliAllocBudget.atState_pool]

/-- Relocatable `[LibsignalPlacement]` budget counterpart of `ArchiveOverGenPlacedOk` on `lsProg_51 H`. -/
abbrev ArchiveOverGenPlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_51 H) (blkPl_51).base
    (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverGenSpec M A lim))

/-- Relocatable `[LibsignalPlacement]` budget counterpart of `PromoteStateOverGenPlacedOk` on `lsProg_47 H`. -/
abbrev PromoteStateOverGenPlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_47 H) (blkPl_47).base
    (withLsCodeLoaded lsmpl (ArchiveDefsBudget.promoteOverGenSpec M A lim))

/-- Relocatable `[LibsignalPlacement]` budget counterpart of `ArchiveOverPlacedOkX` on `lsProg_51 H`. -/
abbrev ArchiveOverPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_51 H) (blkPl_51).base
    (withLsCodeLoaded lsmpl (ArchiveDefsBudget.archiveOverSpecX M A lim))

/-- Relocatable `[LibsignalPlacement]` budget counterpart of `PromoteStateOverPlacedOkX` on `lsProg_47 H`. -/
abbrev PromoteStateOverPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_47 H) (blkPl_47).base
    (withLsCodeLoaded lsmpl (ArchiveDefsBudget.promoteOverSpecX M A lim))

/-! ## `ArchiveCoreEnv` Decomposition and `FitsEnv` Projections -/

theorem freeOnlyEvs_rustDealloc (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem growOneVecU8Events_zero :
    growOneVecU8Events 0#64 = rustAllocEvents 96 8 := rfl

theorem growOneVecU8Env_zero_iff {x : GrowOneCall} {evs : List AllocEvent}
    (hx : x.cap = 0#64) :
    GrowOneVecU8Env x evs ↔ evs = rustAllocEvents 96 8 := by
  constructor
  · intro h
    have heq := rawVecGrowEvents_eq_of_env h
    rwa [hx] at heq
  · rintro rfl
    have hev := rawVecGrowEnv_events 24 4 8 x
    rwa [hx] at hev

theorem fitsEnv_allocEnc_tail_of_archiveCoreEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {prevCap : BitVec 64} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr : List AllocEvent}
    (hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess))
    (hClr : FreeOnlyEvs evsClr) :
    FitsEnv M lim (M.stepEvents evsClr st)
      (SeqEnv
        (fun evs => evs = rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
          FreeOnlyEvs)) :=
  FitsEnv.seq_right hFit hClr

theorem fitsEvents_allocEnc_of_archiveCoreEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {prevCap : BitVec 64} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr : List AllocEvent}
    (hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess))
    (hClr : FreeOnlyEvs evsClr) :
    FitsEvents M lim (M.stepEvents evsClr st)
      (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1) := by
  have h0 := FitsEnv.seq_left (fitsEnv_allocEnc_tail_of_archiveCoreEnv hFit hClr)
  exact h0 _ rfl

theorem fitsEnv_growTail_of_archiveCoreEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {prevCap : BitVec 64} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr : List AllocEvent}
    (hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess))
    (hClr : FreeOnlyEvs evsClr) :
    FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (M.stepEvents evsClr st))
      (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
        FreeOnlyEvs) :=
  FitsEnv.seq_right (fitsEnv_allocEnc_tail_of_archiveCoreEnv hFit hClr) rfl

theorem fitsEvents_growOneZero_of_archiveCoreEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr : List AllocEvent}
    (hFit : FitsEnv M lim st (ArchiveCoreEnv 0#64 G sess))
    (hClr : FreeOnlyEvs evsClr) :
    FitsEvents M lim
      (M.stepEvents (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (M.stepEvents evsClr st))
      (rustAllocEvents 96 8) := by
  have h0 := FitsEnv.seq_left (fitsEnv_growTail_of_archiveCoreEnv hFit hClr)
  exact h0 (rustAllocEvents 96 8) (by simp)

theorem fitsEnv_growOneZero_of_archiveCoreEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr : List AllocEvent} {x : GrowOneCall}
    (hx : x.cap = 0#64)
    (hFit : FitsEnv M lim st (ArchiveCoreEnv 0#64 G sess))
    (hClr : FreeOnlyEvs evsClr) :
    FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (M.stepEvents evsClr st))
      (GrowOneVecU8Env x) := by
  intro evs hevs
  rw [(growOneVecU8Env_zero_iff hx).mp hevs]
  exact fitsEvents_growOneZero_of_archiveCoreEnv hFit hClr

theorem archiveCoreEnv_of_parts {prevCap : BitVec 64} {G : SessionGhost}
    {sess : Session (List (BitVec 8))}
    {evsClr evsGrow evsDrop : List AllocEvent}
    (hClr : FreeOnlyEvs evsClr)
    (hGrow : if prevCap = 0#64 then evsGrow = rustAllocEvents 96 8 else evsGrow = [])
    (hDrop : FreeOnlyEvs evsDrop) :
    let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
    ArchiveCoreEnv prevCap G sess
      (evsClr ++ (rustAllocEvents encLen 1 ++ (evsGrow ++ evsDrop))) :=
  SeqEnv.append hClr (SeqEnv.append rfl (SeqEnv.append hGrow hDrop))

theorem archiveCoreEnv_zero_of_parts {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsClr evsGrow evsDrop : List AllocEvent}
    (hClr : FreeOnlyEvs evsClr)
    (hGrow : evsGrow = rustAllocEvents 96 8)
    (hDrop : FreeOnlyEvs evsDrop) :
    let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
    ArchiveCoreEnv 0#64 G sess
      (evsClr ++ (rustAllocEvents encLen 1 ++ (evsGrow ++ evsDrop))) :=
  archiveCoreEnv_of_parts hClr (by simp [hGrow]) hDrop

theorem archiveCoreEnv_nonzero_of_parts {prevCap : BitVec 64} {G : SessionGhost}
    {sess : Session (List (BitVec 8))}
    {evsClr evsDrop : List AllocEvent}
    (hprev : prevCap ≠ 0#64)
    (hClr : FreeOnlyEvs evsClr)
    (hDrop : FreeOnlyEvs evsDrop) :
    let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
    ArchiveCoreEnv prevCap G sess
      (evsClr ++ (rustAllocEvents encLen 1 ++ evsDrop)) := by
  simpa using
    (archiveCoreEnv_of_parts (prevCap := prevCap) (G := G) (sess := sess)
      (evsGrow := []) hClr (by simp [hprev]) hDrop)

/-! ## Relocatable Budget Callee Sub-Specifications at `serializeSubStackX` -/

abbrev sessionLenSubSpecX :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.sessionLenSubSpecX
abbrev encodeRawSubSpecX :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.encodeRawSubSpecX
set_option linter.unusedVariables false in
abbrev dropLocal1SubSpecX [CryptoVerification.LibsignalPlacement] :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.dropLocal1SubSpecX
set_option linter.unusedVariables false in
abbrev rustAllocSubSpecX [CryptoVerification.LibsignalPlacement] :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.rustAllocSubSpecX
set_option linter.unusedVariables false in
abbrev rustAllocNoOomSubSpecX [CryptoVerification.LibsignalPlacement] :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.rustAllocNoOomSubSpecX
abbrev shimSubSpecX :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.shimSubSpecX
abbrev memcpySubSpecX :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.memcpySubSpecX

abbrev sessionLen_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.sessionLen_placed_sub_okX
abbrev sessionLen_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.sessionLen_placed_sub_clX
abbrev encodeRaw_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.encodeRaw_placed_sub_okX
abbrev encodeRaw_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.encodeRaw_placed_sub_clX
abbrev dropLocal1_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.dropLocal1_placed_sub_okX
abbrev dropLocal1_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.dropLocal1_placed_sub_clX
abbrev alloc_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.alloc_placed_sub_okX
abbrev alloc_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.alloc_placed_sub_clX
abbrev allocNoOom_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.allocNoOom_placed_sub_okX
abbrev allocNoOom_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.allocNoOom_placed_sub_clX
abbrev shim_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.shim_placed_sub_okX
abbrev shim_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.shim_placed_sub_clX
abbrev memcpy_placed_sub_okX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.memcpy_placed_sub_okX
abbrev memcpy_placed_sub_clX :=
  @LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.memcpy_placed_sub_clX

/-! ### Pre-Reserved 0-Allocation `SessionStructure::encode_raw` -/

/-- `0`-allocation (`VmPreserved`) contract for `SessionStructure::encode_raw` (Block `14`) at
`encodeRawStackX` when the destination `Vec<u8>` already has sufficient capacity
(`x.bs.length + (encSessionMem x.G x.s).length ≤ x.cap.toNat`), as in
`archive_current_state_inner`'s `Vec::with_capacity(encoded_len)` path. -/
def encodeRawPreallocSpecX (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length ≤ x.cap.toNat ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp encodeRawStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encSessionMem x.G x.s) ∗
      stackAt s0.sp encodeRawStackX

/-- Block `14` (`SessionStructure::encode_raw`) satisfies the pre-reserved `0`-allocation contract
at `encodeRawStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeRawPreallocPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_14 H) (blkPl_14).base
    (withLsCodeLoaded lsmpl (encodeRawPreallocSpecX A))

/-- Pre-reserved `0`-allocation `SessionStructure::encode_raw` lifted to `serializeSubStackX`. -/
def encodeRawPreallocSubSpecX (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length ≤ x.cap.toNat ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encSessionMem x.G x.s) ∗
      stackAt s0.sp serializeSubStackX

theorem encodeRawPrealloc_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hRaw : EncodeRawPreallocPlacedOkX A H) :
    subroutine_ok callerProg (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawPreallocSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - encodeRawStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hRaw))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawPreallocSubSpecX, encodeRawPreallocSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [encodeRawPreallocSubSpecX, encodeRawPreallocSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem encodeRawPrealloc_placed_sub_clX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hRaw : EncodeRawPreallocPlacedOkX A H) :
    subroutine_ok callerProg (blkPl_14).base
      (withLsCl lsmpl (encodeRawPreallocSubSpecX A)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (encodeRawPrealloc_placed_sub_okX hRaw)

/-! ### Budget-Threaded `__rust_dealloc` at `serializeSubStackX` -/

/-- Budget-threaded `__rust_dealloc` lifted to `serializeSubStackX` (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`, stepping `st` by `rustDeallocEvents size align`). -/
abbrev rustDeallocSubSpecX [CryptoVerification.LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetExternSpecWithStack M A lim serializeSubStackX

theorem dealloc_arch_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.dealloc (callerProg := callerProg)))
    (fun ⟨p, size, align, st⟩ s0 => ?_)
    (fun ⟨p, size, align, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · dsimp only [rustDeallocSubSpecX, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [rustDeallocSubSpecX, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem dealloc_arch_placed_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (dealloc_arch_placed_okX hC)

/-! ### Budget-Threaded `RawVec<Vec<u8>>::grow_one` at `serializeSubStackX` -/

/-- Conditional-OOM budget contract for `RawVec<Vec<u8>>::grow_one` lifted to `serializeSubStackX`. -/
def growOneBudgetCondSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      x.cap.toNat * 24 < 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool lim (M.stepEvents (growOneVecU8Events x.cap) st) sf ∗
      stackAt s0.sp serializeSubStackX
  onPanic := fun (x, _) s0 sf =>
    let newBytes := max (2 * x.cap.toNat) 4 * 24
    ⌜(¬ RustLayoutOk newBytes 8 ∨ NullAllowed newBytes 8) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    let newBytes := max (2 * x.cap.toNat) 4 * 24
    ⌜RustLayoutOk newBytes 8 ∧
      ¬ FitsEvents M lim st (growOneVecU8Events x.cap) ∧
      OomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` contract (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) for
`RawVec<Vec<u8>>::grow_one` lifted to `serializeSubStackX`. -/
def growOneNoOomSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (growOneVecU8Events x.cap)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool lim (M.stepEvents (growOneVecU8Events x.cap) st) sf ∗
      stackAt s0.sp serializeSubStackX

/-- Envelope-form budget contract (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) for
`RawVec<Vec<u8>>::grow_one` lifted to `serializeSubStackX`. -/
def growOneSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneVecU8Env x)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneVecU8Env x evs⌝ ∗
        (∃∗ (p' : BitVec 64),
          ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
          (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp serializeSubStackX

theorem growOneCond_arch_placed_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetCondSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneBudgetCondSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCl_map_panic_oom' hGrow
    fun ⟨x, st⟩ R s0 hpre =>
      ⟨(x, st),
        memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
          (serializeSubStackX - extHookStack) ∗ R,
        ?_, fun sf hpost => ?_,
        fun _ hpan => satisfies_drop_mid_entails (Entails.refl _) hpan,
        fun _ hoom => satisfies_drop_mid_entails (Entails.refl _) hoom⟩
  · dsimp only [growOneBudgetCondSubSpecX, growOneVecU8BudgetCondSpec,
      rawVecGrowBudgetCondSpec] at hpre ⊢
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [growOneBudgetCondSubSpecX, growOneVecU8BudgetCondSpec,
      rawVecGrowBudgetCondSpec, rawVecNewCap, newCapVecU8, growOneVecU8Events] at hpost ⊢
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem growOneCond_arch_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetCondSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneBudgetCondSubSpecX M A lim)) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl (growOneCond_arch_placed_clX hGrow)

theorem growOneNoOom_arch_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8NoOomSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneNoOomSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl hGrow)
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [growOneNoOomSubSpecX, growOneVecU8NoOomSpec, rawVecGrowNoOomSpec,
      rawVecNewCap, growOneVecU8Events,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [growOneNoOomSubSpecX, growOneVecU8NoOomSpec, rawVecGrowNoOomSpec,
      rawVecNewCap, newCapVecU8, growOneVecU8Events,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem growOneNoOom_arch_placed_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8NoOomSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneNoOomSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (growOneNoOom_arch_placed_okX hGrow)

theorem growOne_arch_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl hGrow)
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [growOneSubSpecX, growOneVecU8BudgetSpec, rawVecGrowBudgetSpec,
      rawVecNewCap, GrowOneVecU8Env,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [growOneSubSpecX, growOneVecU8BudgetSpec, rawVecGrowBudgetSpec,
      rawVecNewCap, newCapVecU8, GrowOneVecU8Env]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem growOne_arch_placed_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (growOne_arch_placed_okX hGrow)

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
