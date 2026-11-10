/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public meta import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldChainsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.LoopWPlaced
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionRecord::deserialize` Proof

Proves `sessDeserialize_budget_placed_ok` for `libsignal_protocol::SessionRecord::deserialize`
(Block `46`, `recDeserializeStack = 65,536` B) on `DeserializeScopeP_Q NonEmptyV1Q` over
`(M : AllocCostModel) [HasFineReallocCredit M]`, establishing symbolic cost bounds
(`sessDeserSmallCost`, `sessDeserLargeLive`, `sessDeserPeakLarge`), `2 MiB` wire-slice bounds, and
the capacity-preserving `prostSSGQAtCap` → `sessionRecordAt` representation bridge.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  IdentityKey PublicKey ChainKey ReceiverChain SenderChain MessageKeyGenerator
  SessionState maxReceiverChains maxMessageKeys
)
open CryptoGames.LibsignalSessionApi (
  PendingPreKey PendingKyberPreKey Session SessionRecord
)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  LibsignalCodeLoaded LibsignalRoLoaded
  withLsCodeLoaded withLsCl lsmpl lsρ
)
open CryptoVerification.RustHeap (
  RustAlloc vecAt vecBuf vecHeader vecOf arrayAt vecU8At vecU8
)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalSessionRepr (
  VecPin MessageKeyGhost ChainGhost
  vecGhostAt optChainKeyAt messageKeyAt chainAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  TailVecGhost SenderChainGhost SessionGhost noneCap
  optSenderChainAt optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost sessionStateReprAt sessionRecordAt PendingRel KyberRel
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded
  extHookStack sessionMemcpySpec SeedsLen32
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  sliceCursorAt sliceCursorAfter
)
open CryptoVerification.LibsignalProtoCodec (
  WireType encodeKey encodeVarint decodeVarint decodeVarint_encodeVarint
)
open CryptoVerification.E2E.Record (
  A0 encodeRecord encSession recDeserializeStack
  lenField bytesField msgField
)
open CryptoVerification.E2E.Record.Placed (blkPC_46 blkPl_46 lsProg_46)
open CryptoVerification.E2E.Record.Serialization (
  CanonRecord CanonCur CanonSession CanonChain CanonSender CanonPending
)
open CryptoVerification.E2E.Record.DeserializeSeed (
  deserSpL deserSaved deserCalleeStack ls_call_ro_of_cl deserPlacedPC
)
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp (
  stepPre_loopIter stepPost_loopIter deserFixed_loopIter
  deserOutRegion_loopIter deserOutRegion_eq_loopIter
  sep_perm1_loopIter sep_perm2_loopIter sep_perm3_loopIter
)
open CryptoVerification.E2E.Record.L1GX (pidAt kyberAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG SSG GenField DeserializeGenGhost
  recvChainG senderChainG ssgOf
  prostMsgKeyAt prostChainGAt
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG (
  deserCalleeUnused_loopIterW stackAt_deserCallee_split_loopIterW
  ule_zero_ofNat_succ_placed_loopIterG
)
open Proofs.libsignal.Hooks2 (
  mergeFieldStackX
)
open Symbolic.Swarm.TRREF.B3Defs (
  NonEmptyV1Q DeserializeScopeP_Q
)
open Symbolic.Swarm.TRREF.B3DeserQ (
  ExtraGQ SSGQ GenFieldQ MergeFieldQGhost
  clearPqSession clearPqRecord
  recFieldsQ ssgqAfter ssgqOf deserLocalsQ
  encodeRecord_eq_recFieldsQ recFieldsQ_ok recFieldsQ_fresh
  ssgqAfter_recFieldsQ encodeRecord_length_ltQ encodeRecord_length_lt62_of_Q
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEvents fitsEvents_append
  rustAllocEvents rustDeallocEvents rustReallocEvents
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  bytesLargeLive vec104LargeLive vec104PeakLarge vec104LargeLive_zero
  vecCap4Of vecCap4Next vecCap4Push IsPow2Cap4 isPow2Cap4_next
  vecCap4Of_zero vecCap4Of_succ vecCap4Of_mono vecCap4Of_pow2 le_vecCap4Of
  vec104GrowEvents vec104CumOfCap vec104CumRem vec104CumRem_zero vec104CumRem_self
  vec104CumOfCap_le_of_pow2 vec104PeakLarge_le_of_pow2 vec104LargeLive_le_peakLarge
  sgnCapLargeLive messageKeyLargeLive chainPairLargeLive chainGhostLargeLive
  senderChainLargeLive optTailVecLargeLive ssStateLargeLive ssLargeLive
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  withVmPreserved AllocContractsBudgetPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm (
  decodeVarintSliceSomeSpecGen decode_varint_slice_some_placed_ok_cl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  bytesMergeOutCap bytesMergeOutCap_zero_zero bytesMergeOutCap_zero_pos
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  vecU8FreshCap vecU8FreshCap_entails_vecU8 emptyCells_entails_vecU8FreshCap
  prostChainGAtCap prostChainGAtCap_entails_prostChainGAt
  chainMergeSmallCost chainMergeLargeLive chainMergePeakLarge
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  pendingAt9PCap kyberAtCap kyberAt14Cap kyberAtCap_eq_kyberAt14Cap_sep
  prostSSGQAtCap prostSSGQScalars
  IsBasicFieldQ nextCapRecv mergeFieldQEvents
  basicFieldSmallCost basicFieldLargeLive basicFieldPeakLarge
  GenFieldQ.FreshBytes mergeFieldQBudgetSpecW
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldChainsBudget (
  fieldQSmallCost fieldQLargeLive fieldQPeakLarge
  fieldQCost_of_basic stepEvents_mergeFieldQ_telescope
  mergeFieldAllQ_budget_placed_ok mergeFieldAllQ_caller_ok
)

/-! ## 1. `GrowOneVecU8BudgetPlacedOk`, `sessDeserEvents`, & Symbolic Cost Functions -/

/-- Contract type for `<alloc::raw_vec::RawVec<Vec<u8>>>::grow_one` (
Block `23`, `stride = 24, align = 8, initCap = 4`, `previous_sessions` outer `Vec<Vec<u8>>`):
unused on `DeserializeScopeP_Q NonEmptyV1Q` (`r.prev = []` has no tag-`2` `SessionRecord` fields)
and ready for `Prev1` (`r.prev.length ≤ 1`) without modifying `DeserBudget`. -/
def GrowOneVecU8BudgetPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (_A : RustCliAllocBudget M) (_lim : BudgetLimits) (_H : LibsignalHooks) : Prop :=
  ∀ (_x : GrowGhost) (_st : M.σ), True

/-- Number of tag-`7` (`receiver_chains`) fields in a `GenFieldQ` list. -/
def recvCount : List GenFieldQ → Nat
  | [] => 0
  | .base (.recv _) :: rest => 1 + recvCount rest
  | _ :: rest => recvCount rest

@[simp]
theorem recvCount_nil : recvCount [] = 0 := rfl

theorem recvCount_append (xs ys : List GenFieldQ) :
    recvCount (xs ++ ys) = recvCount xs + recvCount ys := by
  induction xs with
  | nil => simp [recvCount]
  | cons fl rest ih =>
    cases fl with
    | base f => cases f <;> simp [recvCount, ih, Nat.add_assoc]
    | _ => simp [recvCount, ih]

theorem foldl_apply_recv_length (v0 : SSGQ) (flds : List GenFieldQ) :
    ((flds.foldl SSGQ.apply v0).base.recv).length =
      v0.base.recv.length + recvCount flds := by
  induction flds generalizing v0 with
  | nil => simp [recvCount]
  | cons fl rest ih =>
    simp only [List.foldl_cons, ih]
    cases fl with
    | base f =>
      (cases f <;> simp [SSGQ.apply, SSG.apply, recvCount, List.length_append]); omega
    | _ => simp [SSGQ.apply, recvCount]

theorem ssgqAfter_recv_length (r : SessionRecord (List (BitVec 8))) (k : Nat) :
    ((ssgqAfter r k).base.recv).length = recvCount ((recFieldsQ r).take k) := by
  unfold ssgqAfter
  rw [foldl_apply_recv_length]
  simp [SSGQ.empty, SSG.empty]

/-- Sequence of `capRecv` updates across a list of `GenFieldQ` fields. -/
def stepCapRecvList (capRecv curRecvLen : Nat) : List GenFieldQ → Nat × Nat
  | [] => (capRecv, curRecvLen)
  | fl :: rest =>
    let capRecv' := nextCapRecv capRecv curRecvLen fl
    let curRecvLen' := match fl with | .base (.recv _) => curRecvLen + 1 | _ => curRecvLen
    stepCapRecvList capRecv' curRecvLen' rest

/-- Exact `capRecv` progression lemma: starting from `(cap, n)` with `cap = vecCap4Of n`,
stepping `nextCapRecv` across `flds` produces `(vecCap4Of (n + recvCount flds), n + recvCount flds)`. -/
theorem vecCap4Next_eq_vecCap4Of_succ (n : Nat) (heq : n = vecCap4Of n) :
    vecCap4Next (vecCap4Of n) = vecCap4Of (n + 1) := by
  rw [vecCap4Of_succ, vecCap4Push]
  have hnlt : ¬ n < vecCap4Of n := by omega
  simp [hnlt]

theorem vecCap4Of_succ_eq_self_of_lt (n : Nat) (hlt : n < vecCap4Of n) :
    vecCap4Of (n + 1) = vecCap4Of n := by
  rw [vecCap4Of_succ, vecCap4Push]
  simp [hlt]

theorem vecCap4Of_le_mono {a b : Nat} (hab : a ≤ b) :
    vecCap4Of a ≤ vecCap4Of b :=
  vecCap4Of_mono hab

theorem isPow2Cap4_vecCap4Of (n : Nat) : IsPow2Cap4 (vecCap4Of n) :=
  vecCap4Of_pow2 n

theorem nextCapRecv_eq_vecCap4Of (n : Nat) (fl : GenFieldQ) :
    let n' := match fl with | .base (.recv _) => n + 1 | _ => n
    nextCapRecv (vecCap4Of n) n fl = vecCap4Of n' := by
  cases fl with
  | base f =>
    cases f with
    | recv c =>
      dsimp only [nextCapRecv]
      rw [vecCap4Of_succ, vecCap4Push]
      have hle := le_vecCap4Of n
      split_ifs <;> omega
    | _ => rfl
  | _ => rfl

/-- Complete `AllocEvent` trace emitted across `SessionStructure::merge_field` on `flds`,
starting from `(capRecv, curRecvLen)`. -/
def fieldsEventsAux (capRecv curRecvLen : Nat) : List GenFieldQ → List AllocEvent
  | [] => []
  | fl :: rest =>
    let capRecv' := nextCapRecv capRecv curRecvLen fl
    let curRecvLen' := match fl with | .base (.recv _) => curRecvLen + 1 | _ => curRecvLen
    mergeFieldQEvents capRecv curRecvLen fl ++ fieldsEventsAux capRecv' curRecvLen' rest

/-- Complete `AllocEvent` trace of `SessionRecord::deserialize` on `r` (`DeserializeScopeP_Q`). -/
def sessDeserEvents (r : SessionRecord (List (BitVec 8))) : List AllocEvent :=
  fieldsEventsAux 0 0 (recFieldsQ r)

/-- Prefix `AllocEvent` trace after merging the first `k` fields of `recFieldsQ r`. -/
def sessDeserEventsPrefix (r : SessionRecord (List (BitVec 8))) (k : Nat) : List AllocEvent :=
  fieldsEventsAux 0 0 ((recFieldsQ r).take k)

theorem fieldsEventsAux_append (n : Nat) (xs ys : List GenFieldQ) :
    fieldsEventsAux (vecCap4Of n) n (xs ++ ys) =
      fieldsEventsAux (vecCap4Of n) n xs ++
        fieldsEventsAux (vecCap4Of (n + recvCount xs)) (n + recvCount xs) ys := by
  induction xs generalizing n with
  | nil => simp [fieldsEventsAux, recvCount]
  | cons fl rest ih =>
    let n' := match fl with | .base (.recv _) => n + 1 | _ => n
    have hcap : nextCapRecv (vecCap4Of n) n fl = vecCap4Of n' := nextCapRecv_eq_vecCap4Of n fl
    have hcnt : n' + recvCount rest = n + recvCount (fl :: rest) := by
      cases fl with
      | base f => (cases f <;> simp [n', recvCount]); omega
      | _ => simp [n', recvCount]
    simp only [List.cons_append, fieldsEventsAux]
    rw [hcap]
    change mergeFieldQEvents (vecCap4Of n) n fl ++ fieldsEventsAux (vecCap4Of n') n' (rest ++ ys) = _
    rw [ih n', hcnt, List.append_assoc]
    rfl

theorem sessDeserEvents_eq_prefix_append_suffix (r : SessionRecord (List (BitVec 8))) (k : Nat) :
    let n := recvCount ((recFieldsQ r).take k)
    sessDeserEvents r =
      sessDeserEventsPrefix r k ++
        fieldsEventsAux (vecCap4Of n) n ((recFieldsQ r).drop k) := by
  intro n
  unfold sessDeserEvents sessDeserEventsPrefix
  have hsplit : recFieldsQ r = (recFieldsQ r).take k ++ (recFieldsQ r).drop k :=
    (List.take_append_drop k (recFieldsQ r)).symm
  conv_lhs => rw [hsplit]
  change fieldsEventsAux (vecCap4Of 0) 0 ((recFieldsQ r).take k ++ (recFieldsQ r).drop k) = _
  rw [fieldsEventsAux_append 0 ((recFieldsQ r).take k) ((recFieldsQ r).drop k), Nat.zero_add]
  rfl

theorem sessDeserEventsPrefix_succ (r : SessionRecord (List (BitVec 8))) {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    let n := recvCount ((recFieldsQ r).take k)
    sessDeserEventsPrefix r (k + 1) =
      sessDeserEventsPrefix r k ++ mergeFieldQEvents (vecCap4Of n) n ((recFieldsQ r)[k]) := by
  intro n
  unfold sessDeserEventsPrefix
  rw [List.take_succ_eq_append_getElem hk]
  change fieldsEventsAux (vecCap4Of 0) 0 ((recFieldsQ r).take k ++ [(recFieldsQ r)[k]]) = _
  rw [fieldsEventsAux_append 0 ((recFieldsQ r).take k) [(recFieldsQ r)[k]], Nat.zero_add]
  simp [fieldsEventsAux]
  rfl

/-- Final `receiver_chains` capacity `vecCap4Of (recvCount (recFieldsQ r))` produced by
`SessionRecord::deserialize` on `r`. -/
def sessDeserRecvCap (r : SessionRecord (List (BitVec 8))) : Nat :=
  vecCap4Of (recvCount (recFieldsQ r))

/-- Total symbolic small-slot cost of `SessionRecord::deserialize` on `r`. -/
def sessDeserSmallCost (M : AllocCostModel) [HasFineReallocCredit M]
    (r : SessionRecord (List (BitVec 8))) : Nat :=
  ((recFieldsQ r).map (fieldQSmallCost M)).sum + vec104CumOfCap M (sessDeserRecvCap r)

/-- Total symbolic post-deserialize direct-`mmap` live cost of `r`
(equals `ssLargeLive M G` for the canonical output `SessionGhost`). -/
def sessDeserLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (r : SessionRecord (List (BitVec 8))) : Nat :=
  ((recFieldsQ r).map (fieldQLargeLive M)).sum + vec104LargeLive M (sessDeserRecvCap r)

/-- Prefix-aware symbolic transient direct-`mmap` peak across `flds` under `capMaxRecv`. -/
def fieldsPeakAux (M : AllocCostModel) [HasFineReallocCredit M]
    (capMaxRecv capRecv curRecvLen L_acc : Nat) : List GenFieldQ → Nat
  | [] => L_acc + vec104LargeLive M capRecv
  | fl :: rest =>
    let p1 := L_acc + vec104LargeLive M capRecv + fieldQPeakLarge M fl
    let p2 := L_acc + fieldQLargeLive M fl + vec104PeakLarge M capMaxRecv
    let capRecv' := nextCapRecv capRecv curRecvLen fl
    let curRecvLen' := match fl with | .base (.recv _) => curRecvLen + 1 | _ => curRecvLen
    max (max p1 p2)
      (fieldsPeakAux M capMaxRecv capRecv' curRecvLen' (L_acc + fieldQLargeLive M fl) rest)

/-- Total symbolic transient direct-`mmap` peak of `SessionRecord::deserialize` on `r`. -/
def sessDeserPeakLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (r : SessionRecord (List (BitVec 8))) : Nat :=
  fieldsPeakAux M (sessDeserRecvCap r) 0 0 0 (recFieldsQ r)

private theorem vecCap4Of_lt_vecCap4Next (n : Nat) :
    vecCap4Of n < vecCap4Next (vecCap4Of n) := by
  have hp := isPow2Cap4_vecCap4Of n
  rcases hp with h0 | ⟨k, hpow⟩
  · rw [h0]; decide
  · have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hne : vecCap4Of n ≠ 0 := by omega
    unfold vecCap4Next
    simp only [hne, ↓reduceIte]
    omega

/-- Multi-field telescoping bound across `fieldsEventsAux` from `(vecCap4Of n, n)` up to
`capMaxRecv = vecCap4Of (n + recvCount flds)`. -/
theorem stepEvents_fieldsEventsAux_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (n : Nat) (flds : List GenFieldQ) (hOk : ∀ fl ∈ flds, fl.Ok)
    {L₀ L_acc P_bound : Nat} (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L₀ + L_acc + vec104LargeLive M (vecCap4Of n))
    (hpeak : HasFineReallocCredit.peakLarge st ≤ P_bound)
    (hP : L₀ + fieldsPeakAux M (vecCap4Of (n + recvCount flds)) (vecCap4Of n) n L_acc flds ≤ P_bound) :
    let capMax := vecCap4Of (n + recvCount flds)
    let st' := M.stepEvents (fieldsEventsAux (vecCap4Of n) n flds) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (flds.map (fieldQSmallCost M)).sum + vec104CumRem M capMax (vecCap4Of n) ∧
    HasFineReallocCredit.liveLarge st' ≤
      L₀ + (L_acc + (flds.map (fieldQLargeLive M)).sum) + vec104LargeLive M capMax ∧
    HasFineReallocCredit.peakLarge st' ≤ P_bound := by
  induction flds generalizing n L_acc st with
  | nil =>
    simp only [fieldsEventsAux, AllocCostModel.stepEvents_nil, recvCount, Nat.add_zero,
      List.map_nil, List.sum_nil]
    rw [vec104CumRem_self M (vecCap4Of n)]
    exact ⟨by omega, by omega, hpeak⟩
  | cons fl rest ih =>
    let n' := match fl with | .base (.recv _) => n + 1 | _ => n
    let capMax := vecCap4Of (n + recvCount (fl :: rest))
    have hn_cnt : n' + recvCount rest = n + recvCount (fl :: rest) := by
      cases fl with
      | base f => (cases f <;> simp [n', recvCount]); omega
      | _ => simp [n', recvCount]
    have hcap' : nextCapRecv (vecCap4Of n) n fl = vecCap4Of n' := nextCapRecv_eq_vecCap4Of n fl
    have hle_max : vecCap4Of n ≤ capMax := vecCap4Of_le_mono (by omega)
    have hrecv_lt : ∀ c, fl = .base (.recv c) → n = vecCap4Of n → vecCap4Of n < capMax := by
      intro c hfl heq
      subst hfl
      have hlt1 := vecCap4Of_lt_vecCap4Next n
      rw [vecCap4Next_eq_vecCap4Of_succ n heq] at hlt1
      have hle2 : vecCap4Of (n + 1) ≤ capMax := by
        dsimp only [capMax, recvCount]
        exact vecCap4Of_le_mono (by omega)
      omega
    dsimp only [fieldsPeakAux] at hP
    rw [hcap'] at hP
    have hp_max1 : L₀ + max (L_acc + vec104LargeLive M (vecCap4Of n) + fieldQPeakLarge M fl)
        (L_acc + fieldQLargeLive M fl + vec104PeakLarge M capMax) ≤ P_bound :=
      Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) L₀) hP
    have hp_rest : L₀ + fieldsPeakAux M capMax (vecCap4Of n') n'
        (L_acc + fieldQLargeLive M fl) rest ≤ P_bound :=
      Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) L₀) hP
    have hp_fl : (L₀ + L_acc) + vec104LargeLive M (vecCap4Of n) + fieldQPeakLarge M fl ≤ P_bound := by
      have := Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) L₀) hp_max1
      omega
    have hp_grow : (L₀ + L_acc) + fieldQLargeLive M fl + vec104PeakLarge M capMax ≤ P_bound := by
      have := Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) L₀) hp_max1
      omega
    set C_max := HasFineReallocCredit.cumSmall st +
      ((fl :: rest).map (fieldQSmallCost M)).sum + vec104CumRem M capMax (vecCap4Of n)
    have hcum1 : HasFineReallocCredit.cumSmall st + (rest.map (fieldQSmallCost M)).sum +
        fieldQSmallCost M fl + vec104CumRem M capMax (vecCap4Of n) ≤ C_max := by
      simp only [C_max, List.map_cons, List.sum_cons]; omega
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_mergeFieldQ_telescope M
      (hOk fl List.mem_cons_self) h33
      (isPow2Cap4_vecCap4Of n) (isPow2Cap4_vecCap4Of _) hle_max hrecv_lt
      hcum1 (by omega) hpeak hp_fl hp_grow
    rw [hcap'] at hc1 hl1
    change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
    simp only [fieldsEventsAux, AllocCostModel.stepEvents_append]
    rw [hcap']
    change HasFineReallocCredit.cumSmall
        (M.stepEvents (fieldsEventsAux (vecCap4Of n') n' rest)
          (M.stepEvents (mergeFieldQEvents (vecCap4Of n) n fl) st)) ≤ _ ∧
      HasFineReallocCredit.liveLarge
        (M.stepEvents (fieldsEventsAux (vecCap4Of n') n' rest)
          (M.stepEvents (mergeFieldQEvents (vecCap4Of n) n fl) st)) ≤ _ ∧
      HasFineReallocCredit.peakLarge
        (M.stepEvents (fieldsEventsAux (vecCap4Of n') n' rest)
          (M.stepEvents (mergeFieldQEvents (vecCap4Of n) n fl) st)) ≤ _
    set st1 := M.stepEvents (mergeFieldQEvents (vecCap4Of n) n fl) st
    have hP_ih : L₀ + fieldsPeakAux M (vecCap4Of (n' + recvCount rest)) (vecCap4Of n') n'
        (L_acc + fieldQLargeLive M fl) rest ≤ P_bound := by
      change L₀ + fieldsPeakAux M (vecCap4Of (n + recvCount (fl :: rest))) (vecCap4Of n') n'
        (L_acc + fieldQLargeLive M fl) rest ≤ P_bound at hp_rest
      rwa [hn_cnt]
    obtain ⟨hc2, hl2, hp2⟩ := ih n' (fun f hf => hOk f (List.mem_cons_of_mem fl hf))
      st1 (L_acc := L_acc + fieldQLargeLive M fl) (by omega) hp1 hP_ih
    rw [hn_cnt] at hc2 hl2
    have hc_done : HasFineReallocCredit.cumSmall
        (M.stepEvents (fieldsEventsAux (vecCap4Of n') n' rest) st1) ≤ C_max :=
      Nat.le_trans hc2 (by omega)
    dsimp only [C_max, capMax] at hc_done
    simp only [List.map_cons, List.sum_cons] at hc_done ⊢
    exact ⟨hc_done, by omega, hp2⟩

/-- End-to-end symbolic budget theorem for `sessDeserEvents r`:
bounds `cumSmall`, `liveLarge`, and `peakLarge` after stepping all fields of `recFieldsQ r`. -/
theorem stepEvents_sessDeserEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (st₀ : M.σ) :
    let st' := M.stepEvents (sessDeserEvents r) st₀
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st₀ + sessDeserSmallCost M r ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st₀ + sessDeserLargeLive M r ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st₀)
        (HasFineReallocCredit.liveLarge st₀ + sessDeserPeakLarge M r) := by
  have h0 : vecCap4Of 0 = 0 := rfl
  have hll0 : vec104LargeLive M 0 = 0 := vec104LargeLive_zero M
  have hrem0 : vec104CumRem M (vecCap4Of (recvCount (recFieldsQ r))) 0 =
      vec104CumOfCap M (vecCap4Of (recvCount (recFieldsQ r))) :=
    vec104CumRem_zero M _
  set L₀ := HasFineReallocCredit.liveLarge st₀
  set P_bound := max (HasFineReallocCredit.peakLarge st₀) (L₀ + sessDeserPeakLarge M r)
  have h := stepEvents_fieldsEventsAux_bounds M h33 0 (recFieldsQ r) (recFieldsQ_ok r hr)
    (L₀ := L₀) (L_acc := 0) (P_bound := P_bound) st₀
    (by simp [h0, hll0]; omega) (Nat.le_max_left _ _)
    (by simp only [Nat.zero_add, h0]; exact Nat.le_max_right _ _)
  simp only [Nat.zero_add, h0] at h
  change _ ∧ _ ∧ _ at h
  unfold sessDeserEvents sessDeserSmallCost sessDeserLargeLive sessDeserRecvCap
  rw [hrem0] at h
  exact ⟨by omega, by omega, h.2.2⟩

/-! ## 2. Peak Sum Bound, `FreshBytes` Invariant, & Symbolic `2 MiB` Wire-Slice Bounds -/

theorem fieldQLargeLive_le_peakLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (fl : GenFieldQ) :
    fieldQLargeLive M fl ≤ fieldQPeakLarge M fl := by
  cases fl with
  | base f =>
    cases f with
    | sender c =>
      dsimp only [fieldQLargeLive, fieldQPeakLarge, chainMergeLargeLive, chainMergePeakLarge]
      exact vec104LargeLive_le_peakLarge M (vecCap4Of_pow2 _)
    | recv c =>
      dsimp only [fieldQLargeLive, fieldQPeakLarge, chainMergeLargeLive, chainMergePeakLarge]
      exact vec104LargeLive_le_peakLarge M (vecCap4Of_pow2 _)
    | version _ | lik _ | rik _ | root _ | prevCounter _ | pending _ =>
      dsimp only [fieldQLargeLive, fieldQPeakLarge, basicFieldLargeLive, basicFieldPeakLarge]
      split_ifs <;> omega
  | _ =>
    dsimp only [fieldQLargeLive, fieldQPeakLarge, basicFieldLargeLive, basicFieldPeakLarge]
    split_ifs <;> omega

theorem fieldsPeakAux_le_sum (M : AllocCostModel) [HasFineReallocCredit M]
    {capMaxRecv : Nat} (hpow : IsPow2Cap4 capMaxRecv)
    (n L_acc : Nat) (flds : List GenFieldQ)
    (hmax : vecCap4Of (n + recvCount flds) ≤ capMaxRecv) :
    fieldsPeakAux M capMaxRecv (vecCap4Of n) n L_acc flds ≤
      L_acc + (flds.map (fieldQPeakLarge M)).sum + vec104PeakLarge M capMaxRecv := by
  induction flds generalizing n L_acc with
  | nil =>
    simp only [fieldsPeakAux, List.map_nil, List.sum_nil, Nat.add_zero]
    simp only [recvCount, Nat.add_zero] at hmax
    have h1 := Nat.le_trans (vec104LargeLive_le_peakLarge M (vecCap4Of_pow2 n))
      (vec104PeakLarge_le_of_pow2 M (vecCap4Of_pow2 n) hpow hmax)
    omega
  | cons fl rest ih =>
    let n' := match fl with | .base (.recv _) => n + 1 | _ => n
    have hn_cnt : n' + recvCount rest = n + recvCount (fl :: rest) := by
      cases fl with
      | base f => (cases f <;> simp [n', recvCount]); omega
      | _ => simp [n', recvCount]
    have hcap' : nextCapRecv (vecCap4Of n) n fl = vecCap4Of n' := nextCapRecv_eq_vecCap4Of n fl
    have hle_n : vecCap4Of n ≤ capMaxRecv :=
      Nat.le_trans (vecCap4Of_le_mono (by omega)) hmax
    have hll_n : vec104LargeLive M (vecCap4Of n) ≤ vec104PeakLarge M capMaxRecv :=
      Nat.le_trans (vec104LargeLive_le_peakLarge M (vecCap4Of_pow2 n))
        (vec104PeakLarge_le_of_pow2 M (vecCap4Of_pow2 n) hpow hle_n)
    have hfl_le := fieldQLargeLive_le_peakLarge M fl
    have hmax' : vecCap4Of (n' + recvCount rest) ≤ capMaxRecv := by
      rw [hn_cnt]; exact hmax
    have hih := ih n' (L_acc + fieldQLargeLive M fl) hmax'
    dsimp only [fieldsPeakAux]
    rw [hcap']
    change max (max (L_acc + vec104LargeLive M (vecCap4Of n) + fieldQPeakLarge M fl)
        (L_acc + fieldQLargeLive M fl + vec104PeakLarge M capMaxRecv))
        (fieldsPeakAux M capMaxRecv (vecCap4Of n') n' (L_acc + fieldQLargeLive M fl) rest) ≤ _
    simp only [List.map_cons, List.sum_cons]
    refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨by omega, by omega⟩, by omega⟩

theorem sessDeserPeakLarge_le_sum (M : AllocCostModel) [HasFineReallocCredit M]
    (r : SessionRecord (List (BitVec 8))) :
    sessDeserPeakLarge M r ≤
      ((recFieldsQ r).map (fieldQPeakLarge M)).sum + vec104PeakLarge M (sessDeserRecvCap r) := by
  unfold sessDeserPeakLarge sessDeserRecvCap
  have h := fieldsPeakAux_le_sum M (vecCap4Of_pow2 (recvCount (recFieldsQ r)))
    0 0 (recFieldsQ r) (by simp)
  simpa using h

private theorem foldl_lik_empty_of_tag_ne_2 (v0 : SSGQ) (h0 : v0.base.lik = [])
    (xs : List GenFieldQ) (hxs : ∀ fl ∈ xs, fl.tag ≠ 2) :
    (xs.foldl SSGQ.apply v0).base.lik = [] := by
  induction xs generalizing v0 with
  | nil => exact h0
  | cons fl rest ih =>
    apply ih (SSGQ.apply v0 fl) ?_ (fun f hf => hxs f (List.mem_cons_of_mem fl hf))
    have hne := hxs fl List.mem_cons_self
    cases fl with
    | base f =>
      cases f with
      | lik _ => exact False.elim (hne rfl)
      | _ => exact h0
    | _ => exact h0

private theorem foldl_rik_empty_of_tag_ne_3 (v0 : SSGQ) (h0 : v0.base.rik = [])
    (xs : List GenFieldQ) (hxs : ∀ fl ∈ xs, fl.tag ≠ 3) :
    (xs.foldl SSGQ.apply v0).base.rik = [] := by
  induction xs generalizing v0 with
  | nil => exact h0
  | cons fl rest ih =>
    apply ih (SSGQ.apply v0 fl) ?_ (fun f hf => hxs f (List.mem_cons_of_mem fl hf))
    have hne := hxs fl List.mem_cons_self
    cases fl with
    | base f =>
      cases f with
      | rik _ => exact False.elim (hne rfl)
      | _ => exact h0
    | _ => exact h0

private theorem foldl_root_empty_of_tag_ne_4 (v0 : SSGQ) (h0 : v0.base.root = [])
    (xs : List GenFieldQ) (hxs : ∀ fl ∈ xs, fl.tag ≠ 4) :
    (xs.foldl SSGQ.apply v0).base.root = [] := by
  induction xs generalizing v0 with
  | nil => exact h0
  | cons fl rest ih =>
    apply ih (SSGQ.apply v0 fl) ?_ (fun f hf => hxs f (List.mem_cons_of_mem fl hf))
    have hne := hxs fl List.mem_cons_self
    cases fl with
    | base f =>
      cases f with
      | root _ => exact False.elim (hne rfl)
      | _ => exact h0
    | _ => exact h0

private theorem filter_tag_base_recv_nil (cs : List ReceiverChain) (t : Nat)
    (ht : t ≠ 7) :
    ((cs.map (fun c => GenFieldQ.base (.recv (recvChainG c)))).filter
      (fun fl => fl.tag == t)) = [] := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have hneq : ((GenFieldQ.base (.recv (recvChainG c))).tag == t) = false := by
      simp [GenFieldQ.tag, GenField.tag, beq_eq_false_iff_ne, ht.symm]
    simp [List.filter, hneq, ih]

private theorem filter_tag_pendingFieldX_nil (pOpt : Option PendingPreKey) (t : Nat)
    (ht : t ≠ 9) :
    (((CryptoVerification.E2E.Record.L1GX.pendingFieldX pOpt).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).filter
      (fun fl => fl.tag == t)) = [] := by
  rcases pOpt with _ | p
  · rfl
  · dsimp only [CryptoVerification.E2E.Record.L1GX.pendingFieldX]
    split_ifs
    · rcases p.preKeyId with _ | i <;>
        simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
          GenFieldQ.tag, GenField.tag, List.filter, beq_eq_false_iff_ne, ht.symm]
    · simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
        GenFieldQ.tag, List.filter, beq_eq_false_iff_ne, ht.symm]

private theorem filter_tag_eq_zero_of_ne {xs : List GenFieldQ} {t : Nat}
    (h : ∀ fl ∈ xs, fl.tag ≠ t) :
    (xs.filter (fun fl => fl.tag == t)).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro fl hfl
  simp [beq_iff_eq, h fl hfl]

set_option maxHeartbeats 800000 in
private theorem filter_tag_le_one_recFieldsQ
    (r : SessionRecord (List (BitVec 8))) (t : Nat) (ht : t = 2 ∨ t = 3 ∨ t = 4) :
    ((recFieldsQ r).filter (fun fl => fl.tag == t)).length ≤ 1 := by
  unfold recFieldsQ
  rcases r.currentSession with _ | s
  · simp
  · dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ,
      CryptoVerification.E2E.Record.L1GX.genFieldsX,
      CryptoVerification.E2E.Record.DeserializeGeneral.genFields, clearPqSession]
    have ht7 : t ≠ 7 := by omega
    have ht9 : t ≠ 9 := by omega
    have hrecv := filter_tag_base_recv_nil s.state.receiverChains t ht7
    have hpend := filter_tag_pendingFieldX_nil s.pendingPreKey t ht9
    have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
        CryptoVerification.E2E.Record.L1GX.GenFieldX.base) = GenFieldQ.base := by
      funext f; rfl
    have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
        CryptoVerification.E2E.Record.L1GX.GenFieldX.base ∘
        fun c => GenField.recv (recvChainG c)) =
        (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
      funext c; rfl
    simp only [List.map_append, List.map_map, hfn_recv, hfn, List.filter_append, List.length_append,
      ↓reduceIte, List.filter_nil, List.length_nil]
    rw [hrecv, hpend]
    have hz1 : (((if s.state.sessionVersion = 0 then []
        else [GenField.version s.state.sessionVersion]).map GenFieldQ.base).filter
        (fun fl => fl.tag == t)).length = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hz5 : (((if s.state.previousCounter = 0 then []
        else [GenField.prevCounter s.state.previousCounter]).map GenFieldQ.base).filter
        (fun fl => fl.tag == t)).length = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hz10 : (((if s.remoteRegistrationId = 0 then []
        else [CryptoVerification.E2E.Record.L1GX.GenFieldX.remReg s.remoteRegistrationId]).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).filter
        (fun fl => fl.tag == t)).length = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.tag]; omega
    have hz11 : (((if s.localRegistrationId = 0 then []
        else [CryptoVerification.E2E.Record.L1GX.GenFieldX.locReg s.localRegistrationId]).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).filter
        (fun fl => fl.tag == t)).length = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.tag]; omega
    have hz13 : (((if s.aliceBaseKey = [] then []
        else [CryptoVerification.E2E.Record.L1GX.GenFieldX.abk s.aliceBaseKey]).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).filter
        (fun fl => fl.tag == t)).length = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.tag]; omega
    have hz15b : (((if s.state.pqRatchetState = [] then []
        else [GenFieldQ.pq s.state.pqRatchetState]).filter
        (fun fl => fl.tag == t)).length) = 0 := by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag]; omega
    have hz_sc : ∀ c : SenderChain,
        (([GenField.sender (senderChainG c)].map GenFieldQ.base).filter
          (fun fl => fl.tag == t)).length = 0 := fun c => by
      refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
      subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hz_ky : ∀ k : PendingKyberPreKey,
        (([CryptoVerification.E2E.Record.L1GX.GenFieldX.kyber k.preKeyId k.ciphertext].map
          Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).filter
          (fun fl => fl.tag == t)).length = 0 := fun k => by
      refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
      subst hfl; dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.tag]; omega
    have hlik_ne : ∀ u : Nat, u ≠ 2 →
        (((if s.state.localIdentity.serialize = [] then []
          else [GenField.lik s.state.localIdentity.serialize]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length = 0 := fun u hu => by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hrik_ne : ∀ (ik : IdentityKey) (u : Nat), u ≠ 3 →
        (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length = 0 := fun ik u hu => by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hroot_ne : ∀ u : Nat, u ≠ 4 →
        (((if keyToBytes32 s.state.rootKey = [] then []
          else [GenField.root (keyToBytes32 s.state.rootKey)]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length = 0 := fun u hu => by
      split_ifs
      · rfl
      · refine filter_tag_eq_zero_of_ne fun fl hfl => ?_
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hfl
        subst hfl; dsimp only [GenFieldQ.tag, GenField.tag]; omega
    have hlik_le : ∀ u : Nat,
        (((if s.state.localIdentity.serialize = [] then []
          else [GenField.lik s.state.localIdentity.serialize]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length ≤ 1 := fun u =>
      Nat.le_trans (List.length_filter_le _ _) (by split_ifs <;> simp)
    have hrik_le : ∀ (ik : IdentityKey) (u : Nat),
        (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length ≤ 1 := fun ik u =>
      Nat.le_trans (List.length_filter_le _ _) (by split_ifs <;> simp)
    have hroot_le : ∀ u : Nat,
        (((if keyToBytes32 s.state.rootKey = [] then []
          else [GenField.root (keyToBytes32 s.state.rootKey)]).map GenFieldQ.base).filter
          (fun fl => fl.tag == u)).length ≤ 1 := fun u =>
      Nat.le_trans (List.length_filter_le _ _) (by split_ifs <;> simp)
    rw [hz1, hz5, hz10, hz11, hz13, hz15b]
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add]
    rcases s.state.senderChain with _ | c <;>
      rcases s.pendingKyberPreKey with _ | k <;>
      simp only [List.map_nil, List.filter_nil, List.length_nil, hz_sc, hz_ky,
        Nat.add_zero, Nat.zero_add]
    all_goals
      rcases ht with rfl | rfl | rfl
      · have h1 := hlik_le 2
        have h3 := hroot_ne 2 (by decide)
        rcases s.state.remoteIdentity with _ | ik
        · simp only [List.map_nil, List.filter_nil, List.length_nil, h3]; omega
        · have h2 := hrik_ne ik 2 (by decide)
          dsimp only; rw [h2, h3]; omega
      · have h1 := hlik_ne 3 (by decide)
        have h3 := hroot_ne 3 (by decide)
        rcases s.state.remoteIdentity with _ | ik
        · simp only [List.map_nil, List.filter_nil, List.length_nil, h1, h3]; omega
        · have h2 := hrik_le ik 3
          dsimp only; rw [h1, h3]; omega
      · have h1 := hlik_ne 4 (by decide)
        have h3 := hroot_le 4
        rcases s.state.remoteIdentity with _ | ik
        · simp only [List.map_nil, List.filter_nil, List.length_nil, h1]; omega
        · have h2 := hrik_ne ik 4 (by decide)
          dsimp only; rw [h1, h2]; omega

private theorem not_tag_mem_take_of_filter_le_one {xs : List GenFieldQ} {t k : Nat}
    (hflt : (xs.filter (fun fl => fl.tag == t)).length ≤ 1)
    (hk : k < xs.length) (htag : xs[k].tag = t) :
    ∀ fl ∈ xs.take k, fl.tag ≠ t := by
  have hsplit : xs = xs.take k ++ (xs[k] :: xs.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : ((xs.take k).filter (fun fl => fl.tag == t)).length = 0 := by
    conv at hflt => lhs; rw [hsplit]
    simp only [List.filter_append, List.filter_cons, htag, beq_self_eq_true, ↓reduceIte,
      List.length_append, List.length_cons] at hflt
    omega
  intro fl hmem hfl
  have hmem_f : fl ∈ (xs.take k).filter (fun fl => fl.tag == t) :=
    List.mem_filter.2 ⟨hmem, beq_iff_eq.2 hfl⟩
  have hpos := List.length_pos_of_mem hmem_f
  omega

/-- Every field `recFieldsQ r[k]` satisfies `GenFieldQ.FreshBytes (ssgqAfter r k)`. -/
theorem freshBytes_ssgqAfter
    (r : SessionRecord (List (BitVec 8))) {k : Nat} (hk : k < (recFieldsQ r).length) :
    GenFieldQ.FreshBytes (ssgqAfter r k) ((recFieldsQ r)[k]) := by
  generalize hfl : (recFieldsQ r)[k] = fl
  cases fl with
  | base f =>
    cases f with
    | lik b =>
      dsimp only [GenFieldQ.FreshBytes, ssgqAfter]
      refine foldl_lik_empty_of_tag_ne_2 SSGQ.empty rfl _ ?_
      exact not_tag_mem_take_of_filter_le_one
        (filter_tag_le_one_recFieldsQ r 2 (Or.inl rfl)) hk (by rw [hfl]; rfl)
    | rik b =>
      dsimp only [GenFieldQ.FreshBytes, ssgqAfter]
      refine foldl_rik_empty_of_tag_ne_3 SSGQ.empty rfl _ ?_
      exact not_tag_mem_take_of_filter_le_one
        (filter_tag_le_one_recFieldsQ r 3 (Or.inr (Or.inl rfl))) hk (by rw [hfl]; rfl)
    | root b =>
      dsimp only [GenFieldQ.FreshBytes, ssgqAfter]
      refine foldl_root_empty_of_tag_ne_4 SSGQ.empty rfl _ ?_
      exact not_tag_mem_take_of_filter_le_one
        (filter_tag_le_one_recFieldsQ r 4 (Or.inr (Or.inr rfl))) hk (by rw [hfl]; rfl)
    | _ => trivial
  | _ => trivial

private theorem length_le_flatMap_of_mem {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | hm
    · omega
    · have := ih hm; omega

private theorem pq_length_le_encodeRecord {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length ≤ (encodeRecord r).length := by
  by_cases hpq : s.state.pqRatchetState = []
  · simp [hpq]
  · have hmem : GenFieldQ.pq s.state.pqRatchetState ∈ recFieldsQ r := by
      simp only [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ, hpq, ↓reduceIte,
        List.mem_append, List.mem_singleton, or_true]
    have h1 := length_le_flatMap_of_mem GenFieldQ.enc hmem
    have henc_pq : s.state.pqRatchetState.length ≤
        (GenFieldQ.pq s.state.pqRatchetState).enc.length := by
      simp only [GenFieldQ.enc, GenFieldQ.payload, List.length_append]
      omega
    have henc_rec := encodeRecord_eq_recFieldsQ r hr
    rw [henc_rec]
    simp only [List.length_append]
    omega

set_option maxHeartbeats 400000 in
private theorem recvCount_recFieldsQ_le {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r) :
    recvCount (recFieldsQ r) ≤ 5 := by
  obtain ⟨_, s, hs, hscope⟩ := hr
  have h5 : s.state.receiverChains.length ≤ 5 := hscope.1
  have hmap_cnt : ∀ cs : List ReceiverChain,
      recvCount (cs.map (fun c => GenFieldQ.base (.recv (recvChainG c)))) = cs.length := by
    intro cs; induction cs with
    | nil => rfl
    | cons _ _ ih => simp [recvCount, ih]; omega
  have hpend_cnt : recvCount
      ((CryptoVerification.E2E.Record.L1GX.pendingFieldX s.pendingPreKey).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    rcases s.pendingPreKey with _ | p
    · rfl
    · dsimp only [CryptoVerification.E2E.Record.L1GX.pendingFieldX]
      split_ifs
      · rcases p.preKeyId with _ | i <;> rfl
      · rfl
  have hc1 : recvCount ((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc2 : recvCount ((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc3 : ∀ ik : IdentityKey,
      recvCount ((if ik.serialize = [] then []
        else [GenField.rik ik.serialize]).map GenFieldQ.base) = 0 := fun _ => by
    split_ifs <;> rfl
  have hc4 : recvCount ((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc5 : recvCount ((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc6 : ∀ c : SenderChain,
      recvCount ([GenField.sender (senderChainG c)].map GenFieldQ.base) = 0 := fun _ => rfl
  have hc10 : recvCount ((if s.remoteRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.remReg s.remoteRegistrationId]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc11 : recvCount ((if s.localRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.locReg s.localRegistrationId]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc13 : recvCount ((if s.aliceBaseKey = [] then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.abk s.aliceBaseKey]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc14 : ∀ ky : PendingKyberPreKey,
      recvCount ([CryptoVerification.E2E.Record.L1GX.GenFieldX.kyber ky.preKeyId ky.ciphertext].map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := fun _ => rfl
  have hc15 : recvCount (if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]) = 0 := by
    split_ifs <;> rfl
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base) = GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  unfold recFieldsQ
  rw [hs]
  dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ,
    CryptoVerification.E2E.Record.L1GX.genFieldsX,
    CryptoVerification.E2E.Record.DeserializeGeneral.genFields, clearPqSession]
  simp only [List.map_append, List.map_map, hfn_recv, hfn, recvCount_append,
    ↓reduceIte, List.map_nil]
  rw [hmap_cnt, hpend_cnt, hc1, hc2, hc4, hc5, hc10, hc11, hc13, hc15]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | sc <;>
    rcases s.pendingKyberPreKey with _ | ky <;>
    simp only [List.map_nil, hc3, hc6, hc14, show recvCount [] = 0 from rfl] <;>
    omega

private theorem noPq_fieldQPeakLarge_eq_zero (M : AllocCostModel) [HasFineReallocCredit M]
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    {fx : CryptoVerification.E2E.Record.L1GX.GenFieldX}
    (hnpq : Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.NoPq fx)
    (hok : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ fx).Ok)
    (hnot_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ fx).tag ≠ 7) :
    fieldQPeakLarge M (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ fx) = 0 := by
  cases fx with
  | pq _ => cases hnpq
  | base f =>
    cases f with
    | recv _ => exact False.elim (hnot_recv rfl)
    | sender c =>
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok,
        GenField.Ok] at hok
      rw [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        chainMergePeakLarge, hok.2.2.2, List.length_nil]
      have h0 : vecCap4Of 0 = 0 := rfl
      rw [h0]; unfold vec104PeakLarge vec104LargeLive; simp
    | version _ | prevCounter _ =>
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
      simp
    | lik b | rik b | pending b =>
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok,
        GenField.Ok] at hok
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
      have hle : b.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
      simp [hle]
    | root b =>
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok,
        GenField.Ok] at hok
      dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
      have hle : b.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
      simp [hle]
  | pendingId _ k =>
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok] at hok
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
      basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
    have hle : k.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp [hle]
  | pendingSpk _ k _ =>
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok] at hok
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
      basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
    have hle : k.length ≤ HasFineReallocCredit.smallMaxReq M := by have := hok.1; omega
    simp [hle]
  | remReg _ | locReg _ =>
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
      basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
    simp
  | abk b =>
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok] at hok
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
      basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
    have hle : b.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp [hle]
  | kyber _ ct =>
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, GenFieldQ.Ok] at hok
    dsimp only [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
      basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
    have hle : ct.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp [hle]

private theorem vec104PeakLarge_eq_zero_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : Nat) (h : cap * 104 ≤ HasFineReallocCredit.smallMaxReq M) :
    vec104PeakLarge M cap = 0 := by
  unfold vec104PeakLarge
  split_ifs with h4 h8
  · rfl
  · unfold vec104LargeLive
    have h4le : 4 * 104 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp [h4le]
  · have hdiv : (cap / 2) * 104 ≤ HasFineReallocCredit.smallMaxReq M := by
      have hle : cap / 2 ≤ cap := Nat.div_le_self cap 2
      exact Nat.le_trans (Nat.mul_le_mul_right 104 hle) h
    have hih := vec104PeakLarge_eq_zero_of_le M (cap / 2) hdiv
    have hl1 : vec104LargeLive M (cap / 2) = 0 := by unfold vec104LargeLive; simp [hdiv]
    have hl2 : vec104LargeLive M cap = 0 := by unfold vec104LargeLive; simp [h]
    simp [hih, hl1, hl2]
termination_by cap
decreasing_by omega

private theorem vec104PeakLarge_recvChain_le (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat}
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {rc : ReceiverChain} (hmk : rc.messageKeys.length ≤ maxMessageKeys) :
    fieldQPeakLarge M (.base (.recv (recvChainG rc))) ≤ 2048 * 104 + cLarge := by
  have h2000 : rc.messageKeys.length ≤ 2000 := hmk
  have hcap : vecCap4Of rc.messageKeys.length ≤ 2048 := by
    have h1 := vecCap4Of_le_mono h2000
    have h2 : vecCap4Of 2000 = 2048 := by decide
    omega
  dsimp only [fieldQPeakLarge, chainMergePeakLarge, recvChainG]
  refine Nat.le_trans
    (vec104PeakLarge_le_of_pow2 M (vecCap4Of_pow2 _) (Or.inr ⟨9, by decide⟩) hcap) ?_
  conv_lhs => unfold vec104PeakLarge
  have h1 : ¬ (2048 < 4) := by decide
  have h2 : ¬ (2048 < 8) := by decide
  have hdiv : 2048 / 2 = 1024 := by decide
  simp only [h1, h2, hdiv, ↓reduceIte]
  rw [vec104PeakLarge_eq_zero_of_le M 1024 hsplit]
  have hl1024 : vec104LargeLive M 1024 = 0 := by unfold vec104LargeLive; simp [hsplit]
  rw [hl1024, Nat.zero_add, Nat.zero_max]
  unfold vec104LargeLive
  by_cases hs : 2048 * 104 ≤ HasFineReallocCredit.smallMaxReq M
  · simp [hs]
  · simp only [hs, ↓reduceIte]
    exact hlarge (2048 * 104) (by omega)

private theorem sum_recvChains_peakLarge_le (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat}
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    (cs : List ReceiverChain) (hmk : ∀ rc ∈ cs, rc.messageKeys.length ≤ maxMessageKeys) :
    ((cs.map (fun rc => GenFieldQ.base (.recv (recvChainG rc)))).map
      (fieldQPeakLarge M)).sum ≤ cs.length * (2048 * 104 + cLarge) := by
  induction cs with
  | nil => simp
  | cons rc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := vec104PeakLarge_recvChain_le M hsplit hlarge (hmk rc List.mem_cons_self)
    have h2 := ih (fun c hc => hmk c (List.mem_cons_of_mem rc hc))
    omega

private theorem sum_map_le_sum_map {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private theorem serialize_pk_length_cap (pk : PublicKey) :
    pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

private theorem serialize_ik_length_cap (ik : IdentityKey) :
    ik.serialize.length = 33 :=
  serialize_pk_length_cap ik.publicKey

set_option maxHeartbeats 800000 in
private theorem sum_genFieldsX_clearPq_peakLarge_le (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat}
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    (((CryptoVerification.E2E.Record.L1GX.genFieldsX (clearPqSession s)).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).map (fieldQPeakLarge M)).sum ≤
      5 * (2048 * 104 + cLarge) := by
  have hok_all := recFieldsQ_ok r hr
  have hmem_sub : ∀ fl ∈ (CryptoVerification.E2E.Record.L1GX.genFieldsX (clearPqSession s)).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fl ∈ recFieldsQ r := by
    intro fl hfl
    simp only [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ, List.mem_append]
    exact Or.inl hfl
  have ⟨⟨_, _, hr_repr⟩, s', hs', hscope⟩ := hr
  have hss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst hss'
  have h5 : s.state.receiverChains.length ≤ 5 := hscope.1
  have hmk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys :=
    (hr_repr s hs).1
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hle33 : 33 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hroot_len : keyToBytes32 s.state.rootKey ≠ [] →
      (keyToBytes32 s.state.rootKey).length = 32 := fun he => by
    apply hok_all (.base (.root (keyToBytes32 s.state.rootKey)))
    apply hmem_sub
    rw [List.mem_map]
    refine ⟨.base (.root (keyToBytes32 s.state.rootKey)), ?_, rfl⟩
    simp [CryptoVerification.E2E.Record.L1GX.genFieldsX,
      CryptoVerification.E2E.Record.DeserializeGeneral.genFields, clearPqSession, he]
  have habk_len : s.aliceBaseKey ≠ [] → s.aliceBaseKey.length = 33 := fun he => by
    apply hok_all (.abk s.aliceBaseKey)
    apply hmem_sub
    rw [List.mem_map]
    refine ⟨.abk s.aliceBaseKey, ?_, rfl⟩
    simp [CryptoVerification.E2E.Record.L1GX.genFieldsX, clearPqSession, he]
  dsimp only [CryptoVerification.E2E.Record.L1GX.genFieldsX,
    CryptoVerification.E2E.Record.DeserializeGeneral.genFields, clearPqSession]
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base) = GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  simp only [List.map_append, List.map_map, hfn_recv, hfn, List.sum_append,
    ↓reduceIte, List.map_nil, List.sum_nil]
  have hrecv := Nat.le_trans
    (sum_recvChains_peakLarge_le M hsplit hlarge s.state.receiverChains hmk)
    (Nat.mul_le_mul_right (2048 * 104 + cLarge) h5)
  have hpend0 : (((CryptoVerification.E2E.Record.L1GX.pendingFieldX s.pendingPreKey).map
      (fieldQPeakLarge M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    rcases s.pendingPreKey with _ | p
    · rfl
    · dsimp only [CryptoVerification.E2E.Record.L1GX.pendingFieldX]
      split_ifs
      · rcases p.preKeyId with _ | i <;>
          simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
            basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen,
            serialize_pk_length_cap p.baseKey, hle33]
      · simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
          basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen,
          serialize_pk_length_cap p.baseKey, hle33]
  have h1 : (((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map
      (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
  have h2 : (((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map
      (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen,
      serialize_ik_length_cap s.state.localIdentity, hle33]
  have h4 : (((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map
      (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs with he
    · rfl
    · simp [fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen,
        hroot_len he, hle32]
  have h5_pc : (((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map
      (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
  have h10 : (((if s.remoteRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.remReg s.remoteRegistrationId]).map
      (fieldQPeakLarge M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
  have h11 : (((if s.localRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.locReg s.localRegistrationId]).map
      (fieldQPeakLarge M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
  have h13 : (((if s.aliceBaseKey = [] then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.abk s.aliceBaseKey]).map
      (fieldQPeakLarge M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs with he
    · rfl
    · simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen, habk_len he, hle33]
  have hrik_p0 : ∀ ik : IdentityKey,
      (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map
        (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 := fun ik => by
    split_ifs <;> simp [fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen,
      serialize_ik_length_cap ik, hle33]
  have hsc_p0 : ∀ c : SenderChain,
      (([GenField.sender (senderChainG c)].map (fieldQPeakLarge M ∘ GenFieldQ.base)).sum) = 0 :=
    fun c => by
      simp [fieldQPeakLarge, chainMergePeakLarge, senderChainG, show vecCap4Of 0 = 0 from rfl]
  have hky_p0 : ∀ k : PendingKyberPreKey, s.pendingKyberPreKey = some k →
      (([CryptoVerification.E2E.Record.L1GX.GenFieldX.kyber k.preKeyId k.ciphertext].map
        (fieldQPeakLarge M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 :=
    fun k hk_eq => by
      have hlen1569 : k.ciphertext.length = 1569 := hscope.2.2.1 k hk_eq
      have hle1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M := by omega
      simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQPeakLarge,
        basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen, hlen1569, hle1569]
  simp only [List.map_map] at hrecv
  rw [h1, h2, h4, h5_pc, hpend0, h10, h11, h13]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | c <;>
    rcases hky : s.pendingKyberPreKey with _ | k
  all_goals
    try (have hky0 := hky_p0 _ hky; simp only [hky0])
    simp only [List.map_nil, List.sum_nil, hrik_p0, hsc_p0]
    omega

/-- Symbolic post-deserialize large-`mmap` live bound for any decodable wire slice
`|encodeRecord r| ≤ 2 ^ 21` on `DeserializeScopeP_Q NonEmptyV1Q`:
bounded by `(2 ^ 21 + 5 * 2048 * 104) + 6 * cLarge` (`= 3,162,112 + 6 * cLarge`, well below the
wire-universal `2 ^ 20 * 104 + cLarge` envelope `109,060,343` B in Tier T2 `cLarge = 8,439`). -/
theorem sessDeserLargeLive_le_of_encode_le_2MiB
    (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat} (_hc : 208 ≤ cLarge)
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserLargeLive M r ≤ (2 ^ 21 + 5 * 2048 * 104) + 6 * cLarge := by
  have ⟨_, s, hs, _⟩ := hr
  have hpq_le : s.state.pqRatchetState.length ≤ 2 ^ 21 :=
    Nat.le_trans (pq_length_le_encodeRecord hr hs) hlen
  have hrc_cap : sessDeserRecvCap r ≤ 8 := by
    unfold sessDeserRecvCap
    have h1 := vecCap4Of_le_mono (recvCount_recFieldsQ_le hr)
    have h2 : vecCap4Of 5 = 8 := by decide
    omega
  have hrc0 : vec104LargeLive M (sessDeserRecvCap r) = 0 := by
    unfold vec104LargeLive
    have hsm : sessDeserRecvCap r * 104 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp [hsm]
  have hpre_peak := sum_genFieldsX_clearPq_peakLarge_le M hsplit hlarge hr hs
  have hpre_live : (((CryptoVerification.E2E.Record.L1GX.genFieldsX (clearPqSession s)).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ).map (fieldQLargeLive M)).sum ≤
      5 * (2048 * 104 + cLarge) :=
    Nat.le_trans (sum_map_le_sum_map _ _ _ (fun fl _ => fieldQLargeLive_le_peakLarge M fl)) hpre_peak
  have hpq_live : (((if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]).map (fieldQLargeLive M)).sum) ≤
      2 ^ 21 + cLarge := by
    split_ifs with he
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        fieldQLargeLive, basicFieldLargeLive, MergeFieldBasicBudget.basicFieldByteLen]
      by_cases hsm : s.state.pqRatchetState.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp [hsm]
      · simp only [hsm, ↓reduceIte]
        have := hlarge s.state.pqRatchetState.length (by omega)
        omega
  unfold sessDeserLargeLive
  rw [hrc0, Nat.add_zero]
  have hrec : recFieldsQ r =
      (CryptoVerification.E2E.Record.L1GX.genFieldsX (clearPqSession s)).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ++
      (if s.state.pqRatchetState = [] then [] else [GenFieldQ.pq s.state.pqRatchetState]) := by
    simp [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ, clearPqSession]
  rw [hrec, List.map_append, List.sum_append]
  omega

/-- Symbolic transient `realloc` peak large-`mmap` bound during
`SessionRecord::deserialize` at `|encodeRecord r| ≤ 2 ^ 21` on `DeserializeScopeP_Q NonEmptyV1Q`:
bounded by `(2 * 2 ^ 21 + 5 * 2048 * 104) + 7 * cLarge` (`= 5,259,264 + 7 * cLarge`, well below
the wire-universal `163,594,734` B envelope in Tier T2 `cLarge = 8,439`). -/
theorem sessDeserPeakLarge_le_of_encode_le_2MiB
    (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat} (_hc : 208 ≤ cLarge)
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserPeakLarge M r ≤ (2 * 2 ^ 21 + 5 * 2048 * 104) + 7 * cLarge := by
  have ⟨_, s, hs, _⟩ := hr
  have hpq_le : s.state.pqRatchetState.length ≤ 2 ^ 21 :=
    Nat.le_trans (pq_length_le_encodeRecord hr hs) hlen
  have hrc_cap : sessDeserRecvCap r ≤ 8 := by
    unfold sessDeserRecvCap
    have h1 := vecCap4Of_le_mono (recvCount_recFieldsQ_le hr)
    have h2 : vecCap4Of 5 = 8 := by decide
    omega
  have hrc0 : vec104PeakLarge M (sessDeserRecvCap r) = 0 :=
    vec104PeakLarge_eq_zero_of_le M (sessDeserRecvCap r) (by omega)
  have hpre_peak := sum_genFieldsX_clearPq_peakLarge_le M hsplit hlarge hr hs
  have hpq_peak : (((if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]).map (fieldQPeakLarge M)).sum) ≤
      2 * (2 ^ 21 + cLarge) := by
    split_ifs with he
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        fieldQPeakLarge, basicFieldPeakLarge, MergeFieldBasicBudget.basicFieldByteLen]
      by_cases hsm : s.state.pqRatchetState.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp [hsm]
      · simp only [hsm, ↓reduceIte]
        have := hlarge s.state.pqRatchetState.length (by omega)
        omega
  refine Nat.le_trans (sessDeserPeakLarge_le_sum M r) ?_
  rw [hrc0, Nat.add_zero]
  have hrec : recFieldsQ r =
      (CryptoVerification.E2E.Record.L1GX.genFieldsX (clearPqSession s)).map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ++
      (if s.state.pqRatchetState = [] then [] else [GenFieldQ.pq s.state.pqRatchetState]) := by
    simp [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ, clearPqSession]
  rw [hrec, List.map_append, List.sum_append]
  omega

/-- Corollary comparing `sessDeserLargeLive M r` against the universal wire-slice envelope
`2 ^ 20 * 104 + cLarge` (`109,060,343` B at Tier T2 `cLarge = 8,439`). -/
theorem sessDeserLargeLive_le_universal_envelope
    (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat} (hc : 208 ≤ cLarge) (hc_hi : cLarge ≤ 1024 * 104)
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserLargeLive M r ≤ 2 ^ 20 * 104 + cLarge := by
  have h := sessDeserLargeLive_le_of_encode_le_2MiB M hc hsplit hlarge hr hlen
  omega

/-- Corollary comparing `sessDeserPeakLarge M r` against the universal wire-slice envelope
`2 ^ 20 * 104 + 2 ^ 19 * 104 + 2 * cLarge` (`163,594,734` B at Tier T2 `cLarge = 8,439`). -/
theorem sessDeserPeakLarge_le_universal_envelope
    (M : AllocCostModel) [HasFineReallocCredit M]
    {cLarge : Nat} (hc : 208 ≤ cLarge) (hc_hi : cLarge ≤ 1024 * 104)
    (hsplit : 1024 * 104 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlarge : ∀ req : Nat, HasFineReallocCredit.smallMaxReq M < req →
      HasFineReallocCredit.largeCost M req ≤ req + cLarge)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2 ^ 21) :
    sessDeserPeakLarge M r ≤ 2 ^ 20 * 104 + 2 ^ 19 * 104 + 2 * cLarge := by
  have h := sessDeserPeakLarge_le_of_encode_le_2MiB M hc hsplit hlarge hr hlen
  omega


/-! ## 3. Capacity-Preserving `prostSSGQAtCap_move` & Representation Bridge `deserReprCapQA_ok` -/

open CryptoVerification.LibsignalSessionRepr (leBytes)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_lscl_vm sepWP_seq_vmPreserved
  subroutine_ok_withLsCl_withVmPreserved_withHookStack_mono
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  vecU8FreshCap_move_bytes prostMsgKeyAtCap prostMsgKeyAtCap_entails_prostMsgKeyAt
  arrayAt_prostMsgKeyAtCap_entails prostChainGAtCap_move_bytes
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  mergeFieldQBudgetRawSpecW mergeFieldQFitsEvents fitsEvents_mergeFieldQFits_of_events
  basicFieldByteLen
)

private def RelocAt_cap (k n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, P a ⊢
    ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
      ⌜bs.length = n ∧ ∀ b : BitVec 64, (((b + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H) ⊢ P b⌝ ∗
      ((a + BitVec.ofNat 64 k) ↦ₛ bs) ∗ H

private theorem relocAt_congr_cap {k n : Nat} {P Q : BitVec 64 → SepProp}
    (heq : ∀ a, Q a = P a) (hP : RelocAt_cap k n P) : RelocAt_cap k n Q := by
  intro a
  rw [heq a]
  refine Entails.trans (hP a) ?_
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [heq b]
  exact hrec b

private theorem relocAt_pointsToBytes_cap (k : Nat) (off : BitVec 64) (bs : List (BitVec 8))
    {n : Nat} (hoff : off = BitVec.ofNat 64 k) (hn : bs.length = n) :
    RelocAt_cap k n (fun a => (a + off) ↦ₛ bs) := by
  subst hoff
  intro a
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hn, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact Entails.refl _

private theorem relocAt_pointsTo32_cap (k : Nat) (off : BitVec 64) (w : BitVec 32)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_cap k 4 (fun a => (a + off) ↦₃₂ w) :=
  relocAt_congr_cap (fun a => pointsTo32_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_cap k off (unpack32 w) hoff (unpack32_length w))

private theorem relocAt_pointsTo64_cap (k : Nat) (off : BitVec 64) (w : BitVec 64)
    (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_cap k 8 (fun a => (a + off) ↦₆₄ w) :=
  relocAt_congr_cap (fun a => pointsTo64_eq_pointsToBytes (a + off) w)
    (relocAt_pointsToBytes_cap k off (unpack64 w) hoff (unpack64_length w))

private theorem relocAt_memRegion_cap (k : Nat) (off : BitVec 64) (n : Nat)
    (hoff : off = BitVec.ofNat 64 k) (hn : n ≤ 2 ^ 64) :
    RelocAt_cap k n (fun a => memRegion (a + off) n) := by
  subst hoff
  intro a
  dsimp only
  rw [memRegion_eq_exists_bytes (a + BitVec.ofNat 64 k) n hn]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp, ← hlen]
  exact pointsToBytes_entails_memRegion (b + BitVec.ofNat 64 k) bs

private theorem relocAt_const_right_cap {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_cap k n P) :
    RelocAt_cap k n (fun a => P a ∗ H0) := by
  intro a
  dsimp only
  refine Entails.trans (sepConj_mono_left (hP a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.sepExists_right bs (Entails.sepExists_right (H ∗ H0) ?_)
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  rw [← sepConj_assoc]
  exact sepConj_mono_left (hrec b)

private theorem relocAt_const_left_cap {k n : Nat} {P : BitVec 64 → SepProp} (H0 : SepProp)
    (hP : RelocAt_cap k n P) :
    RelocAt_cap k n (fun a => H0 ∗ P a) :=
  relocAt_congr_cap (fun a => sepConj_comm H0 (P a)) (relocAt_const_right_cap H0 hP)

private theorem relocAt_exists_cap {α : Type} {k n : Nat} {P : α → BitVec 64 → SepProp}
    (hP : ∀ x, RelocAt_cap k n (P x)) :
    RelocAt_cap k n (fun a => ∃∗ x : α, P x a) := by
  intro a
  apply Entails.sepExists_elim; intro x
  refine Entails.trans (hP x a) ?_
  apply Entails.sepExists_elim; intro bs
  refine Entails.sepExists_right bs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  refine Entails.pure_right ⟨hlen, fun b => ?_⟩ (Entails.refl _)
  exact Entails.trans (hrec b) (Entails.sepExists_right x (Entails.refl _))

private theorem relocAt_sep_cap {k1 n1 k2 n2 : Nat} {P Q : BitVec 64 → SepProp}
    (hP : RelocAt_cap k1 n1 P) (hQ : RelocAt_cap k2 n2 Q) (hk : k1 + n1 = k2) :
    RelocAt_cap k1 (n1 + n2) (fun a => P a ∗ Q a) := by
  subst hk
  intro a
  dsimp only
  refine Entails.trans (sepConj_mono (hP a) (hQ a)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  apply Entails.sepExists_elim; intro H2
  apply Entails.sepExists_elim; intro bs1
  apply Entails.sepExists_elim; intro H1
  have hperm_in :
      (⌜bs1.length = n1 ∧ ∀ b, (((b + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ H1) ⊢ P b⌝ ∗
        ((a + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ H1) ∗
      (⌜bs2.length = n2 ∧ ∀ b, (((b + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2) ∗ H2) ⊢ Q b⌝ ∗
        ((a + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2) ∗ H2) =
      ⌜bs1.length = n1 ∧ ∀ b, (((b + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ H1) ⊢ P b⌝ ∗
      (⌜bs2.length = n2 ∧ ∀ b, (((b + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2) ∗ H2) ⊢ Q b⌝ ∗
        ((((a + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ ((a + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2)) ∗
          (H1 ∗ H2))) := by sep_ac_rfl
  rw [hperm_in]
  apply Entails.pure_left; rintro ⟨hlen1, hrec1⟩
  apply Entails.pure_left; rintro ⟨hlen2, hrec2⟩
  have ha_join : ∀ c : BitVec 64,
      ((c + BitVec.ofNat 64 k1) ↦ₛ (bs1 ++ bs2)) =
        ((c + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ ((c + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2) := by
    intro c
    rw [pointsToBytes_append, hlen1, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
  rw [ha_join a]
  refine Entails.pure_right ⟨by simp [hlen1, hlen2], fun b => ?_⟩ (Entails.refl _)
  rw [ha_join b]
  have hperm_out :
      (((b + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ ((b + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2)) ∗
        (H1 ∗ H2) =
      (((b + BitVec.ofNat 64 k1) ↦ₛ bs1) ∗ H1) ∗
        (((b + BitVec.ofNat 64 (k1 + n1)) ↦ₛ bs2) ∗ H2) := by sep_ac_rfl
  rw [hperm_out]
  exact sepConj_mono (hrec1 b) (hrec2 b)

private theorem relocAt_vecU8FreshCap_cap (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (bs : List (BitVec 8)) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_cap k 24 (fun a => vecU8FreshCap A (a + off) bs) := by
  subst hoff
  intro a
  refine Entails.trans (vecU8FreshCap_move_bytes A bs (a + BitVec.ofNat 64 k)) ?_
  apply Entails.sepExists_elim; intro hbs
  refine Entails.sepExists_right hbs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  exact Entails.pure_right ⟨hlen, fun b => hrec (b + BitVec.ofNat 64 k)⟩ (Entails.refl _)

private theorem relocAt_prostChainGAtCap_cap (k : Nat) (off : BitVec 64) (A : RustAlloc)
    (capMk : Nat) (c : ChainG) (hoff : off = BitVec.ofNat 64 k) :
    RelocAt_cap k 104 (fun a => prostChainGAtCap A (a + off) capMk c) := by
  subst hoff
  intro a
  refine Entails.trans (prostChainGAtCap_move_bytes A capMk c (a + BitVec.ofNat 64 k)) ?_
  apply Entails.sepExists_elim; intro hbs
  refine Entails.sepExists_right hbs ?_
  apply Entails.sepExists_elim; intro H
  refine Entails.sepExists_right H ?_
  apply Entails.pure_left; rintro ⟨hlen, hrec⟩
  exact Entails.pure_right ⟨hlen, fun b => hrec (b + BitVec.ofNat 64 k)⟩ (Entails.refl _)

private theorem relocAt_vecRecvCap_cap (A : RustAlloc) (capRecv : Nat) (recv : List ChainG) :
    RelocAt_cap 0x48 24 (fun ss =>
      ∃∗ ptrRecv : BitVec 64,
        vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
          (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv recv) := by
  refine relocAt_exists_cap fun ptrRecv => ?_
  refine relocAt_congr_cap (P := fun ss =>
      (((ss + 0x48#64) ↦₆₄ BitVec.ofNat 64 capRecv) ∗
        (((ss + 0x50#64) ↦₆₄ ptrRecv) ∗
          ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 recv.length))) ∗
      vecBuf A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (BitVec.ofNat 64 capRecv) ptrRecv recv) (fun ss => ?_) ?_
  · unfold vecAt vecHeader
    rw [show ss + 0x48#64 + 8#64 = ss + 0x50#64 by bv_omega,
        show ss + 0x48#64 + 16#64 = ss + 0x58#64 by bv_omega]
  · exact relocAt_const_right_cap _
      (relocAt_sep_cap
        (relocAt_pointsTo64_cap 0x48 0x48#64 (BitVec.ofNat 64 capRecv) rfl)
        (relocAt_sep_cap
          (relocAt_pointsTo64_cap 0x50 0x50#64 ptrRecv rfl)
          (relocAt_pointsTo64_cap 0x58 0x58#64 (BitVec.ofNat 64 recv.length) rfl) rfl) rfl)

private theorem relocAt_pidAt_cap (pid : Option (BitVec 32)) (spkId : BitVec 32) :
    RelocAt_cap 0x110 24 (fun ss =>
      pidAt ss pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
        ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4)) := by
  have htail : RelocAt_cap 0x118 16 (fun ss =>
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4) :=
    relocAt_sep_cap (relocAt_pointsTo64_cap 0x118 0x118#64 0#64 rfl)
      (relocAt_sep_cap (relocAt_pointsTo32_cap 0x120 0x120#64 spkId rfl)
        (relocAt_memRegion_cap 0x124 0x124#64 4 rfl (by decide)) rfl) rfl
  rcases pid with _ | i
  · refine relocAt_congr_cap (P := fun ss =>
        (((ss + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x114#64) 4) ∗
          (((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4))
      (fun ss => by unfold pidAt; sep_ac_rfl) ?_
    exact relocAt_sep_cap
      (relocAt_sep_cap (relocAt_pointsTo32_cap 0x110 0x110#64 0#32 rfl)
        (relocAt_memRegion_cap 0x114 0x114#64 4 rfl (by decide)) rfl) htail rfl
  · refine relocAt_congr_cap (P := fun ss =>
        (((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i)) ∗
          (((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spkId) ∗ memRegion (ss + 0x124#64) 4))
      (fun ss => by unfold pidAt; sep_ac_rfl) ?_
    exact relocAt_sep_cap
      (relocAt_sep_cap (relocAt_pointsTo32_cap 0x110 0x110#64 1#32 rfl)
        (relocAt_pointsTo32_cap 0x114 0x114#64 i rfl) rfl) htail rfl

private theorem relocAt_kyberAtCap_cap (A : RustAlloc)
    (kyber : Option (BitVec 32 × List (BitVec 8))) (v : SSGQ) :
    RelocAt_cap 0x128 48 (fun ss =>
      kyberAtCap A ss kyber
        (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
          ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))) := by
  have hsc : RelocAt_cap 0x148 16 (fun ss =>
      ((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg)) :=
    relocAt_sep_cap (relocAt_pointsTo32_cap 0x148 0x148#64 v.base.version rfl)
      (relocAt_sep_cap (relocAt_pointsTo32_cap 0x14c 0x14c#64 v.base.prevCounter rfl)
        (relocAt_sep_cap (relocAt_pointsTo32_cap 0x150 0x150#64 v.ext.remReg rfl)
          (relocAt_pointsTo32_cap 0x154 0x154#64 v.ext.locReg rfl) rfl) rfl) rfl
  refine relocAt_congr_cap (fun ss => kyberAtCap_eq_kyberAt14Cap_sep A ss kyber _) ?_
  refine relocAt_sep_cap ?_ hsc rfl
  rcases kyber with _ | ⟨i, ct⟩
  · exact relocAt_sep_cap (relocAt_pointsTo64_cap 0x128 0x128#64 noneCap rfl)
      (relocAt_memRegion_cap 0x130 0x130#64 24 rfl (by decide)) rfl
  · exact relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0x128 0x128#64 A ct rfl)
      (relocAt_sep_cap (relocAt_pointsTo32_cap 0x140 0x140#64 i rfl)
        (relocAt_memRegion_cap 0x144 0x144#64 4 rfl (by decide)) rfl) rfl

private def prostSSGQAfterLikCap (A : RustAlloc) (capRecv : Nat) (v : SSGQ) (ss : BitVec 64) :
    SepProp :=
  vecU8FreshCap A (ss + 0x18#64) v.base.rik ∗
    vecU8FreshCap A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
        (ss + 0x48#64) (BitVec.ofNat 64 capRecv) ptrRecv v.base.recv) ∗
    vecU8FreshCap A (ss + 0x60#64) v.ext.abk ∗
    vecU8FreshCap A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ∗
    pendingAt9PCap A ss v.toSSGX ∗
    kyberAtCap A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

private theorem relocAt_prostSSGQAfterLikCap (A : RustAlloc) (capRecv : Nat) (v : SSGQ) :
    RelocAt_cap 0x18 320 (prostSSGQAfterLikCap A capRecv v) := by
  have hsender : RelocAt_cap 0x90 104 (fun ss =>
      match v.base.sender with
      | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
      | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) := by
    cases v.base.sender with
    | none =>
      exact relocAt_sep_cap (relocAt_pointsTo64_cap 0x90 0x90#64 noneCap rfl)
        (relocAt_memRegion_cap 0x98 0x98#64 96 rfl (by decide)) rfl
    | some c =>
      exact relocAt_prostChainGAtCap_cap 0x90 0x90#64 A (vecCap4Of c.keys.length) c rfl
  have hpending : RelocAt_cap 0xf8 48 (fun ss => pendingAt9PCap A ss v.toSSGX) := by
    unfold pendingAt9PCap
    have hpb : v.toSSGX.base = v.base := rfl
    rw [hpb]
    cases v.base.pending with
    | none =>
      exact relocAt_sep_cap (relocAt_pointsTo64_cap 0xf8 0xf8#64 noneCap rfl)
        (relocAt_memRegion_cap 0x100 0x100#64 40 rfl (by decide)) rfl
    | some k =>
      exact relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0xf8 0xf8#64 A k rfl)
        (relocAt_pidAt_cap v.toSSGX.ext.pid v.toSSGX.ext.spkId) rfl
  exact relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0x18 0x18#64 A v.base.rik rfl)
    (relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0x30 0x30#64 A v.base.root rfl)
      (relocAt_sep_cap (relocAt_vecRecvCap_cap A capRecv v.base.recv)
        (relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0x60 0x60#64 A v.ext.abk rfl)
          (relocAt_sep_cap (relocAt_vecU8FreshCap_cap 0x78 0x78#64 A v.ext.pq rfl)
            (relocAt_sep_cap hsender
              (relocAt_sep_cap hpending
                (relocAt_kyberAtCap_cap A v.ext.kyber v) rfl) rfl) rfl) rfl) rfl) rfl) rfl

private def vecU8Heap_cap (A : RustAlloc) (w0 ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if w0 = 0 then emp
    else A.live ptr w0.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (w0.toNat - bs.length)

private def likTail_cap (A : RustAlloc) (w0 ptr : BitVec 64) (lik : List (BitVec 8))
    (ss : BitVec 64) : SepProp :=
  (((ss + 8#64) ↦₆₄ ptr) ∗ ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 lik.length)) ∗
    vecU8Heap_cap A w0 ptr lik

private theorem relocAt_likTail_cap (A : RustAlloc) (w0 ptr : BitVec 64) (lik : List (BitVec 8)) :
    RelocAt_cap 8 16 (likTail_cap A w0 ptr lik) :=
  relocAt_const_right_cap (vecU8Heap_cap A w0 ptr lik)
    (relocAt_sep_cap
      (relocAt_pointsTo64_cap 8 8#64 ptr rfl)
      (relocAt_pointsTo64_cap 16 16#64 (BitVec.ofNat 64 lik.length) rfl) rfl)

private theorem vecU8At_eq_word0_sep_likTail_cap (A : RustAlloc) (ss w0 ptr : BitVec 64)
    (lik : List (BitVec 8)) :
    vecU8At A ss w0 ptr lik = (ss ↦₆₄ w0) ∗ likTail_cap A w0 ptr lik ss := by
  unfold vecU8At vecHeader likTail_cap vecU8Heap_cap
  sep_ac_rfl

private theorem vecU8Heap_w0_ne_noneCap_cap (A : RustAlloc) (w0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Heap_cap A w0 ptr bs ⊢ ⌜w0 ≠ noneCap⌝ ∗ vecU8Heap_cap A w0 ptr bs := by
  unfold vecU8Heap_cap
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hne : w0 ≠ noneCap := by
    intro heq; subst heq; revert hlt; decide
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

/-- Capacity-preserving stack-to-out relocation of `prostSSGQAtCap`:
decomposes the 344-byte `SessionStructure` into word 0 `w0 ≠ noneCap` + 336-byte `rest` + heap
frame `H`, reconstructing `prostSSGQAtCap A b capRecv v` at any target address `b`. -/
theorem prostSSGQAtCap_move (A : RustAlloc) (a : BitVec 64) (capRecv : Nat) (v : SSGQ) :
    prostSSGQAtCap A a capRecv v ⊢
      ∃∗ w0 : BitVec 64, ∃∗ rest : List (BitVec 8), ∃∗ H : SepProp,
        ⌜w0 ≠ noneCap ∧ rest.length = 336 ∧
          ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢
            prostSSGQAtCap A b capRecv v⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ rest) ∗ H := by
  change (vecU8FreshCap A a v.base.lik ∗ prostSSGQAfterLikCap A capRecv v a) ⊢ _
  unfold vecU8FreshCap
  set w0 := bytesMergeOutCap 0#64 v.base.lik.length
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  rw [vecU8At_eq_word0_sep_likTail_cap, sepConj_assoc]
  have hne_step :
      (likTail_cap A w0 ptr v.base.lik a ∗ prostSSGQAfterLikCap A capRecv v a) ⊢
        ⌜w0 ≠ noneCap⌝ ∗ (likTail_cap A w0 ptr v.base.lik a ∗ prostSSGQAfterLikCap A capRecv v a) := by
    unfold likTail_cap
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (vecU8Heap_w0_ne_noneCap_cap A w0 ptr v.base.lik))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans (sepConj_mono_right hne_step) ?_
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw0
  have hreloc := relocAt_sep_cap (relocAt_likTail_cap A w0 ptr v.base.lik)
    (relocAt_prostSSGQAfterLikCap A capRecv v) rfl
  refine Entails.trans (sepConj_mono_right (hreloc a)) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro rest
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro H
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hrest_len, hrec⟩
  refine Entails.sepExists_right w0
    (Entails.sepExists_right rest (Entails.sepExists_right H ?_))
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  rw [h8]
  refine Entails.pure_right ⟨hw0, hrest_len, fun b => ?_⟩ (Entails.refl _)
  refine Entails.trans (sepConj_mono_right (hrec b)) ?_
  change ((b ↦₆₄ w0) ∗ (likTail_cap A w0 ptr v.base.lik b ∗ prostSSGQAfterLikCap A capRecv v b)) ⊢
    ((∃∗ p', vecU8At A b w0 p' v.base.lik) ∗ prostSSGQAfterLikCap A capRecv v b)
  rw [← sepConj_assoc, ← vecU8At_eq_word0_sep_likTail_cap]
  exact sepConj_mono_left (Entails.sepExists_right ptr (Entails.refl _))

/-- `Satisfies`-level unpacking of `prostSSGQAtCap_move` at `L + 0x420#64` for loop exit. -/
theorem satisfies_prostSSGQAtCap_move {A : RustAlloc} {m : Memory} {L : BitVec 64}
    {capRecv : Nat} {v : SSGQ} {R : SepProp}
    (h : m ⊨ prostSSGQAtCap A (L + 0x420#64) capRecv v ∗ R) :
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧
      (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢
        prostSSGQAtCap A b capRecv v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R) := by
  have h428 : L + 0x420#64 + 8#64 = L + 0x428#64 := by bv_omega
  have hmove_ent := prostSSGQAtCap_move A (L + 0x420#64) capRecv v
  rw [h428] at hmove_ent
  have h1 := Satisfies.mono (sepConj_mono_left hmove_ent) h
  simp only [sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨w0, rest, H, h1⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hw0, hrest, hrebuild⟩, h1⟩
  exact ⟨w0, rest, H, hw0, hrest, hrebuild, by simpa only [sepConj_assoc] using h1⟩

/-- For any `n < 2 ^ 62` and `8 ≤ HasFineReallocCredit.smallMaxReq M`, `bytesMergeOutCap 0#64 n`
has the exact same `bytesLargeLive M` cost as `n`. -/
theorem bytesLargeLive_bytesMergeOutCap (M : AllocCostModel) [HasFineReallocCredit M]
    (h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M) {n : Nat} (hn : n < 2 ^ 62) :
    bytesLargeLive M (bytesMergeOutCap 0#64 n).toNat = bytesLargeLive M n := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [bytesMergeOutCap_zero_zero]
    rfl
  · rw [bytesMergeOutCap_zero_pos (Nat.pos_of_ne_zero hn0)]
    have hmax_lt : max n 8 < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt]
    by_cases hle8 : n ≤ 8
    · have hm8 : max n 8 = 8 := Nat.max_eq_right hle8
      rw [hm8]
      unfold bytesLargeLive
      have hs1 : 8 ≤ HasFineReallocCredit.smallMaxReq M := h8
      have hs2 : n ≤ HasFineReallocCredit.smallMaxReq M := by omega
      simp [hs1, hs2]
    · have hm_n : max n 8 = n := Nat.max_eq_left (by omega)
      rw [hm_n]

private theorem bytesLargeLive_eq_zero_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    {n : Nat} (hle : n ≤ HasFineReallocCredit.smallMaxReq M) :
    bytesLargeLive M n = 0 := by
  unfold bytesLargeLive
  simp [hle]

private theorem deserialize_serialize_pk_cap (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

private theorem arrayAt_map_entails_zip_cap {α β γ : Type}
    (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (stride : Nat) :
    ∀ (xs : List α) (base : BitVec 64),
      (∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) →
      arrayAt elem1 stride base (xs.map f) ⊢
        ∃∗ gs : List γ,
          ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
            arrayAt elem2 stride base (gs.zip xs)
  | [], _, _ => by
    dsimp only [List.map, arrayAt]
    refine Entails.sepExists_right [] ?_
    exact Entails.pure_right ⟨rfl, fun _ h => by cases h⟩ (Entails.refl _)
  | x :: xs, base, h => by
    dsimp only [List.map, arrayAt]
    have hx := h x List.mem_cons_self base
    have hxs := arrayAt_map_entails_zip_cap elem1 elem2 P f stride xs
      (base + BitVec.ofNat 64 stride) (fun y hy b => h y (List.mem_cons_of_mem x hy) b)
    refine Entails.trans (sepConj_mono hx hxs) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hpx
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right (g :: gs) ?_
    refine Entails.pure_right ⟨by simp [hlen], fun gx hgx => ?_⟩ ?_
    · simp only [List.zip_cons_cons, List.mem_cons] at hgx
      rcases hgx with rfl | hgx
      · exact hpx
      · exact hpz gx hgx
    · dsimp only [List.zip_cons_cons, arrayAt]
      exact Entails.refl _

private theorem vecAt_map_entails_zip_cap {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v cap ptr : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecAt A stride align elem1 v cap ptr (xs.map f) ⊢
      ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecAt vecBuf
  rw [List.length_map]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbuf
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbuf.1)
    subst hnil
    refine Entails.sepExists_right [] ?_
    refine Entails.pure_right ⟨rfl, fun _ h => by cases h⟩ ?_
    rw [sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    have harr := arrayAt_map_entails_zip_cap elem1 elem2 P f stride xs ptr h
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left harr))) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right gs ?_
    refine Entails.pure_right ⟨hlen, hpz⟩ ?_
    have hzip_len : (gs.zip xs).length = xs.length := by
      rw [List.length_zip, hlen, Nat.min_self]
    rw [hzip_len, sepConj_pure_left_comm]
    exact Entails.pure_right hbuf (Entails.refl _)

private def MsgKeyCapInv (mg : MessageKeyGhost) : Prop :=
  mg.cipher.cap = 0#64 ∧ mg.mac.cap = 0#64 ∧ mg.iv.cap = 0#64 ∧ mg.seed.cap = 32#64

private theorem messageKeyLargeLive_of_inv (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) {mg : MessageKeyGhost} (hi : MsgKeyCapInv mg) :
    messageKeyLargeLive M mg = 0 := by
  rcases hi with ⟨hc, hm, hiv, hs⟩
  unfold messageKeyLargeLive
  rw [hc, hm, hiv, hs]
  have hz0 : bytesLargeLive M 0 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
  have hz32 : bytesLargeLive M 32 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
  simp [hz0, hz32]

private theorem prostMsgKeyAtCap_entails_messageKeyAt_cap (A : RustAlloc) (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) (a : BitVec 64) :
    prostMsgKeyAtCap A mk a ⊢
      ∃∗ mg : MessageKeyGhost, ⌜MsgKeyCapInv mg⌝ ∗ messageKeyAt A (mg, mk) a := by
  have hne : mk.seed ≠ [] := by intro h; rw [h] at hseed; cases hseed
  unfold prostMsgKeyAtCap vecU8FreshCap
  simp only [List.length_nil, bytesMergeOutCap_zero_zero, hseed,
    show bytesMergeOutCap 0#64 32 = 32#64 by decide,
    sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun seedPtr => Entails.sepExists_elim fun ivPtr =>
    Entails.sepExists_elim fun macPtr => Entails.sepExists_elim fun cipherPtr => ?_
  let mg : MessageKeyGhost := {
    cipher := ⟨0#64, cipherPtr⟩
    mac := ⟨0#64, macPtr⟩
    iv := ⟨0#64, ivPtr⟩
    seed := ⟨32#64, seedPtr⟩
  }
  refine Entails.sepExists_right mg ?_
  refine Entails.pure_right ⟨rfl, rfl, rfl, rfl⟩ ?_
  unfold messageKeyAt
  exact Entails.pure_right hne (Entails.refl _)

private def ChainCapInv (cg : ChainGhost) (c : ReceiverChain) : Prop :=
  CanonChain (cg, c) ∧
  cg.srk.cap = 33#64 ∧
  cg.priv.cap = 0#64 ∧
  cg.mkCap = BitVec.ofNat 64 (vecCap4Of c.messageKeys.length) ∧
  (∀ mg ∈ cg.keys, MsgKeyCapInv mg) ∧
  (match c.chainKey with
   | none => cg.ck.cap = 0#64
   | some _ => cg.ck.cap = 32#64)

private theorem chainPair_eq_chainGhost_of_inv (M : AllocCostModel) [HasFineReallocCredit M]
    {cg : ChainGhost} {c : ReceiverChain} (hi : ChainCapInv cg c) :
    chainPairLargeLive M (cg, c) = chainGhostLargeLive M cg := by
  obtain ⟨-, -, -, -, -, hck⟩ := hi
  unfold chainPairLargeLive chainGhostLargeLive sgnCapLargeLive
  dsimp only
  rcases hck_eq : c.chainKey with _ | ck <;> simp only [hck_eq] at hck <;> rw [hck] <;> simp

private theorem chainGhostLargeLive_of_inv (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {cg : ChainGhost} {c : ReceiverChain}
    (hmax : c.messageKeys.length ≤ maxMessageKeys) (hi : ChainCapInv cg c) :
    chainGhostLargeLive M cg = vec104LargeLive M (vecCap4Of c.messageKeys.length) := by
  obtain ⟨-, hsrk, hpriv, hmkCap, hkeys, hck⟩ := hi
  have hcap_lt : vecCap4Of c.messageKeys.length < 2 ^ 64 := by
    have h1 := vecCap4Of_le_mono (show c.messageKeys.length ≤ 2000 from hmax)
    have h2 : vecCap4Of 2000 = 2048 := by decide
    omega
  have hkeys0 : (cg.keys.map (messageKeyLargeLive M)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    rcases List.mem_map.1 hx with ⟨mg, hmg, rfl⟩
    exact messageKeyLargeLive_of_inv M h33 (hkeys mg hmg)
  have hck0 : sgnCapLargeLive M cg.ck.cap = 0 := by
    unfold sgnCapLargeLive
    rcases hck_eq : c.chainKey with _ | ck <;> simp only [hck_eq] at hck
    · rw [hck]; simp
    · rw [hck]
      simp [bytesLargeLive_eq_zero_of_le M (n := 32) (by omega)]
  have hmk_nat : cg.mkCap.toNat = vecCap4Of c.messageKeys.length := by
    rw [hmkCap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  have hsrk_nat : cg.srk.cap.toNat = 33 := by rw [hsrk]; rfl
  have hpriv_nat : cg.priv.cap.toNat = 0 := by rw [hpriv]; rfl
  unfold chainGhostLargeLive
  rw [hsrk_nat, hpriv_nat, hmk_nat, hkeys0, hck0]
  have hz33 : bytesLargeLive M 33 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
  have hz0 : bytesLargeLive M 0 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
  simp [hz33, hz0]

private theorem prostChainKeyCap_entails_optChainKeyAt_cap (A : RustAlloc) (o : Option ChainKey)
    (a : BitVec 64) :
    (match o.map (fun ck => (ck.index, keyToBytes32 ck.key)) with
     | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
     | some (i, k) => vecU8FreshCap A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
         memRegion (a + 0x64#64) 4) ⊢
      ∃∗ ckPin : VecPin,
        ⌜match o with | none => ckPin.cap = 0#64 | some _ => ckPin.cap = 32#64⌝ ∗
          optChainKeyAt A ckPin o (a + 72#64) := by
  rcases o with _ | ck
  · dsimp only [Option.map, optChainKeyAt]
    refine Entails.sepExists_right ⟨0#64, 0#64⟩ ?_
    refine Entails.pure_right rfl ?_
    have ha : a + 72#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha]
    exact Entails.refl _
  · dsimp only [Option.map, optChainKeyAt]
    unfold vecU8FreshCap
    have hklen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
    rw [hklen, show bytesMergeOutCap 0#64 32 = 32#64 by decide, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right ⟨32#64, ptr⟩ ?_
    refine Entails.pure_right rfl ?_
    have ha1 : a + 72#64 + 24#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
    have ha2 : a + 72#64 + 28#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
    rw [ha1, ha2]
    exact Entails.refl _

private theorem exists_mem_zip_of_length_eq {α β : Type} :
    ∀ {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y : β, (x, y) ∈ xs.zip ys
  | [], _, _, _, hx => nomatch hx
  | _ :: _, [], _, hlen, _ => nomatch hlen
  | x0 :: xs, y0 :: ys, x, hlen, hx => by
      rcases List.mem_cons.1 hx with rfl | hrest
      · exact ⟨y0, List.mem_cons_self⟩
      · obtain ⟨y, hy⟩ := exists_mem_zip_of_length_eq (Nat.succ.inj hlen) hrest
        exact ⟨y, List.mem_cons_of_mem _ hy⟩

private theorem prostChainGAtCap_recv_entails_chainAt_cap (A : RustAlloc) (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) (a : BitVec 64) :
    prostChainGAtCap A a (vecCap4Of (recvChainG c).keys.length) (recvChainG c) ⊢
      ∃∗ cg : ChainGhost,
        ⌜ChainCapInv cg c⌝ ∗ chainAt A (cg, c) a := by
  unfold prostChainGAtCap recvChainG
  dsimp only
  set mkCap := BitVec.ofNat 64 (vecCap4Of c.messageKeys.length)
  have hkeys :
      (∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b)
          (a + 0x30#64) mkCap ptrMk c.messageKeys) ⊢
      ∃∗ ptrMk : BitVec 64, ∃∗ keys : List MessageKeyGhost,
        ⌜keys.length = c.messageKeys.length ∧
          (∀ gx ∈ keys.zip c.messageKeys, MsgKeyCapInv gx.1)⌝ ∗
          vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) mkCap ptrMk
            (keys.zip c.messageKeys) := by
    apply Entails.sepExists_elim; intro ptrMk
    refine Entails.sepExists_right ptrMk ?_
    conv_lhs => rw [show c.messageKeys = c.messageKeys.map id by simp]
    exact vecAt_map_entails_zip_cap A 104 8 (fun mk b => prostMsgKeyAtCap A mk b)
      (messageKeyAt A) (fun gx => MsgKeyCapInv gx.1) id (a + 0x30#64) mkCap ptrMk c.messageKeys
      (fun mk hmk b => prostMsgKeyAtCap_entails_messageKeyAt_cap A mk (hseeds mk hmk) b)
  have hck := prostChainKeyCap_entails_optChainKeyAt_cap A c.chainKey a
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hkeys hck))) ?_
  unfold vecU8FreshCap
  have hsrk_len : c.senderRatchetKey.serialize.length = 33 :=
    serialize_pk_length_cap c.senderRatchetKey
  simp only [hsrk_len, show bytesMergeOutCap 0#64 33 = 33#64 by decide,
    List.length_nil, bytesMergeOutCap_zero_zero,
    sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ckPin =>
    Entails.sepExists_elim fun mkPtr => Entails.sepExists_elim fun keys =>
    Entails.sepExists_elim fun privPtr => Entails.sepExists_elim fun srkPtr => ?_
  have hperm :
      vecU8At A a 33#64 srkPtr c.senderRatchetKey.serialize ∗
        vecU8At A (a + 0x18#64) 0#64 privPtr [] ∗
        (⌜keys.length = c.messageKeys.length ∧
            (∀ gx ∈ keys.zip c.messageKeys, MsgKeyCapInv gx.1)⌝ ∗
          vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) mkCap mkPtr
            (keys.zip c.messageKeys)) ∗
        (⌜match c.chainKey with | none => ckPin.cap = 0#64 | some _ => ckPin.cap = 32#64⌝ ∗
          optChainKeyAt A ckPin c.chainKey (a + 72#64)) =
      ⌜keys.length = c.messageKeys.length ∧
          (∀ gx ∈ keys.zip c.messageKeys, MsgKeyCapInv gx.1)⌝ ∗
        (⌜match c.chainKey with | none => ckPin.cap = 0#64 | some _ => ckPin.cap = 32#64⌝ ∗
          (vecU8At A a 33#64 srkPtr c.senderRatchetKey.serialize ∗
            vecU8At A (a + 0x18#64) 0#64 privPtr [] ∗
            vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) mkCap mkPtr
              (keys.zip c.messageKeys) ∗
            optChainKeyAt A ckPin c.chainKey (a + 72#64))) := by sep_ac_rfl
  rw [hperm]
  apply Entails.pure_left; rintro ⟨hkeyslen, hkeys_inv⟩
  apply Entails.pure_left; intro hck_inv
  let cg : ChainGhost := {
    srk := ⟨33#64, srkPtr, c.senderRatchetKey.serialize⟩
    priv := ⟨0#64, privPtr, []⟩
    mkCap := mkCap
    mkPtr := mkPtr
    keys := keys
    ck := ckPin
  }
  have hall_keys : ∀ mg ∈ keys, MsgKeyCapInv mg := fun mg hmg => by
    obtain ⟨mk, hmem_zip⟩ := exists_mem_zip_of_length_eq hkeyslen hmg
    exact hkeys_inv (mg, mk) hmem_zip
  refine Entails.sepExists_right cg ?_
  refine Entails.pure_right ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, hall_keys, hck_inv⟩ ?_
  unfold chainAt
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_cap c.senderRatchetKey, hmax, hkeyslen,
      serialize_pk_length_cap c.senderRatchetKey, rfl⟩ ?_
  dsimp only [cg, vecGhostAt]
  exact Entails.refl _

private theorem prostRecvGCap_entails_vecAt_chainAt_cap (A : RustAlloc)
    (s : Session (List (BitVec 8)))
    (hseeds : SeedsLen32 s.state)
    (hmax : ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (capRecv : Nat) (a : BitVec 64) :
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c p => prostChainGAtCap A p (vecCap4Of c.keys.length) c)
        a (BitVec.ofNat 64 capRecv) ptrRecv (s.state.receiverChains.map recvChainG)) ⊢
      ∃∗ ptrRecv : BitVec 64, ∃∗ chains : List ChainGhost,
        ⌜chains.length = s.state.receiverChains.length ∧
          (∀ gc ∈ chains.zip s.state.receiverChains, ChainCapInv gc.1 gc.2)⌝ ∗
          vecAt A 104 8 (chainAt A) a (BitVec.ofNat 64 capRecv) ptrRecv
            (chains.zip s.state.receiverChains) := by
  apply Entails.sepExists_elim; intro ptrRecv
  refine Entails.sepExists_right ptrRecv ?_
  exact vecAt_map_entails_zip_cap A 104 8
    (fun c p => prostChainGAtCap A p (vecCap4Of c.keys.length) c)
    (chainAt A) (fun gc => ChainCapInv gc.1 gc.2) recvChainG
    a (BitVec.ofNat 64 capRecv) ptrRecv s.state.receiverChains
    (fun c hc b => prostChainGAtCap_recv_entails_chainAt_cap A c (hseeds c hc) (hmax c hc) b)

private theorem prostSenderGCap_entails_optSenderChainAt_cap (A : RustAlloc)
    (scOpt : Option SenderChain)
    (hclamp : ∀ sc, scOpt = some sc →
      CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
        sc.ratchetKey.privateKey.bytes)
    (ss : BitVec 64) :
    (match scOpt.map senderChainG with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAtCap A (ss + 0x90#64) (vecCap4Of c.keys.length) c) ⊢
      ∃∗ sg : Option SenderChainGhost,
        ⌜CanonSender sg scOpt ∧
          (∀ M [HasFineReallocCredit M], 33 ≤ HasFineReallocCredit.smallMaxReq M →
            (match sg with | none => 0 | some g => senderChainLargeLive M g) = 0)⌝ ∗
          optSenderChainAt A (ss + 0x90#64) sg scOpt := by
  rcases scOpt with _ | sc
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right ⟨trivial, fun _ _ _ => rfl⟩ ?_
    unfold optSenderChainAt
    rw [show ss + 0x90#64 + 8#64 = ss + 0x98#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map]
    unfold prostChainGAtCap senderChainG vecU8FreshCap
    have hsrk_len : sc.ratchetKey.publicKey.serialize.length = 33 :=
      serialize_pk_length_cap sc.ratchetKey.publicKey
    have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 := by
      simp [sc.ratchetKey.privateKey.bytes.toList_length]
    have hck_len : (keyToBytes32 sc.chainKey.key).length = 32 := by simp [keyToBytes32]
    have hcap0 : vecCap4Of ([] : List MessageKeyGenerator).length = 0 := rfl
    simp only [hsrk_len, hpriv_len, hck_len, hcap0,
      show bytesMergeOutCap 0#64 33 = 33#64 by decide,
      show bytesMergeOutCap 0#64 32 = 32#64 by decide,
      BitVec.ofNat_eq_ofNat, sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ckPtr => Entails.sepExists_elim fun mkPtr =>
      Entails.sepExists_elim fun privPtr => Entails.sepExists_elim fun srkPtr => ?_
    let g : SenderChainGhost := {
      srk := ⟨33#64, srkPtr, sc.ratchetKey.publicKey.serialize⟩
      priv := ⟨32#64, privPtr, sc.ratchetKey.privateKey.bytes.toList⟩
      mkCap := 0#64
      mkPtr := mkPtr
      ck := ⟨32#64, ckPtr⟩
    }
    refine Entails.sepExists_right (some g) ?_
    refine Entails.pure_right ⟨⟨rfl, rfl⟩, fun M _ h33 => ?_⟩ ?_
    · unfold senderChainLargeLive vec104LargeLive
      dsimp only [g]
      have hz33 : bytesLargeLive M 33 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
      have hz32 : bytesLargeLive M 32 = 0 := bytesLargeLive_eq_zero_of_le M (by omega)
      simp [hz33, hz32]
    · unfold optSenderChainAt
      refine Entails.pure_right
        ⟨deserialize_serialize_pk_cap _, rfl, hclamp sc rfl, serialize_pk_length_cap _⟩ ?_
      dsimp only [g, vecGhostAt, optChainKeyAt]
      have hv_eq : vecAt A 104 8 (fun mk b => prostMsgKeyAtCap A mk b)
          (ss + 0x90#64 + 0x30#64) 0#64 mkPtr [] =
          vecAt A 104 8 (messageKeyAt A) (ss + 0x90#64 + 0x30#64) 0#64 mkPtr [] := rfl
      rw [hv_eq,
        show ss + 0x90#64 + 72#64 + 24#64 = ss + 0x90#64 + 0x60#64 by rw [BitVec.add_assoc]; rfl,
        show ss + 0x90#64 + 72#64 + 28#64 = ss + 0x90#64 + 0x64#64 by rw [BitVec.add_assoc]; rfl]
      exact Entails.refl _

private def pendingTail_cap (w0 w1 spkId w2 : BitVec 32) : List (BitVec 8) :=
  unpack32 w0 ++ (unpack32 w1 ++ (unpack64 0#64 ++ (unpack32 spkId ++ unpack32 w2)))

private theorem pendingTail_pointsToBytes_cap (ss : BitVec 64) (w0 w1 spkId w2 : BitVec 32) :
    ((ss + 0x110#64) ↦₃₂ w0) ∗ ((ss + 0x114#64) ↦₃₂ w1) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ spkId) ∗ ((ss + 0x124#64) ↦₃₂ w2) =
      ((ss + 0xf8#64 + 24#64) ↦ₛ pendingTail_cap w0 w1 spkId w2) := by
  have ha0 : ss + 0xf8#64 + 24#64 = ss + 0x110#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x110#64 + 4#64 = ss + 0x114#64 := by rw [BitVec.add_assoc]; rfl
  have ha2 : ss + 0x114#64 + 4#64 = ss + 0x118#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 0x118#64 + 8#64 = ss + 0x120#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x120#64 + 4#64 = ss + 0x124#64 := by rw [BitVec.add_assoc]; rfl
  unfold pendingTail_cap
  rw [ha0, pointsToBytes_append, unpack32_length,
    ha1, pointsToBytes_append, unpack32_length,
    ha2, pointsToBytes_append, unpack64_length,
    ha3, pointsToBytes_append, unpack32_length, ha4]
  simp only [← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem prostPendingCap_entails_optTailVecAt_cap (A : RustAlloc)
    (s : Session (List (BitVec 8))) (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (ss : BitVec 64) :
    pendingAt9PCap A ss (ssgqOf s).toSSGX ⊢
      ∃∗ pg : Option TailVecGhost,
        ⌜CanonPending pg s.pendingPreKey ∧
          PendingRel pg s.pendingPreKey ∧
          pg.isSome = s.state.pendingPreKey ∧
          (∀ M [HasFineReallocCredit M], 33 ≤ HasFineReallocCredit.smallMaxReq M →
            optTailVecLargeLive M pg = 0)⌝ ∗
          optTailVecAt A 48 (ss + 0xf8#64) pg := by
  unfold Session.Wf at hwf
  unfold pendingAt9PCap ssgqOf ssgOf
  dsimp only [SSGQ.toSSGX, ExtraGQ.toExtraG]
  rcases hpend : s.pendingPreKey with _ | p
  · dsimp only [Option.map]
    refine Entails.sepExists_right none ?_
    have hsome : (none : Option TailVecGhost).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    refine Entails.pure_right ⟨trivial, trivial, hsome, fun _ _ _ => rfl⟩ ?_
    unfold optTailVecAt
    rw [show ss + 0xf8#64 + 8#64 = ss + 0x100#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map, Option.bind, Option.getD]
    have hts := hp p hpend
    have hsome : (some (⟨⟨0, 0, []⟩, []⟩ : TailVecGhost)).isSome = s.state.pendingPreKey := by
      rw [hwf, hpend]; rfl
    have hpk_len : p.baseKey.serialize.length = 33 := serialize_pk_length_cap p.baseKey
    rcases hpre : p.preKeyId with _ | i
    · unfold pidAt vecU8FreshCap
      rw [hpk_len, show bytesMergeOutCap 0#64 33 = 33#64 by decide,
        memRegion_four (ss + 0x114#64), memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w1 =>
        Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨33#64, ptr, p.baseKey.serialize⟩
        tail := pendingTail_cap 0#32 w1 p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_cap p.baseKey, ?_, ?_, ?_, hpk_len⟩
        · rw [hpre]; rfl
        · rw [hts]; rfl
        · simp only [g, pendingTail_cap, leBytes, unpack32, unpack64, BitVec.extractLsb',
            Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨rfl, hrel, hsome, fun M _ h33 => ?_⟩ ?_
      · unfold optTailVecLargeLive
        exact bytesLargeLive_eq_zero_of_le M (n := 33) (by omega)
      · unfold optTailVecAt
        refine Entails.pure_right (rfl : (pendingTail_cap 0#32 w1 p.signedPreKeyId w2).length = 24) ?_
        dsimp only [g, vecGhostAt]
        rw [← pendingTail_pointsToBytes_cap ss 0#32 w1 p.signedPreKeyId w2]
        exact Entails.refl _
    · unfold pidAt vecU8FreshCap
      rw [hpk_len, show bytesMergeOutCap 0#64 33 = 33#64 by decide,
        memRegion_four (ss + 0x124#64)]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun ptr => ?_
      let g : TailVecGhost := {
        vec := ⟨33#64, ptr, p.baseKey.serialize⟩
        tail := pendingTail_cap 1#32 i p.signedPreKeyId w2
      }
      refine Entails.sepExists_right (some g) ?_
      have hrel : PendingRel (some g) (some p) := by
        refine ⟨deserialize_serialize_pk_cap p.baseKey, ?_, ?_, ?_, hpk_len⟩
        · rw [hpre]
          exact ⟨rfl, by simp only [g, pendingTail_cap, leBytes, unpack32, unpack64,
            BitVec.extractLsb', Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl⟩
        · rw [hts]; rfl
        · simp only [g, pendingTail_cap, leBytes, unpack32, unpack64, BitVec.extractLsb',
            Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
      refine Entails.pure_right ⟨rfl, hrel, hsome, fun M _ h33 => ?_⟩ ?_
      · unfold optTailVecLargeLive
        exact bytesLargeLive_eq_zero_of_le M (n := 33) (by omega)
      · unfold optTailVecAt
        refine Entails.pure_right (rfl : (pendingTail_cap 1#32 i p.signedPreKeyId w2).length = 24) ?_
        dsimp only [g, vecGhostAt]
        rw [← pendingTail_pointsToBytes_cap ss 1#32 i p.signedPreKeyId w2]
        exact Entails.refl _

private def kyberTail_cap (i w : BitVec 32) : List (BitVec 8) := unpack32 i ++ unpack32 w

private theorem kyberTail_pointsToBytes_cap (ss : BitVec 64) (i w : BitVec 32) :
    ((ss + 0x140#64) ↦₃₂ i) ∗ ((ss + 0x144#64) ↦₃₂ w) =
      ((ss + 0x128#64 + 24#64) ↦ₛ kyberTail_cap i w) := by
  have ha0 : ss + 0x128#64 + 24#64 = ss + 0x140#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x140#64 + 4#64 = ss + 0x144#64 := by rw [BitVec.add_assoc]; rfl
  unfold kyberTail_cap
  rw [ha0, pointsToBytes_append, unpack32_length, ha1]
  simp only [← pointsTo32_eq_pointsToBytes]

private theorem prostKyberCap_entails_optTailVecAt_cap (A : RustAlloc)
    (o : Option PendingKyberPreKey) (ss : BitVec 64) :
    kyberAt14Cap A ss (o.map (fun k => (k.preKeyId, k.ciphertext))) ⊢
      ∃∗ kg : Option TailVecGhost,
        ⌜KyberRel kg o ∧
          (∀ M [HasFineReallocCredit M], 8 ≤ HasFineReallocCredit.smallMaxReq M →
            (∀ k, o = some k → k.ciphertext.length < 2 ^ 62) →
            optTailVecLargeLive M kg =
              match o with
              | none => 0
              | some k => bytesLargeLive M k.ciphertext.length)⌝ ∗
          optTailVecAt A 32 (ss + 0x128#64) kg := by
  rcases ho : o with _ | k
  · dsimp only [Option.map, kyberAt14Cap]
    refine Entails.sepExists_right none ?_
    refine Entails.pure_right ⟨trivial, fun _ _ _ _ => rfl⟩ ?_
    unfold optTailVecAt
    rw [show ss + 0x128#64 + 8#64 = ss + 0x130#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _
  · dsimp only [Option.map, kyberAt14Cap]
    unfold vecU8FreshCap
    rw [memRegion_four (ss + 0x144#64)]
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w => Entails.sepExists_elim fun ptr => ?_
    let g : TailVecGhost := {
      vec := ⟨bytesMergeOutCap 0#64 k.ciphertext.length, ptr, k.ciphertext⟩
      tail := kyberTail_cap k.preKeyId w
    }
    refine Entails.sepExists_right (some g) ?_
    have hrel : KyberRel (some g) (some k) := by
      refine ⟨rfl, ?_⟩
      simp only [g, kyberTail_cap, leBytes, unpack32, BitVec.extractLsb',
        Nat.shiftRight_eq_div_pow, List.range, List.range.loop, List.map]; rfl
    refine Entails.pure_right ⟨hrel, fun M _ h8 hlt => ?_⟩ ?_
    · unfold optTailVecLargeLive
      exact bytesLargeLive_bytesMergeOutCap M h8 (hlt k rfl)
    · unfold optTailVecAt
      refine Entails.pure_right (rfl : (kyberTail_cap k.preKeyId w).length = 8) ?_
      dsimp only [g, vecGhostAt]
      rw [← kyberTail_pointsToBytes_cap ss k.preKeyId w]
      exact Entails.refl _

private theorem sum_chainPair_eq_chainGhost (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ (gs : List ChainGhost) (cs : List ReceiverChain),
      gs.length = cs.length →
      (∀ gc ∈ gs.zip cs, ChainCapInv gc.1 gc.2) →
      ((gs.zip cs).map (chainPairLargeLive M)).sum =
        (gs.map (chainGhostLargeLive M)).sum
  | [], [], _, _ => rfl
  | _ :: _, [], h, _ => by cases h
  | [], _ :: _, h, _ => by cases h
  | g :: gs, c :: cs, hlen, hinv => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have h1 := chainPair_eq_chainGhost_of_inv M (hinv (g, c) List.mem_cons_self)
    have h2 := sum_chainPair_eq_chainGhost M gs cs (by simp at hlen; exact hlen)
      (fun gc hgc => hinv gc (List.mem_cons_of_mem _ hgc))
    rw [h1, h2]

private theorem sum_chainGhost_eq_recvChains (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (gs : List ChainGhost) (cs : List ReceiverChain),
      gs.length = cs.length →
      (∀ c ∈ cs, c.messageKeys.length ≤ maxMessageKeys) →
      (∀ gc ∈ gs.zip cs, ChainCapInv gc.1 gc.2) →
      (gs.map (chainGhostLargeLive M)).sum =
        (cs.map (fun c => vec104LargeLive M (vecCap4Of c.messageKeys.length))).sum
  | [], [], _, _, _ => rfl
  | _ :: _, [], h, _, _ => by cases h
  | [], _ :: _, h, _, _ => by cases h
  | g :: gs, c :: cs, hlen, hmax, hinv => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := chainGhostLargeLive_of_inv M h33 (hmax c List.mem_cons_self)
      (hinv (g, c) List.mem_cons_self)
    have h2 := sum_chainGhost_eq_recvChains M h33 gs cs (by simp at hlen; exact hlen)
      (fun rc hrc => hmax rc (List.mem_cons_of_mem _ hrc))
      (fun gc hgc => hinv gc (List.mem_cons_of_mem _ hgc))
    rw [h1, h2]

private theorem sum_recFieldsQ_fieldQLargeLive_eq (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {r : SessionRecord (List (BitVec 8))} (_hr : DeserializeScopeP_Q NonEmptyV1Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    ((recFieldsQ r).map (fieldQLargeLive M)).sum =
      (s.state.receiverChains.map (fun c => vec104LargeLive M (vecCap4Of c.messageKeys.length))).sum +
      bytesLargeLive M s.aliceBaseKey.length +
      (match s.pendingKyberPreKey with
       | none => 0
       | some k => bytesLargeLive M k.ciphertext.length) +
      bytesLargeLive M s.state.pqRatchetState.length := by
  have hle0 : (0 : Nat) ≤ HasFineReallocCredit.smallMaxReq M := Nat.zero_le _
  have hle32 : (32 : Nat) ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hle33 : (33 : Nat) ≤ HasFineReallocCredit.smallMaxReq M := h33
  have hv0 : vec104LargeLive M 0 = 0 := by unfold vec104LargeLive; simp
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base) = GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘
      CryptoVerification.E2E.Record.L1GX.GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  have hpend0 : (((CryptoVerification.E2E.Record.L1GX.pendingFieldX s.pendingPreKey).map
      (fieldQLargeLive M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    rcases s.pendingPreKey with _ | p
    · rfl
    · have hpk : p.baseKey.serialize.length = 33 := serialize_pk_length_cap p.baseKey
      dsimp only [CryptoVerification.E2E.Record.L1GX.pendingFieldX]
      split_ifs <;> rcases p.preKeyId with _ | i <;>
        simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQLargeLive,
          basicFieldLargeLive, basicFieldByteLen, List.sum_cons, List.sum_nil, hpk, hle33]
  have hrecv_eq : ((s.state.receiverChains.map
      (fieldQLargeLive M ∘ fun c => GenFieldQ.base (.recv (recvChainG c)))).sum) =
      (s.state.receiverChains.map (fun c => vec104LargeLive M (vecCap4Of c.messageKeys.length))).sum :=
    rfl
  have habk_eq : (((if s.aliceBaseKey = [] then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.abk s.aliceBaseKey]).map
      (fieldQLargeLive M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) =
      bytesLargeLive M s.aliceBaseKey.length := by
    by_cases he : s.aliceBaseKey = [] <;>
      by_cases hsm : s.aliceBaseKey.length ≤ HasFineReallocCredit.smallMaxReq M <;>
      simp [bytesLargeLive, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQLargeLive,
        basicFieldLargeLive, basicFieldByteLen, List.sum_cons, List.sum_nil, he, hsm]
  have hpq_eq : (((if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]).map (fieldQLargeLive M)).sum) =
      bytesLargeLive M s.state.pqRatchetState.length := by
    by_cases he : s.state.pqRatchetState = [] <;>
      by_cases hsm : s.state.pqRatchetState.length ≤ HasFineReallocCredit.smallMaxReq M <;>
      simp [bytesLargeLive, fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
        List.sum_cons, List.sum_nil, he, hsm]
  have hlik : s.state.localIdentity.serialize.length = 33 := serialize_ik_length_cap _
  have hroot : (keyToBytes32 s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hv_ver : (((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map
      (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
      List.sum_cons, List.sum_nil, hle0]
  have hv_lik : (((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map
      (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
      List.sum_cons, List.sum_nil, hlik, hle33]
  have hv_root : (((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map
      (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
      List.sum_cons, List.sum_nil, hroot, hle32]
  have hpc0 : (((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map
      (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
      List.sum_cons, List.sum_nil, hle0]
  have hrem0 : (((if s.remoteRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.remReg s.remoteRegistrationId]).map
      (fieldQLargeLive M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen, List.sum_cons, List.sum_nil, hle0]
  have hloc0 : (((if s.localRegistrationId = 0 then []
      else [CryptoVerification.E2E.Record.L1GX.GenFieldX.locReg s.localRegistrationId]).map
      (fieldQLargeLive M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen, List.sum_cons, List.sum_nil, hle0]
  have hrik_zero : ∀ ik : IdentityKey,
      (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map
        (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 := fun ik => by
    split_ifs <;> simp [fieldQLargeLive, basicFieldLargeLive, basicFieldByteLen,
      List.sum_cons, List.sum_nil, serialize_ik_length_cap ik, hle33]
  have hsc_zero : ∀ c : SenderChain,
      (([GenField.sender (senderChainG c)].map (fieldQLargeLive M ∘ GenFieldQ.base)).sum) = 0 :=
    fun c => by
      simp [fieldQLargeLive, chainMergeLargeLive, senderChainG,
        List.sum_cons, List.sum_nil, show vecCap4Of 0 = 0 from rfl, hv0]
  have hky_val : ∀ k : PendingKyberPreKey,
      (([CryptoVerification.E2E.Record.L1GX.GenFieldX.kyber k.preKeyId k.ciphertext].map
        (fieldQLargeLive M ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) =
        bytesLargeLive M k.ciphertext.length := fun k => by
    by_cases hsm : k.ciphertext.length ≤ HasFineReallocCredit.smallMaxReq M <;>
      simp [bytesLargeLive, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQLargeLive,
        basicFieldLargeLive, basicFieldByteLen, List.sum_cons, List.sum_nil, hsm]
  simp only [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ,
    CryptoVerification.E2E.Record.L1GX.genFieldsX,
    CryptoVerification.E2E.Record.DeserializeGeneral.genFields, clearPqSession,
    List.map_append, List.map_map, hfn_recv, hfn, List.sum_append,
    ↓reduceIte, List.map_nil, List.sum_nil]
  rw [hv_ver, hv_lik, hv_root, hpc0, hrecv_eq, hpend0, hrem0, hloc0, habk_eq, hpq_eq]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | c <;>
    rcases s.pendingKyberPreKey with _ | k <;>
    simp only [List.map_nil, List.sum_nil, hrik_zero, hsc_zero, hky_val] <;>
    omega

/-- Capacity-aware `SessionStructure` representation bridge (`prostSSGQAtCap_reprA`):
entails `sessionStateReprAt A a G s` with `CanonSession G s`, unconditional
`ssStateLargeLive M G s.state = ssLargeLive M G`, and
`33 ≤ smallMaxReq M → ssLargeLive M G = sessDeserLargeLive M r` — with **zero modifications**
to `sessionStateReprAt` or `sessionRecordAt`. -/
theorem prostSSGQAtCap_reprA (A : RustAlloc)
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (a : BitVec 64) :
    prostSSGQAtCap A a (sessDeserRecvCap r) (ssgqOf s) ⊢
      ∃∗ G : SessionGhost,
        ⌜CanonSession G s ∧
          (∀ M [HasFineReallocCredit M], ssStateLargeLive M G s.state = ssLargeLive M G) ∧
          (∀ M [HasFineReallocCredit M], 33 ≤ HasFineReallocCredit.smallMaxReq M →
            ssLargeLive M G = sessDeserLargeLive M r)⌝ ∗
          sessionStateReprAt A a G s := by
  have ⟨⟨hr_in, _, hr_repr⟩, s', hs', hscope⟩ := hr
  have hss' : s = s' := Option.some.inj (hs.symm.trans hs')
  subst hss'
  obtain ⟨hseeds, -, -⟩ := hr_in s hs
  obtain ⟨hmax_mk, hclamp, hwf, -⟩ := hr_repr s hs
  obtain ⟨-, hpend_fields, hky_fields, -⟩ := hscope
  have henc_lt62 : (encodeRecord r).length < 2 ^ 62 :=
    Nat.lt_trans (encodeRecord_length_ltQ hr) (by decide)
  have habk_lt62 : s.aliceBaseKey.length < 2 ^ 62 := by
    by_cases he : s.aliceBaseKey = []
    · simp [he]
    · have hmem : GenFieldQ.abk s.aliceBaseKey ∈ recFieldsQ r := by
        simp only [recFieldsQ, hs, Symbolic.Swarm.TRREF.B3DeserQ.genFieldsQ, List.mem_append]
        refine Or.inl (List.mem_map.2 ⟨.abk s.aliceBaseKey, ?_, rfl⟩)
        simp [CryptoVerification.E2E.Record.L1GX.genFieldsX, clearPqSession, he]
      have hok : s.aliceBaseKey.length = 33 := recFieldsQ_ok r hr _ hmem
      omega
  have hpq_lt62 : s.state.pqRatchetState.length < 2 ^ 62 :=
    Nat.lt_of_le_of_lt (pq_length_le_encodeRecord hr hs) henc_lt62
  have hky_lt62 : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 62 := by
    intro k hk
    have hok : k.ciphertext.length = 1569 := hky_fields k hk
    omega
  unfold prostSSGQAtCap
  rw [kyberAtCap_eq_kyberAt14Cap_sep]
  have hrecv := prostRecvGCap_entails_vecAt_chainAt_cap A s hseeds hmax_mk (sessDeserRecvCap r) (a + 0x48#64)
  have hsender := prostSenderGCap_entails_optSenderChainAt_cap A s.state.senderChain hclamp a
  have hpending := prostPendingCap_entails_optTailVecAt_cap A s hwf hpend_fields a
  have hky := prostKyberCap_entails_optTailVecAt_cap A s.pendingKyberPreKey a
  dsimp only [ssgqOf, ssgOf] at hrecv hsender hky ⊢
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hrecv)))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun chainsPtr => Entails.sepExists_elim fun chains => ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hchains_len, hchains_inv⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hsender))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro sg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hsender_canon, hsender_ll⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hpending)))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hpending_canon, hpending_rel, hpending_some, hpending_ll⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro kg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hkyber_rel, hkyber_ll⟩
  unfold vecU8FreshCap
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun pqPtr =>
    Entails.sepExists_elim fun alicePtr =>
    Entails.sepExists_elim fun rootPtr =>
    Entails.sepExists_elim fun rikPtr =>
    Entails.sepExists_elim fun likPtr => ?_
  set rikBytes := (s.state.remoteIdentity.map IdentityKey.serialize).getD []
  let G : SessionGhost := {
    localIk := ⟨bytesMergeOutCap 0#64 s.state.localIdentity.serialize.length, likPtr,
      s.state.localIdentity.serialize⟩
    remoteIk := ⟨bytesMergeOutCap 0#64 rikBytes.length, rikPtr, rikBytes⟩
    root := ⟨bytesMergeOutCap 0#64 (keyToBytes32 s.state.rootKey).length, rootPtr⟩
    chainsCap := BitVec.ofNat 64 (sessDeserRecvCap r)
    chainsPtr := chainsPtr
    chains := chains
    alice := ⟨bytesMergeOutCap 0#64 s.aliceBaseKey.length, alicePtr, s.aliceBaseKey⟩
    pq := ⟨bytesMergeOutCap 0#64 s.state.pqRatchetState.length, pqPtr⟩
    sender := sg, pending := pg, kyber := kg
    regIds := unpack32 s.remoteRegistrationId ++ unpack32 s.localRegistrationId }
  refine Entails.sepExists_right G ?_
  have hchains_canon : ∀ gc ∈ chains.zip s.state.receiverChains, CanonChain gc :=
    fun gc hgc => (hchains_inv gc hgc).1
  have hcanon : CanonSession G s :=
    ⟨rfl, rfl, hsender_canon, hchains_len, hchains_canon, hpending_canon⟩
  have hstate_eq : ∀ M [HasFineReallocCredit M], ssStateLargeLive M G s.state = ssLargeLive M G := by
    intro M _
    unfold ssStateLargeLive ssLargeLive
    rw [sum_chainPair_eq_chainGhost M chains s.state.receiverChains hchains_len hchains_inv]
  have hdeser_eq : ∀ M [HasFineReallocCredit M], 33 ≤ HasFineReallocCredit.smallMaxReq M →
      ssLargeLive M G = sessDeserLargeLive M r := by
    intro M _ h33
    have h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hrc_lt : sessDeserRecvCap r < 2 ^ 64 := by
      unfold sessDeserRecvCap
      have h1 := vecCap4Of_le_mono (recvCount_recFieldsQ_le hr)
      have h2 : vecCap4Of 5 = 8 := by decide
      omega
    have hlik0 : bytesLargeLive M G.localIk.cap.toNat = 0 := by
      dsimp only [G]
      rw [bytesLargeLive_bytesMergeOutCap M h8 (by rw [serialize_ik_length_cap]; decide),
        serialize_ik_length_cap]
      exact bytesLargeLive_eq_zero_of_le M (by omega)
    have hrik0 : bytesLargeLive M G.remoteIk.cap.toNat = 0 := by
      dsimp only [G, rikBytes]
      rcases s.state.remoteIdentity with _ | ik
      · simp [bytesMergeOutCap_zero_zero, bytesLargeLive_eq_zero_of_le M (n := 0) (by omega)]
      · simp only [Option.map, Option.getD, serialize_ik_length_cap]
        rw [bytesLargeLive_bytesMergeOutCap M h8 (by decide)]
        exact bytesLargeLive_eq_zero_of_le M (by omega)
    have hroot0 : bytesLargeLive M G.root.cap.toNat = 0 := by
      dsimp only [G]
      have hrlen : (keyToBytes32 s.state.rootKey).length = 32 := by simp [keyToBytes32]
      rw [hrlen, bytesLargeLive_bytesMergeOutCap M h8 (by decide)]
      exact bytesLargeLive_eq_zero_of_le M (by omega)
    have halice_ll : bytesLargeLive M G.alice.cap.toNat = bytesLargeLive M s.aliceBaseKey.length :=
      bytesLargeLive_bytesMergeOutCap M h8 habk_lt62
    have hpq_ll : bytesLargeLive M G.pq.cap.toNat = bytesLargeLive M s.state.pqRatchetState.length :=
      bytesLargeLive_bytesMergeOutCap M h8 hpq_lt62
    have hch_cap : G.chainsCap.toNat = sessDeserRecvCap r := by
      dsimp only [G]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrc_lt]
    have hch_sum := sum_chainGhost_eq_recvChains M h33 chains s.state.receiverChains
      hchains_len hmax_mk hchains_inv
    unfold ssLargeLive sessDeserLargeLive
    rw [hlik0, hrik0, hroot0, hch_cap, halice_ll, hpq_ll]
    dsimp only [G]
    rw [hch_sum, hpending_ll M h33, hkyber_ll M h8 hky_lt62,
      sum_recFieldsQ_fieldQLargeLive_eq M h33 hr hs]
    have hsg0 := hsender_ll M h33
    rcases sg with _ | sg0 <;> rcases s.pendingKyberPreKey with _ | k0 <;>
      dsimp only at hsg0 ⊢ <;> omega
  refine Entails.pure_right ⟨hcanon, hstate_eq, hdeser_eq⟩ ?_
  unfold sessionStateReprAt
  have hreg1 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      List.range, List.range.loop, List.map]; rfl
  have hreg2 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    simp only [G, leBytes, unpack32, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      List.range, List.range.loop, List.map]; rfl
  refine Entails.pure_right ⟨hpending_rel, hkyber_rel, rfl, hreg1, hreg2⟩ ?_
  unfold sessionStateAt
  have hrem_deser :
      match s.state.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey := by
    dsimp only [G, rikBytes]
    rcases s.state.remoteIdentity with _ | ik
    · rfl
    · exact deserialize_serialize_pk_cap ik.publicKey
  have hrem_len : s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33 := by
    dsimp only [G, rikBytes]
    rcases s.state.remoteIdentity with _ | ik <;> simp [serialize_ik_length_cap]
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_cap s.state.localIdentity.publicKey,
      hrem_deser, hchains_len, hpending_some, rfl,
      serialize_ik_length_cap s.state.localIdentity, hrem_len⟩ ?_
  dsimp only [G, rikBytes, vecGhostAt]
  have ha150 : a + 0x150#64 + 4#64 = a + 0x154#64 := by rw [BitVec.add_assoc]; rfl
  rw [pointsToBytes_append, unpack32_length, ha150,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  exact Entails.refl _

private theorem vecAt_prev_zero_eq_cap (A : RustAlloc) (out : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp]
  rw [eq_true hpure, pure_true, sepConj_emp]

/-- Record-level representation bridge (`deserReprCapQA_ok`):
rewrites the raw output at `out` into `sessionRecordAt A out g r` with `CanonRecord g r`,
`ssStateLargeLive M G s_sess.state = ssLargeLive M G`, and
`33 ≤ smallMaxReq M → ssLargeLive M G = sessDeserLargeLive M r`. -/
theorem deserReprCapQA_ok (M : AllocCostModel) [HasFineReallocCredit M] (A : RustAlloc)
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (out : BitVec 64) :
    ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
      prostSSGQAtCap A (out + 0x18#64) (sessDeserRecvCap r)
        (ssgqAfter r (recFieldsQ r).length)) ⊢
      ∃∗ g : RecordGhost,
        ⌜CanonRecord g r ∧
          (∀ G, g.cur = some G →
            (∀ s_sess, r.currentSession = some s_sess →
              ssStateLargeLive M G s_sess.state = ssLargeLive M G) ∧
            (33 ≤ HasFineReallocCredit.smallMaxReq M →
              ssLargeLive M G = sessDeserLargeLive M r))⌝ ∗
          sessionRecordAt A out g r := by
  obtain ⟨s, hs, _⟩ := hr.2
  rw [ssgqAfter_recFieldsQ r hr s hs]
  have hgrp :
      ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
        prostSSGQAtCap A (out + 0x18#64) (sessDeserRecvCap r) (ssgqOf s)) =
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        prostSSGQAtCap A (out + 0x18#64) (sessDeserRecvCap r) (ssgqOf s)) := by sep_ac_rfl
  rw [hgrp]
  refine Entails.trans (sepConj_mono_right (prostSSGQAtCap_reprA A r hr s hs (out + 0x18#64))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hcanon, hstate_eq, hdeser_eq⟩ => ?_
  refine Entails.sepExists_right ⟨0#64, 8#64, some G⟩ ?_
  refine Entails.pure_right ⟨?_, ?_⟩ ?_
  · unfold CanonRecord CanonCur
    rw [hs]
    exact hcanon
  · intro G' hG'
    injection hG' with hG'
    subst hG'
    refine ⟨fun s_sess hs_sess => ?_, fun h33 => hdeser_eq M h33⟩
    have hse : s_sess = s := Option.some.inj (hs_sess.symm.trans hs)
    subst hse
    exact hstate_eq M
  · unfold sessionRecordAt
    rw [hs]
    dsimp only
    rw [vecAt_prev_zero_eq_cap A]
    exact Entails.refl _


/-! ## 4. Capacity-Aware Loop Invariant, Entry, & Iteration -/

/-- Outer field-loop budget invariant for `SessionRecord::deserialize` (Block `46`, `lsProg_46 H`). -/
def DeserLoopBudgetInv [LibsignalPlacement]
    (M : AllocCostModel) [HasFineReallocCredit M]
    (_A : RustCliAllocBudget M) (lim : BudgetLimits)
    (r : SessionRecord (List (BitVec 8))) (st₀ : M.σ) (k : Nat) (st : M.σ) : Prop :=
  st = M.stepEvents (sessDeserEventsPrefix r k) st₀ ∧
    FitsEvents M lim st₀ (sessDeserEvents r)

/-- Capacity-explicit counterpart of `deserLocalsQ` at `L = deserSpL s0.sp`. -/
def deserLocalsQCap (A : RustAlloc) (L p : BitVec 64)
    (bs rest : List (BitVec 8)) (capRecv : Nat) (v : SSGQ) : SepProp :=
  memRegion L 0x3f8 ∗
    sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGQAtCap A (L + 0x420#64) capRecv v ∗
    memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
    memRegion (L + 0x6f0#64) 0x20

section LoopBody

open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_lscl_vm sepWP_seq_vmPreserved
  subroutine_ok_withLsCl_withVmPreserved_withHookStack_mono
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  mergeFieldQBudgetRawSpecW mergeFieldQFitsEvents fitsEvents_mergeFieldQFits_of_events
)
@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_sdb (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl
open CryptoVerification.LibsignalProtoCodec (encodeVarintAux encodeVarint_ne_nil)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSliceGhost VarintSlicePre sliceCursorAt sliceCursorAfter
)

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp.ofNat_succ_sub_one_loopIter

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_sdb (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setPC_sdb (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_sdb (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_advancePC_sdb (s : State) :
    s.advancePC.tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setPState_sdb (s : State) (ps : PState) :
    (s.setPState ps).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeReg64_sdb (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeReg32_sdb (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeReg_sdb (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases w <;> cases r <;> rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeVReg128_sdb (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_sdb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_sdb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_sdb (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_sdb (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local simp, local arm64_norm]
private theorem int64_toBitVec_mk_sdb (u : UInt64) :
    ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl
@[local simp, local arm64_norm]
private theorem uint64_toBitVec_mk_sdb (v : BitVec 64) :
    ({ toBitVec := v } : UInt64).toBitVec = v := rfl
@[local simp, local arm64_norm]
private theorem bitVec_toFin_mk_64_sdb (n : Nat) (h : n < 18446744073709551616 := by decide) :
    ({ toFin := ⟨n, h⟩ } : BitVec 64) = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm
@[local arm64_norm]
private theorem int64_raw_toBitVec_sdb (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm
@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1904_sub_96_sdb (L : BitVec 64) :
    L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_1808_sdb (L : BitVec 64) :
    L + 1808#64 - 1808#64 = L := by bv_omega
@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_40_sdb (L : BitVec 64) :
    L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

/-- Machine-state loop invariant at `deserPlacedPC 0x254#64 = (blkPl_46).base + 596#64`. -/
private def DeserLoopStateInv [LibsignalPlacement]
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (st₀ : M.σ) (k : Nat) (s : State) : Prop :=
  s.pc = (blkPl_46).base + 596#64 ∧
  s.status = .Running ∧
  (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
  LibsignalCodeRoLoaded lsmpl s.mem ∧
  s.sp = deserSpL s0.sp ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
  s.readReg64 .x19 = x.out ∧
  s.readReg64 .x20 = 0#64 ∧
  s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
  ∃ st, DeserLoopBudgetInv M A lim x.r st₀ k st ∧
    s.mem ⊨ deserLocalsQCap A.repAlloc (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc)
        (vecCap4Of (recvCount ((recFieldsQ x.r).take k)))
        (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ A.pool lim st s ∗
      stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R

private theorem encodeVarint_of_lt_128_sdb {n : Nat} (hn : n < 128) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

private theorem encodeVarint_cons_of_ge_128_sdb {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 62) :
    encodeVarint (BitVec.ofNat 64 n) =
      BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn,
    show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7,
    show (0x80 : BitVec 64).toNat = 128 from rfl,
    Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

private theorem signExtend64_bit63_eq_false_iff_sdb (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

private theorem signExtend64_bit63_eq_true_iff_sdb (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

private theorem signExtend64_eq_zeroExtend64_of_le_sdb (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

private theorem signExtend64_ofNat8_lt_128_sdb {n : Nat} (hn : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_sdb _ hle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

private theorem sp_sub_1904_aligned_sdb {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'
  have hlt := sp0.isLt
  have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega
  · rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega

private theorem pointsTo64_zero_split32_sdb (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private theorem empty_vecU8FreshCap_sdb (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8FreshCap A v [] :=
  emptyCells_entails_vecU8FreshCap A v 1#64 (by decide)

private theorem empty_vecChainGCap_sdb (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptrRecv : BitVec 64,
        vecAt A 104 8 (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c)
          v 0#64 ptrRecv [] := by
  refine Entails.sepExists_right 8#64 ?_
  dsimp only [vecAt, vecHeader, vecBuf]
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (fun c a => prostChainGAtCap A a (vecCap4Of c.keys.length) c) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  exact Entails.pure_right (by decide) (Entails.refl _)

private def ssRawCells_sdb (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗
  (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗
  (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗
  (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗
  ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGQAtCap_empty_intro_sdb (A : RustAlloc) (L : BitVec 64) :
    ssRawCells_sdb L ∗ memRegion (L + 0x4b8#64) 96 ∗
      memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢
      prostSSGQAtCap A (L + 0x420#64) 0 ⟨SSG.empty, ExtraGQ.empty⟩ := by
  unfold ssRawCells_sdb prostSSGQAtCap pendingAt9PCap kyberAtCap
    SSGQ.toSSGX SSG.empty ExtraGQ.empty
  dsimp only [BitVec.ofNat_eq_ofNat]
  have h1 := empty_vecU8FreshCap_sdb A (L + 0x420#64)
  have h2 := empty_vecU8FreshCap_sdb A (L + 0x420#64 + 0x18#64)
  have h3 := empty_vecU8FreshCap_sdb A (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainGCap_sdb A (L + 0x420#64 + 0x48#64)
  have h5 := empty_vecU8FreshCap_sdb A (L + 0x420#64 + 0x60#64)
  have h6 := empty_vecU8FreshCap_sdb A (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_sdb (L + 0x568#64), pointsTo64_zero_split32_sdb (L + 0x570#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

private def deserSavedAt_sdb (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSavedAt_eq_sdb (s0 : State) :
    deserSavedAt_sdb (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_sdb deserSaved deserSpL; dsimp only
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

private def ssUninitCells_sdb (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) :
    SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗
  ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗
  ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗
  ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗ ((L + 1152#64) ↦₆₄ c12) ∗
  ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗
  ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗
  ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗
  ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)

private def step1aPre_sdb (L p : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗
  ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗
  ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗
  ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗
  ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗
  ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗
  ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗
  ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗
  ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)

private def step1aPost_sdb (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_sdb L s0 ∗ (L ↦₆₄ 0#64) ∗
  ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
  ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
  ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)

private theorem memRegion_succ8_sdb (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_sdb (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64,
      ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64,
      ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_sdb L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide),
    memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_sdb
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  sep_ac_rfl

private theorem memRegion_1904_split_sdb (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_sdb L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 8 1896 (by decide),
    memRegion_split (L + 8#64) 1008 888 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 840 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 504 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 136 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 128 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64 + 8#64) 32 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 1; simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_sdb, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_sdb
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  sep_ac_rfl

private theorem stackAt_recDeserialize_split_sdb (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack =
      stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 =
    memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private def deserFixedLocalsCap_sdb (A : RustAlloc) (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
    ((L + 0x418#64) ↦₆₄ 0#64) ∗ prostSSGQAtCap A (L + 0x420#64) 0 ⟨SSG.empty, ExtraGQ.empty⟩ ∗
    memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_sdb (A : RustAlloc) (L p : BitVec 64) (len1 : Nat) (s0 : State)
    (hL : L = deserSpL s0.sp) :
    ssRawCells_sdb L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗
      memRegion (L + 1360#64) 24 ∗ deserSavedAt_sdb L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
      ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗
      memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsCap_sdb A L ∗ deserSaved s0 := by
  have hss := prostSSGQAtCap_empty_intro_sdb A L
  have hm0 : (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
    rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)
  have hds : deserSavedAt_sdb L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_sdb s0
  unfold deserFixedLocalsCap_sdb
  rw [hds,
    show (0x408#64 : BitVec 64) = 1032#64 from rfl,
    show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl,
    show (0x6f0#64 : BitVec 64) = 1776#64 from rfl,
    show (0x20 : Nat) = 32 from rfl]
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (Entails.trans (sepConj_mono (sepConj_mono hss hm0)
      (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
        ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        memRegion (L + 1776#64) 32 ∗ deserSaved s0))) (Entails.of_eq (by sep_ac_rfl)))

private theorem scratch24_368_fold_sdb (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
      ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) = ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_sdb (L + 1400#64)).symm
    rwa [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs
  rw [← sepConj_assoc, h0, memRegion_split (L + 1400#64) 24 344 (by decide),
    memRegion_split (L + 1400#64) 8 16 (by decide), memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
      (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v)
        (pointsTo64_entails_memRegion (L + 1416#64) w))) (Entails.refl _))

private def step2aPre_sdb (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2aPost_sdb (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2bPre_sdb (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))

private def step2bPostPre_sdb (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))

private def step2bPostPost_sdb (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)

private theorem deserLocalsQCap_of_2a_sdb (A : RustAlloc) (L p : BitVec 64)
    (bs body : List (BitVec 8))
    (heq : bs = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 body.length) ++ body)
    (hN : body.length < 128) :
    step2aPost_sdb L p body.length ∗ ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsCap_sdb A L =
    deserLocalsQCap A L p bs body 0 ⟨SSG.empty, ExtraGQ.empty⟩ := by
  have hpfx : bs = 0x0a#8 :: BitVec.ofNat 8 body.length :: body := by
    rw [heq, show encodeKey 1 .lengthDelimited = [0x0a#8] from rfl,
      encodeVarint_of_lt_128_sdb hN]; rfl
  have hsub : bs.length - body.length = 2 := by
    rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ bs) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗
        ((p + 1#64 + 1#64) ↦ₛ body) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsQCap sliceCursorAfter deserFixedLocalsCap_sdb step2aPost_sdb
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  sep_ac_rfl

private theorem deserLocalsQCap_of_2b_sdb (A : RustAlloc) (L p : BitVec 64)
    (bs body : List (BitVec 8))
    (heq : bs = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 body.length) ++ body) :
    let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_sdb L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocalsCap_sdb A L ⊢
    deserLocalsQCap A L p bs body 0 ⟨SSG.empty, ExtraGQ.empty⟩ := by
  intro vlen
  have hfold : step2bPostPost_sdb L p vlen body.length ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 body.length) := by
    unfold step2bPostPost_sdb
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 body.length))
        (scratch24_368_fold_sdb L (BitVec.ofNat 64 body.length) (BitVec.ofNat 64 vlen)))
  refine Entails.trans (sepConj_mono_left hfold) ?_
  have hpfx : bs = 0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by
    rw [heq]; rfl
  have hsub : bs.length - body.length = 1 + vlen := by
    rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ bs) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsQCap sliceCursorAfter deserFixedLocalsCap_sdb
  rw [hsub, hptr, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_1a_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2 ^ 62)
    (hnext : ∀ s1 : State, s1.pc = (blkPl_46).base + 260#64 → s1.status = .Running →
      s1.sp = L → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      s1.readReg64 .x0 = 2#64 → s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_sdb L p len1 s0)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 260#64) s0
      (step1aPre_sdb L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      (fun s1 P1 => VmPreserved s0 s1 ∧ post s1 P1) := by
  dsimp only [lsProg_46]
  unfold step1aPre_sdb
  have hcbz : (BitVec.ofNat 64 (1 + len1) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + len1 = 0 at hnat; omega
  have hsub1 : BitVec.ofNat 64 (1 + len1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + len1) - 1#64 = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  by_vm_steps (
    (iterate 49 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])) ?_
    unfold step1aPost_sdb deserSavedAt_sdb; rw [hnone]
    simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
      Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_1b_vm_sdb [LibsignalPlacement] {H : LibsignalHooks} (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 348#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = s.readReg64 .x19 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = s.readReg64 .x29 → post s' (ssRawCells_sdb L)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 348#64) s
      (ssUninitCells_sdb L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      (fun s' P' => VmPreserved s s' ∧ post s' P') := by
  dsimp only [lsProg_46]
  unfold ssUninitCells_sdb
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  by_vm_steps (
    (iterate 22 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
    unfold ssRawCells_sdb; rw [hnone]; sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_2a_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_sdb L p N)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s (step2aPre_sdb L p N)
      (fun s' P' => VmPreserved s s' ∧ post s' P') := by
  dsimp only [lsProg_46]
  unfold step2aPre_sdb
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_sdb hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_sdb (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hsub1 : BitVec.ofNat 64 (1 + N) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + N) - 1#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  by_vm_steps (
    (iterate 14 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
    unfold step2aPost_sdb; sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_2b_pre_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hVN_lt : vlen + N < 2 ^ 62)
    (hnext : ∀ s' : State, s'.pc = lsmpl.base 76 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .lr = (blkPl_46).base + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_sdb L p vlen N)) :
    SepWP (lsProg_46 H) (lsmpl.base 76) s (step2bPre_sdb L p vlen N)
      (fun s' P' => VmPreserved s s' ∧ post s' P') := by
  dsimp only [lsProg_46]
  unfold step2bPre_sdb
  have hcbz : (BitVec.ofNat 64 (vlen + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change vlen + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_sdb (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (vlen + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (vlen + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  by_vm_steps (
    (iterate 10 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])) ?_
    unfold step2bPre_sdb; sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem step_2b_post_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hVN_lt : vlen + N < 2 ^ 62)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_sdb L p vlen N)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s (step2bPostPre_sdb L p vlen N)
      (fun s' P' => VmPreserved s s' ∧ post s' P') := by
  dsimp only [lsProg_46]
  unfold step2bPostPre_sdb
  have hsub2 : BitVec.ofNat 64 (vlen + N) - BitVec.ofNat 64 vlen = BitVec.ofNat 64 N := by
    rw [BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (vlen + N)).ult (BitVec.ofNat 64 vlen) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show vlen < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  by_vm_steps (
    (iterate 14 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
    unfold step2bPostPost_sdb; sep_ac_rfl)

set_option maxHeartbeats 1200000 in
private theorem step_1_combined_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (A : RustAlloc) (p out : BitVec 64) (bs body : List (BitVec 8)) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s0.readReg64 .x8 = out)
    (heq : bs = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 body.length) ++ body)
    (hrec_lt : bs.length < 2 ^ 62) (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (p ↦ₛ bs) ∗ memRegion out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (lsProg_46 H).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp
    let rest1 := encodeVarint (BitVec.ofNat 64 body.length) ++ body
    ∃ s2, Steps (lsProg_46 H) s0 s2 ∧ VmPreserved s0 s2 ∧ s2.pc = (blkPl_46).base + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧
      (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
      s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = L + 1032#64 ∧
      s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨
        (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsCap_sdb A L ∗ deserSaved s0) ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_sdb (decide_eq_true_iff.mp hal)
  have hbs_cons : bs = 0x0a#8 :: rest1 := by rw [heq]; rfl
  have hv_pos : 0 < (encodeVarint (BitVec.ofNat 64 body.length)).length :=
    List.length_pos_iff.mpr (encodeVarint_ne_nil _)
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2 ^ 62 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by
    rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (p ↦₈ 0x0a#8)) ∗
      (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_sdb s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; sep_ac_rfl
  rw [memRegion_1904_split_sdb L p] at hm0a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0,
    u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨
      step1aPre_sdb L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    convert hm0b using 1; sep_ac_rfl
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hvm1, rfl,
    hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1a_vm_sdb L p out rest1.length
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_sdb L p rest1.length s0 ∧
        s'.sp = L ∧ (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧
        s'.readReg64 .x0 = 2#64 ∧ s'.readReg64 .x19 = out ∧ s'.readReg64 .x21 = noneCap ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x24 = 1#64 ∧
        s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun _ _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' =>
        ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_sdb L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_sdb at hm1; convert hm1 using 1; sep_ac_rfl
  rw [memRegion_1064_336_cells_sdb L] at hm1a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨
      ssUninitCells_sdb L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_sdb L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_sdb at hm1b ⊢; convert hm1b using 1; sep_ac_rfl
  obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, hvm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1b_vm_sdb L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_sdb L ∧
        s'.sp = L ∧ (s'.trace = s1.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s1) ∧
        s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun _ _ _ hsp' htr' hx19' hx23' hx29' =>
        ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s2, hst1.trans hst2, hvm1.trans hvm2, hpc2, hrun2, hsp2,
    ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_sdb A L p rest1.length s0 rfl)) hm2

set_option maxHeartbeats 1600000 in
private theorem deserLoopEntryQBudget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (st₀ : M.σ) (hfit0 : FitsEvents M lim st₀ (sessDeserEvents x.r))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length)
    (hx8 : s0.readReg64 .x8 = x.out) (hal : s0.spAligned = true)
    (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗
      A.pool lim st₀ s0 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL0 : (lsProg_46 H).CodeLoaded s0.mem) :
    ∃ s', Steps (lsProg_46 H) s0 s' ∧
      DeserLoopStateInv M A lim x R s0 st₀ 0 s' := by
  have heq := encodeRecord_eq_recFieldsQ x.r hr
  have hrec_lt : (encodeRecord x.r).length < 2 ^ 62 :=
    Nat.lt_trans (encodeRecord_length_ltQ hr) (by decide)
  obtain ⟨halignL, _⟩ := sp_sub_1904_aligned_sdb (decide_eq_true_iff.mp hal)
  have hm0' : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗
      stackAt s0.sp recDeserializeStack ∗ (A.pool lim st₀ s0 ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  set body := (recFieldsQ x.r).flatMap GenFieldQ.enc
  obtain ⟨s2, hst2, hvm12, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_vm_sdb A.repAlloc x.p x.out (encodeRecord x.r) body
      (A.pool lim st₀ s0 ∗ R) s0 hpc hrun hx0 hx1 hx8 heq hrec_lt hal hm0' hL0
  set L := deserSpL s0.sp
  set N := body.length
  set rest1 := encodeVarint (BitVec.ofNat 64 N) ++ body
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by rw [heq]; rfl
  have hrest1_lt : rest1.length < 2 ^ 62 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hinv0 : DeserLoopBudgetInv M A lim x.r st₀ 0 st₀ := ⟨rfl, hfit0⟩
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: body := by
      simp only [rest1, encodeVarint_of_lt_128_sdb hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_sdb L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ body) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsCap_sdb A.repAlloc L ∗ deserSaved s0 ∗
          memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool lim st₀ s0 ∗ R)) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2
      unfold step2aPre_sdb; convert hm2 using 1; sep_ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hvm23, rfl, hsp3, htr3,
      hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2a_vm_sdb L x.p x.out N
        (post := fun s' P => P = step2aPost_sdb L x.p N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x20 = 0#64 ∧
          s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN
        (fun _ _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hvm03 := hvm12.trans hvm23
    refine ⟨s3, hst2.trans hst3, hpc3, hrun3,
      ⟨htr3.1.trans htr2.1, htr3.2.trans htr2.2⟩,
      hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen,
      hsp3, by rw [State.spAligned, hsp3]; exact decide_eq_true halignL,
      hx29_3, hx19_3, hx20_3, hx23_3, st₀, hinv0, ?_⟩
    rw [← A.pool_transport lim st₀ s0 s3 hvm03] at hm3
    have hloc := deserLocalsQCap_of_2a_sdb A.repAlloc L x.p (encodeRecord x.r) body heq hN
    change s3.mem ⊨ deserLocalsQCap A.repAlloc L x.p (encodeRecord x.r) body 0
        ⟨SSG.empty, ExtraGQ.empty⟩ ∗
      memRegion x.out 368 ∗ A.pool lim st₀ s3 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [← hloc]; convert hm3 using 1; sep_ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    set vlen := (encodeVarint (BitVec.ofNat 64 N)).length
    set vtail := encodeVarintAux 9 (BitVec.ofNat 64 N >>> 7)
    have hlen1 : rest1.length = vlen + N := List.length_append
    have hVN_lt : vlen + N < 2 ^ 62 := by rw [← hlen1]; exact hrest1_lt
    have hN_lt : N < 2 ^ 62 := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: (vtail ++ body) := by
      simp only [rest1, vtail, encodeVarint_cons_of_ge_128_sdb hN_ge hN_lt, List.cons_append]
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) =
        ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗
          ((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_sdb L x.p vlen N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) ∗
          (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocalsCap_sdb A.repAlloc L ∗
          deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗
          (A.pool lim st₀ s0 ∗ R)) := by
      rw [hlen1, hm2_bytes] at hm2
      unfold step2bPre_sdb; convert hm2 using 1; sep_ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hvm23, rfl,
      hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2b_pre_vm_sdb L x.p x.out vlen N
        (post := fun s' P => P = step2bPre_sdb L x.p vlen N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .lr = (blkPl_46).base + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hVN_lt
        (fun _ _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim
        hm2c (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : VarintSlicePre rest1 := Or.inl (by omega)
    have hcrl3 : LibsignalCodeRoLoaded lsmpl s3.mem :=
      hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen
    have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, body) :=
      decodeVarint_encodeVarint (BitVec.ofNat 64 N) body
    have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 76)
        (withLsCl lsmpl (decodeVarintSliceSomeSpecGen (deserCalleeStack - 0x50))) :=
      decode_varint_slice_some_placed_ok_cl (callerProg := lsProg_46 H)
        (errStack := deserCalleeStack - 0x50) (by decide)
    let gvar : DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp :=
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗
        memRegion (L + 1424#64) 344 ∗ (x.p ↦₈ 0x0a#8) ∗
        deserFixedLocalsCap_sdb A.repAlloc L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗
        A.pool lim st₀ s0
    have hstk_eq : 0x50 + (deserCalleeStack - 0x50) = deserCalleeStack := by decide
    have hm3_call : s3.mem ⊨
        (withLsCl lsmpl (decodeVarintSliceSomeSpecGen (deserCalleeStack - 0x50))).pre
          (gvar, BitVec.ofNat 64 N, body) s3 ∗ (F_call ∗ R) := by
      dsimp only [withLsCl, decodeVarintSliceSomeSpecGen, gvar]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl3.1, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx1_3, hx2_3_nat, by omega, hpre_slice, hdec⟩, ?_⟩
      unfold step2bPre_sdb at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide),
        show L + 1400#64 + 24#64 = L + 1424#64 by bv_omega] at hm3
      dsimp only [F_call]
      rw [hsp3, hstk_eq, hm2_bytes]
      convert hm3 using 1; sep_ac_rfl
    obtain ⟨s4, hst4, hpost4, _⟩ :=
      hcall.no_fault_before_outcome (gvar, BitVec.ofNat 64 N, body) (F_call ∗ R)
        s3 hpc3 hrun3 hm3_call hal3 ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ |
        ⟨_, hm4_pan⟩ | ⟨_, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = (blkPl_46).base + 540#64 := by rw [hpc4, hlr_3]
      have hsp4' : s4.sp = L := by rw [hsp4, hsp3]
      have hx19_4 : s4.readReg64 .x19 = x.out := by rw [hcs4.1, hx19_3]
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by rw [hcs4.2.1, hx20_3]
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by rw [hcs4.2.2.2.2.1, hx23_3]
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by rw [hcs4.2.2.2.2.2.2.2.2.2.2.1, hx29_3]
      have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
        hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (htr3.2.trans htr2.2)
      have hsub1 : rest1.length - body.length = vlen := by
        rw [hlen1]; change (vlen + N) - N = vlen; omega
      dsimp only [withLsCl, decodeVarintSliceSomeSpecGen, gvar] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨_hcl4, hm4⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨⟨htr4, hvm34⟩, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_sdb L x.p vlen N ∗
          (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
            deserFixedLocalsCap_sdb A.repAlloc L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗
            stackAt L deserCalleeStack ∗ (A.pool lim st₀ s0 ∗ R)) := by
        dsimp only [F_call] at hm4
        unfold step2bPostPre_sdb
        rw [hsp3, hstk_eq, pointsTo64_zero_split32_sdb (L + 1400#64), hsub1,
          show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega,
          show L + 1400#64 + 8#64 = L + 1408#64 by bv_omega,
          show L + 1400#64 + 16#64 = L + 1416#64 by bv_omega] at hm4
        convert hm4 using 1; sep_ac_rfl
      obtain ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, hvm45, rfl, hsp5, htr5,
        hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, _hoom⟩⟩ :=
        (step_2b_post_vm_sdb L x.p x.out vlen N
          (post := fun s' P => P = step2bPostPost_sdb L x.p vlen N ∧
            s'.sp = L ∧ (s'.trace = s4.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s4) ∧
            s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x20 = 0#64 ∧
            s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hVN_lt
          (fun _ _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim
          hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hsteps_all := (hst2.trans (hst3.trans hst4)).trans hst5
      have hvm05 := ((hvm12.trans hvm23).trans hvm34).trans hvm45
      refine ⟨s5, hsteps_all, hpc5, hrun5,
        ⟨(htr5.1.trans htr4).trans (htr3.1.trans htr2.1), htr5.2.trans hv4⟩,
        hcrl0.of_keepsFrozen hsteps_all.keepsFrozen,
        hsp5, by rw [State.spAligned, hsp5]; exact decide_eq_true halignL,
        hx29_5, hx19_5, hx20_5, hx23_5, st₀, hinv0, ?_⟩
      rw [← A.pool_transport lim st₀ s0 s5 hvm05] at hm5
      have hm5a : s5.mem ⊨
          ((step2bPostPost_sdb L x.p vlen N ∗ memRegion (L + 1424#64) 344) ∗
            ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsCap_sdb A.repAlloc L) ∗
          (memRegion x.out 368 ∗ A.pool lim st₀ s5 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
        convert hm5 using 1; sep_ac_rfl
      exact Satisfies.mono
        (sepConj_mono_left (deserLocalsQCap_of_2b_sdb A.repAlloc L x.p (encodeRecord x.r) body heq))
        hm5a
    · exact False.elim (not_satisfies_false_sepConj hm4_pan)
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

private def keyByte_sdb (fl : GenFieldQ) : BitVec 8 :=
  BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)

private theorem enc_eq_keyByte_cons_sdb (fl : GenFieldQ) :
    fl.enc = keyByte_sdb fl :: fl.payload := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem drop_flatMap_enc_sdb {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r).drop k).flatMap GenFieldQ.enc =
      (recFieldsQ r)[k].enc ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

private theorem ssgqAfter_succ_sdb {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    ssgqAfter r (k + 1) = (ssgqAfter r k).apply (recFieldsQ r)[k] := by
  simp only [ssgqAfter, List.take_succ_eq_append_getElem hk,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

private def preBytes_sdb (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++
    ((recFieldsQ r).take k).flatMap GenFieldQ.enc

private def curPtr_sdb (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) :
    BitVec 64 :=
  p + BitVec.ofNat 64 (preBytes_sdb r k).length

private theorem encodeRecord_eq_preBytes_append_sdb {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    encodeRecord r = preBytes_sdb r k ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
  have hs : (recFieldsQ r).flatMap GenFieldQ.enc =
      ((recFieldsQ r).take k).flatMap GenFieldQ.enc ++
        ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFieldsQ r hr, preBytes_sdb,
    List.append_assoc, List.append_assoc, ← hs, ← List.append_assoc]

private theorem payload_rest_length_lt_sdb {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length < 2 ^ 33 := by
  have h1 := encodeRecord_length_ltQ hr
  rw [encodeRecord_eq_preBytes_append_sdb hr k, drop_flatMap_enc_sdb hk,
    enc_eq_keyByte_cons_sdb, List.cons_append, List.length_append, List.length_cons] at h1
  omega

private theorem sliceCursorAfter_split_key_sdb (L p : BitVec 64)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
        (((recFieldsQ r).drop k).flatMap GenFieldQ.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_sdb p r k) ∗
        ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64
          (((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length + 1)) ∗
        (curPtr_sdb p r k ↦₈ keyByte_sdb (recFieldsQ r)[k]) ∗
        ((curPtr_sdb p r k + 1#64) ↦ₛ
          ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) ∗
        (p ↦ₛ preBytes_sdb r k) := by
  unfold sliceCursorAfter
  have hsub : (encodeRecord r).length - (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length =
      (preBytes_sdb r k).length := by
    rw [encodeRecord_eq_preBytes_append_sdb hr k, List.length_append]; omega
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc =
      keyByte_sdb (recFieldsQ r)[k] ::
        ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
    rw [drop_flatMap_enc_sdb hk, enc_eq_keyByte_cons_sdb, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_sdb r k) ∗
        (curPtr_sdb p r k ↦₈ keyByte_sdb (recFieldsQ r)[k]) ∗
        ((curPtr_sdb p r k + 1#64) ↦ₛ
          ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_sdb hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_sdb, pointsToBytes_cons]
  rw [hsub, ← curPtr_sdb, show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega,
    hbs_split, hrem, List.length_cons]
  sep_ac_rfl

private theorem sliceCursorAfter_unsplit_key_sdb (L p : BitVec 64)
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    sliceCursorAfter (L + 0x3f8#64) (curPtr_sdb p r k + 1#64)
        ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)
        (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) ∗
      (curPtr_sdb p r k ↦₈ keyByte_sdb (recFieldsQ r)[k]) ∗
      (p ↦ₛ preBytes_sdb r k) =
    sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r)
      (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
  let fl := (recFieldsQ r)[k]
  let rest := ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_sdb fl :: (fl.payload ++ rest) := by
    rw [drop_flatMap_enc_sdb hk, enc_eq_keyByte_cons_sdb, List.cons_append]
  have hbs_eq : encodeRecord r = preBytes_sdb r k ++ (keyByte_sdb fl :: (fl.payload ++ rest)) := by
    rw [encodeRecord_eq_preBytes_append_sdb hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by
    rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length =
      (preBytes_sdb r k).length + 1 + fl.payload.length := by
    rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_sdb p r k + 1#64 + BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) =
      p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_sdb, BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) =
      (p ↦ₛ preBytes_sdb r k) ∗ (curPtr_sdb p r k ↦₈ keyByte_sdb fl) ∗
        ((curPtr_sdb p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_sdb, pointsToBytes_cons]
  unfold sliceCursorAfter
  rw [hptr, hbs_pts]
  sep_ac_rfl

private theorem deserLocalsQCap_decomp_sdb (A : RustAlloc) (L p : BitVec 64)
    (bs rest : List (BitVec 8)) (capRecv : Nat) (v : SSGQ) :
    deserLocalsQCap A L p bs rest capRecv v =
      sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
        prostSSGQAtCap A (L + 0x420#64) capRecv v ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        deserFixed_loopIter L := by
  unfold deserLocalsQCap deserFixed_loopIter
  sep_ac_rfl

private def kbNormOk_sdb (i : Fin 128) : Bool :=
  let kb : BitVec 8 := BitVec.ofNat 8 i.val
  let t : Nat := i.val / 8
  let w : Nat := i.val % 8
  !(decide (0 < t) && decide (w < 6)) ||
    (((BitVec.signExtend 64 kb).getLsbD 63 == false) &&
     ((BitVec.signExtend 64 kb) >>> 32 == 0#64) &&
     ((6#64).ule (BitVec.signExtend 64 kb &&& 7#64) == false) &&
     (BitVec.zeroExtend 64
        (BitVec.truncate 32
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 kb)) >>> 3)) ==
        BitVec.ofNat 64 t) &&
     (BitVec.zeroExtend 64 (BitVec.ofNat 32 t) == BitVec.ofNat 64 t) &&
     ((BitVec.ofNat 64 t == 0#64) == false) &&
     ((BitVec.ofNat 64 t).setWidth 32 == BitVec.ofNat 32 t) &&
     ((BitVec.signExtend 64 kb &&& 7#64).setWidth 8 == BitVec.ofNat 8 w) &&
     ((kb &&& 7#8) == BitVec.ofNat 8 w))

private theorem kbNormOk_all_sdb : (List.finRange 128).all kbNormOk_sdb = true := by decide

private theorem kb_norm_props_sdb {kb : BitVec 8}
    (hkb : kb.toNat < 128) (htag : 0 < kb.toNat / 8) (hwt : kb.toNat % 8 < 6) :
    (BitVec.signExtend 64 kb).getLsbD 63 = false ∧
    (BitVec.signExtend 64 kb) >>> 32 = 0#64 ∧
    (6#64).ule (BitVec.signExtend 64 kb &&& 7#64) = false ∧
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 kb)) >>> 3)) =
      BitVec.ofNat 64 (kb.toNat / 8) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 32 (kb.toNat / 8)) = BitVec.ofNat 64 (kb.toNat / 8) ∧
    (BitVec.ofNat 64 (kb.toNat / 8) == 0#64) = false ∧
    (BitVec.ofNat 64 (kb.toNat / 8)).setWidth 32 = BitVec.ofNat 32 (kb.toNat / 8) ∧
    (BitVec.signExtend 64 kb &&& 7#64).setWidth 8 = BitVec.ofNat 8 (kb.toNat % 8) ∧
    (kb &&& 7#8) = BitVec.ofNat 8 (kb.toNat % 8) := by
  have hi := List.all_eq_true.mp kbNormOk_all_sdb ⟨kb.toNat, hkb⟩ (List.mem_finRange _)
  have hkb_eq : BitVec.ofNat 8 kb.toNat = kb := by apply BitVec.eq_of_toNat_eq; simp
  dsimp only [kbNormOk_sdb] at hi
  rw [hkb_eq] at hi
  simp only [htag, hwt, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at hi
  rcases hi with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem keyByte_sdb_bounds (fl : GenFieldQ) :
    (keyByte_sdb fl).toNat < 128 ∧
    0 < (keyByte_sdb fl).toNat / 8 ∧
    (keyByte_sdb fl).toNat % 8 < 6 ∧
    (keyByte_sdb fl).toNat / 8 = fl.tag ∧
    (keyByte_sdb fl).toNat % 8 = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp [keyByte_sdb, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt, WireType.toNat]


open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCl_map')
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)

private theorem le_vecCap4Of_sdb (n : Nat) : n ≤ vecCap4Of n :=
  le_vecCap4Of n

private theorem recvCount_take_le_sdb {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    recvCount ((recFieldsQ r).take k) ≤ 5 := by
  have h := recvCount_recFieldsQ_le hr
  have hsplit : recFieldsQ r = (recFieldsQ r).take k ++ (recFieldsQ r).drop k :=
    (List.take_append_drop k (recFieldsQ r)).symm
  rw [hsplit, recvCount_append] at h
  omega

private theorem recvCount_take_succ_sdb {r : SessionRecord (List (BitVec 8))} {k : Nat}
    (hk : k < (recFieldsQ r).length) :
    recvCount ((recFieldsQ r).take (k + 1)) =
      match (recFieldsQ r)[k] with
      | .base (.recv _) => recvCount ((recFieldsQ r).take k) + 1
      | _ => recvCount ((recFieldsQ r).take k) := by
  rw [List.take_succ_eq_append_getElem hk, recvCount_append]
  cases (recFieldsQ r)[k] with
  | base f => cases f <;> simp [recvCount]
  | _ => simp [recvCount]

set_option maxHeartbeats 800000 in
private theorem step_iter_pre_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (L curPtr : BitVec 64) (kb : BitVec 8) (n : Nat) (s : State)
    {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 596#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64) (hx20 : s.readReg64 .x20 = 0#64)
    (hx23 : s.readReg64 .x23 = L + 0x408#64)
    (hkb : kb.toNat < 128) (htag : 0 < kb.toNat / 8) (hwt : kb.toNat % 8 < 6)
    (hn : n < 2 ^ 62)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 15 → sm.status = .Running → sm.sp = s.sp →
      (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      sm.readReg64 .lr = (blkPl_46).base + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 →
      (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 (kb.toNat / 8) →
      (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 (kb.toNat % 8) →
      sm.readReg64 .x3 = L + 0x6e8#64 →
      (sm.readReg64 .x4).setWidth 32 = 99#32 →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 →
      sm.readReg64 .x29 = L + 0x710#64 →
      post sm (stepPost_loopIter L curPtr kb n)) :
    SepWP (lsProg_46 H) (lsmpl.base 15) s (stepPre_loopIter L curPtr kb n)
      (fun sm Pm => VmPreserved s sm ∧ post sm Pm) := by
  dsimp only [lsProg_46]
  have hule := ule_zero_ofNat_succ_placed_loopIterG hn
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := kb_norm_props_sdb hkb htag hwt
  unfold stepPre_loopIter
  by_vm_steps (
    (iterate 22 wp_step)
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    refine Eq.ndrec (motive := fun P => post _ P)
      (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
    rfl)

set_option maxHeartbeats 400000 in
private theorem step_iter_post_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (s2 : State) {P : SepProp} {post : State → SepProp → Prop}
    (hpc2 : s2.pc = (blkPl_46).base + 748#64) (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_46).base + 596#64 → sf.status = .Running → sf.sp = s2.sp →
      (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) →
      sf.readReg64 .x19 = s2.readReg64 .x19 → sf.readReg64 .x20 = s2.readReg64 .x20 →
      sf.readReg64 .x23 = s2.readReg64 .x23 → sf.readReg64 .x29 = s2.readReg64 .x29 →
      post sf P) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s2 P
      (fun sf Pf => VmPreserved s2 sf ∧ post sf Pf) := by
  dsimp only [lsProg_46]
  by_vm_steps (
    wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    refine ⟨by simp_all [arm64_norm], ?_⟩
    exact hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))

set_option maxHeartbeats 1600000 in
private theorem deserLoopIterQBudget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (R : SepProp) (s0 : State) (st₀ : M.σ) {k : Nat} (hk : k < (recFieldsQ x.r).length)
    {s : State} (hs : DeserLoopStateInv M A lim x R s0 st₀ k s)
    (hL : (lsProg_46 H).CodeLoaded s.mem) :
    ∃ s', Steps (lsProg_46 H) s s' ∧
      DeserLoopStateInv M A lim x R s0 st₀ (k + 1) s' := by
  rcases hs with ⟨hpc, hrun, htr, hcrl, hsp, hal, hx29, hx19, hx20, hx23, st, ⟨hst_eq, hfit0⟩, hmem⟩
  let L := deserSpL s0.sp
  let fl := (recFieldsQ x.r)[k]
  let rest := ((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc
  let payRest := fl.payload ++ rest
  let curPtr := curPtr_sdb x.p x.r k
  let nRecv := recvCount ((recFieldsQ x.r).take k)
  let capRecv := vecCap4Of nRecv
  have hn_lt62 : payRest.length < 2 ^ 62 :=
    Nat.lt_trans (payload_rest_length_lt_sdb hr hk) (by decide)
  obtain ⟨hkb_lt, htag_pos, hwt_lt, hkb_tag, hkb_wt⟩ := keyByte_sdb_bounds fl
  set F_loop : SepProp :=
    (x.p ↦ₛ preBytes_sdb x.r k) ∗
      prostSSGQAtCap A.repAlloc (L + 0x420#64) capRecv (ssgqAfter x.r k) ∗
      ((curPtr + 1#64) ↦ₛ payRest) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX ∗
      deserSaved s0 ∗ (A.pool lim st s ∗ R)
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_sdb fl) payRest.length ∗ F_loop := by
    have hmem0 : s.mem ⊨ deserLocalsQCap A.repAlloc L x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) capRecv (ssgqAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ (A.pool lim st s ∗ R) := by
      dsimp only [L, capRecv, nRecv] at hmem ⊢
      convert hmem using 1; sep_ac_rfl
    rw [deserLocalsQCap_decomp_sdb, deserOutRegion_eq_loopIter,
      sliceCursorAfter_split_key_sdb L x.p hr hk,
      stackAt_deserCallee_split_loopIterW L, sep_perm1_loopIter] at hmem0
    exact hmem0
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hvm1, hpcm, hrunm, hspm, htrm, hlrm,
      hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom⟩⟩ :=
    (step_iter_pre_vm_sdb L curPtr (keyByte_sdb fl) payRest.length s
      (post := fun sm Pm =>
        sm.pc = lsmpl.base 15 ∧ sm.status = .Running ∧ sm.sp = s.sp ∧
        (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        sm.readReg64 .lr = (blkPl_46).base + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧
        (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 ((keyByte_sdb fl).toNat / 8) ∧
        (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 ((keyByte_sdb fl).toNat % 8) ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧ (sm.readReg64 .x4).setWidth 32 = 99#32 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x23 = L + 0x408#64 ∧ sm.readReg64 .x29 = L + 0x710#64 ∧
        Pm = stepPost_loopIter L curPtr (keyByte_sdb fl) payRest.length)
      hpc hrun hx29 hx20 hx23 hkb_lt htag_pos hwt_lt hn_lt62
      (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  subst hPm
  rw [hkb_tag] at hx1m
  rw [hkb_wt] at hx2m
  have hcrl_m : LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hLm : (lsProg_46 H).CodeLoaded sm.mem := hsteps1.codeLoaded hL
  have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by simp only [State.spAligned] at hal ⊢; rwa [hspm]
  have hcall := mergeFieldAllQ_caller_ok (callerProg := lsProg_46 H) (callerBlk := 46) hA
  let g : MergeFieldQGhost :=
    ⟨L + 0x420#64, ssgqAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp :=
    (curPtr ↦₈ keyByte_sdb fl) ∗ (x.p ↦ₛ preBytes_sdb x.r k) ∗
      deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗
      deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFieldsQ_ok x.r hr fl (List.getElem_mem hk)
  have hfresh : fl.Fresh (ssgqAfter x.r k) := recFieldsQ_fresh x.r hr k hk
  have hfreshB : GenFieldQ.FreshBytes (ssgqAfter x.r k) fl := freshBytes_ssgqAfter x.r hk
  have hrecv_len : (ssgqAfter x.r k).base.recv.length = nRecv := ssgqAfter_recv_length x.r k
  have hpow : IsPow2Cap4 capRecv := isPow2Cap4_vecCap4Of nRecv
  have hle_cap : (ssgqAfter x.r k).base.recv.length ≤ capRecv := by
    rw [hrecv_len]; exact le_vecCap4Of_sdb nRecv
  have hcap62 : capRecv < 2 ^ 62 := by
    dsimp only [capRecv, nRecv]
    have h1 := vecCap4Of_le_mono (recvCount_take_le_sdb hr k)
    have h2 : vecCap4Of 5 = 8 := by decide
    omega
  have hfit_ev : FitsEvents M lim st (mergeFieldQEvents capRecv nRecv fl) := by
    have hsplit := sessDeserEvents_eq_prefix_append_suffix x.r k
    dsimp only at hsplit
    have hf0 := hfit0
    rw [hsplit, fitsEvents_append] at hf0
    have hf_suf := hf0.2
    rw [← hst_eq, List.drop_eq_getElem_cons hk] at hf_suf
    dsimp only [fieldsEventsAux] at hf_suf
    rw [fitsEvents_append] at hf_suf
    exact hf_suf.1
  have hfit_mf : FitsEvents M lim st
      (mergeFieldQFitsEvents capRecv (ssgqAfter x.r k).base.recv.length fl) := by
    rw [hrecv_len]; exact fitsEvents_mergeFieldQFits_of_events hfit_ev
  have hpre_mf : sm.mem ⊨
      (mergeFieldQBudgetSpecW M A lim (fun _ => True)).pre (g, capRecv, st) sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldQBudgetSpecW, withLsCodeRoLoaded, mergeFieldQBudgetRawSpecW, g]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl_m, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hfreshB,
      hn_lt62, hpow, hle_cap, hcap62, hfit_mf⟩, ?_⟩
    dsimp only [stepPost_loopIter, F_loop] at hmm
    rw [← A.pool_transport lim st s sm hvm1] at hmm
    rw [hspm_L]
    unfold sliceCursorAt
    rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega]
    dsimp only [F_mf, payRest] at hmm ⊢
    convert hmm using 1; sep_ac_rfl
  obtain ⟨s2, hsteps2, hout, -⟩ :=
    hcall.no_fault_before_outcome (g, capRecv, st) (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨_, hpan2⟩ | ⟨_, _, hex2⟩ | ⟨_, hoom2⟩
  · rw [hlrm] at hpc2
    dsimp only [mergeFieldQBudgetSpecW, withLsCodeRoLoaded, mergeFieldQBudgetRawSpecW, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    let st' := M.stepEvents (mergeFieldQEvents capRecv (ssgqAfter x.r k).base.recv.length fl) st
    let capRecv' := nextCapRecv capRecv (ssgqAfter x.r k).base.recv.length fl
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hvm3, hpcf, hrunf, hspf, htrf,
        hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom⟩⟩ :=
      (step_iter_post_vm_sdb s2
        (P := prostSSGQAtCap A.repAlloc (L + 0x420#64) capRecv' ((ssgqAfter x.r k).apply fl) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
          A.pool lim st' s2 ∗ stackAt sm.sp mergeFieldStackX)
        (post := fun sf P_f =>
          sf.pc = (blkPl_46).base + 596#64 ∧ sf.status = .Running ∧ sf.sp = s2.sp ∧
          (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧ sf.readReg64 .x20 = s2.readReg64 .x20 ∧
          sf.readReg64 .x23 = s2.readReg64 .x23 ∧ sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGQAtCap A.repAlloc (L + 0x420#64) capRecv' ((ssgqAfter x.r k).apply fl) ∗
            ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
            sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗
            A.pool lim st' s2 ∗ stackAt sm.sp mergeFieldStackX))
        hpc2 hrun2 hx0_2
        (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim
        hmem2 (hsteps2.codeLoaded hLm)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    subst hPf
    have hsteps_all : Steps (lsProg_46 H) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L)
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned] at hal ⊢
      rwa [hsp_sf.trans hsp.symm]
    have hst'_eq : st' = M.stepEvents (sessDeserEventsPrefix x.r (k + 1)) st₀ := by
      dsimp only [st']
      rw [hrecv_len, hst_eq, ← AllocCostModel.stepEvents_append, ← sessDeserEventsPrefix_succ x.r hk]
    have hcap'_eq : capRecv' = vecCap4Of (recvCount ((recFieldsQ x.r).take (k + 1))) := by
      dsimp only [capRecv', capRecv, fl, nRecv]
      rw [hrecv_len, nextCapRecv_eq_vecCap4Of (recvCount ((recFieldsQ x.r).take k)) (recFieldsQ x.r)[k],
        recvCount_take_succ_sdb hk]
      rfl
    refine ⟨sf, hsteps_all, hpcf, hrunf,
      ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)),
       htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩,
      hcrl.of_keepsFrozen hsteps_all.keepsFrozen,
      hsp_sf, hal_sf,
      hx29f.trans (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29m),
      hx19f.trans (hcs2.1.trans (hx19m.trans hx19)),
      hx20f.trans (hcs2.2.1.trans hx20m),
      hx23f.trans (hcs2.2.2.2.2.1.trans hx23m),
      st', ⟨hst'_eq, hfit0⟩, ?_⟩
    rw [← A.pool_transport lim st' s2 sf hvm3, hspm_L] at hmf
    change sf.mem ⊨ deserLocalsQCap A.repAlloc L x.p (encodeRecord x.r)
        (((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc)
        (vecCap4Of (recvCount ((recFieldsQ x.r).take (k + 1))))
        (ssgqAfter x.r (k + 1)) ∗
      memRegion x.out 368 ∗ A.pool lim st' sf ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [← hcap'_eq, ssgqAfter_succ_sdb hk, deserLocalsQCap_decomp_sdb, deserOutRegion_eq_loopIter,
      ← sliceCursorAfter_unsplit_key_sdb L x.p hr hk, stackAt_deserCallee_split_loopIterW L]
    dsimp only [F_mf] at hmf
    convert hmf using 1; sep_ac_rfl
  · exact (not_satisfies_false_sepConj hpan2).elim
  · exact (not_satisfies_false_sepConj hex2).elim
  · exact (not_satisfies_false_sepConj hoom2).elim

private def memcpyVmDeserSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp deserCalleeStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp deserCalleeStack

private theorem stackAt_deserCallee_split_extHook_sdb (sp : BitVec 64) :
    stackAt sp deserCalleeStack =
      memRegion (sp - 63632#64) 47248 ∗ stackAt sp extHookStack := by
  have h0 := ProofLib.stackAt_split_bottom sp extHookStack 47248 (by decide)
  rwa [show extHookStack + 47248 = deserCalleeStack by decide,
    show BitVec.ofNat 64 deserCalleeStack = 63632#64 by rfl] at h0

private theorem memcpy_deser_of_budgetPlaced_sdb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_46 H) (lsρ "memcpy") (withLsCl lsmpl memcpyVmDeserSpec) := by
  refine subroutine_ok_withLsCl_map'
    (LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget.memcpy_extern_of_budgetPlaced
      hA (callerProg := lsProg_46 H))
    fun ⟨dst, src, bs⟩ R s0 hpre =>
      ⟨(dst, src, bs), memRegion (s0.sp - 63632#64) 47248 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcpyVmDeserSpec,
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget.memcpyVmExternSpecX] at hpre ⊢
    rw [stackAt_deserCallee_split_extHook_sdb s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [memcpyVmDeserSpec,
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget.memcpyVmExternSpecX] at hpost ⊢
    rw [stackAt_deserCallee_split_extHook_sdb s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

private theorem w0_add_one_ne_zero_sdb {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    w0 + 1#64 ≠ 0#64 := by unfold noneCap at h; bv_omega
private theorem w0_add_one_beq_zero_sdb {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    (w0 + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; exact w0_add_one_ne_zero_sdb h

private def deserSavedAtL_sdb (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSaved_eq_atL_sdb (s0 : State) :
    deserSaved s0 = deserSavedAtL_sdb (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_sdb deserSpL
  rw [show s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 by bv_omega]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem sliceCursorAfter_nil_sdb (L p : BitVec 64) (bs : List (BitVec 8)) :
    sliceCursorAfter (L + 0x3f8#64) p bs [] =
      ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold sliceCursorAfter
  rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, List.length_nil, Nat.sub_zero]

private theorem memRegion_3f8_split_sdb (L : BitVec 64) :
    memRegion L 0x3f8 =
      memRegion L 8 ∗ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 3 * 336) (by decide) rfl (by decide),
    memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 3 * 336) (n := 336) (k := 2 * 336) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 2 * 336) (n := 336) (k := 336) (by decide) (by bv_omega) (by decide)]

private theorem satisfies_memRegion_out_split_sdb {m : Memory} {out : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64,
      m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗
        ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360) (by decide) rfl (by decide),
    memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336) (by decide) (by bv_omega) (by decide),
    ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩
  exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem deserSavedAtL_entails_memRegion_sdb (L : BitVec 64) (s0 : State) :
    deserSavedAtL_sdb L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_sdb
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) :
      memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 =
        memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n)) (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide), join 32 (by decide), join 40 (by decide),
    join 48 (by decide), join 56 (by decide), join 64 (by decide), join 72 (by decide), join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_sdb (s0 : State) (c0 w0 : BitVec 64)
    (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗ (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_sdb L s0) ⊢ stackAt s0.sp recDeserializeStack := by
  intro L
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by
    rw [← hrest]; exact ProofLib.pointsToBytes_entails_memRegion a rest
  have hloc : memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_sdb L s0 ⊢ memRegion L 0x770 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono (hb (L + 8#64)) (sepConj_mono (hb (L + 0x158#64)) (sepConj_mono (hb (L + 0x2a8#64))
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (hb (L + 0x428#64)) (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_right (deserSavedAtL_entails_memRegion_sdb L s0))))))))))))))) ?_
    have join (n k : Nat) (h : n + k ≤ 2 ^ 64) :
        memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
      (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
    simp only [← sepConj_assoc]
    rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide), join 1016 8 (by decide), join 1024 8 (by decide),
      join 1032 8 (by decide), join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide), join 1064 336 (by decide),
      join 1400 0x170 (by decide), join 1768 8 (by decide), join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
    exact Entails.refl _
  refine Entails.trans (sepConj_mono_right hloc) ?_
  unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by
    dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]; bv_omega
  rw [h1, memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L)
    (N := recDeserializeStack) (n := deserCalleeStack) (k := recDeserializeStack - deserCalleeStack) (by decide)
    (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega) (by decide)]
  exact Entails.refl _

set_option maxHeartbeats 1200000 in
private theorem dexit_sepWP_vm_sdb [LibsignalPlacement] {H : LibsignalHooks}
    (hmc_vm : subroutine_ok (lsProg_46 H) (lsρ "memcpy") (withLsCl lsmpl memcpyVmDeserSpec))
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = (blkPl_46).base + 596#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = 0#64) (hw0 : w0 ≠ noneCap) (hrest : rest.length = 336)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_46 H) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗
        ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗
        memRegion (out + 0x20#64) 336 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_sdb L s0)
      (fun sf P_f =>
        VmPreserved s sf ∧ sf.sp = L + 0x770#64 ∧ sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x400#64) ↦₆₄ 0#64) ∗
          ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
          ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
          (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗
          ((out + 0x20#64) ↦ₛ rest) ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_sdb L s0)) := by
  subst hsp
  dsimp only [lsProg_46] at hmc_vm ⊢
  have hw0_ne := w0_add_one_ne_zero_sdb hw0
  have hw0_beq := w0_add_one_beq_zero_sdb hw0
  unfold deserSavedAtL_sdb
  wp_steps_lscl_vm_s (lsρ "memcpy") as hvm1 hcl1
  wp_call hmc_vm (s.sp + 8#64, s.sp + 0x428#64, rest)
  have hvm_acc1 := hvm1.trans ‹_›
  wp_steps_lscl_vm_s (lsρ "memcpy") as hvm2 hcl2
  wp_call hmc_vm (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  have hvm_acc2 := (hvm_acc1.trans hvm2).trans ‹_›
  wp_steps_lscl_vm_s (lsρ "memcpy") as hvm3 hcl3
  wp_call hmc_vm (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  have hvm_acc3 := (hvm_acc2.trans hvm3).trans ‹_›
  wp_steps_lscl_vm_s (lsρ "memcpy") as hvm4 hcl4
  wp_call hmc_vm (out + 0x20#64, s.sp + 0x158#64, rest)
  have hvm_acc4 := (hvm_acc3.trans hvm4).trans ‹_›
  wp_steps_to_tgt_vm_s as hvm5
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨hvm_acc4.trans hvm5,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

end LoopBody

/-- Image-free base contract of budget-threaded `SessionRecord::deserialize` (Block `46`,
`recDeserializeStack`), refining `sessDeserializeExtSpec Scope A.repAlloc` with `A.pool lim st s`,
`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`, **zero changes to `sessionRecordAt`**, and explicit output
ghost bounds `ssStateLargeLive M G s_sess.state = ssLargeLive M G` and
`33 ≤ smallMaxReq M → ssLargeLive M G = sessDeserLargeLive M x.r`. -/
def sessDeserializeBudgetRawSpec (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DeserializeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ Scope x.r ∧
      FitsEvents M lim st (sessDeserEvents x.r)⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗
      A.pool lim st s ∗ stackAt s.sp recDeserializeStack
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents (sessDeserEvents x.r) st
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗
      (∃∗ g : RecordGhost,
        ⌜CanonRecord g x.r ∧
          (∀ G, g.cur = some G →
            (∀ s_sess, x.r.currentSession = some s_sess →
              ssStateLargeLive M G s_sess.state = ssLargeLive M G) ∧
            (33 ≤ HasFineReallocCredit.smallMaxReq M →
              ssLargeLive M G = sessDeserLargeLive M x.r))⌝ ∗
          sessionRecordAt A.repAlloc x.out g x.r) ∗
      A.pool lim st' sf ∗ stackAt s0.sp recDeserializeStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded spec for `SessionRecord::deserialize`
(Block `46`, `lsProg_46 H`, `recDeserializeStack`), refining `sessDeserializeExtSpec Scope A.repAlloc`
with `A.pool lim st s`, `onOom := ⌜False⌝`, `onPanic := ⌜False⌝`, **zero changes to `sessionRecordAt`**,
and explicit output ghost bound `ssLargeLive M G = sessDeserLargeLive M x.r`. -/
def sessDeserializeBudgetPlacedSpec [LibsignalPlacement]
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DeserializeGenGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (sessDeserializeBudgetRawSpec Scope M A lim)

set_option maxHeartbeats 1600000 in
private theorem deserLoopExitQBudget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (R : SepProp) (s0 : State) (st₀ : M.σ)
    {s : State} (hs : DeserLoopStateInv M A lim x R s0 st₀ (recFieldsQ x.r).length s)
    (hL : (lsProg_46 H).CodeLoaded s.mem) :
    reaches_outcome (lsProg_46 H)
      (sessDeserializeBudgetPlacedSpec (DeserializeScopeP_Q NonEmptyV1Q) M A lim)
      (x, st₀) R s0 s := by
  rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hcrl, hsp, hal, hx29, hx19, hx20, _hx23,
    st, ⟨hst_eq, _hfit0⟩, hmem⟩
  let L := deserSpL s0.sp
  let v := ssgqAfter x.r (recFieldsQ x.r).length
  let bs := encodeRecord x.r
  have hcap_end : vecCap4Of (recvCount ((recFieldsQ x.r).take (recFieldsQ x.r).length)) =
      sessDeserRecvCap x.r := by
    rw [List.take_length]; rfl
  have hst_end : st = M.stepEvents (sessDeserEvents x.r) st₀ := by
    rw [hst_eq]; unfold sessDeserEventsPrefix sessDeserEvents; rw [List.take_length]
  change s.mem ⊨ deserLocalsQCap A.repAlloc L x.p bs
      (((recFieldsQ x.r).drop (recFieldsQ x.r).length).flatMap GenFieldQ.enc)
      (vecCap4Of (recvCount ((recFieldsQ x.r).take (recFieldsQ x.r).length))) v ∗
    memRegion x.out 368 ∗ A.pool lim st s ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R at hmem
  rw [List.drop_length, List.flatMap_nil, hcap_end] at hmem
  unfold deserLocalsQCap at hmem
  rw [sliceCursorAfter_nil_sdb L x.p bs, memRegion_3f8_split_sdb L, deserSaved_eq_atL_sdb s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨
      prostSSGQAtCap A.repAlloc (L + 0x420#64) (sessDeserRecvCap x.r) v ∗
      (memRegion x.out 368 ∗ memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
       memRegion (L + 0x6f0#64) 0x20 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_sdb L s0 ∗
       (A.pool lim st s ∗ R)) := by
    dsimp only [c0]; convert hmem using 1; sep_ac_rfl
  obtain ⟨w0, rest, Hframe, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGQAtCap_move hmem1
  have hmem3 : s.mem ⊨
      memRegion x.out 368 ∗
      (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ Hframe ∗
       memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗
       ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
       memRegion (L + 0x6f0#64) 0x20 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_sdb L s0 ∗
       (A.pool lim st s ∗ R)) := by
    convert hmem2 using 1; sep_ac_rfl
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_sdb hmem3
  let F := (x.p ↦ₛ bs) ∗ Hframe ∗ memRegion L 8 ∗
    ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗
    memRegion (L + 0x6f0#64) 0x20 ∗ A.pool lim st s ∗ R
  have hmem4 : s.mem ⊨
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
        ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
        ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
        ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗
        ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗ memRegion (x.out + 0x20#64) 336 ∗
        stackAt L deserCalleeStack ∗ deserSavedAtL_sdb L s0) ∗ F := by
    dsimp only [F]; convert hmem3' using 1; sep_ac_rfl
  have hwp := dexit_sepWP_vm_sdb (memcpy_deser_of_budgetPlaced_sdb hA)
    (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
    hpc hrun hsp hal hx29 hx19 hx20 hw0 hrest hcrl.1 hvregs
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hvm_exit, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by rw [hspf]; dsimp [L, deserSpL]; bv_omega
  refine reaches_outcome_steps hsteps
    (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩))
  dsimp only [F] at hmf
  rw [← A.pool_transport lim st s sf hvm_exit, hst_end] at hmf
  have hmf1 : sf.mem ⊨
      ((x.p ↦ₛ bs) ∗
       ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
         (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe)) ∗
       (stackAt L deserCalleeStack ∗
        (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
          ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗
          ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗
          ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗
          ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
          deserSavedAtL_sdb L s0))) ∗
      (A.pool lim (M.stepEvents (sessDeserEvents x.r) st₀) sf ∗ R) := by
    dsimp only [L] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hss_out : ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ Hframe ⊢
      prostSSGQAtCap A.repAlloc (x.out + 0x18#64) (sessDeserRecvCap x.r) v := by
    have hr' := hrebuild (x.out + 0x18#64)
    rwa [show x.out + 0x18#64 + 8#64 = x.out + 0x20#64 by bv_omega] at hr'
  have hstk := dexit_frame_entails_stackAt_sdb s0 c0 w0 rest hrest
  dsimp only at hstk
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  have hmf3 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (deserReprCapQA_ok M A.repAlloc x.r hr x.out)))) hmf2
  dsimp only [sessDeserializeBudgetPlacedSpec, withLsCodeRoLoaded, sessDeserializeBudgetRawSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩
  dsimp only [bs] at hmf3
  convert hmf3 using 1; sep_ac_rfl

private theorem deserLoopQBudget_run [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : DeserializeGenGhost} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    {R : SepProp} {s0 : State} {st₀ : M.σ} :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length →
      DeserLoopStateInv M A lim x R s0 st₀ k s →
      (lsProg_46 H).CodeLoaded s.mem →
      reaches_outcome (lsProg_46 H)
        (sessDeserializeBudgetPlacedSpec (DeserializeScopeP_Q NonEmptyV1Q) M A lim)
        (x, st₀) R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs hL
    simp only [Nat.add_zero] at hk; subst hk
    exact deserLoopExitQBudget_placed_ok hA x hr R s0 st₀ hs hL
  | succ m ih =>
    intro k s hk hs hL
    have hlt : k < (recFieldsQ x.r).length := by omega
    obtain ⟨s', hst, hs'⟩ := deserLoopIterQBudget_placed_ok hA x hr R s0 st₀ hlt hs hL
    exact reaches_outcome_steps hst (ih (k + 1) s' (by omega) hs' (hst.codeLoaded hL))

/-- Main relocatable `[LibsignalPlacement]` theorem for `SessionRecord::deserialize` (Block `46`,
`lsProg_46 H`) on `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem sessDeserialize_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeBudgetPlacedSpec (DeserializeScopeP_Q NonEmptyV1Q) M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st₀⟩ R s0 hpc hrun hpre hal hL0
  dsimp only [sessDeserializeBudgetPlacedSpec, withLsCodeRoLoaded, sessDeserializeBudgetRawSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcrl0, hpre_raw⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx8, hr, hfit0⟩, hm0⟩
  have hm0' : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗
      A.pool lim st₀ s0 ∗ stackAt s0.sp recDeserializeStack ∗ R := by
    convert hm0 using 1; sep_ac_rfl
  obtain ⟨s1, hst1, hs1⟩ := deserLoopEntryQBudget_placed_ok x hr st₀ hfit0 R s0
    hpc hrun hx0 hx1 hx8 hal hcrl0 hm0' hL0
  exact reaches_outcome_steps hst1
    (deserLoopQBudget_run hA hr (recFieldsQ x.r).length 0 s1 (Nat.zero_add _) hs1 (hst1.codeLoaded hL0))

/-- Contravariant `Scope ⊆ DeserializeScopeP_Q NonEmptyV1Q` specialization (for `StoreSpecs.Session` /
`scopeKit` callers). -/
theorem sessDeserialize_budget_placed_ok_of_sub [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeBudgetPlacedSpec Scope M A lim) := by
  refine subroutine_ok_map (sessDeserialize_budget_placed_ok hA)
    fun ⟨x, st₀⟩ R s0 hpre => ⟨(x, st₀), R, ?_, fun sf hpost => hpost⟩
  dsimp only [sessDeserializeBudgetPlacedSpec, withLsCodeRoLoaded, sessDeserializeBudgetRawSpec] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hp := hpre.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hsub x.r hp.1.2.2.2.1, hp.1.2.2.2.2⟩, hp.2⟩

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
