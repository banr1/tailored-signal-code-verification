/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

/-!
# Budget-Threaded Relocatable Seam Specifications for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Defines `RustCliAllocBudget`-threaded top-level specifications for Block `427` and
budget-threaded peer `blockProgram` callee contracts consumed by `spqr::send`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto ShaCompress)
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall SpqrModel spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (States V1State spqrAuthApi spqrDecodeState spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1ReceivedAt chunkedCt1SampledAt chunkedCt2SampledAt
   chunkedEkReceivedCt1SampledAt chunkedHeaderSentAt chunkedStatesSize
   optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkSize polyNextChunkStack)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost resultChunkedStatesAt statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap decodeStateResultAt
   decodeStateStackX)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendCalleeStack)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrCoinsAfterPlaced spqrCoinsAtPlaced statesFromPbJumpTablePlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs statesIntoPbPlacedSpecX)

/-! ## 1. `VmPreserved`-Strengthened `signal_session_coins_fill` (`Block 618`) Specifications -/

/-- Relocatable `VmPreserved`-strengthened specification of `signal_session_coins_fill` (`Block 618`),
    so `A.pool lim st` frames across `signal_session_coins_fill` calls with zero allocator events. -/
def spqrCoinsFillSpecPlaced [LibsignalPlacement] (stk : Nat) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved (CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillSpecPlaced stk)

/-- `spqrCoinsFillSpecPlaced` with fixed tape ghost `(cur, rest)`. -/
def spqrCoinsFillAtSpecPlaced [LibsignalPlacement] (stk : Nat) (cur : BitVec 64)
    (rest : List (BitVec 8)) : Spec (BitVec 64 × Nat) :=
  withVmPreserved (CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced stk cur rest)

theorem spqrCoinsFillAtPlaced_of_after0 [LibsignalPlacement] {P : Program} {addr cur : BitVec 64}
    {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (spqrCoinsFillSpecPlaced stk)) :
    subroutine_ok P addr (spqrCoinsFillAtSpecPlaced stk cur rest) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, len⟩ R s0 hpc hrun hpre hsp => ?_
  exact h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem spqrCoinsFillAtPlaced_of_after0_cl [LibsignalPlacement] {P : Program} {addr cur : BitVec 64}
    {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (spqrCoinsFillSpecPlaced stk))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (spqrCoinsFillAtSpecPlaced stk cur rest)) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, len⟩ R s0 hpc hrun hpre hsp => ?_
  exact h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem spqrCoinsFillAtPlaced_of_after0_cro [LibsignalPlacement] {P : Program} {addr cur : BitVec 64}
    {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (withLsCodeRoLoaded lsmpl (spqrCoinsFillSpecPlaced stk))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (spqrCoinsFillAtSpecPlaced stk cur rest)) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, len⟩ R s0 hpc hrun hpre hsp => ?_
  exact h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

/-! ## 2. Public `Block 427` Top-Level Budget Specifications (`spqr::send::<Coins>`) -/

/-- Default bounded allocation-event envelope of `spqr::send::<signal_session_ratchet::Coins>`
    (`Block 427`), linear in the serialized state length (`4 * x.st.bytes.length + 16384`). -/
def SpqrSendCoinsEnv (x : SendCall) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * x.st.bytes.length + 16384) evs

theorem spqrSendCoinsEnv_nonempty (x : SendCall) :
    ∃ evs, SpqrSendCoinsEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 512 (4 * x.st.bytes.length + 16384)⟩

/-- Envelope-parametric relocatable `[LibsignalPlacement]` budget contract for
    `spqr::send::<signal_session_ratchet::Coins>` (`Block 427`).
    Retains the genuine protocol panic `S.sendPanics x.st.bytes x.rest` while dropping
    `allocFailedIn s0 sf` (`onOom = ⌜False⌝` under `FitsEnv`). -/
def spqrSendCoinsPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel)
    (Env : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v ∧
      FitsEnv M lim st (Env x)⌝ ∗
      x.st.at A.repAlloc ∗ memRegion x.ret 72 ∗
      spqrCoinsAtPlaced ctl x.cur x.rest ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st s ∗ stackAt s.sp spqrSendStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ S.sendPanics x.st.bytes x.rest ∧ Env x evs⌝ ∗
      x.st.at A.repAlloc ∗
      spqrSendResultAt A.repAlloc x.ret (S.send x.st.bytes x.rest) ∗
      spqrCoinsAfterPlaced ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp spqrSendStack
  onPanic := fun (x, _) s0 sf =>
    ⌜S.sendPanics x.st.bytes x.rest ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Default relocatable `[LibsignalPlacement]` budget contract for
    `spqr::send::<signal_session_ratchet::Coins>` (`Block 427`). -/
abbrev spqrSendCoinsPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecOfEnv M A lim ctl S SpqrSendCoinsEnv

/-- Envelope-parametric `[LibsignalPlacement]` inner `Spec` of `spqrSendSpecT` for `<Coins>` (`Block 427`)
    with `tokenInitPlacedAt` framed and `st.bytes.length < 2 ^ 32`, `64 ≤ rest.length`. -/
def spqrSendCoinsPlacedSpecTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel)
    (Env : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) :=
  { spqrSendCoinsPlacedSpecOfEnv M A lim ctl S Env with
    pre := fun (x, st) s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpecOfEnv M A lim ctl S Env).pre (x, st) s
    post := fun (x, st) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpecOfEnv M A lim ctl S Env).post (x, st) s0 sf }

/-- Default `[LibsignalPlacement]` budget `spqrSendCoinsPlacedSpecT` (`Block 427`). -/
abbrev spqrSendCoinsPlacedSpecT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecTOfEnv M A lim ctl S SpqrSendCoinsEnv

/-! ## 3. Peer Callee Envelopes, Specifications & `CliSpqrSendPeerSeams` -/

/-- Bounded allocation envelope of `spqr::decode_state` (`Block 325`). -/
def DecodeStatePlacedEnv (x : DecodeStateGhost) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 96 (4 * x.st.bytes.length + 4096) evs

theorem decodeStatePlacedEnv_nonempty (x : DecodeStateGhost) :
    ∃ evs, DecodeStatePlacedEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 96 (4 * x.st.bytes.length + 4096)⟩

/-- Envelope-parametric relocatable specification for `spqr::decode_state` (`Block 325`). -/
def decodeStatePlacedSpecXOfEnv [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : DecodeStateGhost → List AllocEvent → Prop) :
    Spec (DecodeStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗ stackAt s.sp decodeStateStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodeStateStackX

/-- Default relocatable budget specification for `spqr::decode_state` (`Block 325`). -/
abbrev decodeStatePlacedSpecX [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeStateGhost × M.σ) :=
  decodeStatePlacedSpecXOfEnv H_inner M A lim DecodeStatePlacedEnv

/-- Bounded allocation envelope of `<States>::from_pb` (`Block 333`). -/
def StatesFromPbEnv (x : StatesFromPbGhost) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 96 (4 * (V1State.encodeRaw x.pb).length + 4096) evs

theorem statesFromPbEnv_nonempty (x : StatesFromPbGhost) :
    ∃ evs, StatesFromPbEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 96 (4 * (V1State.encodeRaw x.pb).length + 4096)⟩

/-- Envelope-parametric relocatable specification for `<States>::from_pb` (`Block 333`). -/
def statesFromPbPlacedSpecXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesFromPbGhost → List AllocEvent → Prop) :
    Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧ v1StatePtsBound x.pb ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStackX

/-- Default relocatable budget specification for `<States>::from_pb` (`Block 333`). -/
abbrev statesFromPbPlacedSpecX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbPlacedSpecXOfEnv M A lim F StatesFromPbEnv

/-- Bounded allocation envelope of `<Message>::serialize` (`Block 352`: serialized SPQR message
    is at most `≤ 64` bytes). -/
def MessageSerializeEnv {P : CryptoVerification.LibsignalSpqrV1.PolyApi}
    (_x : MessageSerializeGhost P) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 8 256 evs

theorem messageSerializeEnv_nonempty {P : CryptoVerification.LibsignalSpqrV1.PolyApi}
    (x : MessageSerializeGhost P) :
    ∃ evs, MessageSerializeEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 8 256⟩

/-- Envelope-parametric budget specification of `<Message>::serialize` (`Block 352`). -/
def messageSerializeSpecXOfEnv (P : CryptoVerification.LibsignalSpqrV1.PolyApi)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : MessageSerializeGhost P → List AllocEvent → Prop) :
    Spec (MessageSerializeGhost P × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (Env x)⌝ ∗
      messageAt P x.msgA x.msg ∗ memRegion x.ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp messageSerializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      messageAt P x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp messageSerializeStackX

/-- Default budget specification of `<Message>::serialize` (`Block 352`). -/
abbrev messageSerializeSpecX (P : CryptoVerification.LibsignalSpqrV1.PolyApi)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (MessageSerializeGhost P × M.σ) :=
  messageSerializeSpecXOfEnv P M A lim MessageSerializeEnv

/-- Bounded allocation envelope shared by the five `States/Leaves` `send_*_chunk` transitions
    (`Blocks 335, 336, 344, 345, 354`), each delegating to `PolyEncoder::next_chunk` (`Block 416`). -/
def SpqrSendChunkEnv (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 64 16384 evs

theorem spqrSendChunkEnv_nonempty : ∃ evs, SpqrSendChunkEnv evs :=
  ⟨[], SpqrBoundedEvs.nil 64 16384⟩

/-- Envelope-parametric relocatable specification of `<EkReceivedCt1Sampled>::send_ct1_chunk` (`Block 344`). -/
def ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 960)

abbrev ekReceivedCt1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F × M.σ) :=
  ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F (fun _ => SpqrSendChunkEnv)

/-- Envelope-parametric relocatable specification of `<Ct2Sampled>::send_ct2_chunk` (`Block 354`). -/
def ct2SampledSendCt2ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt2SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 896)

abbrev ct2SampledSendCt2ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct2SampledSendCt2ChunkGhost F × M.σ) :=
  ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F (fun _ => SpqrSendChunkEnv)

/-- Envelope-parametric relocatable specification of `<HeaderSent>::send_ek_chunk` (`Block 336`). -/
def headerSentSendEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1328)

abbrev headerSentSendEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (HeaderSentSendEkChunkGhost F × M.σ) :=
  headerSentSendEkChunkPlacedSpecOfEnv M A lim F (fun _ => SpqrSendChunkEnv)

/-- Envelope-parametric relocatable specification of `<Ct1Received>::send_ek_chunk` (`Block 345`). -/
def ct1ReceivedSendEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1ReceivedAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 944)

abbrev ct1ReceivedSendEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1ReceivedSendEkChunkGhost F × M.σ) :=
  ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F (fun _ => SpqrSendChunkEnv)

/-- Envelope-parametric relocatable specification of `<Ct1Sampled>::send_ct1_chunk` (`Block 335`). -/
def ct1SampledSendCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A.repAlloc x.stA x.st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt1SampledAt A.repAlloc x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (polyNextChunkStack + 1376)

abbrev ct1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1SampledSendCt1ChunkGhost F × M.σ) :=
  ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F (fun _ => SpqrSendChunkEnv)

/-- Budget-threaded seam bundle of the peer `blockProgram` callee contracts consumed by `Block 427`. -/
structure CliSpqrSendPeerSeams [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (C : Crypto)
    (ext : String → Option (State → State)) : Prop where
  /-- Block `325`: `spqr::decode_state`. -/
  decodeState_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap M A lim))
  /-- Block `326`: `spqr::encode_varint`. -/
  encodeVarint_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim))
  /-- Block `328`: `spqr::chain_from_version_negotiation`. -/
  chainFromVn_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 328 (Rust.withPanics ext))
      (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith C.F) M A lim))
  /-- Block `333`: `<States>::from_pb`. -/
  statesFromPb_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim C.F))
  /-- Block `334`: `<States>::into_pb`. -/
  statesIntoPb_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim C.F))
  /-- Block `352`: `<Message>::serialize`. -/
  messageSerialize_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim))
  /-- Block `336`: `<HeaderSent>::send_ek_chunk`. -/
  headerSentSendEkChunk_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext))
      (lsmpl.base 336)
      (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec M A lim C.F))
  /-- Block `345`: `<Ct1Received>::send_ek_chunk`. -/
  ct1ReceivedSendEkChunk_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext))
      (lsmpl.base 345)
      (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec M A lim C.F))
  /-- Block `335`: `<Ct1Sampled>::send_ct1_chunk`. -/
  ct1SampledSendCt1Chunk_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext))
      (lsmpl.base 335)
      (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec M A lim C.F))
  /-- Block `344`: `<EkReceivedCt1Sampled>::send_ct1_chunk`. -/
  ekReceivedCt1SampledSendCt1Chunk_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext))
      (lsmpl.base 344)
      (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec M A lim C.F))
  /-- Block `354`: `<Ct2Sampled>::send_ct2_chunk`. -/
  ct2SampledSendCt2Chunk_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext))
      (lsmpl.base 354)
      (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec M A lim C.F))
  /-- Block `618`: `signal_session_coins_fill`. -/
  coinsFill_ok :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 618 (Rust.withPanics ext))
      (lsmpl.base 618) (spqrCoinsFillSpecPlaced spqrSendCalleeStack)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
