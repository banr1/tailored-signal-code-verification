/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 10 Aux (Budget-Threaded)

Allocator-event envelopes (`Ct1SampledRecvPreEnv` / `Ct1SampledRecvPostEnv`), `FitsEnv`
decomposition lemmas, sequencing adapters, and the budget-threaded Path 5c (`ack = true`) theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 lsProg_332 lsmpl
  sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded sepWP_seq_lscro sessionMemcpySpec
)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chunk Error Mac Message MlKem PolyDecoder PolyEncoder States
  StatesResult spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled send_ct2_encoder)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1SentEkReceived Ct2Sent)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.Drop (
  chunkedStatesSize unchunkedCt1SentAt unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt
  vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves (
  AuthWords ct2SentWordsList optVecU8At relocatedHeap
  unchunkedCt1SentRecvEkResAt wordsAt wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  CopyScratchStack EpilogueStoreStack StatesRecvGhost TraceCalleeSaved Words16
  copyScratchStackAt epilogueStoreStackPart1At polyEncoderTagVal resultV1RecvAt
  sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_4240_add_4144
  sp_sub_4240_add_48 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
  sp_sub_96_add_80 sp_sub_96_sub_4096 statesRecvCalleeStackX
  statesRecvJumpTablePlacedAt statesRecvRoPlacedAt statesRecvSavedCells statesRecvStackX
  states_recv_ct1Sampled_eq_some_ok_ack unchunkedCt1SentEkReceivedAt_extract_words16 v1RecvSize
  words16_entails_memRegion_128
)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open LibsignalBinary.Proofs.SpqrV1.States.Recv (spqrDeallocSym)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkEnv AddChunkSlotsEnv addChunkSlotsEnv_nil
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageEnv decodedMessageEnv_nonempty
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  Ct1AckRecvEkTailPreEnv PolyDecoderDecodedMessagePostEnv PolyDecoderDecodedMessagePreEnv
  SendCt2EncoderBytesPreEnv SendCt2EncoderPostEnv ct1AckRecvEkTailPreEnv_nonempty
  sendCt2EncoderSpec unchunkedCt1SentRecvEkSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9PlacedBudget (
  statesRecvRoPlacedAt_eq_unchunkedSendCt2
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv statesRecvVariantPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget (
  UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
)

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] addChunkTotal decodedMessageTotal DecodedMessageEnv

/-! ## 1. Allocation-Event Envelopes for `<States>::recv` on `.ct1Sampled` -/

/-- Allocation-phase prefix envelope of `<States>::recv` (`Block 332`) on `States.ct1Sampled st`
    (`tag = 0#64 ∨ tag = 1#64`):
    - `msg.epoch ≠ st.uc.epoch`: `[]`.
    - `msg.epoch = st.uc.epoch`, `.ek chunk`: `AddChunkSlotsEnv` followed by `DecodedMessageEnv`.
    - `msg.epoch = st.uc.epoch`, `.ekCt1Ack chunk`: `AddChunkSlotsEnv`, `DecodedMessageEnv`, and
      `Ct1AckRecvEkTailPreEnv` (`recv_ek` + `send_ct2` + `send_ct2_encoder`).
    - `msg.epoch = st.uc.epoch`, any other payload: `[]`. -/
def Ct1SampledRecvPreEnv {F : ShaCompress} (K : MlKem)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  if msg.epoch = st.uc.epoch then
    match msg.payload with
    | .ek chunk =>
      let dec1 := addChunkTotal st.receiving_ek chunk
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts) (DecodedMessageEnv dec1) evs
    | .ekCt1Ack chunk =>
      let dec1 := addChunkTotal st.receiving_ek chunk
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv dec1)
          (Ct1AckRecvEkTailPreEnv K st.uc (decodedMessageTotal dec1)))
        evs
    | _ => evs = []
  else
    evs = []

/-- Postcondition allocator-event envelope of `<States>::recv` (`Block 332`) on
    `States.ct1Sampled st`: `Ct1SampledRecvPreEnv K st msg` followed by trailing `FreeOnlyEvs`
    from epilogue deallocations. -/
def Ct1SampledRecvPostEnv {F : ShaCompress} (K : MlKem)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (Ct1SampledRecvPreEnv K st msg) FreeOnlyEvs evs

abbrev Ct1SampledRecvEnv {F : ShaCompress} (K : MlKem) :=
  @Ct1SampledRecvPostEnv F K

theorem ct1SampledRecvPostEnv_of_pre {F : ShaCompress} {K : MlKem}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {evs : List AllocEvent} (h : Ct1SampledRecvPreEnv K st msg evs) :
    Ct1SampledRecvPostEnv K st msg evs :=
  SeqEnv.inl h

theorem ct1SampledRecvPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs, Ct1SampledRecvPreEnv K st msg evs := by
  by_cases heq : msg.epoch = st.uc.epoch
  · by_cases hek : ∃ chunk, msg.payload = .ek chunk
    · obtain ⟨chunk, hpay⟩ := hek
      obtain ⟨eDec, heDec⟩ := decodedMessageEnv_nonempty (addChunkTotal st.receiving_ek chunk)
      refine ⟨eDec, ?_⟩
      unfold Ct1SampledRecvPreEnv
      rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
      exact Or.inr ⟨[], eDec, rfl, addChunkSlotsEnv_nil st.receiving_ek.pts, heDec⟩
    · by_cases hack : ∃ chunk, msg.payload = .ekCt1Ack chunk
      · obtain ⟨chunk, hpay⟩ := hack
        obtain ⟨eDec, heDec⟩ := decodedMessageEnv_nonempty (addChunkTotal st.receiving_ek chunk)
        obtain ⟨eTail, heTail⟩ := ct1AckRecvEkTailPreEnv_nonempty K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
        refine ⟨eDec ++ eTail, ?_⟩
        unfold Ct1SampledRecvPreEnv
        rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
        exact Or.inr ⟨[], eDec ++ eTail, rfl, addChunkSlotsEnv_nil st.receiving_ek.pts,
          Or.inr ⟨eDec, eTail, rfl, heDec, heTail⟩⟩
      · refine ⟨[], ?_⟩
        unfold Ct1SampledRecvPreEnv
        rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]
        split
        · next c hc => exact False.elim (hek ⟨c, hc⟩)
        · next c hc => exact False.elim (hack ⟨c, hc⟩)
        · rfl
  · refine ⟨[], ?_⟩
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_right_iff.mpr (fun h => absurd h heq)]

theorem ct1SampledRecvPostEnv_nonempty {F : ShaCompress} (K : MlKem)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs, Ct1SampledRecvPostEnv K st msg evs :=
  let ⟨evs, h⟩ := ct1SampledRecvPreEnv_nonempty K st msg
  ⟨evs, SeqEnv.inl h⟩

theorem ct1SampledRecvPostEnv_of_freeOnly_ne {F : ShaCompress} (K : MlKem)
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {evs : List AllocEvent}
    (hne : msg.epoch ≠ st.uc.epoch) (hfree : FreeOnlyEvs evs) :
    Ct1SampledRecvPostEnv K st msg evs := by
  have hpreEq : Ct1SampledRecvPreEnv K st msg = (· = []) := by
    funext e
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
  have hpre : Ct1SampledRecvPreEnv K st msg [] := by rw [hpreEq]
  exact Or.inr ⟨[], evs, rfl, hpre, hfree⟩

theorem ct1SampledRecvPostEnv_nil_other {F : ShaCompress} (K : MlKem)
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    (heq : msg.epoch = st.uc.epoch)
    (hnot_ek : ∀ c, msg.payload ≠ .ek c)
    (hnot_ack : ∀ c, msg.payload ≠ .ekCt1Ack c) :
    Ct1SampledRecvPostEnv K st msg [] := by
  apply SeqEnv.inl
  unfold Ct1SampledRecvPreEnv
  rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]
  split
  · next c hp => exact False.elim (hnot_ek c hp)
  · next c hp => exact False.elim (hnot_ack c hp)
  · rfl

theorem fitsEnv_ek_of_pre {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {st_cost : M.σ} (fsp msgA : BitVec 64)
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hfits : FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg)) :
    FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩) ∧
    (∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64,
          addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩)) := by
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk)) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have h0 : FitsEnv M lim st_cost
      (SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))) := by
    rwa [← hPreEq]
  exact ⟨FitsEnv.seq_left h0, fun _ hAdd => FitsEnv.seq_right h0 hAdd⟩

theorem ct1SampledRecvPostEnv_ek_nil {F : ShaCompress} (K : MlKem)
    {fsp msgA : BitVec 64}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    {evsAdd evsDec : List AllocEvent}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec) :
    Ct1SampledRecvPostEnv K st msg (evsAdd ++ evsDec) := by
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk)) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  apply SeqEnv.inl
  rw [hPreEq]
  exact SeqEnv.append hAdd hDec

theorem ct1SampledRecvPostEnv_ek_free {F : ShaCompress} (K : MlKem)
    {fsp msgA : BitVec 64}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    {evsAdd evsDec evsTail : List AllocEvent}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec)
    (hFree : FreeOnlyEvs evsTail) :
    Ct1SampledRecvPostEnv K st msg ((evsAdd ++ evsDec) ++ evsTail) := by
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk)) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have hpre : Ct1SampledRecvPreEnv K st msg (evsAdd ++ evsDec) := by
    rw [hPreEq]
    exact SeqEnv.append hAdd hDec
  exact SeqEnv.append hpre hFree

theorem fitsEnv_ekCt1Ack_of_pre {M : AllocCostModel} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {st_cost : M.σ} (fsp msgA : BitVec 64)
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hfits : FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg)) :
    FitsEnv M lim st_cost
      (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩) ∧
    (∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64,
          addChunkTotal st.receiving_ek chunk,
          decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩)) ∧
    (∀ evsAdd evsDec,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd →
      PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
        addChunkTotal st.receiving_ek chunk,
        decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec →
      FitsEnv M lim (M.stepEvents (evsAdd ++ evsDec) st_cost)
        (Ct1AckRecvEkTailPreEnv K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)))) := by
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
          (Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)))) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have h0 : FitsEnv M lim st_cost
      (SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
          (Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))))) := by
    rwa [← hPreEq]
  refine ⟨FitsEnv.seq_left h0, fun _ hAdd => FitsEnv.seq_left (FitsEnv.seq_right h0 hAdd),
    fun evsAdd evsDec hAdd hDec => ?_⟩
  rw [M.stepEvents_append]
  exact FitsEnv.seq_right (FitsEnv.seq_right h0 hAdd) hDec

theorem ct1SampledRecvPostEnv_ekCt1Ack_none {F : ShaCompress} (K : MlKem)
    {fsp msgA : BitVec 64}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    {evsAdd evsDec evsTail : List AllocEvent}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = none)
    (hAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec)
    (hFree : FreeOnlyEvs evsTail) :
    Ct1SampledRecvPostEnv K st msg ((evsAdd ++ evsDec) ++ evsTail) := by
  have hTailEq :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) = (· = []) := by
    funext evs
    rw [hdec]
    rfl
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
          (Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)))) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have hTail :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) [] := by
    rw [hTailEq]
  have hDecTail :
      SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
        (Ct1AckRecvEkTailPreEnv K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))) evsDec := by
    have h := SeqEnv.append hDec hTail
    rwa [List.append_nil] at h
  have hpre : Ct1SampledRecvPreEnv K st msg (evsAdd ++ evsDec) := by
    rw [hPreEq]
    exact SeqEnv.append hAdd hDecTail
  exact SeqEnv.append hpre hFree

theorem ct1SampledRecvPostEnv_ekCt1Ack_err {F : ShaCompress} (K : MlKem)
    {fsp msgA : BitVec 64}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    {decoded : Bytes} {err : Error}
    {evsAdd evsDec evsTail : List AllocEvent}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err))
    (hAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec)
    (hFree : FreeOnlyEvs evsTail) :
    Ct1SampledRecvPostEnv K st msg ((evsAdd ++ evsDec) ++ evsTail) := by
  have hTailEq :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) = (· = []) := by
    funext evs
    rw [hdec]
    dsimp only [Ct1AckRecvEkTailPreEnv]
    rw [hrek]
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
          (Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)))) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have hTail :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) [] := by
    rw [hTailEq]
  have hDecTail :
      SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
        (Ct1AckRecvEkTailPreEnv K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))) evsDec := by
    have h := SeqEnv.append hDec hTail
    rwa [List.append_nil] at h
  have hpre : Ct1SampledRecvPreEnv K st msg (evsAdd ++ evsDec) := by
    rw [hPreEq]
    exact SeqEnv.append hAdd hDecTail
  exact SeqEnv.append hpre hFree

theorem fitsEnv_some_ok_ack_of_tail {M : AllocCostModel} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {st_mid : M.σ} (fsp : BitVec 64)
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {chunk : Chunk} {decoded : Bytes}
    {uc_ek : Ct1SentEkReceived (spqrAuthApi F)}
    {outUc : Ct2Sent (spqrAuthApi F)} {ct2 : Bytes} {mac : Mac}
    {evsRek : List AllocEvent}
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (hfits_tail : FitsEnv M lim st_mid
      (Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))))
    (hevsRek : FreeOnlyEvs evsRek) :
    FitsEnv M lim (M.stepEvents evsRek st_mid)
      (UnchunkedSendCt2PreEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩) ∧
    (∀ evsSc : List AllocEvent,
      UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      FitsEnv M lim (M.stepEvents evsSc (M.stepEvents evsRek st_mid))
        (SendCt2EncoderBytesPreEnv ct2.length mac.length)) := by
  have hTailEq :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) =
      SeqEnv FreeOnlyEvs
        (SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc_ek, outUc, ct2, mac⟩)
          (SendCt2EncoderBytesPreEnv ct2.length mac.length)) := by
    funext evs
    rw [hdec]
    dsimp only [Ct1AckRecvEkTailPreEnv]
    rw [hrek]
    dsimp only
    rw [hsc]
  have h0 : FitsEnv M lim st_mid
      (SeqEnv FreeOnlyEvs
        (SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc_ek, outUc, ct2, mac⟩)
          (SendCt2EncoderBytesPreEnv ct2.length mac.length))) := by
    rwa [← hTailEq]
  have h1 := FitsEnv.seq_right h0 hevsRek
  refine ⟨FitsEnv.mono
    (fun _ h => UnchunkedSendCt2PostEnv.of_pre (x := ⟨0#64, 0#64, uc_ek, outUc, ct2, mac⟩) h)
    (FitsEnv.seq_left h1),
    fun _ hSc => FitsEnv.seq_right h1 hSc⟩

theorem ct1SampledRecvPostEnv_ekCt1Ack_ok {F : ShaCompress} (K : MlKem)
    {fsp msgA : BitVec 64}
    {st : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi} {chunk : Chunk}
    {decoded : Bytes} {uc_ek : Ct1SentEkReceived (spqrAuthApi F)}
    {outUc : Ct2Sent (spqrAuthApi F)} {ct2 : Bytes} {mac : Mac} {outEnc : PolyEncoder}
    {evsAdd evsDec evsRek evsSc evsEnc evsDrop : List AllocEvent}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (hAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec)
    (hRek : FreeOnlyEvs evsRek)
    (hSc : UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc)
    (hEnc : SendCt2EncoderPostEnv ⟨0#64, 0#64, ct2, 0#64, mac, outEnc⟩ evsEnc)
    (hDrop : FreeOnlyEvs evsDrop) :
    Ct1SampledRecvPostEnv K st msg
      (((evsAdd ++ evsDec) ++ evsRek ++ (evsSc ++ evsEnc)) ++ evsDrop) := by
  have hTailEq :
      Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) =
      SeqEnv FreeOnlyEvs
        (SeqEnv (UnchunkedSendCt2Env ⟨0#64, 0#64, uc_ek, outUc, ct2, mac⟩)
          (SendCt2EncoderBytesPreEnv ct2.length mac.length)) := by
    funext evs
    rw [hdec]
    dsimp only [Ct1AckRecvEkTailPreEnv]
    rw [hrek]
    dsimp only
    rw [hsc]
  have hPreEq :
      Ct1SampledRecvPreEnv K st msg =
      SeqEnv (AddChunkSlotsEnv st.receiving_ek.pts)
        (SeqEnv (DecodedMessageEnv (addChunkTotal st.receiving_ek chunk))
          (Ct1AckRecvEkTailPreEnv K st.uc
            (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)))) := by
    funext evs
    unfold Ct1SampledRecvPreEnv
    rw [ite_eq_left_iff.mpr (fun h => absurd heq h), hpay]
  have hSc0 : UnchunkedSendCt2Env ⟨0#64, 0#64, uc_ek, outUc, ct2, mac⟩ evsSc := hSc
  rcases hEnc with hEncPre | ⟨evsEncPre, evsEncFree, rfl, hEncPre, hEncFree⟩
  · have hTail :
        Ct1AckRecvEkTailPreEnv K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
          (evsRek ++ (evsSc ++ evsEnc)) := by
      rw [hTailEq]
      exact SeqEnv.append hRek (SeqEnv.append hSc0 hEncPre)
    have hPre :
        Ct1SampledRecvPreEnv K st msg
          (evsAdd ++ (evsDec ++ (evsRek ++ (evsSc ++ evsEnc)))) := by
      rw [hPreEq]
      exact SeqEnv.append hAdd (SeqEnv.append hDec hTail)
    have hAssoc :
        evsAdd ++ (evsDec ++ (evsRek ++ (evsSc ++ evsEnc))) ++ evsDrop =
          ((evsAdd ++ evsDec) ++ evsRek ++ (evsSc ++ evsEnc)) ++ evsDrop := by
      simp only [List.append_assoc]
    exact hAssoc ▸ SeqEnv.append hPre hDrop
  · have hTail :
        Ct1AckRecvEkTailPreEnv K st.uc
          (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
          (evsRek ++ (evsSc ++ evsEncPre)) := by
      rw [hTailEq]
      exact SeqEnv.append hRek (SeqEnv.append hSc0 hEncPre)
    have hPre :
        Ct1SampledRecvPreEnv K st msg
          (evsAdd ++ (evsDec ++ (evsRek ++ (evsSc ++ evsEncPre)))) := by
      rw [hPreEq]
      exact SeqEnv.append hAdd (SeqEnv.append hDec hTail)
    have hAssoc :
        evsAdd ++ (evsDec ++ (evsRek ++ (evsSc ++ evsEncPre))) ++ (evsEncFree ++ evsDrop) =
          ((evsAdd ++ evsDec) ++ evsRek ++ (evsSc ++ (evsEncPre ++ evsEncFree))) ++ evsDrop := by
      simp only [List.append_assoc]
    exact hAssoc ▸ SeqEnv.append hPre (FreeOnlyEvs.append hEncFree hDrop)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero lsmpl_base_332_eq
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144

/-! ## 2. Relocatable Sequencing Adapters -/

set_option maxHeartbeats 800000 in
theorem ct1Sampled_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcro' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcro' hQ))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_seq_vm_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcro' hvm hQ))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_seq_state_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm Pm → SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hQ hcl' =>
    h2 sm Pm hpc hrun hcl' hQ)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hvm hQ))

/-! ## 3. Path 5c Precondition Framing Lemmas & Budget-Threaded Theorem (`+11496 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre0_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (st_cost : M.σ) (s_in : State)
    (fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder) (decoded : Bytes)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
      polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
      wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
      memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s_in ∗
      stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
      messageAt spqrPolyApi msgA msg ⊢
    optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (fsp + 976#64) 1776 ∗ A.pool lim st_cost s_in ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) :=
  Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (st_cost : M.σ) (s1 : State)
    (fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F))
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) (.ok uc_ek) ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
      A.pool lim st_cost s1 ∗ stackAt fsp statesRecvCalleeStackX ∗
      (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) ⊢
    ∃∗ c_ek : Words16,
      ⌜c_ek.w0.toNat < 2 ^ 63⌝ ∗
      wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
      copyScratchStackAt fsp sc ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A.repAlloc a uc_ek)
          (wordsBytes c_ek.toList) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s1 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64)
        rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left
    (unchunkedCt1SentEkReceivedAt_extract_words16 A.repAlloc (fsp + 1856#64) uc_ek)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c_ek
  exact Entails.sepExists_right c_ek (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (st_cost : M.σ) (s3 : State)
    (fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F))
    (c_uc c_ek : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    wordsAt (fsp + 1856#64) c_ek.toList ∗
      wordsAt (fsp + 3856#64) c_ek.toList ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A.repAlloc a uc_ek)
          (wordsBytes c_ek.toList) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s3 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) ⊢
    (memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 3856#64) uc_ek ∗
      memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st_cost s3 ∗ stackAt fsp statesRecvCalleeStackX) ∗
    (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
      memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
      memRegion outA v1RecvSize ∗
      (statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) := by
  refine Entails.trans (sepConj_mono_left (words16_entails_memRegion_128 (fsp + 1856#64) c_ek)) ?_
  have hek :=
    CryptoVerification.SpqrV1.States.Recv.Relocatable.reconstruct_128
      (fun a => unchunkedCt1SentEkReceivedAt A.repAlloc a uc_ek)
      (fsp + 3856#64) c_ek
  have h1856_join :
      memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768 =
      memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        memRegion (fsp + 2312#64) 440 := by
    rw [← ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768)
          (b' := fsp + 1984#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 400) (k := 496)
          (b' := fsp + 2256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2256#64) (n := 56) (k := 440)
          (b' := fsp + 2312#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 8) (k := 152)
        (b' := fsp + 3992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3992#64) (n := 104) (k := 48)
        (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      statesRecvRoPlacedAt_eq_unchunkedSendCt2]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768) ∗
    (wordsAt (fsp + 3856#64) c_ek.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A.repAlloc a uc_ek)
        (wordsBytes c_ek.toList)) ∗
    (memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st_cost s3 ∗ stackAt fsp statesRecvCalleeStackX) ∗
    (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3984#64) 8 ∗
      memRegion (fsp + 4096#64) 48 ∗ memRegion outA v1RecvSize ∗
      (statesRecvJumpTablePlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) by sep_ac_rfl)) ?_
  rw [h1856_join]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hek)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `SepWP` for Path 5c from `+11496 -> s0.x30`
    (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`):
    calls `<Ct1Sent>::recv_ek`, `<Ct1SentEkReceived>::send_ct2`, `send_ct2_encoder`, deallocates
    `ct2`/`mac`/`sending_ct1`/`dec'`, and returns
    `Ok { key := none, state := .ct2Sampled { uc := outUc, sending_ct2 := outEnc } }`. -/
theorem ct1Sampled_path_some_ok_ack_sepWP_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_in : M.σ)
    (s0 s_in : State) (fsp selfA outA msgA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfits_tail : FitsEnv M lim st_in
      (Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = 1#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    let dec' := addChunkTotal st.receiving_ek chunk
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool lim st_in s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg)
      (fun sf Pf =>
        ∃ evsRek evsSc evsEnc evsDrop : List AllocEvent,
          FreeOnlyEvs evsRek ∧
          UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc ∧
          SendCt2EncoderPostEnv ⟨0#64, 0#64, ct2, 0#64, mac, outEnc⟩ evsEnc ∧
          FreeOnlyEvs evsDrop ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA ((States.ct1Sampled st).recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents (evsRek ++ (evsSc ++ evsEnc) ++ evsDrop) st_in) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  intro dec'
  refine SepWP.weaken_pre
    (ct1Sampled_some_ok_ack_pre0_placed st_in s_in fsp selfA outA msgA s0 st msg dec' decoded
      c_uc sc k) ?_
  refine ct1Sampled_seq_state_lscl hcl
    (ArmCt1SampledPart8PlacedBudget.ct1Sampled_some_to_11528_placed hrecv_ek st_in s_in fsp st.uc
      c_uc decoded (.ok uc_ek) _ hcl (by simpa [StatesResult.ofError] using hrek)
      hfsp_align hpc hrun hsp hx20) ?_
  rintro s1 P1 hpc1 hrun1 hcl1
    ⟨evsRek, hevsRek, hP1, hsp1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx28_1, hx29_1, htr1⟩
  obtain ⟨hfits_sc, hfits_enc⟩ := fitsEnv_some_ok_ack_of_tail fsp hdec hrek hsc hfits_tail hevsRek
  refine SepWP.weaken_pre
    (Entails.trans hP1
      (ct1Sampled_some_ok_ack_pre1_placed (M.stepEvents evsRek st_in) s1 fsp selfA outA msgA s0
        st msg dec' uc_ek c_uc sc k)) ?_
  apply ProofLib.SepWP.exists_left; intro c_ek
  wp_focus_pure; intro hw0_ek
  refine ct1Sampled_seq_vm_lscl hcl1
    (ArmCt1SampledPart8PlacedBudget.ct1Sampled_recv_ek_ok_copy_sc_placed s1 fsp sc c_ek _
      hw0_ek hfsp_align hpc1 hrun1 hsp1) ?_
  intro s2 hpc2 hrun2 hcl2 hvm12
    ⟨hsp2, _, _, _, hx19_2, _, hx21_2, hx22_2, hx23_2, _, _, hx28_2, hx29_2, htr2⟩
  refine ct1Sampled_seq_vm_lscl hcl2
    (ArmCt1SampledPart5PlacedBudget.ct1Sampled_ok_branch_ack_placed s2 _ hpc2 hrun2
      (hx22_2.trans (hx22_1.trans hx22))) ?_
  intro s3 hpc3 hrun3 hcl3 hvm23
    ⟨hsp3, _, _, _, hx19_3, _, hx21_3, hx23_3, _, _, hx28_3, hx29_3, htr3⟩
  rw [← A.pool_transport lim (M.stepEvents evsRek st_in) s1 s3 (hvm12.trans hvm23)]
  refine SepWP.weaken_pre
    (ct1Sampled_some_ok_ack_pre3_placed (M.stepEvents evsRek st_in) s3 fsp selfA outA msgA s0
      st msg dec' uc_ek c_uc c_ek sc k) ?_
  refine ArmCt1SampledPart6PlacedBudget.ct1Sampled_send_ct2_and_encode_placed
    hsendCt2 hsendCt2Enc (M.stepEvents evsRek st_in) s0 s3 fsp uc_ek outUc ct2 mac outEnc
    hsc henc hfits_sc hfits_enc _ hcl3 hfsp_align hpc3 hrun3 (hsp3.trans hsp2)
    (htr3.trans (htr2.trans (htr1.trans htr)))
    (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
    (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))) ?_
  intro s4 evsSc evsEnc g_uc ct2Cap ct2Ptr macCap macPtr
    hpc4 hrun4 hsp4 hx19_4 hx20_4 _ _ hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 hcl4
    hevsSc hevsEnc
  rw [states_recv_ct1Sampled_eq_some_ok_ack K st msg chunk decoded uc_ek outUc ct2 mac outEnc
        heq hpay hlen hsort hdec hrek hsc henc]
  refine SepWP.mono
    (ArmCt1SampledPart9PlacedBudget.ct1Sampled_some_ok_ack_from_11696_placed hdealloc hmemcpy
      (M.stepEvents (evsSc ++ evsEnc) (M.stepEvents evsRek st_in))
      s0 s4 fsp selfA outA st dec' c_uc outUc outEnc g_uc ct2Cap ct2Ptr macCap macPtr
      { sc with wb0 := c_ek.w1 } k (messageAt spqrPolyApi msgA msg)
      hcl4 hfsp_align hsp0_align hfsp hpc4 hrun4 hsp4
      (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))))
      hx20_4 hx25_4 hx26_4 hx27_4
      (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))))
      hx29_4 htr4) ?_
  rintro sf Pf _ _ ⟨evsDrop, hevsDrop, hPf, hsp_f, hcs_f, htr_f⟩
  have hst_eq :
      M.stepEvents evsDrop (M.stepEvents (evsSc ++ evsEnc) (M.stepEvents evsRek st_in)) =
        M.stepEvents (evsRek ++ (evsSc ++ evsEnc) ++ evsDrop) st_in := by
    simp only [← M.stepEvents_append, List.append_assoc]
  exact ⟨evsRek, evsSc, evsEnc, evsDrop, hevsRek, hevsSc, hevsEnc, hevsDrop,
    Entails.trans hPf (Entails.of_eq (by rw [hst_eq]; sep_ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 800000 in
/-- `SepWPp` Path 5c exit theorem for `statesRecvVariantPlacedSpecOfPrePostEnv` on
    `States.ct1Sampled st` (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`). -/
theorem ct1Sampled_path_some_ok_ack_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (evsAdd evsDec : List AllocEvent)
    (s0 s_in : State) (fsp selfA outA msgA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hevsAdd : AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, st.receiving_ek, chunk⟩ evsAdd)
    (hevsDec : PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64,
      addChunkTotal st.receiving_ek chunk,
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk)⟩ evsDec)
    (hfits_tail : FitsEnv M lim (M.stepEvents (evsAdd ++ evsDec) st_cost)
      (Ct1AckRecvEkTailPreEnv K st.uc
        (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = 1#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    let dec' := addChunkTotal st.receiving_ek chunk
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) := by
  intro dec'
  refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
    s0 s_in outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
  refine SepWP.mono
    (ct1Sampled_path_some_ok_ack_sepWP_placed hdealloc hmemcpy hrecv_ek hsendCt2 hsendCt2Enc
      (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s_in fsp selfA outA msgA st msg chunk decoded
      uc_ek outUc ct2 mac outEnc c_uc sc k hcl heq hpay hlen hsort hdec hrek hsc henc hfits_tail
      hfsp_align hsp0_align hfsp hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx28 hx29 htr) ?_
  rintro sf Pf _ _ ⟨evsRek, evsSc, evsEnc, evsDrop, hevsRek, hevsSc, hevsEnc, hevsDrop,
    hPf, hsp_f, hcs_f, htr_f⟩
  have hst_eq :
      M.stepEvents (evsRek ++ (evsSc ++ evsEnc) ++ evsDrop)
          (M.stepEvents (evsAdd ++ evsDec) st_cost) =
        M.stepEvents (((evsAdd ++ evsDec) ++ evsRek ++ (evsSc ++ evsEnc)) ++ evsDrop) st_cost := by
    simp only [← M.stepEvents_append, List.append_assoc]
  exact ⟨⟨((evsAdd ++ evsDec) ++ evsRek ++ (evsSc ++ evsEnc)) ++ evsDrop,
    ct1SampledRecvPostEnv_ekCt1Ack_ok K heq hpay hdec hrek hsc
      hevsAdd hevsDec hevsRek hevsSc hevsEnc hevsDrop,
    by rwa [hst_eq] at hPf⟩,
    hsp_f, hcs_f, htr_f⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux
