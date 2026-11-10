/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget

/-!
# Exact Block-`332`-Aligned `<States>::recv` Protocol-Guarded Envelopes and Specs

Refines `SpqrStatesRecvPeakSpec`'s `<States>::recv` trace envelopes (`StatesRecvEnv'`,
`StatesRecvProtoEnv'`, `StatesRecvExactTightEnv`) to align with every panic split and trailing
epilogue deallocation of the compiled Block `332` arms (`recv_ct2_chunk` `OptSecret32AllocEnv` and
`ct1Len != 960 || dkLen != 2400` panic split, `recv_ek_chunk` `uc.recv_ek` / `send_ct2` guards, and
outer epilogue `FreeOnlyEvs`), preserving the aggregate credit (`1,647,247 / 0 / 0 / 93,776`) and
slot-group (`3,732 * FineScale` and split `27,105,719`) bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsProg_332 lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes CIPHERTEXT1_SIZE Chunk DECAPSULATION_KEY_SIZE Epoch Message MlKem
   SortedSetPt States V1State protoPolyDecoderToPb spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1Sampled Ct2Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (Ct1Received EkSentCt1Received HeaderSent KeysSampled KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.StateSize
  (except_bind_eq_ok optRaw rawAuth rawChCt1Acknowledged rawChCt1Sampled rawChEkSentCt1Received
   rawChHeaderSent rawChNoHeaderReceived rawInnerState rawPolyDec rawUcCt1Sent
   rawUcEkSentCt1Received rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
  (decodedMessage_fine_phaseGroupSpec_split rustAlloc_align16_fine_groupSpec
   rustRealloc_align16_fine_groupSpec statesRecvTightGroupS_split)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
  (NonFreeBound.append_eq PhaseCreditSpec.append_eq addChunkSlots_fine_replicate16_phaseCreditSpec
   addChunkSlots_fine_two_mul_phaseCreditSpec addChunkSlots_nonFreeBound
   decodedMessage_fine_tight_phaseCreditSpec decodedMessage_ptsNeeded_le_576_nonFreeBound
   encodeBytes_fine_1152_phaseCreditSpec encodeBytes_nonFreeBound
   fineSmallAllocCost_le_9789_of_le_1280 libcruxHmacSha256_fine_phaseCreditSpec
   libcruxHmacSha256_phaseCreditSpec ptsLenSum sendCt2ConcatHmac_nonFreeBound
   sendCt2Reserve128_fine_le_1088_phaseCreditSpec sendCt2Reserve128_nonFreeBound
   sendCt2Reserve128_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
  (AuthUpdateEnv NoHeaderReceivedRecvHdrChunkBodyEnv SendCt2EncoderEnv SendCt2EncoderGrowEnv
   StatesProtocolSizes UnchunkedSendCt2BySizesEnv addChunkTotal_ptsNeeded_uncond
   authUpdate_fine_two_mul_phaseCreditSpec authUpdate_nonFreeBound authUpdate_phaseCreditSpec
   isEkReceivedCt1AckMsg isStatesProtoSized isStatesProtoSized_eq_true_iff optBytesLen
   optBytesLen_decodedMessageTotal_le rawPolyDec_intoPb_eq recvCt2AllocMacCt2Events
   recvHdrChunkTail_fine_le_96_phaseCreditSpec recvHdrChunkTail_nonFreeBound
   sendCt2Encoder_128_32_phaseCreditSpec sendCt2Encoder_fine_128_32_phaseCreditSpec
   sendCt2Encoder_nonFreeBound sliceConcat2Events_phaseCreditSpec statesRecvTightDeltaCum
   statesRecvTightDeltaLive statesRecvTightDeltaPeak statesRecvTightGroupS
   statesRecvTightRawMaxReq unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec
   unchunkedSendCt2BySizes_nonFreeBound unchunkedSendCt2BySizes_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotEnv AddChunkSlotsEnv addChunkSlotsEnv_nil growOnePtEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (Ct1AckRecvEkTailPreEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (noHeaderReceivedRecvHdrChunkEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudget
  (states_recv_ct1Acknowledged_placed_ofEnv_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux
  (StatesRecvCt1AcknowledgedEnv statesRecvCt1AcknowledgedPostEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudget
  (states_recv_ct1Received_exact_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux
  (Ct1ReceivedArmPostEnv Ct1ReceivedArmPreEnv ct1ReceivedArmPostEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudget
  (states_recv_ct1Sampled_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux
  (Ct1SampledRecvEnv ct1SampledRecvPostEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget
  (StatesRecvEkReceivedCt1SampledEnv statesRecvEkReceivedCt1SampledPostEnv_nonempty
   states_recv_ekReceivedCt1Sampled_placed_ofEnv_cro_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudget
  (StatesRecvEkSentCt1ReceivedEnv statesRecvEkSentCt1ReceivedEnv_nonempty
   states_recv_ekSentCt1Received_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudget
  (HeaderSentArmEnv headerSentArmPostEnv_nonempty states_recv_headerSent_env_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2PlacedBudget
  (KeysSampledArmPostEnv KeysSampledArmPreEnv keysSampledArmPostEnv_nonempty
   states_recv_keysSampled_exact_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2PlacedBudget
  (StatesRecvNoHeaderReceivedEnv statesRecvNoHeaderReceivedEnv_nonempty
   states_recv_noHeaderReceived_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget
  (KeysUnsampledRecvPostEnv states_recv_keysUnsampled_placed_ok_cro_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget
  (HeaderReceivedRecvPostEnv states_recv_headerReceived_placed_ok_cro_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3PlacedBudget
  (Ct2SampledRecvPostEnv states_recv_ct2Sampled_placed_ok_cro_ext_ofPrePostEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
  (StatesRecvPlacedContracts states_recv_placed_ok_ext_of_variants_ofEnv
   states_recv_placed_ok_x_of_ext_ofEnv subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget
  (OptSecret32AllocEnv optSecret32AllocEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget (StatesRecvPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
   sendCt2Reserve128Events sendCt2Seg23Events)

/-! ## Block-`332`-Aligned `<States>::recv` Envelopes -/

/-- Post-`decoded_message` envelope for `<EkSentCt1Received>::recv_ct2_chunk`, modeling the
`ct1Len != 960 || dkLen != 2400` unwrap-panic split after `recvCt2AllocMacCt2Events` and the
trailing `OptSecret32AllocEnv` allocation after `sendCt2ConcatHmacEvents`. -/
def RecvCt2ChunkTailEnv' (rootKeyLen ct1Len dkLen : Nat) : Option Bytes → List AllocEvent → Prop
  | none, evs => FreeOnlyEvs evs
  | some ct2Full, evs =>
    if ct2Full.length < 128 then
      FreeOnlyEvs evs
    else if ct1Len != 960 || dkLen != 2400 then
      SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs evs
    else
      SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
        (SeqEnv (· = rustAllocEvents 32 1)
          (SeqEnv (· = sliceConcat2Events 41)
            (SeqEnv (· = rustAllocEvents 32 1)
              (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                (SeqEnv (SendCt2Reserve128Env ct1Len)
                  (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                    (SeqEnv FreeOnlyEvs
                      (SeqEnv OptSecret32AllocEnv FreeOnlyEvs))))))))
        evs

/-- Pre-state-pinned envelope for `<EkSentCt1Received>::recv_ct2_chunk`. -/
def EkSentCt1ReceivedRecvCt2ChunkEnv' {F : ShaCompress}
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (epoch : Epoch) (chunk : Chunk)
    (evs : List AllocEvent) : Prop :=
  if epoch != s.uc.epoch then
    evs = []
  else
    let receivingCt2 := addChunkTotal s.receiving_ct2 chunk
    SeqEnv (AddChunkSlotsEnv s.receiving_ct2.pts)
      (SeqEnv (DecodedMessageEnv receivingCt2)
        (RecvCt2ChunkTailEnv' s.uc.auth.rootKey.length s.uc.ct1.length s.uc.dk.length
          (decodedMessageTotal receivingCt2)))
      evs

/-- Post-`decoded_message` prefix tail for `<Ct1Sampled>::recv_ek_chunk` and
`<Ct1Acknowledged>::recv_ek_chunk`, matching on `uc.recv_ek K uc.epoch ekBytes` and `uc1.send_ct2 K`
and sequencing leading `FreeOnlyEvs` before `UnchunkedSendCt2BySizesEnv` and `SendCt2EncoderEnv 128 32`.
-/
def RecvEkChunkSendCt2TailEnv' {F : ShaCompress} (K : MlKem) (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    Option Bytes → List AllocEvent → Prop
  | none, evs => FreeOnlyEvs evs
  | some ekBytes, evs =>
    if !sendCt2OnDone then
      FreeOnlyEvs evs
    else
      match uc.recv_ek K uc.epoch ekBytes with
      | .error _ => FreeOnlyEvs evs
      | .ok uc1 =>
        SeqEnv FreeOnlyEvs
          (match uc1.send_ct2 K with
           | .error _ => FreeOnlyEvs
           | .ok (_outUc, _ct2, _mac) =>
             SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
               (SendCt2EncoderEnv 128 32))
          evs

/-- 11-constructor pre-state-pinned allocator trace envelope for `<spqr::v1::chunked::states::States>::recv` with outer epilogue `FreeOnlyEvs`.
-/
def StatesRecvEnv' {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  match st with
  | .keysUnsampled _ => FreeOnlyEvs
  | .keysSampled s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct1 _ =>
        SeqEnv
          (SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
            (EncodeBytesEnv s.uc.ek.length))
          FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .headerSent s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct1 chunk =>
        SeqEnv
          (SeqEnv (AddChunkSlotsEnv s.receiving_ct1.pts)
            (DecodedMessageEnv (addChunkTotal s.receiving_ct1 chunk)))
          FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct1Received s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct2 _ =>
        SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ekSentCt1Received s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct2 chunk =>
        SeqEnv (EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .noHeaderReceived s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .hdr chunk =>
        SeqEnv (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .headerReceived _ => FreeOnlyEvs
  | .ct1Sampled s =>
    if msg.epoch == s.uc.epoch then
      let chunkAck? : Option (Chunk × Bool) := match msg.payload with
        | .ek chunk => some (chunk, false)
        | .ekCt1Ack chunk => some (chunk, true)
        | _ => none
      match chunkAck? with
      | none => FreeOnlyEvs
      | some (chunk, ack) =>
        let receivingEk := addChunkTotal s.receiving_ek chunk
        SeqEnv
          (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
            (SeqEnv (DecodedMessageEnv receivingEk)
              (RecvEkChunkSendCt2TailEnv' K ack s.uc
                (decodedMessageTotal receivingEk))))
          FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ekReceivedCt1Sampled s =>
    if msg.epoch == s.uc.epoch then
      if isEkReceivedCt1AckMsg msg then
        match s.uc.send_ct2 K with
        | .error _ => FreeOnlyEvs
        | .ok (_outUc, _ct2, _mac) =>
          SeqEnv
            (SeqEnv (UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length)
              (SendCt2EncoderEnv 128 32))
            FreeOnlyEvs
      else
        FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct1Acknowledged s =>
    if msg.epoch == s.uc.epoch then
      let chunk? : Option Chunk := match msg.payload with
        | .ek chunk => some chunk
        | .ekCt1Ack chunk => some chunk
        | _ => none
      match chunk? with
      | none => FreeOnlyEvs
      | some chunk =>
        let receivingEk := addChunkTotal s.receiving_ek chunk
        SeqEnv
          (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
            (SeqEnv (DecodedMessageEnv receivingEk)
              (RecvEkChunkSendCt2TailEnv' K true s.uc
                (decodedMessageTotal receivingEk))))
          FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct2Sampled _ => FreeOnlyEvs

/-- Protocol-sized wrapper around `StatesRecvEnv' K` (coinciding with `StatesRecvEnv' K` on every `States.from_pb` state).
-/
def StatesRecvProtoEnv' {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  if isStatesProtoSized st then StatesRecvEnv' K st msg else FreeOnlyEvs

/-- Exact 11-arm Block-`332` post-envelope (`StatesRecvExactTightEnv`). -/
def StatesRecvExactTightEnv {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) (evs : List AllocEvent) : Prop :=
  match x.self with
  | .keysUnsampled st => KeysUnsampledRecvPostEnv st x.msg evs
  | .keysSampled st => KeysSampledArmPostEnv st x.msg evs
  | .headerSent st => HeaderSentArmEnv st x.msg evs
  | .ct1Received st => Ct1ReceivedArmPostEnv st x.msg evs
  | .ekSentCt1Received _ => StatesRecvEkSentCt1ReceivedEnv x evs
  | .noHeaderReceived _ => StatesRecvNoHeaderReceivedEnv x evs
  | .headerReceived st => HeaderReceivedRecvPostEnv st x.msg evs
  | .ct1Sampled st => Ct1SampledRecvEnv K st x.msg evs
  | .ekReceivedCt1Sampled _ => StatesRecvEkReceivedCt1SampledEnv K x evs
  | .ct1Acknowledged _ => StatesRecvCt1AcknowledgedEnv K x evs
  | .ct2Sampled st => Ct2SampledRecvPostEnv st x.msg evs

/-! ## Non-Emptiness and `States.from_pb` / `StatesProtocolSizes` Bridges -/

theorem ekSentCt1Received_dk_length_of_from_pb {F : ShaCompress}
    {pb : V1State} {s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok (.ekSentCt1Received s)) :
    s.uc.dk.length = 2400 := by
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    cases inner <;>
      dsimp only [Functor.map, Except.map] at h <;>
      split at h <;> try contradiction
    all_goals try (cases Except.ok.inj h)
    rename_i pbSt v hv
    unfold EkSentCt1Received.from_pb at hv
    dsimp only [Bind.bind, Except.bind] at hv
    cases huc_opt : pbSt.uc with
    | none =>
      rw [huc_opt] at hv
      split at hv <;> [split at hv <;> contradiction; contradiction]
    | some u =>
      rw [huc_opt] at hv
      cases hrec : pbSt.receivingCt2 with
      | none =>
        rw [hrec] at hv; dsimp only at hv
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
        cases hv2
      | some d =>
        rw [hrec] at hv; dsimp only at hv
        split at hv
        · contradiction
        · rcases except_bind_eq_ok hv with ⟨uc, huc, hv2⟩
          rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
          cases Except.ok.inj hv3
          unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb at huc
          split at huc <;> [skip; contradiction]
          rename_i hcond
          cases hauth : u.auth <;> rw [hauth] at huc
          · contradiction
          · cases Except.ok.inj huc
            exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).1

theorem statesRecvEnv'_nonempty {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs : List AllocEvent, StatesRecvEnv' K st msg evs := by
  have hFree : ∃ evs : List AllocEvent, FreeOnlyEvs evs := ⟨[], FreeOnlyEvs.nil⟩
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new)))⟩
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil s.receiving_ct1.pts))⟩
    · exact hFree
  | ct1Received s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], Or.inl (addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new))⟩
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      unfold EkSentCt1ReceivedRecvCt2ChunkEnv'
      split
      · exact ⟨[], Or.inl rfl⟩
      · exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil s.receiving_ct2.pts))⟩
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      unfold NoHeaderReceivedRecvHdrChunkBodyEnv
      split
      · exact ⟨[], Or.inl rfl⟩
      · exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil s.receiving_hdr.pts))⟩
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil s.receiving_ek.pts))⟩
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          dsimp only
          have h1 : UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length
              (((sendCt2Seg23Events s.uc.es ++ []) ++ sendCt2ConcatHmacEvents s.uc.ct1.length) ++
                []) :=
            ConcatEnv.append
              (ConcatEnv.append (ConcatEnv.append rfl (Or.inl rfl)) rfl)
              FreeOnlyEvs.nil
          exact ⟨_, Or.inl (Or.inl h1)⟩
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals exact ⟨[], Or.inl (Or.inl (addChunkSlotsEnv_nil s.receiving_ek.pts))⟩
    · exact hFree
  | ct2Sampled _ => exact hFree

theorem statesRecvProtoEnv'_nonempty {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs : List AllocEvent, StatesRecvProtoEnv' K st msg evs := by
  unfold StatesRecvProtoEnv'
  split
  · exact statesRecvEnv'_nonempty K st msg
  · exact ⟨[], FreeOnlyEvs.nil⟩

theorem statesRecvExactTightEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) :
    ∃ evs : List AllocEvent, StatesRecvExactTightEnv K x evs := by
  rcases x with ⟨outA, selfA, msgA, self, msg⟩
  cases self with
  | keysUnsampled st =>
    dsimp only [StatesRecvExactTightEnv, KeysUnsampledRecvPostEnv]
    split
    · exact ⟨[], FreeOnlyEvs.nil⟩
    · exact ⟨[], rfl⟩
  | keysSampled st => exact keysSampledArmPostEnv_nonempty st msg
  | headerSent st => exact headerSentArmPostEnv_nonempty st msg
  | ct1Received st => exact ct1ReceivedArmPostEnv_nonempty st msg
  | ekSentCt1Received st =>
    exact statesRecvEkSentCt1ReceivedEnv_nonempty ⟨outA, selfA, msgA, .ekSentCt1Received st, msg⟩
  | noHeaderReceived st =>
    exact statesRecvNoHeaderReceivedEnv_nonempty ⟨outA, selfA, msgA, .noHeaderReceived st, msg⟩
  | headerReceived st =>
    dsimp only [StatesRecvExactTightEnv, HeaderReceivedRecvPostEnv]
    split
    · exact ⟨[], FreeOnlyEvs.nil⟩
    · exact ⟨[], rfl⟩
  | ct1Sampled st => exact ct1SampledRecvPostEnv_nonempty K st msg
  | ekReceivedCt1Sampled st =>
    exact statesRecvEkReceivedCt1SampledPostEnv_nonempty K
      ⟨outA, selfA, msgA, .ekReceivedCt1Sampled st, msg⟩
  | ct1Acknowledged st =>
    exact statesRecvCt1AcknowledgedPostEnv_nonempty K
      ⟨outA, selfA, msgA, .ct1Acknowledged st, msg⟩
  | ct2Sampled st =>
    dsimp only [StatesRecvExactTightEnv, Ct2SampledRecvPostEnv]
    split
    · exact ⟨[], FreeOnlyEvs.nil⟩
    · exact ⟨[], rfl⟩

theorem statesRecvProtoEnv'_eq_of_protocolSizes {F : ShaCompress} (K : MlKem)
    {st : States spqrPolyApi (spqrAuthApi F)} (hproto : StatesProtocolSizes st)
    (msg : Message spqrPolyApi) :
    StatesRecvProtoEnv' K st msg = StatesRecvEnv' K st msg := by
  unfold StatesRecvProtoEnv'
  rw [(isStatesProtoSized_eq_true_iff st).mpr hproto]
  simp only [↓reduceIte]

theorem statesRecvProtoEnv'_eq_of_from_pb {F : ShaCompress} (K : MlKem)
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    StatesRecvProtoEnv' K st msg = StatesRecvEnv' K st msg :=
  statesRecvProtoEnv'_eq_of_protocolSizes K (StatesProtocolSizes.of_from_pb hfrom) msg

/-! ## Leaf and Aggregate `PhaseCreditSpec` and `PhaseGroupSpec` Bounds -/

private theorem seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {cum req : Nat}
    (h : PhaseCreditSpec M E cum 0 0 req) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) cum 0 0 req :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by decide) (by decide) (by omega)

private theorem uc_recv_ek_ct1_eq {F : ShaCompress} (K : MlKem)
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {epoch : Epoch} {ekBytes : Bytes}
    {uc1 : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    (h : uc.recv_ek K epoch ekBytes = .ok uc1) :
    uc1.ct1 = uc.ct1 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · contradiction
  · split at h
    · cases Except.ok.inj h
      rfl
    · contradiction

private theorem optSecret32Alloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M OptSecret32AllocEnv 9603 8227 8227 32 := by
  unfold OptSecret32AllocEnv
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem optSecret32Alloc_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel OptSecret32AllocEnv 738 0 0 32 := by
  unfold OptSecret32AllocEnv
  have h32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (smallAllocCost_le_738_of_le_44 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  exact ((PhaseCreditSpec.nil fineCostModel).or h32).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem sliceConcat2Events_fine_le_44 {n : Nat} (hn : n ≤ 44) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) 738 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (smallAllocCost_le_738_of_le_44 hn) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

/-- Regime-uniform `PhaseCreditSpec` for `RecvCt2ChunkTailEnv'` under `ModelHyps M`. -/
theorem recvCt2ChunkTail'_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rootKeyLen ct1Len dkLen : Nat) (optCt2 : Option Bytes) :
    let n := optBytesLen optCt2
    PhaseCreditSpec M (RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen optCt2)
      (2 * n + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (n + rootKeyLen + 3 * ct1Len + 140430)
      (n + rootKeyLen + 3 * ct1Len + 140430)
      (max n (max (rootKeyLen + 64) (2 * ct1Len + 254))) := by
  cases optCt2 with
  | none =>
    change PhaseCreditSpec M (RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen none)
      (2 * 0 + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (0 + rootKeyLen + 3 * ct1Len + 140430)
      (0 + rootKeyLen + 3 * ct1Len + 140430)
      (max 0 (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)
  | some ct2Full =>
    change PhaseCreditSpec M (RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full))
      (2 * ct2Full.length + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 140430)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 140430)
      (max ct2Full.length (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    have h1 :
        PhaseCreditSpec M (· = recvCt2AllocMacCt2Events ct2Full.length)
          (2 * ct2Full.length + 19334) (ct2Full.length + 16518) (ct2Full.length + 16518)
          (max ct2Full.length 128) := by
      unfold recvCt2AllocMacCt2Events
      have ha :
          PhaseCreditSpec M
            (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
            (2 * (ct2Full.length - 128) + 9539) (ct2Full.length - 128 + 8195)
            (ct2Full.length - 128 + 8195) (ct2Full.length - 128) := by
        split
        · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
        · exact PhaseCreditSpec.rustAlloc_aff hM (req := ct2Full.length - 128) (al := 1)
            (by decide)
      have hb := PhaseCreditSpec.rustAlloc_aff hM (req := 128) (al := 1) (by decide)
      exact (PhaseCreditSpec.append_eq ha hb).mono (by omega) (by omega) (by omega) (by omega)
    have hFree := PhaseCreditSpec.freeOnly_of_hyps hM
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (by omega) (by omega) (by omega) (by omega)
    · by_cases hpan : (ct1Len != 960 || dkLen != 2400) = true
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by omega) (by omega) (by omega) (by omega)
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env ct1Len)
                          (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
        have h3 := sliceConcat2Events_phaseCreditSpec hM 41
        have h4 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
        have h5 := authUpdate_phaseCreditSpec hM rootKeyLen 32
        have h6 := sendCt2Reserve128_phaseCreditSpec hM ct1Len
        have h7 :
            PhaseCreditSpec M (· = sendCt2ConcatHmacEvents ct1Len)
              (2 * ct1Len + 48485) (ct1Len + 41358) (ct1Len + 41358) (max (ct1Len + 171) 64) := by
          unfold sendCt2ConcatHmacEvents
          have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 35 + 8 + (ct1Len + 128)) (al := 1)
            (by decide)
          exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
            (by omega) (by omega) (by omega) (by omega)
        have hOpt := optSecret32Alloc_phaseCreditSpec hM
        exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono
          (by omega) (by omega) (by omega) (by omega)

/-- `fineCostModel` `PhaseCreditSpec` for `RecvCt2ChunkTailEnv'` (`Δlive = Δpeak = 0`). -/
theorem recvCt2ChunkTail'_fine_two_mul_phaseCreditSpec {rootKeyLen ct1Len : Nat} (dkLen : Nat)
    (hrk : rootKeyLen + 32 ≤ 135167) (hct1 : ct1Len ≤ 1088)
    {optCt2 : Option Bytes} (hn : optBytesLen optCt2 ≤ 160) :
    PhaseCreditSpec fineCostModel (RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen optCt2)
      (2 * rootKeyLen + 53867) 0 0 (max (rootKeyLen + 64) 2430) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  cases optCt2 with
  | none =>
    exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ct2Full =>
    dsimp only [optBytesLen] at hn
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have h1 :
          PhaseCreditSpec fineCostModel (· = recvCt2AllocMacCt2Events ct2Full.length)
            10527 0 0 128 := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            PhaseCreditSpec fineCostModel
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
              738 0 0 32 := by
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · have hsm : ct2Full.length - 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
              rw [fineCostModel_smallMaxReq_eq]; omega
            exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
              (req := ct2Full.length - 128) (al := 1) (by decide) hsm).mono
              (smallAllocCost_le_738_of_le_44 (by omega))
              (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have hb := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 128) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
        exact (PhaseCreditSpec.append_eq ha hb).mono
          (by decide) (by decide) (by decide) (by decide)
      by_cases hpan : (ct1Len != 960 || dkLen != 2400) = true
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by omega) (by decide) (by decide) (by omega)
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env ct1Len)
                          (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        have h32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (smallAllocCost_le_738_of_le_44 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
        have h41 := sliceConcat2Events_fine_le_44 (n := 41) (by decide)
        have h5 := authUpdate_fine_two_mul_phaseCreditSpec hrk
        have h6 := sendCt2Reserve128_fine_le_1088_phaseCreditSpec hct1
        have h7 :
            PhaseCreditSpec fineCostModel (· = sendCt2ConcatHmacEvents ct1Len)
              15348 0 0 1280 := by
          unfold sendCt2ConcatHmacEvents
          have hsm : 35 + 8 + (ct1Len + 128) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
            rw [fineCostModel_smallMaxReq_eq]; omega
          have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
            (req := 35 + 8 + (ct1Len + 128)) (al := 1) (by decide) hsm).mono
            (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
            (Nat.le_refl 0) (Nat.le_refl 0) (show 35 + 8 + (ct1Len + 128) ≤ 1280 by omega)
          exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
            (by decide) (by decide) (by decide) (by decide)
        have hOpt := optSecret32Alloc_fine_phaseCreditSpec
        exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono
          (by omega) (by decide) (by decide) (by omega)

private theorem recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec {F : ShaCompress} (K : MlKem)
    (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hct1 : uc.ct1.length ≤ 1088) (optEk : Option Bytes) :
    PhaseCreditSpec fineCostModel (RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc optEk)
      205872 0 0 2430 := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  cases optEk with
  | none =>
    exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ekBytes =>
    by_cases hsd : (!sendCt2OnDone) = true
    · have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd]
      rw [heq]
      exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · cases hrek : uc.recv_ek K uc.epoch ekBytes with
      | error _ =>
        have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
          funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek]
        rw [heq]
        exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
      | ok uc1 =>
        have hct1' : uc1.ct1.length ≤ 1088 := by
          rw [uc_recv_ek_ct1_eq K hrek]
          exact hct1
        cases hsc : uc1.send_ct2 K with
        | error _ =>
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs FreeOnlyEvs := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (hFree.seq hFree).mono
            (by decide) (by decide) (by decide) (by decide)
        | ok val =>
          rcases val with ⟨_, _, _⟩
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs
                (SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
                  (SendCt2EncoderEnv 128 32)) := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec uc1.es hct1'
          have h2 := sendCt2Encoder_fine_128_32_phaseCreditSpec
          exact (hFree.seq (h1.seq h2)).mono
            (by decide) (by decide) (by decide) (by decide)

private theorem raw46880_dec_cum_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    16 * ptsSum + 9571 * 16 ≤ 339248 := by
  have hp : ptsSum ≤ 11632 := by omega
  have hm : 16 * ptsSum ≤ 16 * 11632 := Nat.mul_le_mul_left 16 hp
  exact Nat.le_trans (Nat.add_le_add_right hm _) (by decide)

private theorem raw46880_dec_req_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    8 * ptsSum + 16 ≤ 93072 := by
  omega

private theorem raw46880_ct2'_cum_le {ptsSum rk rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hsum : (rk + 960) + rawDec ≤ 46880) :
    (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53867)) ≤ statesRecvTightDeltaCum := by
  have hcomb : 4 * ptsSum + rk ≤ 45568 := by omega
  have hlin : 16 * ptsSum + 2 * rk ≤ 4 * 45568 := by omega
  have hconst : 4 * 45568 + 9571 * 16 + 1022346 + 53867 ≤ statesRecvTightDeltaCum := by decide
  have h1 : (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53867)) =
      (16 * ptsSum + 2 * rk) + (9571 * 16 + 1022346 + 53867) := by omega
  rw [h1]
  exact Nat.le_trans (Nat.add_le_add_right hlin _) (by
    simpa only [Nat.add_assoc] using hconst)

private theorem statesRecv'_tight_of_protocolSizes_46880_phaseCreditSpec {F : ShaCompress}
    (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st)
    (hraw46 : rawV1State st.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv' K st msg)
      statesRecvTightDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightRawMaxReq := by
  have hFree :
      PhaseCreditSpec fineCostModel FreeOnlyEvs
        statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq :=
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := addChunkSlots_fine_replicate16_phaseCreditSpec
      have h2 : PhaseCreditSpec fineCostModel (EncodeBytesEnv s.uc.ek.length) 33744 0 0 1152 := by
        rw [hproto]
        exact encodeBytes_fine_1152_phaseCreditSpec
      exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct1
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_ct1.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, HeaderSent.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChHeaderSent, optRaw]
          omega
        have hreq93 := raw46880_dec_req_le hraw hdec_le
        have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct1.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) hreq93
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt1) (by omega)).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rCt1.ptsNeeded) ≤ 960 by omega)
        exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
          (by decide) (by decide) (by decide) (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly fineCostModel_modelHyps
        addChunkSlots_fine_replicate16_phaseCreditSpec).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct2
        rw [hlen16] at hraw
        have hsum_le :
            (s.uc.auth.rootKey.length + 960) +
              rawPolyDec (protoPolyDecoderToPb s.receiving_ct2.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, EkSentCt1Received.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb,
            spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
            rawV1State, rawInnerState, rawChEkSentCt1Received, rawUcEkSentCt1Received,
            rawAuth, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv'
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 :
                PhaseCreditSpec fineCostModel (AddChunkSlotsEnv s.receiving_ct2.pts)
                  (16 * ptsLenSum s.receiving_ct2.pts + 9571 * 16) 0 0 91152 := by
              have hb := addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct2.pts
                (by omega)
              rw [hlen16] at hb
              exact hb.mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt2) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rCt2.ptsNeeded) ≤ 256 by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 := (recvCt2ChunkTail'_fine_two_mul_phaseCreditSpec
              (rootKeyLen := s.uc.auth.rootKey.length) (ct1Len := s.uc.ct1.length)
              s.uc.dk.length (by omega) (by omega) hn160).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max (s.uc.auth.rootKey.length + 64) 2430 ≤ 45632 by omega)
            exact (h1.seq (h2.seq h3)).mono
              (raw46880_ct2'_cum_le hraw hsum_le)
              (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_hdr
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, NoHeaderReceived.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChNoHeaderReceived, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 48 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_hdr.pts
              (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
              (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rHdr) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rHdr.ptsNeeded) ≤ 256 by omega)
            have hn96 : optBytesLen (decodedMessageTotal rHdr) ≤ 96 := by
              have := optBytesLen_decodedMessageTotal_le rHdr; omega
            have h3 := recvHdrChunkTail_fine_le_96_phaseCreditSpec hn96
            exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Sampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Sampled, rawUcCt1Sent, optRaw]
        omega
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (RecvEkChunkSendCt2TailEnv' K ack s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec K ack s.uc
          (by omega) (decodedMessageTotal rEk)
        exact seq_freeOnly fineCostModel_modelHyps
          ((h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          dsimp only [StatesProtocolSizes] at hproto
          have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec s.uc.es
            (ct1Len := s.uc.ct1.length) (by omega)
          have h2 := sendCt2Encoder_fine_128_32_phaseCreditSpec
          exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
            (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Acknowledged.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Acknowledged, rawUcCt1Sent, optRaw]
        omega
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec K true s.uc
          (by omega) (decodedMessageTotal rEk)
        exact seq_freeOnly fineCostModel_modelHyps
          ((h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide))
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Tight `PhaseCreditSpec` (`1,647,247 / 0 / 0 / 93,776`) for `StatesRecvProtoEnv' K`. -/
theorem statesRecvProtoEnv'_tight_creditSpec {F : ShaCompress} (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (StatesRecvProtoEnv' K st0 msg)
      statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv'_eq_of_protocolSizes K hproto msg]
    exact statesRecv'_tight_of_protocolSizes_46880_phaseCreditSpec K st0 msg hproto hpts hraw46
  · have heq : StatesRecvProtoEnv' K st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv'; simp [hb]
    rw [heq]
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

private theorem sliceConcat2Events_nonFreeBound (n : Nat) :
    NonFreeBound (· = sliceConcat2Events n) 1 := by
  unfold sliceConcat2Events
  split
  · exact NonFreeBound.nil.mono (by decide)
  · exact NonFreeBound.rustAlloc n 1

private theorem optSecret32Alloc_nonFreeBound :
    NonFreeBound OptSecret32AllocEnv 1 := by
  rintro evs (rfl | rfl)
  · exact (NonFreeBound.nil.mono (by decide)) _ rfl
  · exact NonFreeBound.rustAlloc 32 1 _ rfl

private theorem recvCt2ChunkTail'_nonFreeBound (rootKeyLen ct1Len dkLen : Nat)
    (optCt2 : Option Bytes) :
    NonFreeBound (RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen optCt2) 17 := by
  cases optCt2 with
  | none => exact NonFreeBound.freeOnly.mono (by decide)
  | some ct2Full =>
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact NonFreeBound.freeOnly.mono (by decide)
    · have h1 : NonFreeBound (· = recvCt2AllocMacCt2Events ct2Full.length) 2 := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            NonFreeBound
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
              1 := by
          split
          · exact NonFreeBound.nil.mono (by decide)
          · exact NonFreeBound.rustAlloc (ct2Full.length - 128) 1
        exact (NonFreeBound.append_eq ha (NonFreeBound.rustAlloc 128 1)).mono (by decide)
      by_cases hpan : (ct1Len != 960 || dkLen != 2400) = true
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq NonFreeBound.freeOnly).mono (by decide)
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env ct1Len)
                          (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq
          ((NonFreeBound.rustAlloc 32 1).seq
            ((sliceConcat2Events_nonFreeBound 41).seq
              ((NonFreeBound.rustAlloc 32 1).seq
                ((authUpdate_nonFreeBound rootKeyLen 32).seq
                  ((sendCt2Reserve128_nonFreeBound ct1Len).seq
                    ((sendCt2ConcatHmac_nonFreeBound ct1Len).seq
                      (NonFreeBound.freeOnly.seq
                        (optSecret32Alloc_nonFreeBound.seq NonFreeBound.freeOnly))))))))).mono
          (by decide)

private theorem recvEkChunkSendCt2Tail'_nonFreeBound {F : ShaCompress} (K : MlKem)
    (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (optEk : Option Bytes) :
    NonFreeBound (RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc optEk) 26 := by
  cases optEk with
  | none => exact NonFreeBound.freeOnly.mono (by decide)
  | some ekBytes =>
    by_cases hsd : (!sendCt2OnDone) = true
    · have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd]
      rw [heq]
      exact NonFreeBound.freeOnly.mono (by decide)
    · cases hrek : uc.recv_ek K uc.epoch ekBytes with
      | error _ =>
        have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
          funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek]
        rw [heq]
        exact NonFreeBound.freeOnly.mono (by decide)
      | ok uc1 =>
        cases hsc : uc1.send_ct2 K with
        | error _ =>
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs FreeOnlyEvs := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (NonFreeBound.freeOnly.seq NonFreeBound.freeOnly).mono (by decide)
        | ok val =>
          rcases val with ⟨_, _, _⟩
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs
                (SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
                  (SendCt2EncoderEnv 128 32)) := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (NonFreeBound.freeOnly.seq
            ((unchunkedSendCt2BySizes_nonFreeBound uc1.es uc1.ct1.length).seq
              (sendCt2Encoder_nonFreeBound 128 32))).mono (by decide)

private theorem statesRecv'_tight_nonFreeBound {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    NonFreeBound (StatesRecvEnv' K st msg) 1244 := by
  have hFree : NonFreeBound FreeOnlyEvs 1244 := NonFreeBound.freeOnly.mono (by decide)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      have h1 : NonFreeBound (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) 16 := by
        simpa using addChunkSlots_nonFreeBound (List.replicate 16 SortedSetPt.new)
      exact ((h1.seq (encodeBytes_nonFreeBound s.uc.ek.length)).seq NonFreeBound.freeOnly).mono
        (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ct1.pts) 16 :=
          hproto ▸ addChunkSlots_nonFreeBound s.receiving_ct1.pts
        have hr_pts : (addChunkTotal s.receiving_ct1 chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ct1 chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        exact ((h1.seq h2).seq NonFreeBound.freeOnly).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      have h1 : NonFreeBound (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) 16 := by
        simpa using addChunkSlots_nonFreeBound (List.replicate 16 SortedSetPt.new)
      exact (h1.seq NonFreeBound.freeOnly).mono (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : NonFreeBound (EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk) 1244 := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv'
          split
          · exact NonFreeBound.nil.mono (by decide)
          · dsimp only
            have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ct2.pts) 16 :=
              hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ct2.pts
            have hr_pts : (addChunkTotal s.receiving_ct2 chunk).ptsNeeded ≤ 576 := by
              have := addChunkTotal_ptsNeeded_uncond s.receiving_ct2 chunk; omega
            have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
            have h3 := recvCt2ChunkTail'_nonFreeBound s.uc.auth.rootKey.length s.uc.ct1.length
              s.uc.dk.length (decodedMessageTotal (addChunkTotal s.receiving_ct2 chunk))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact (hbody.seq NonFreeBound.freeOnly).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : NonFreeBound (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) 1244 := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact NonFreeBound.nil.mono (by decide)
          · dsimp only
            have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_hdr.pts) 16 :=
              hproto ▸ addChunkSlots_nonFreeBound s.receiving_hdr.pts
            have hr_pts : (addChunkTotal s.receiving_hdr chunk).ptsNeeded ≤ 576 := by
              have := addChunkTotal_ptsNeeded_uncond s.receiving_hdr chunk; omega
            have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
            have h3 := recvHdrChunkTail_nonFreeBound
              (decodedMessageTotal (addChunkTotal s.receiving_hdr chunk))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact (hbody.seq NonFreeBound.freeOnly).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          NonFreeBound
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (RecvEkChunkSendCt2TailEnv' K ack s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            1244 := fun chunk ack => by
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ek.pts) 16 :=
          hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ek.pts
        have hr_pts : (addChunkTotal s.receiving_ek chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ek chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        have h3 := recvEkChunkSendCt2Tail'_nonFreeBound K ack s.uc
          (decodedMessageTotal (addChunkTotal s.receiving_ek chunk))
        exact ((h1.seq (h2.seq h3)).seq NonFreeBound.freeOnly).mono (by decide)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          exact (((unchunkedSendCt2BySizes_nonFreeBound s.uc.es s.uc.ct1.length).seq
            (sendCt2Encoder_nonFreeBound 128 32)).seq NonFreeBound.freeOnly).mono (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ek.pts) 16 :=
          hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ek.pts
        have hr_pts : (addChunkTotal s.receiving_ek chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ek chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        have h3 := recvEkChunkSendCt2Tail'_nonFreeBound K true s.uc
          (decodedMessageTotal (addChunkTotal s.receiving_ek chunk))
        exact ((h1.seq (h2.seq h3)).seq NonFreeBound.freeOnly).mono (by decide)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Coarse `PhaseGroupSpec` (`statesRecvTightGroupS = 3,732 * FineScale`) for `StatesRecvProtoEnv' K`.
-/
theorem statesRecvProtoEnv'_tight_groupSpec {F : ShaCompress} (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (_hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseGroupSpec fineCostModel (StatesRecvProtoEnv' K st0 msg) statesRecvTightGroupS := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv'_eq_of_protocolSizes K hproto msg]
    exact PhaseGroupSpec.of_nonFreeBound fineCostModel
      (statesRecv'_tight_nonFreeBound K st0 msg hproto hpts)
  · have heq : StatesRecvProtoEnv' K st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv'; simp [hb]
    rw [heq]
    exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

private theorem append_eq_groupSpec
    {a b : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec fineCostModel (· = a) g₁) (h₂ : PhaseGroupSpec fineCostModel (· = b) g₂) :
    PhaseGroupSpec fineCostModel (· = a ++ b) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨a, b, h, rfl, rfl⟩

private theorem seq_freeOnly_right {E : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel E g) :
    PhaseGroupSpec fineCostModel (SeqEnv E FreeOnlyEvs) g :=
  (h.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero g))

private theorem addChunkSlot_fine_phaseGroupSpec (s : SortedSetPt) :
    PhaseGroupSpec fineCostModel (AddChunkSlotEnv s) 140011 := by
  unfold AddChunkSlotEnv
  have hgrow : PhaseGroupSpec fineCostModel (· = growOnePtEvents s.vec.length) 140011 := by
    unfold growOnePtEvents
    split
    · exact rustAlloc_align16_fine_groupSpec (by decide)
    · exact rustRealloc_align16_fine_groupSpec (by decide)
  exact ((PhaseGroupSpec.nil fineCostModel).or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 140011, Nat.le_refl 140011⟩)

private theorem addChunkSlots_fine_phaseGroupSpec :
    ∀ (pts : List SortedSetPt),
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) (140011 * pts.length)
  | [] => (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | s :: rest => by
    dsimp only [AddChunkSlotsEnv]
    have h1 := addChunkSlot_fine_phaseGroupSpec s
    have h2 := addChunkSlots_fine_phaseGroupSpec rest
    refine (h1.seq h2).mono ?_
    rw [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem replicate_flatten_groupSpec {evs0 : List AllocEvent} {g : Nat}
    (h : PhaseGroupSpec fineCostModel (· = evs0) g) :
    ∀ n : Nat, PhaseGroupSpec fineCostModel (· = (List.replicate n evs0).flatten) (n * g)
  | 0 => by simpa using PhaseGroupSpec.nil fineCostModel
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons, Nat.succ_mul]
    exact (append_eq_groupSpec h (replicate_flatten_groupSpec h n)).mono
      (Nat.le_of_eq (Nat.add_comm g (n * g)))

private theorem encodeBytes_160_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 160) 2083248 := by
  have hcond : 160 ≤ 1048576 ∧ 160 % 2 = 0 ∧ 0 < 160 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h160 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 160 2) 130203 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 160) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h160 16).mono (by decide)

private theorem encodeBytes_1152_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 1152) 524288 := by
  have hcond : 1152 ≤ 1048576 ∧ 1152 % 2 = 0 ∧ 0 < 1152 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h1152 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 1152 2) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 1152) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h1152 16).mono (by decide)

private theorem sliceConcat2Events_align16_phaseGroupSpec (n : Nat) :
    PhaseGroupSpec fineCostModel (· = sliceConcat2Events n) 140011 := by
  unfold sliceConcat2Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 140011)
  · exact rustAlloc_align16_fine_groupSpec (by decide)

private theorem libcruxHmacSha256_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = libcruxHmacSha256Events) 121290 := by
  unfold libcruxHmacSha256Events
  have ha64 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 64 1) 34877 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 64) (align := 1)
      (by decide) (by decide)).mono (by decide)
  have hd64 := PhaseGroupSpec.rustDealloc fineCostModel 64 1
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact (append_eq_groupSpec
    (append_eq_groupSpec
      (append_eq_groupSpec
        (append_eq_groupSpec
          (append_eq_groupSpec
            (append_eq_groupSpec ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono (by decide)

private theorem sendCt2Seg23_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (· = sendCt2Seg23Events es) 205547 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
  split
  · have h2080 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 2080 1) 65536 :=
      (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 2080) (align := 1)
        (by decide) (by decide)).mono (by decide)
    have hd2080 := PhaseGroupSpec.rustDealloc fineCostModel 2080 1
    exact (append_eq_groupSpec (append_eq_groupSpec h2080 h128) hd2080).mono (by decide)
  · simpa only [List.nil_append, List.append_nil] using h128.mono (by decide)

private theorem sendCt2Reserve128_fine_phaseGroupSpec (ct1Len : Nat) :
    PhaseGroupSpec fineCostModel (SendCt2Reserve128Env ct1Len) 140011 where
  groups_le b {evs} := by
    rintro (rfl | ⟨cap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2ConcatHmac_960_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = sendCt2ConcatHmacEvents 960) 154058 := by
  unfold sendCt2ConcatHmacEvents
  have hc : PhaseGroupSpec fineCostModel (· = rustAllocEvents (35 + 8 + (960 + 128)) 1) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 35 + 8 + (960 + 128)) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact (append_eq_groupSpec hc libcruxHmacSha256_fine_phaseGroupSpec).mono (by decide)

private theorem unchunkedSendCt2BySizes_960_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (UnchunkedSendCt2BySizesEnv es 960) 499616 := by
  unfold UnchunkedSendCt2BySizesEnv
  have h1 := sendCt2Seg23_fine_phaseGroupSpec es
  have h2 := sendCt2Reserve128_fine_phaseGroupSpec 960
  have h3 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (((h1.concat h2).concat h3).concat h4).mono (by decide)

private theorem sendCt2EncoderGrow_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderGrowEnv 128 32) 140011 where
  groups_le b {evs} := by
    rintro (⟨_, rfl⟩ | ⟨newCap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2Encoder_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderEnv 128 32) 2363270 := by
  unfold SendCt2EncoderEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec 128
  have h2 := sendCt2EncoderGrow_128_32_fine_phaseGroupSpec
  have h3 := encodeBytes_160_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by decide)

private theorem recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec {F : ShaCompress} (K : MlKem)
    (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hct1 : uc.ct1.length = 960) (optEk : Option Bytes) :
    PhaseGroupSpec fineCostModel (RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc optEk) 2862886 := by
  have hFree := PhaseGroupSpec.freeOnly fineCostModel
  cases optEk with
  | none => exact hFree.mono (Nat.zero_le _)
  | some ekBytes =>
    by_cases hsd : (!sendCt2OnDone) = true
    · have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd]
      rw [heq]
      exact hFree.mono (Nat.zero_le _)
    · cases hrek : uc.recv_ek K uc.epoch ekBytes with
      | error _ =>
        have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
          funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek]
        rw [heq]
        exact hFree.mono (Nat.zero_le _)
      | ok uc1 =>
        have hct1' : uc1.ct1.length = 960 := by
          rw [uc_recv_ek_ct1_eq K hrek]
          exact hct1
        cases hsc : uc1.send_ct2 K with
        | error _ =>
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs FreeOnlyEvs := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (hFree.seq hFree).mono (by decide)
        | ok val =>
          rcases val with ⟨_, _, _⟩
          have heq : RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs
                (SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
                  (SendCt2EncoderEnv 128 32)) := by
            funext evs; simp [RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          have h1 : PhaseGroupSpec fineCostModel
              (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length) 499616 := by
            rw [hct1']
            exact unchunkedSendCt2BySizes_960_fine_phaseGroupSpec uc1.es
          exact (hFree.seq (h1.seq sendCt2Encoder_128_32_fine_phaseGroupSpec)).mono (by decide)

private theorem authUpdate_fine_phaseGroupSpec (rootKeyLen kLen : Nat) :
    PhaseGroupSpec fineCostModel (AuthUpdateEnv rootKeyLen kLen) 700055 := by
  unfold AuthUpdateEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec (rootKeyLen + kLen)
  have h2 := sliceConcat2Events_align16_phaseGroupSpec (Authenticator.updateLabel.length + 8)
  have h3 := rustAlloc_align16_fine_groupSpec (sz := 64) (al := 1) (by decide)
  have h4 := rustAlloc_align16_fine_groupSpec (sz := 32) (al := 1) (by decide)
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq (h4.seq (hf.seq (h4.seq hf)))))).mono (by decide)

private theorem optSecret32Alloc_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel OptSecret32AllocEnv 16659 := by
  unfold OptSecret32AllocEnv
  have h32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact ((PhaseGroupSpec.nil fineCostModel).or h32).mono (by decide)

private theorem recvCt2ChunkTail'_960_fine_phaseGroupSpec (rootKeyLen dkLen : Nat)
    (optCt2 : Option Bytes) :
    PhaseGroupSpec fineCostModel (RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen optCt2) 1590815 := by
  have hFree := PhaseGroupSpec.freeOnly fineCostModel
  cases optCt2 with
  | none => exact hFree.mono (Nat.zero_le _)
  | some ct2Full =>
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (Nat.zero_le _)
    · have h1 : PhaseGroupSpec fineCostModel
          (· = recvCt2AllocMacCt2Events ct2Full.length) 280022 := by
        unfold recvCt2AllocMacCt2Events
        have ha : PhaseGroupSpec fineCostModel
            (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
            140011 := by
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact rustAlloc_align16_fine_groupSpec (by decide)
        have hb := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
        exact append_eq_groupSpec ha hb
      by_cases hpan : (dkLen != 2400) = true
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by decide)
      · have heq :
            RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env 960)
                          (SeqEnv (· = sendCt2ConcatHmacEvents 960)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs; simp [RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        have h32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
          (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
            (by decide) (by decide)).mono (by decide)
        have h41 := sliceConcat2Events_align16_phaseGroupSpec 41
        have h5 := authUpdate_fine_phaseGroupSpec rootKeyLen 32
        have h6 := sendCt2Reserve128_fine_phaseGroupSpec 960
        have h7 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
        have hOpt := optSecret32Alloc_fine_phaseGroupSpec
        exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono (by decide)

private theorem statesRecv'_tight_phaseGroupSpec_split {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseGroupSpec fineCostModel (StatesRecvEnv' K st msg) statesRecvTightGroupS_split := by
  have hFree : PhaseGroupSpec fineCostModel FreeOnlyEvs statesRecvTightGroupS_split :=
    (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  have hSlots16 : ∀ (pts : List SortedSetPt), pts.length = 16 →
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) 2240176 := fun pts hlen => by
    have h := addChunkSlots_fine_phaseGroupSpec pts
    rw [hlen] at h
    exact h.mono (by decide)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := hSlots16 (List.replicate 16 SortedSetPt.new) (by simp)
      have h2 : PhaseGroupSpec fineCostModel (EncodeBytesEnv s.uc.ek.length) 524288 := by
        rw [hproto]
        exact encodeBytes_1152_fine_phaseGroupSpec
      exact (seq_freeOnly_right (h1.seq h2)).mono (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hr_pts : (addChunkTotal s.receiving_ct1 chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ct1 chunk; omega
        have h1 := hSlots16 s.receiving_ct1.pts hproto
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        exact (seq_freeOnly_right (h1.seq h2)).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly_right (hSlots16 (List.replicate 16 SortedSetPt.new) (by simp))).mono
        (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hbody : PhaseGroupSpec fineCostModel
            (EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv'
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_ct2 chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_ct2.pts hlen16
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 : PhaseGroupSpec fineCostModel
                (RecvCt2ChunkTailEnv' s.uc.auth.rootKey.length s.uc.ct1.length s.uc.dk.length
                  (decodedMessageTotal rCt2)) 1590815 := by
              rw [hct1]
              exact recvCt2ChunkTail'_960_fine_phaseGroupSpec s.uc.auth.rootKey.length s.uc.dk.length
                (decodedMessageTotal rCt2)
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv']
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : PhaseGroupSpec fineCostModel
            (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_hdr chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_hdr.pts hproto
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 := PhaseGroupSpec.of_nonFreeBound fineCostModel
              (recvHdrChunkTail_nonFreeBound (decodedMessageTotal rHdr))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseGroupSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (RecvEkChunkSendCt2TailEnv' K ack s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightGroupS_split := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 := recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec K ack s.uc hct1
          (decodedMessageTotal rEk)
        exact seq_freeOnly_right ((h1.seq (h2.seq h3)).mono (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          dsimp only [StatesProtocolSizes] at hproto
          have h1 : PhaseGroupSpec fineCostModel
              (UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length) 499616 := by
            rw [hproto]
            exact unchunkedSendCt2BySizes_960_fine_phaseGroupSpec s.uc.es
          exact (seq_freeOnly_right (h1.seq sendCt2Encoder_128_32_fine_phaseGroupSpec)).mono
            (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk),
          PhaseGroupSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (RecvEkChunkSendCt2TailEnv' K true s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightGroupS_split := fun chunk => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 := recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec K true s.uc hct1
          (decodedMessageTotal rEk)
        exact seq_freeOnly_right ((h1.seq (h2.seq h3)).mono (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Split `PhaseGroupSpec` (`statesRecvTightGroupS_split = 27,105,719`) for `StatesRecvProtoEnv' K`.
-/
theorem statesRecvProtoEnv'_tight_split_groupSpec {F : ShaCompress} (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (hpts640 : StatesPtsBoundedAt 640 st0)
    (hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseGroupSpec fineCostModel (StatesRecvProtoEnv' K st0 msg) statesRecvTightGroupS_split := by
  have _ : StatesPtsBoundedAt 640 st0 ∧ rawV1State st0.into_pb ≤ 46880 := ⟨hpts640, hraw46⟩
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv'_eq_of_protocolSizes K hproto msg]
    exact statesRecv'_tight_phaseGroupSpec_split K st0 msg hproto hpts
  · have heq : StatesRecvProtoEnv' K st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv'; simp [hb]
    rw [heq]
    exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

/-! ## Block-`332` Producer and `StatesRecvProtoEnv'` Inclusion -/

private theorem keysSampledArmPre_sub_post {F : ShaCompress}
    (st : KeysSampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    {evs : List AllocEvent} (h : KeysSampledArmPreEnv st msg evs) :
    KeysSampledArmPostEnv st msg evs := by
  unfold KeysSampledArmPreEnv at h
  unfold KeysSampledArmPostEnv
  split at h
  · subst h; simp only [*, ↓reduceIte]; exact FreeOnlyEvs.nil
  · split at h
    · subst h; simp only [*, ↓reduceIte]
    · simp only [*, ↓reduceIte]
      cases hp : msg.payload with
      | ct1 _ => simp only [hp] at h ⊢; exact Or.inl h
      | none | hdr _ | ek _ | ct1Ack _ | ekCt1Ack _ | ct2 _ => simp only [hp] at h ⊢; exact h

private theorem ct1ReceivedArmPre_sub_post {F : ShaCompress}
    (st : Ct1Received spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    {evs : List AllocEvent} (h : Ct1ReceivedArmPreEnv st msg evs) :
    Ct1ReceivedArmPostEnv st msg evs := by
  unfold Ct1ReceivedArmPreEnv at h
  unfold Ct1ReceivedArmPostEnv
  split at h
  · subst h; simp only [*, ↓reduceIte]; exact FreeOnlyEvs.nil
  · split at h
    · subst h; simp only [*, ↓reduceIte]
    · simp only [*, ↓reduceIte]
      cases hp : msg.payload with
      | ct2 _ => simp only [hp] at h ⊢; exact Or.inl h
      | none | hdr _ | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ => simp only [hp] at h ⊢; exact h

/-- Assembled Block-`332` `StatesRecvPlacedOkXOfEnv` contract over `StatesRecvExactTightEnv K`. -/
theorem states_recv_placed_ok_x_exactTight [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts M A lim F K ext) :
    StatesRecvPlacedOkXOfEnv M A lim F K ext (StatesRecvExactTightEnv K) := by
  apply states_recv_placed_ok_x_of_ext_ofEnv
  apply states_recv_placed_ok_ext_of_variants_ofEnv
  intro st msg
  cases st with
  | keysUnsampled s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_keysUnsampled_placed_ok_cro_ext_ofPrePostEnv M A lim F K
        (StatesRecvExactTightEnv K) ext hC s msg)
  | keysSampled s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (PreEnv₁ := fun _ => KeysSampledArmPreEnv s msg)
      (PostEnv₁ := fun _ => KeysSampledArmPostEnv s msg)
      (fun _ _ _ _ hF => FitsEnv.mono (fun _ h => keysSampledArmPre_sub_post s msg h) hF)
      (fun _ _ _ _ h => h)
      (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_keysSampled_exact_placed_ok_ext M A lim F K ext hC s msg))
  | headerSent s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_headerSent_env_placed_ok_ext M A lim F K ext hC s msg)
  | ct1Received s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (PreEnv₁ := fun _ => Ct1ReceivedArmPreEnv s msg)
      (PostEnv₁ := fun _ => Ct1ReceivedArmPostEnv s msg)
      (fun _ _ _ _ hF => FitsEnv.mono (fun _ h => ct1ReceivedArmPre_sub_post s msg h) hF)
      (fun _ _ _ _ h => h)
      (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (states_recv_ct1Received_exact_placed_ok_ext M A lim F K ext hC s msg))
  | ekSentCt1Received s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_ekSentCt1Received_placed_ok_ext M A lim F K ext hC s msg)
  | noHeaderReceived s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_noHeaderReceived_placed_ok_ext M A lim F K ext hC s msg)
  | headerReceived s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_headerReceived_placed_ok_cro_ext_ofPrePostEnv M A lim F K
        (StatesRecvExactTightEnv K) ext hC s msg)
  | ct1Sampled s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_ct1Sampled_placed_ok_ext M A lim F K ext hC s msg)
  | ekReceivedCt1Sampled s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_ekReceivedCt1Sampled_placed_ofEnv_cro_ok_ext A lim F K ext hC s msg)
  | ct1Acknowledged s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_ct1Acknowledged_placed_ofEnv_ok_ext A lim F K ext hC s msg)
  | ct2Sampled s =>
    exact subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (states_recv_ct2Sampled_placed_ok_cro_ext_ofPrePostEnv M A lim F K
        (StatesRecvExactTightEnv K) ext hC s msg)

private theorem w2pb_seqEnv_mono {P P' Q Q' : List AllocEvent → Prop} {evs : List AllocEvent}
    (hP : ∀ e, P e → P' e) (hQ : ∀ e, Q e → Q' e) (h : SeqEnv P Q evs) :
    SeqEnv P' Q' evs := by
  rcases h with hp | ⟨e1, e2, rfl, hp, hq⟩
  · exact Or.inl (hP evs hp)
  · exact Or.inr ⟨e1, e2, rfl, hP e1 hp, hQ e2 hq⟩

private theorem w2pb_seqEnv_split_append {a b : List AllocEvent} {R : List AllocEvent → Prop}
    {evs : List AllocEvent} (h : SeqEnv (· = a ++ b) R evs) :
    SeqEnv (· = a) (SeqEnv (· = b) R) evs := by
  rcases h with rfl | ⟨e1, e2, rfl, rfl, hr⟩
  · exact Or.inr ⟨a, b, rfl, rfl, Or.inl rfl⟩
  · exact Or.inr ⟨a, b ++ e2, List.append_assoc a b e2, rfl, Or.inr ⟨b, e2, rfl, rfl, hr⟩⟩

private theorem w2pb_authUpdateTail_append_free {e f : List AllocEvent}
    (he : SeqEnv FreeOnlyEvs (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs) e)
    (hf : FreeOnlyEvs f) :
    SeqEnv FreeOnlyEvs (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs) (e ++ f) := by
  rcases he with hf1 | ⟨f1, e2, rfl, hf1, rfl | ⟨_, f0, rfl, rfl, hf0⟩⟩
  · exact Or.inl (FreeOnlyEvs.append hf1 hf)
  · exact Or.inr ⟨f1, rustAllocEvents 32 1 ++ f, List.append_assoc .., hf1,
      Or.inr ⟨_, f, rfl, rfl, hf⟩⟩
  · exact Or.inr ⟨f1, rustAllocEvents 32 1 ++ (f0 ++ f), by simp [List.append_assoc], hf1,
      Or.inr ⟨_, f0 ++ f, rfl, rfl, FreeOnlyEvs.append hf0 hf⟩⟩

private theorem w2pb_authUpdateLenEnv_sub (rkLen : Nat) {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.AuthUpdateLenEnv rkLen 32 evs) :
    AuthUpdateEnv rkLen 32 evs := by
  have hpre :
      SeqEnv (LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.AuthUpdatePreAlloc1Env rkLen 32)
        (SeqEnv FreeOnlyEvs (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs)) evs := by
    rcases h with h123 | ⟨e123, f2, rfl, h123, hf2⟩
    · rcases h123 with (hp | ⟨e1, f1, rfl, hp, hf1⟩) | ⟨e12, e3, rfl, hp | ⟨e1, f1, rfl, hp, hf1⟩, ha2⟩
      · exact Or.inl hp
      · exact Or.inr ⟨e1, f1, rfl, hp, Or.inl hf1⟩
      · exact Or.inr ⟨e12, e3, rfl, hp, Or.inr ⟨[], e3, rfl, FreeOnlyEvs.nil, Or.inl ha2⟩⟩
      · exact Or.inr ⟨e1, f1 ++ e3, List.append_assoc .., hp,
          Or.inr ⟨f1, e3, rfl, hf1, Or.inl ha2⟩⟩
    · rcases h123 with (hp | ⟨e1, f1, rfl, hp, hf1⟩) | ⟨e12, e3, rfl, hp | ⟨e1, f1, rfl, hp, hf1⟩, ha2⟩
      · exact Or.inr ⟨e123, f2, rfl, hp, Or.inl hf2⟩
      · exact Or.inr ⟨e1, f1 ++ f2, List.append_assoc .., hp, Or.inl (FreeOnlyEvs.append hf1 hf2)⟩
      · exact Or.inr ⟨e12, e3 ++ f2, List.append_assoc .., hp,
          w2pb_authUpdateTail_append_free (Or.inr ⟨[], e3, rfl, FreeOnlyEvs.nil, Or.inl ha2⟩) hf2⟩
      · exact Or.inr ⟨e1, (f1 ++ e3) ++ f2, by simp [List.append_assoc], hp,
          w2pb_authUpdateTail_append_free (Or.inr ⟨f1, e3, rfl, hf1, Or.inl ha2⟩) hf2⟩
  have hlbl :
      sliceConcat2Events (CryptoVerification.LibsignalSpqrV1.Authenticator.updateLabel.length + 8) =
        rustAllocEvents 53 1 := by decide
  unfold AuthUpdateEnv
  rw [hlbl]
  unfold LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.AuthUpdatePreAlloc1Env at hpre
  exact w2pb_seqEnv_split_append (w2pb_seqEnv_split_append (w2pb_seqEnv_split_append hpre))

private theorem w2pb_recvCt2Reserve_sub {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.RecvCt2ReserveCt1Env evs) :
    SendCt2Reserve128Env 960 evs := by
  rcases h with rfl | ⟨c, hlo, hhi, rfl⟩
  · exact Or.inl rfl
  · have hc : (BitVec.ofNat 64 c).toNat = c := Nat.mod_eq_of_lt (by omega)
    have hne : BitVec.ofNat 64 c ≠ 0#64 := by
      intro h0
      have h0n : (BitVec.ofNat 64 c).toNat = 0 := congrArg BitVec.toNat h0
      omega
    refine Or.inr ⟨BitVec.ofNat 64 c, by omega, by omega, ?_⟩
    unfold LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget.sendCt2Reserve128Events
    rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 hne), hc]

private theorem w2pb_recvCt2MacCt2_eq {n : Nat} (hn : 128 ≤ n) :
    LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2MacCt2AllocEvents n =
      recvCt2AllocMacCt2Events n := by
  unfold LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2MacCt2AllocEvents
    recvCt2AllocMacCt2Events
  by_cases heq : n = 128
  · subst heq; rfl
  · have hle : ¬ (n ≤ 128) := by omega
    simp only [hle, heq, ↓reduceIte]

private theorem w2pb_recvCt2TailEnv_sub (rkLen ct1Len dkLen : Nat) (optCt2 : Option Bytes)
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.RecvCt2TailEnv
      rkLen ct1Len dkLen optCt2 evs) :
    RecvCt2ChunkTailEnv' rkLen ct1Len dkLen optCt2 evs := by
  cases optCt2 with
  | none =>
    subst h
    exact FreeOnlyEvs.nil
  | some ct2Full =>
    dsimp only [LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.RecvCt2TailEnv,
      RecvCt2ChunkTailEnv'] at h ⊢
    by_cases hlt : ct2Full.length < 128
    · simp only [hlt, ↓reduceIte] at h ⊢
      subst h
      exact FreeOnlyEvs.nil
    · simp only [hlt, ↓reduceIte] at h ⊢
      have hge128 : 128 ≤ ct2Full.length := Nat.le_of_not_lt hlt
      by_cases hbad : (ct1Len != 960 || dkLen != 2400) = true
      · simp only [hbad, ↓reduceIte] at h ⊢
        rw [w2pb_recvCt2MacCt2_eq hge128] at h
        exact Or.inl h
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have hct1 : ct1Len = 960 := by
          cases hc : ct1Len == 960
          · simp [bne, hc] at hbad
          · exact beq_iff_eq.mp hc
        subst hct1
        unfold LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.RecvCt2PostDecapsEnv at h
        have hpre_eq :
            LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2MacCt2AllocEvents
                ct2Full.length ++
              LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2PreAuthUpdateEvents =
              ((recvCt2AllocMacCt2Events ct2Full.length ++ rustAllocEvents 32 1) ++
                sliceConcat2Events 41) ++ rustAllocEvents 32 1 := by
          rw [w2pb_recvCt2MacCt2_eq hge128]
          unfold LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2PreAuthUpdateEvents
          simp only [List.append_assoc]
        have hhmac_eq :
            LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.recvCt2HmacEvents =
              sendCt2ConcatHmacEvents 960 := by decide
        have h' :
            SeqEnv
              (· = ((recvCt2AllocMacCt2Events ct2Full.length ++ rustAllocEvents 32 1) ++
                sliceConcat2Events 41) ++ rustAllocEvents 32 1)
              (SeqEnv (AuthUpdateEnv rkLen 32)
                (SeqEnv (SendCt2Reserve128Env 960)
                  (SeqEnv (· = sendCt2ConcatHmacEvents 960)
                    (SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs))))) evs := by
          refine w2pb_seqEnv_mono (fun _ he => hpre_eq ▸ he) (fun _ hrest => ?_) h
          refine w2pb_seqEnv_mono (fun _ => w2pb_authUpdateLenEnv_sub rkLen) (fun _ hrest2 => ?_) hrest
          refine w2pb_seqEnv_mono (fun _ => w2pb_recvCt2Reserve_sub) (fun _ hrest3 => ?_) hrest2
          exact w2pb_seqEnv_mono (fun _ he => hhmac_eq ▸ he) (fun _ he => he) hrest3
        exact w2pb_seqEnv_split_append (w2pb_seqEnv_split_append (w2pb_seqEnv_split_append h'))

private theorem w2pb_ite_pos {α : Sort _} {c : Prop} [Decidable c] (hc : c) (t e : α) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

private theorem w2pb_ite_neg {α : Sort _} {c : Prop} [Decidable c] (hc : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

private theorem w2pb_of_ite_pos {c : Prop} [Decidable c] {P Q : Prop}
    (hc : c) (h : if c then P else Q) : P := by
  split at h <;> [exact h; contradiction]

private theorem w2pb_of_ite_neg {c : Prop} [Decidable c] {P Q : Prop}
    (hc : ¬ c) (h : if c then P else Q) : Q := by
  split at h <;> [contradiction; exact h]

private theorem w2pb_sendCt2_out_lengths {F : ShaCompress} {K : MlKem}
    {st : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    {outUc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F)}
    {ct2 mac : Bytes}
    (h : st.send_ct2 K = .ok (outUc, ct2, mac)) :
    ct2.length = 128 ∧ mac.length = 32 := by
  obtain ⟨henc, hmac, -⟩ := CryptoVerification.SpqrV1.Unchunked.send_ct2_ok_elim h
  obtain ⟨-, -, esVec, ekVec, -, -, rfl⟩ := CryptoVerification.SpqrV1.Unchunked.encaps2_ok_elim henc
  obtain ⟨-, -, rfl⟩ := CryptoVerification.SpqrV1.Unchunked.macCt_ok_elim hmac
  refine ⟨(K.encaps2 esVec ekVec).2, ?_⟩
  let auth0 : CryptoVerification.LibsignalSpqrV1.Authenticator := st.auth
  change (auth0.macCtUnchecked F st.epoch (st.ct1 ++ (K.encaps2 esVec ekVec).toList)).length = 32
  rw [CryptoVerification.SpqrV1.Unchunked.macCtUnchecked_eq_hmacWith]
  exact CryptoVerification.LibsignalSpqrV1.length_hmacWith F auth0.macKey _

private theorem w2pb_sendCt2EncoderPre_sub {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.SendCt2EncoderBytesPreEnv
      128 32 evs) :
    SendCt2EncoderEnv 128 32 evs := by
  unfold LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.SendCt2EncoderBytesPreEnv at h
  have hc :
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.sendCt2EncoderConcatEvents
          128 32 =
        sliceConcat2Events 128 ++
          LibsignalBinary.Heap.rustReallocEvents 128
            (CryptoVerification.LibsignalTripleRatchet.reserveCap 128 128 32) 1 := by decide
  rw [hc] at h
  have h1 := w2pb_seqEnv_split_append h
  refine w2pb_seqEnv_mono (fun _ he => he) (fun _ hrest => ?_) h1
  refine w2pb_seqEnv_mono (fun _ he => ?_) (fun _ he => Or.inl he) hrest
  subst he
  exact Or.inr ⟨CryptoVerification.LibsignalTripleRatchet.reserveCap 128 128 32,
    by decide, by decide, rfl⟩

private theorem w2pb_ct1AckTailPre_sub {F : ShaCompress} (K : MlKem)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (optEk : Option Bytes) {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.Ct1AckRecvEkTailPreEnv
      K uc optEk evs) :
    RecvEkChunkSendCt2TailEnv' K true uc optEk evs := by
  cases optEk with
  | none =>
    subst h
    exact FreeOnlyEvs.nil
  | some ekBytes =>
    dsimp only [
      LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.Ct1AckRecvEkTailPreEnv,
      RecvEkChunkSendCt2TailEnv'] at h ⊢
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hrek : uc.recv_ek K uc.epoch ekBytes with
    | error _ =>
      rw [hrek] at h
      subst h
      exact FreeOnlyEvs.nil
    | ok uc1 =>
      rw [hrek] at h
      refine w2pb_seqEnv_mono (fun _ hf => hf) (fun _ hsc => ?_) h
      cases hs : uc1.send_ct2 K with
      | error _ =>
        rw [hs] at hsc
        subst hsc
        exact FreeOnlyEvs.nil
      | ok val =>
        rcases val with ⟨outUc, ct2, mac⟩
        rw [hs] at hsc
        obtain ⟨hct2, hmac⟩ := w2pb_sendCt2_out_lengths hs
        refine w2pb_seqEnv_mono
          (fun e he => (SpqrStatesRecvPeakSpec.unchunkedSendCt2Env_iff_bySizes
            ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩ e).mp he)
          (fun _ he => w2pb_sendCt2EncoderPre_sub (hct2 ▸ hmac ▸ he))
          hsc

section PassBInclusion

attribute [local irreducible] addChunkTotal decodedMessageTotal DecodedMessageEnv

/-- Every Block-`332` arm trace in `StatesRecvExactTightEnv K` lies in `StatesRecvEnv' K`. -/
theorem statesRecvExactTightEnv_sub_statesRecvEnv' {F : ShaCompress} (K : MlKem)
    (x : StatesRecvGhost F) {evs : List AllocEvent}
    (h : StatesRecvExactTightEnv K x evs) :
    StatesRecvEnv' K x.self x.msg evs := by
  rcases x with ⟨outA, selfA, msgA, self, ⟨epoch, payload⟩⟩
  dsimp only [StatesRecvExactTightEnv] at h ⊢
  cases self with
  | keysUnsampled st =>
    exact LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget.KeysUnsampledRecvPostEnv_to_freeOnly h
  | keysSampled st =>
    dsimp only [StatesRecvEnv', KeysSampledArmPostEnv] at h ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      rw [w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _),
          w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _)] at h
      cases payload <;> dsimp only at h ⊢ <;> first | exact h | (subst h; exact FreeOnlyEvs.nil)
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      split at h
      · exact h
      · split at h
        · subst h; exact FreeOnlyEvs.nil
        · exfalso; bv_omega
  | headerSent st =>
    dsimp only [StatesRecvEnv', HeaderSentArmEnv,
      LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux.HeaderSentArmPostEnv] at h ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      rw [w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _),
          w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _)] at h
      cases payload <;> dsimp only at h ⊢ <;> first | exact h | (subst h; exact FreeOnlyEvs.nil)
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      split at h
      · exact h
      · split at h
        · subst h; exact FreeOnlyEvs.nil
        · exfalso; bv_omega
  | ct1Received st =>
    dsimp only [StatesRecvEnv', Ct1ReceivedArmPostEnv] at h ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      rw [w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _),
          w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _)] at h
      cases payload <;> dsimp only at h ⊢ <;> first | exact h | (subst h; exact FreeOnlyEvs.nil)
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      split at h
      · exact h
      · split at h
        · subst h; exact FreeOnlyEvs.nil
        · exfalso; bv_omega
  | ekSentCt1Received st =>
    have h1 :=
      LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudget.statesRecvEkSentCt1ReceivedEnv_imp_seq_or_freeOnly h
    dsimp only [StatesRecvEnv'] at h1 ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · rw [w2pb_ite_pos heq_b] at h1 ⊢
      cases payload with
      | ct2 chunk =>
        dsimp only at h1 ⊢
        refine w2pb_seqEnv_mono (fun _ hc => ?_) (fun _ hf => hf) h1
        unfold LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget.RecvCt2ChunkEnv at hc
        unfold EkSentCt1ReceivedRecvCt2ChunkEnv'
        dsimp only at hc
        by_cases hbne : (epoch != st.uc.epoch) = true
        · rw [w2pb_ite_pos hbne] at hc ⊢
          exact hc
        · rw [w2pb_ite_neg hbne] at hc ⊢
          exact w2pb_seqEnv_mono (fun _ ha => ha)
            (fun _ hd => w2pb_seqEnv_mono (fun _ hm => hm)
              (fun _ ht => w2pb_recvCt2TailEnv_sub _ _ _ _ ht) hd) hc
      | none | hdr _ | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ =>
        exact h1
    · rw [w2pb_ite_neg heq_b] at h1 ⊢
      exact h1
  | noHeaderReceived st =>
    have h1 :=
      LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2PlacedBudget.statesRecvNoHeaderReceivedEnv_imp_seq_or_freeOnly h
    dsimp only [StatesRecvEnv'] at h1 ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · rw [w2pb_ite_pos heq_b] at h1 ⊢
      cases payload <;> exact h1
    · rw [w2pb_ite_neg heq_b] at h1 ⊢
      exact h1
  | headerReceived st =>
    exact LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget.HeaderReceivedRecvPostEnv_to_freeOnly h
  | ct1Sampled st =>
    dsimp only [StatesRecvEnv']
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      cases payload with
      | ek chunk =>
        dsimp only
        refine w2pb_seqEnv_mono (fun _ hpre => ?_) (fun _ hf => hf) h
        unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
        dsimp only at hpre
        have hpre' := w2pb_of_ite_pos heq hpre
        exact w2pb_seqEnv_mono (fun _ ha => ha) (fun _ hd => Or.inl hd) hpre'
      | ekCt1Ack chunk =>
        dsimp only
        refine w2pb_seqEnv_mono (fun _ hpre => ?_) (fun _ hf => hf) h
        unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
        dsimp only at hpre
        have hpre' := w2pb_of_ite_pos heq hpre
        exact w2pb_seqEnv_mono (fun _ ha => ha)
          (fun _ hd => w2pb_seqEnv_mono (fun _ hm => hm)
            (fun _ ht => w2pb_ct1AckTailPre_sub K st.uc _ ht) hd) hpre'
      | none | hdr _ | ct1 _ | ct1Ack _ | ct2 _ =>
        dsimp only
        rcases h with hpre | ⟨e1, e2, rfl, hpre, hf⟩
        · unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
          dsimp only at hpre
          have h0 : evs = [] := w2pb_of_ite_pos heq hpre
          exact h0 ▸ FreeOnlyEvs.nil
        · unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
          dsimp only at hpre
          have h0 : e1 = [] := w2pb_of_ite_pos heq hpre
          subst h0
          exact hf
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      rcases h with hpre | ⟨e1, e2, rfl, hpre, hf⟩
      · unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
        dsimp only at hpre
        have h0 : evs = [] := w2pb_of_ite_neg hne hpre
        exact h0 ▸ FreeOnlyEvs.nil
      · unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux.Ct1SampledRecvPreEnv at hpre
        dsimp only at hpre
        have h0 : e1 = [] := w2pb_of_ite_neg hne hpre
        subst h0
        exact hf
  | ekReceivedCt1Sampled st =>
    dsimp only [StatesRecvEnv', StatesRecvEkReceivedCt1SampledEnv,
      LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget.StatesRecvEkReceivedCt1SampledPostEnv] at h ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      rw [w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _)] at h
      have hack_eq :
          LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget.isEkAckPayload payload =
            isEkReceivedCt1AckMsg ⟨epoch, payload⟩ := by
        cases payload <;> first | (rename_i b; cases b <;> rfl) | rfl
      by_cases hack : isEkReceivedCt1AckMsg ⟨epoch, payload⟩ = true
      · rw [w2pb_ite_pos hack]
        rw [w2pb_ite_pos ⟨heq, hack_eq.trans hack⟩] at h
        unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget.EkReceivedCt1SampledAckPostEnv
          LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlacedBudget.EkReceivedCt1SampledAckPreEnv at h
        cases hs : st.uc.send_ct2 K with
        | error _ =>
          rw [hs] at h
          rcases h with rfl | ⟨_, _, rfl, rfl, hf⟩
          · exact FreeOnlyEvs.nil
          · exact hf
        | ok val =>
          rcases val with ⟨outUc, ct2, mac⟩
          rw [hs] at h
          obtain ⟨hct2, hmac⟩ := w2pb_sendCt2_out_lengths hs
          refine w2pb_seqEnv_mono (fun _ hpre => ?_) (fun _ hf => hf) h
          exact w2pb_seqEnv_mono
            (fun e he => (SpqrStatesRecvPeakSpec.unchunkedSendCt2Env_iff_bySizes
              ⟨0#64, 0#64, st.uc, outUc, ct2, mac⟩ e).mp he)
            (fun _ he => w2pb_sendCt2EncoderPre_sub (hct2 ▸ hmac ▸ he))
            hpre
      · rw [w2pb_ite_neg hack]
        rw [w2pb_ite_neg (fun ⟨_, h2⟩ => hack (hack_eq.symm.trans h2))] at h
        subst h
        exact FreeOnlyEvs.nil
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      by_cases hgt : epoch > st.uc.epoch
      · rw [w2pb_ite_pos hgt] at h
        exact h
      · rw [w2pb_ite_neg hgt, w2pb_ite_neg (fun ⟨h1, _⟩ => hne h1)] at h
        subst h
        exact FreeOnlyEvs.nil
  | ct1Acknowledged st =>
    dsimp only [StatesRecvEnv', StatesRecvCt1AcknowledgedEnv,
      LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.StatesRecvCt1AcknowledgedPostEnv] at h ⊢
    by_cases heq_b : (epoch == st.uc.epoch) = true
    · have heq : epoch = st.uc.epoch := beq_iff_eq.mp heq_b
      rw [w2pb_ite_pos heq_b]
      rw [w2pb_ite_neg (by rw [heq]; exact BitVec.lt_irrefl _), w2pb_ite_pos heq] at h
      cases payload with
      | ek chunk =>
        dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk?] at h ⊢
        unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPostEnv
          LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPreEnv at h
        refine w2pb_seqEnv_mono (fun _ hpre => ?_) (fun _ hf => hf) h
        exact w2pb_seqEnv_mono (fun _ ha => ha)
          (fun _ hd => w2pb_seqEnv_mono (fun _ hm => hm)
            (fun _ ht => w2pb_ct1AckTailPre_sub K st.uc _ ht) hd) hpre
      | ekCt1Ack chunk =>
        dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk?] at h ⊢
        unfold LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPostEnv
          LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.Ct1AcknowledgedChunkPreEnv at h
        refine w2pb_seqEnv_mono (fun _ hpre => ?_) (fun _ hf => hf) h
        exact w2pb_seqEnv_mono (fun _ ha => ha)
          (fun _ hd => w2pb_seqEnv_mono (fun _ hm => hm)
            (fun _ ht => w2pb_ct1AckTailPre_sub K st.uc _ ht) hd) hpre
      | none | hdr _ | ct1 _ | ct1Ack _ | ct2 _ =>
        dsimp only [LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3PlacedBudgetAux.ct1AckPayloadChunk?] at h ⊢
        subst h
        exact FreeOnlyEvs.nil
    · have hne : epoch ≠ st.uc.epoch := fun heq => heq_b (beq_iff_eq.mpr heq)
      rw [w2pb_ite_neg heq_b]
      by_cases hgt : epoch > st.uc.epoch
      · rw [w2pb_ite_pos hgt] at h
        exact h
      · rw [w2pb_ite_neg hgt, w2pb_ite_neg hne] at h
        subst h
        exact FreeOnlyEvs.nil
  | ct2Sampled st =>
    exact LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3PlacedBudget.Ct2SampledRecvPostEnv_to_freeOnly h

end PassBInclusion

/-- Under `States.from_pb`, every trace in `StatesRecvExactTightEnv K` lies in `StatesRecvProtoEnv' K`.
-/
theorem statesRecvExactTightEnv_sub_statesRecvProtoEnv' {F : ShaCompress} (K : MlKem)
    {pb : V1State} (x : StatesRecvGhost F) {evs : List AllocEvent}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok x.self)
    (h : StatesRecvExactTightEnv K x evs) :
    StatesRecvProtoEnv' K x.self x.msg evs := by
  rw [statesRecvProtoEnv'_eq_of_from_pb K hfrom x.msg]
  exact statesRecvExactTightEnv_sub_statesRecvEnv' K x h

end LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
