/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget

/-!
# Guarded-Tight `W1` (`encrypt`) and `W2` (`decryptSignal`) Exact Slot Specs

**Checked by Lean.**

Defines the `PeerSpqrStateTight640`-guarded `@109` binary-kit slot envelopes
`ckx2_cliEncryptBinaryKitSlotEnvExact` and `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`, their
curried `PhaseCreditSpec` and `PhaseGroupSpec` obligations, and the bundled `SingleSlotFineSpec`
and whole-`main` `FitsEnv` consumers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ChainKey Crypto Mut PublicKey RatchetState ShaCompress TripleRatchet)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk Epoch Message MlKem PqRatchetState SortedSetPt States V1Recv V1State
   VersionNegotiationPB spqrAuthApi spqrDecodeState spqrPolyApi spqrV1)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliRunBudgets parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecSigGhost EncGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget (SendPhase3EnvOfEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
  (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_curried w1EncExactCum w1EncExactGrpS
   w1EncExactLive w1EncExactMaxReq w1EncExactPeak w2DecSigExactCum w2DecSigExactGrpS
   w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak w4DecPkExactCum w4DecPkExactGrpS
   w4DecPkExactLive w4DecPkExactMaxReq w4DecPkExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (tryDecryptCmkSeg4Env tryDecryptCmkStepEnv tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
  (realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
   w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
  (AuthUpdateEnv NoHeaderReceivedRecvHdrChunkBodyEnv SendCt2EncoderEnv UnchunkedSendCt2BySizesEnv
   isEkReceivedCt1AckMsg isStatesProtoSized recvCt2AllocMacCt2Events)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkSlotsEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (EncodeBytesEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget (OptSecret32AllocEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (MessageSerializeEnv)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env sendCt2ConcatHmacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (FromS2GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## `@109` Guarded-Tight `W1` and `W2` Slot Envelope Definitions -/

/-- `spqr::decode_state` tight leaf parameterized by `maxOps`. -/
def ckx2_DecodeStateTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 1307216 79236

/-- `@109` `spqr::decode_state` tight leaf (`maxOps = 109`). -/
abbrev ckx2_DecodeStateTightEnv : List AllocEvent → Prop :=
  ckx2_DecodeStateTightEnvOf 109

/-- Leaf-parametric `spqr::send::<Coins>` byte-slice allocation envelope. -/
def ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv (F : ShaCompress) (K : MlKem)
    (DecBytesEnv : List (BitVec 8) → List AllocEvent → Prop)
    (FromPbValEnv : V1State → List AllocEvent → Prop) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    let decEnv : List AllocEvent → Prop := DecBytesEnv stBs
    let fpbEnv (v1 : V1State) : List AllocEvent → Prop := FromPbValEnv v1
    match spqrDecodeState stBs with
    | .error _ => decEnv evs
    | .ok pq =>
      match pq.inner with
      | none => SeqEnv decEnv FreeOnlyEvs evs
      | some (.v1 v1) =>
        SeqEnv decEnv
          (match States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
           | .error (.panic _) => fpbEnv v1
           | .error (.err _) => SeqEnv (fpbEnv v1) FreeOnlyEvs
           | .ok st_states =>
             SeqEnv (fpbEnv v1)
               (SeqEnv (StatesSendTightEnv F K st_states rest)
                 (match st_states.send K rest with
                  | .ok (sOut, _) =>
                    SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv
                      0#64 pq sOut
                  | .error (.err _) => FreeOnlyEvs
                  | .error (.panic _) => HeaderReceived1aEnv)))
          evs

/-- `PeerSpqrStateTight640`-guarded `@109` `W1` (`encrypt`) binary-kit slot envelope.
When `¬ PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`, the predicate is `True`; outer
`MainOk` consumers discharge `PeerSpqrStateTight640` from `CliPqxdhInputs`. -/
noncomputable def ckx2_cliEncryptBinaryKitSlotEnvExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets) :
    EncGhost → List AllocEvent → Prop :=
  let sendEnv : SpqrSendBudgetEnv :=
    ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv W.C.F W.Q.K
      (fun _ => ckx2_DecodeStateTightEnv)
      (fun _ => StatesFromPbTightEnv)
  fun x evs =>
    PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

/-- Post-`decoded_message` tail envelope for `<EkSentCt1Received>::recv_ct2_chunk`. -/
def ckx2_RecvCt2ChunkTailEnv' (rootKeyLen ct1Len dkLen : Nat) :
    Option Bytes → List AllocEvent → Prop
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

/-- Pre-state-pinned allocation envelope for `<EkSentCt1Received>::recv_ct2_chunk`. -/
def ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' {F : ShaCompress}
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (epoch : Epoch) (chunk : Chunk)
    (evs : List AllocEvent) : Prop :=
  if epoch != s.uc.epoch then
    evs = []
  else
    let receivingCt2 := addChunkTotal s.receiving_ct2 chunk
    SeqEnv (AddChunkSlotsEnv s.receiving_ct2.pts)
      (SeqEnv (DecodedMessageEnv receivingCt2)
        (ckx2_RecvCt2ChunkTailEnv' s.uc.auth.rootKey.length s.uc.ct1.length s.uc.dk.length
          (decodedMessageTotal receivingCt2)))
      evs

/-- Post-`decoded_message` tail envelope for `<Ct1Sampled>::recv_ek_chunk` and
`<Ct1Acknowledged>::recv_ek_chunk`. -/
def ckx2_RecvEkChunkSendCt2TailEnv' {F : ShaCompress} (K : MlKem) (sendCt2OnDone : Bool)
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

/-- 11-constructor pre-state-pinned allocation envelope for `<States>::recv`. -/
def ckx2_StatesRecvEnv' {F : ShaCompress} (K : MlKem)
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
        SeqEnv (ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk) FreeOnlyEvs
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
              (ckx2_RecvEkChunkSendCt2TailEnv' K ack s.uc
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
              (ckx2_RecvEkChunkSendCt2TailEnv' K true s.uc
                (decodedMessageTotal receivingEk))))
          FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct2Sampled _ => FreeOnlyEvs

/-- Protocol-sized wrapper around `ckx2_StatesRecvEnv' K`. -/
def ckx2_StatesRecvProtoEnv' {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  if isStatesProtoSized st then ckx2_StatesRecvEnv' K st msg else FreeOnlyEvs

/-- `(maxOps, RecvProtoEnv)`-parametric linked `spqr::recv` allocation envelope. -/
def ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvTightLinkedEnv F K
    (fun _ => ckx2_DecodeStateTightEnvOf maxOps)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    RecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- `maxOps`-parametric linked `spqr::recv` allocation envelope at `ckx2_StatesRecvProtoEnv' K`. -/
def ckx2_SpqrRecvC07C09aTightLinkedEnvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf maxOps F K (ckx2_StatesRecvProtoEnv' K)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Existentially lifted `maxOps`-parametric linked `spqr::recv` byte-slice envelope. -/
def ckx2_SpqrRecvC07C09aBytesEnvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    ckx2_SpqrRecvC07C09aTightLinkedEnvOf maxOps F K
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Loop-envelope-parametric Segment-4 `consume_message_key` step envelope. -/
def ckx2_tryDecryptCmkStepEnvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) (evs : List AllocEvent) : Prop :=
  if msgCounter < ck.index then
    FreeOnlyEvs evs
  else if (msgCounter - ck.index).toNat ≤ r.maxForwardJumps then
    match r.findReceiverChainIndex senderRatchetKey with
    | none =>
      if ck.index < msgCounter then
        evs = [] ∨ evs = rustAllocEvents 32 1
      else
        evs = []
    | some ci =>
      let cap0 := (trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64
      let len0 := (r.receiverChains[ci]?.map (·.messageKeys.length)).getD 0
      LoopAdvEnv (msgCounter - ck.index).toNat cap0 len0
        (msgCounter == BitVec.allOnes 32) evs
  else
    evs = rustAllocEvents 36 1

/-- Loop-envelope-parametric Segment-4 (`ConsumeMsgKey`) allocation envelope. -/
def ckx2_tryDecryptCmkSeg4EnvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) : List AllocEvent → Prop :=
  SeqEnv fmtWriteEnv
    (SeqEnv (ckx2_tryDecryptCmkStepEnvOf LoopAdvEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck)
      FreeOnlyEvs)

/-- `try_decrypt_with_state` CLI allocation envelope parameterized by `LoopAdvEnv` and `maxOps`. -/
def ckx2_TryDecryptCliLinkedLoopEnvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (maxOps : Nat) (C : Crypto) (K : MlKem)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  let S := spqrV1 C.F K
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (ckx2_tryDecryptCmkSeg4EnvOf LoopAdvEnv FmtWriteEnv)
        (PqRecvEnv S (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- `try_decrypt_with_state` CLI allocation envelope at `CmkLoopAdvanceEvs` and `maxOps`. -/
abbrev ckx2_TryDecryptCliLinkedEnvOf (maxOps : Nat) (C : Crypto) (K : MlKem) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  ckx2_TryDecryptCliLinkedLoopEnvOf CmkLoopAdvanceEvs maxOps C K

/-- `PeerSpqrStateTight640`-guarded `@109` `W2` (`decryptSignal`) binary-kit slot envelope. -/
noncomputable def ckx2_cliDecryptSignalBinaryKitSlotEnvExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets) :
    DecSigGhost → List AllocEvent → Prop :=
  fun x evs =>
    PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
        (ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

theorem ckx2_tryDecryptCmkStepEnvOf_cmk_eq :
    ckx2_tryDecryptCmkStepEnvOf CmkLoopAdvanceEvs = tryDecryptCmkStepEnv :=
  rfl

theorem ckx2_tryDecryptCmkSeg4EnvOf_cmk_eq :
    ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs = tryDecryptCmkSeg4Env :=
  rfl

/-! ## Curried `W1` and `W2` Exact Slot Statement Definitions -/

/-- Curried `W1` (`encrypt`) `PhaseCreditSpec fineCostModel` obligation on
`ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
def ckx2_w1EncExact_phaseCredit_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
    g.c = .send peerV →
    w1R.repAlloc = A.repAlloc →
    W1BinarySendDom (.send peerV) g.i w1R →
    PhaseCreditSpec fineCostModel
      (ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B w1R.x)
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq

/-- Curried `W1` (`encrypt`) `PhaseGroupSpec fineCostModel` obligation on
`ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
def ckx2_w1EncExact_groupSpec_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
    g.c = .send peerV →
    w1R.repAlloc = A.repAlloc →
    W1BinarySendDom (.send peerV) g.i w1R →
    PhaseGroupSpec fineCostModel
      (ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B w1R.x)
      w1EncExactGrpS

/-- Curried `W2` (`decryptSignal`) `PhaseCreditSpec fineCostModel` obligation on
`ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
def ckx2_w2DecSigExact_phaseCredit_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
    g.c = .recv peerV →
    w2R.repAlloc = A.repAlloc →
    W2BinaryWhisperDom (.recv peerV) g.i w2R →
    PhaseCreditSpec fineCostModel
      (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B w2R.x)
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq

/-- Curried `W2` (`decryptSignal`) `PhaseGroupSpec fineCostModel` obligation on
`ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
def ckx2_w2DecSigExact_groupSpec_Stmt [LibsignalPlacement] (W : CliHooks) : Prop :=
  ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
    g.c = .recv peerV →
    w2R.repAlloc = A.repAlloc →
    W2BinaryWhisperDom (.recv peerV) g.i w2R →
    PhaseGroupSpec fineCostModel
      (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B w2R.x)
      w2DecSigExactGrpS

/-! ## Bundled `SingleSlotFineSpec` and Whole-`main` Consumer Wiring -/

/-- Bundled `SingleSlotFineSpec` for `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
def ckx2_w1EncExact_singleSlotFineSpec_of_stmts [LibsignalPlacement] (W : CliHooks)
    (hCredit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hGrp : ckx2_w1EncExact_groupSpec_Stmt W)
    (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w1R : W1BinarySendParams)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV))
    (hc : g.c = .send peerV)
    (hrep : w1R.repAlloc = A.repAlloc)
    (hdom : W1BinarySendDom (.send peerV) g.i w1R) :
    SingleSlotFineSpec (ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B w1R.x) where
  cum := w1EncExactCum
  live := w1EncExactLive
  peak := w1EncExactPeak
  maxReq := w1EncExactMaxReq
  grpS := w1EncExactGrpS
  credit := hCredit g peerV M A w1R hi hp hc hrep hdom
  live_le_peak := Nat.le_refl _
  groups := hGrp g peerV M A w1R hi hp hc hrep hdom

/-- Bundled `SingleSlotFineSpec` for `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
def ckx2_w2DecSigExact_singleSlotFineSpec_of_stmts [LibsignalPlacement] (W : CliHooks)
    (hCredit : ckx2_w2DecSigExact_phaseCredit_Stmt W)
    (hGrp : ckx2_w2DecSigExact_groupSpec_Stmt W)
    (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hc : g.c = .recv peerV)
    (hrep : w2R.repAlloc = A.repAlloc)
    (hdom : W2BinaryWhisperDom (.recv peerV) g.i w2R) :
    SingleSlotFineSpec (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B w2R.x) where
  cum := w2DecSigExactCum
  live := w2DecSigExactLive
  peak := w2DecSigExactPeak
  maxReq := w2DecSigExactMaxReq
  grpS := w2DecSigExactGrpS
  credit := hCredit g peerV M A w2R hi hp hc hrep hdom
  live_le_peak := Nat.le_refl _
  groups := hGrp g peerV M A w2R hi hp hc hrep hdom

/-- Instantiates `realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_curried` with the
curried `W1` and `W2` slot obligations. -/
theorem ckx2_realCliMainBinaryKitEnvOfSlot_fitsEnv_of_stmts [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hEncCredit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hEncGrp : ckx2_w1EncExact_groupSpec_Stmt W)
    (hDecSigCredit : ckx2_w2DecSigExact_phaseCredit_Stmt W)
    (hDecSigGrp : ckx2_w2DecSigExact_groupSpec_Stmt W)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel
        (cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactCum w4DecPkExactLive w4DecPkExactPeak w4DecPkExactMaxReq)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel
        (cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactGrpS) :
    realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt
      (fun {_M} A B => ckx2_cliEncryptBinaryKitSlotEnvExact W A B)
      (fun {_M} A B => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A B)
      img S X W :=
  realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_curried
    (fun {_M} A B => ckx2_cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W
    hEncCredit hEncGrp hDecSigCredit hDecSigGrp hDecPkCredit hDecPkGrp

end LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
