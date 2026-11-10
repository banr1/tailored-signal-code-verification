/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges

/-!
# Parametric `TryDecryptCliLinkedEnvOf` Interface

Defines `(LoopAdvEnv, maxOps, RecvProtoEnv)`-parametric companions to `SpqrRecvC07C09aTightLinkedEnv`,
`SpqrRecvC07C09aBytesEnv`, and `TryDecryptCliLinkedEnv`, together with their specializations at
`StatesRecvProtoEnv' K`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf

open CryptoGames.LibsignalSession
  (ChainKey Crypto Mut PublicKey RatchetState ShaCompress TripleRatchet)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliEnvOfPure TryDecryptCliLinkedEnv tryDecryptCmkSeg4Env
   tryDecryptCmkStepEnv tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges (tlb_DecodeStateTightEnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-- `(maxOps, RecvProtoEnv)`-parametric linked `spqr::recv` envelope instantiating `SpqrRecvTightLinkedEnv` at `tlb_DecodeStateTightEnvOf maxOps`, `StatesFromPbTightEnv`, `StatesIntoPbTightEnv`, and `RecvProtoEnv`.
-/
def SpqrRecvC07C09aTightLinkedEnvRecvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
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
    (fun _ => tlb_DecodeStateTightEnvOf maxOps)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    RecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Existentially lifted 12-ghost `(maxOps, RecvProtoEnv)`-parametric linked `spqr::recv` byte-slice envelope.
-/
def SpqrRecvC07C09aBytesEnvRecvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    SpqrRecvC07C09aTightLinkedEnvRecvOf maxOps F K RecvProtoEnv
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem spqrRecvC07C09aBytesEnvRecvOf_nonempty (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, SpqrRecvC07C09aBytesEnvRecvOf maxOps F K RecvProtoEnv stBs msgBs evs :=
  let _ := msgBs
  ⟨[], spqrRecvTightLinkedEnv_nil_exists F K
    (fun _ => tlb_DecodeStateTightEnvOf maxOps)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    RecvProtoEnv stBs⟩

/-- `maxOps`-parametric linked `spqr::recv` envelope specialized at `StatesRecvProtoEnv' K`. -/
def SpqrRecvC07C09aTightLinkedEnvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvC07C09aTightLinkedEnvRecvOf maxOps F K (StatesRecvProtoEnv' K)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Existentially lifted `maxOps`-parametric linked `spqr::recv` byte-slice envelope at `StatesRecvProtoEnv' K`.
-/
def SpqrRecvC07C09aBytesEnvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    SpqrRecvC07C09aTightLinkedEnvOf maxOps F K
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem spqrRecvC07C09aBytesEnvOf_nonempty (maxOps : Nat) (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, SpqrRecvC07C09aBytesEnvOf maxOps F K stBs msgBs evs :=
  spqrRecvC07C09aBytesEnvRecvOf_nonempty maxOps F K (StatesRecvProtoEnv' K) stBs msgBs

/-- Loop-envelope-parametric Segment-4 `consume_message_key` step envelope. -/
def tryDecryptCmkStepEnvOf
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

def tryDecryptCmkSeg4EnvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) : List AllocEvent → Prop :=
  SeqEnv fmtWriteEnv
    (SeqEnv (tryDecryptCmkStepEnvOf LoopAdvEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck)
      FreeOnlyEvs)

/-- `try_decrypt_with_state` CLI allocation envelope parameterized by `LoopAdvEnv`, `maxOps`, and `RecvProtoEnv`.
-/
abbrev TryDecryptCliLinkedLoopEnvRecvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (maxOps : Nat) (C : Crypto) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  let S := spqrV1 C.F K
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (tryDecryptCmkSeg4EnvOf LoopAdvEnv FmtWriteEnv)
        (PqRecvEnv S (SpqrRecvC07C09aBytesEnvRecvOf maxOps C.F K RecvProtoEnv) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

abbrev TryDecryptCliLinkedEnvRecvOf (maxOps : Nat) (C : Crypto) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliLinkedLoopEnvRecvOf CmkLoopAdvanceEvs maxOps C K RecvProtoEnv

/-- `try_decrypt_with_state` CLI allocation envelope parameterized by `LoopAdvEnv` and `maxOps` at `StatesRecvProtoEnv' K`.
-/
def TryDecryptCliLinkedLoopEnvOf
    (LoopAdvEnv : Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop)
    (maxOps : Nat) (C : Crypto) (K : MlKem)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  let S := spqrV1 C.F K
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (tryDecryptCmkSeg4EnvOf LoopAdvEnv FmtWriteEnv)
        (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

abbrev TryDecryptCliLinkedEnvOf (maxOps : Nat) (C : Crypto) (K : MlKem) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliLinkedLoopEnvOf CmkLoopAdvanceEvs maxOps C K

theorem tryDecryptCmkStepEnvOf_cmk_eq :
    tryDecryptCmkStepEnvOf CmkLoopAdvanceEvs = tryDecryptCmkStepEnv :=
  rfl

theorem tryDecryptCmkSeg4EnvOf_cmk_eq :
    tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs = tryDecryptCmkSeg4Env :=
  rfl

theorem tryDecryptCliLinkedEnvRecvOf_eq_pure (maxOps : Nat) (C : Crypto) (K : MlKem)
    (RecvProtoEnv : States spqrPolyApi (spqrAuthApi C.F) → Message spqrPolyApi →
      List AllocEvent → Prop) :
    TryDecryptCliLinkedEnvRecvOf maxOps C K RecvProtoEnv =
      TryDecryptCliEnvOfPure C (spqrV1 C.F K) FmtWriteEnv
        (SpqrRecvC07C09aBytesEnvRecvOf maxOps C.F K RecvProtoEnv) FormatInnerEnv :=
  rfl

theorem tryDecryptCliLinkedEnvOf_eq_pure (maxOps : Nat) (C : Crypto) (K : MlKem) :
    TryDecryptCliLinkedEnvOf maxOps C K =
      TryDecryptCliEnvOfPure C (spqrV1 C.F K) FmtWriteEnv
        (SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv :=
  rfl

theorem spqrRecvC07C09aTightLinkedEnvOf_eq_recvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem) :
    SpqrRecvC07C09aTightLinkedEnvOf maxOps F K =
      SpqrRecvC07C09aTightLinkedEnvRecvOf maxOps F K (StatesRecvProtoEnv' K) :=
  rfl

theorem spqrRecvC07C09aBytesEnvOf_eq_recvOf (maxOps : Nat) (F : ShaCompress) (K : MlKem) :
    SpqrRecvC07C09aBytesEnvOf maxOps F K =
      SpqrRecvC07C09aBytesEnvRecvOf maxOps F K (StatesRecvProtoEnv' K) :=
  rfl

theorem tryDecryptCliLinkedEnvOf_eq_recvOf (maxOps : Nat) (C : Crypto) (K : MlKem) :
    TryDecryptCliLinkedEnvOf maxOps C K =
      TryDecryptCliLinkedEnvRecvOf maxOps C K (StatesRecvProtoEnv' K) :=
  rfl

theorem spqrRecvC07C09aTightLinkedEnvRecvOf_83_eq (F : ShaCompress) (K : MlKem) :
    SpqrRecvC07C09aTightLinkedEnvRecvOf 83 F K StatesRecvProtoEnv =
      SpqrRecvC07C09aTightLinkedEnv F K :=
  rfl

theorem spqrRecvC07C09aBytesEnvRecvOf_83_eq (F : ShaCompress) (K : MlKem) :
    SpqrRecvC07C09aBytesEnvRecvOf 83 F K StatesRecvProtoEnv =
      SpqrRecvC07C09aBytesEnv F K :=
  rfl

theorem tryDecryptCliLinkedEnvRecvOf_83_eq (C : Crypto) (K : MlKem) :
    TryDecryptCliLinkedEnvRecvOf 83 C K StatesRecvProtoEnv =
      TryDecryptCliLinkedEnv C K :=
  rfl

end LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
