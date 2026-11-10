/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Linked `spqr::recv` Byte-Slice and Block-`507` `TryDecryptCliLinkedEnv` Interface

Pure-definition interface for `SpqrRecvC07C09aBytesEnv`, `spqrRecvC07C09aBytesEnv_nonempty`, and
`TryDecryptCliLinkedEnv`, definitionally equal to
`TryDecryptCliEnvOf C (spqrV1 C.F K) FmtWriteEnv (SpqrRecvC07C09aBytesEnv C.F K) FormatInnerEnv`
without `*TrapPlaced*` imports.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked

open CryptoGames.LibsignalSession
  (ChainKey Crypto Mut PublicKey RatchetState ShaCompress TripleRatchet)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvC07C09aTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
  (spqrRecvC07C09aTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Linked `spqr::recv` Byte-Slice Envelope and Block-`507` `TryDecryptCliLinkedEnv` -/

/-- Existentially lifted 12-ghost linked `spqr::recv` byte-slice envelope matching
`SpqrRecvLinkedWitness.spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked`. -/
def SpqrRecvC07C09aBytesEnv (F : ShaCompress) (K : MlKem)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    SpqrRecvC07C09aTightLinkedEnv F K
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Non-emptiness (`[] ∈ SpqrRecvC07C09aBytesEnv F K stBs msgBs`) for `SeamEnvsInhabited`. -/
theorem spqrRecvC07C09aBytesEnv_nonempty (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, SpqrRecvC07C09aBytesEnv F K stBs msgBs evs :=
  let _ := msgBs
  ⟨[], spqrRecvC07C09aTightLinkedEnv_nil_exists F K stBs⟩

/-- Canonical zero-pointer lift of `TryDecryptEnvArgs` to `TryDecryptGhost` (`rfl`-identical to
`TryDecryptPV1TrapPlacedBudget.envArgsToGhost`). -/
def tryDecryptEnvArgsToGhost (a : TryDecryptEnvArgs) : TryDecryptGhost where
  ret := 0#64
  ss := 0#64
  G := a.G
  st := a.st
  remA := 0#64
  rem := a.rem
  locA := 0#64
  loc := a.loc
  msgA := 0#64
  msgG := a.msgG
  msg := a.msg
  msgType := a.msgType
  cur := 0#64
  rest := a.rest

/-- Pointer-free Segment-4 `consume_message_key` step envelope (`rfl`-identical to
`ConsumeMsgKeyTrapPlacedBudget.CmkStepEnv`). -/
def tryDecryptCmkStepEnv (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
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
      CmkLoopAdvanceEvs (msgCounter - ck.index).toNat cap0 len0
        (msgCounter == BitVec.allOnes 32) evs
  else
    evs = rustAllocEvents 36 1

/-- Full Segment-4 (`ConsumeMsgKey`) allocation-event envelope (`rfl`-identical to
`ConsumeMsgKeyTrapPlacedBudget.CmkSeg4Env`). -/
def tryDecryptCmkSeg4Env (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) : List AllocEvent → Prop :=
  SeqEnv fmtWriteEnv
    (SeqEnv (tryDecryptCmkStepEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck)
      FreeOnlyEvs)

/-- Pure `FromS2GenEnv` formulation of `TryDecryptPV1TrapPlacedBudget.TryDecryptCliEnvOf`
(`rfl`-identical across all inputs). -/
def TryDecryptCliEnvOfPure (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (tryDecryptCmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- Block-`507` `try_decrypt_with_state` CLI allocation envelope instantiated at
`SpqrRecvC07C09aBytesEnv`. -/
abbrev TryDecryptCliLinkedEnv (C : Crypto) (K : MlKem) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOfPure C (spqrV1 C.F K) FmtWriteEnv (SpqrRecvC07C09aBytesEnv C.F K) FormatInnerEnv

end LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
