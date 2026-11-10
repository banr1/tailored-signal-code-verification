/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P2 and Stage P3 Interfaces

Defines budget-threaded Stage P3 spatial predicates over `A.atState lim st_b s`, Block `524`
`ChainClone3OkPlaced` / `SenderChainClone3OkPlaced`, Stage P3 allocation envelopes (`StageP3Env`),
and `StageP3PrevEmptyVRegsPlacedStmt` / `StageP3GenStepsVRegsPlacedStmt` (plus `LibsignalFrozen`
variants).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession
  (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost SignalMessageGhost UuidParser decryptDraws uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (SeedsLen32 SpqrModel TryDecryptGhost rootStack)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.CliHandshake.Placed (blkPC_524 blkPl_524)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
  (genP3S5Model genP3S5ModelPanicProp)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit dpPollEntryPlaced dpPollProgPlaced stageP3Sub5ExtraPrePrevEmpty)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (dropSessionStructureLocal2Spec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneSpec senderChainCloneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromMEnv FromVPostTdEnv SegCloneEnv TryDecryptEnvArgs tryDecryptEnvArgs)

abbrev cliPollStageP2Stack_placed_le_subStack :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStageP2Stack_placed_le_subStack

abbrev genP3CallFrame_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3CallFrame_placed

abbrev genP3S5PostFrame_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed

/-- Budget-threaded relocatable `[LibsignalPlacement]` `genP3Pre_placed` at
`dpPollEntryPlaced + 0x1778#64` over `A.atState lim st_b s`. -/
def genP3Pre_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st_b : M.σ) [LibsignalPlacement]
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3Pre_placed
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg s

/-- Budget-threaded relocatable `[LibsignalPlacement]` `stageP3DispatchOkMid_placed`, evaluating
`A.pool` at the post-Step5 machine state `s'` while indexing stack offsets at `s.sp`. -/
def stageP3DispatchOkMid_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMid_placed
    (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr
    pt b_2c0 G₂ st₂

/-- Budget-threaded relocatable `[LibsignalPlacement]` `stageP3ErrPost_placed`, evaluating
`A.pool` at the exit machine state `sf` while indexing stack offsets at `s.sp`. -/
def stageP3ErrPost_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s sf : State)
    (coroPtr outPtr prevStatesPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPost_placed
    (A.atState lim st_b sf) s0 s coroPtr outPtr prevStatesPtr e

/-- Budget-threaded relocatable `[LibsignalPlacement]` `stageP3DispatchOkMidPrevEmpty_placed`,
evaluating `A.pool` at the post-Step5 machine state `s'` while indexing stack offsets at `s.sp`. -/
def stageP3DispatchOkMidPrevEmpty_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr ptCap ptPtr : BitVec 64) (g : RecordGhost)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMidPrevEmpty_placed
    (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G₂ st₂

/-- Budget-threaded relocatable `[LibsignalPlacement]` `stageP3ErrPostPrevEmpty_placed`,
evaluating `A.pool` at the exit machine state `sf` while indexing stack offsets at `s.sp`. -/
def stageP3ErrPostPrevEmpty_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s sf : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPostPrevEmpty_placed
    (A.atState lim st_b sf) s0 s coroPtr outPtr e

/-- Budget-threaded `[LibsignalPlacement]` `ChainClone3OkPlaced` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def ChainClone3OkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524)
    (chainCloneSpec M A lim)

/-- Budget-threaded `[LibsignalPlacement]` `SenderChainClone3OkPlaced` at Block `524`
(`<SessionStructure_Chain as Clone>::clone [local#5]`). -/
def SenderChainClone3OkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_524).rebase (blkPl_524).base H) (lsmpl.base 524)
    (senderChainCloneSpec M A lim)

/-- Stack-pointer-independent `TryDecryptEnvArgs` at the Stage P3 `try_decrypt_with_state`
call site (`msgType :=.preKey`). -/
def stageP3TryDecryptEnvArgs (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : TryDecryptEnvArgs where
  G := G₁
  st := st
  rem := rem
  loc := loc
  msgG := msgG
  msg := msg
  msgType := .preKey
  rest := rest

/-- Stage P3 `Ok`-branch (`+0x1778 → +0x34dc`) prefix allocation envelope for cloned `G₁`:
`SessionStructure::clone` (`SegCloneEnv`), `try_decrypt_with_state` (`tdEnv`), and
`set_session_state` (`FreeOnlyEvs`). -/
def StageP3OkPrefixEnv (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st)
    (SeqEnv (tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) FreeOnlyEvs)

/-- Stage P3 `st.version = msgVer` full/error allocation envelope for cloned `G₁`:
`SessionStructure::clone` (`SegCloneEnv`), `try_decrypt_with_state` (`tdEnv`), and
`FromVPostTdEnv` (`FreeOnlyEvs ∨ FromMEnv`). -/
def StageP3ErrEnv (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st)
    (SeqEnv (tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) FromVPostTdEnv)

/-- Stage P3 `st.version ≠ msgVer` allocation envelope: `SessionStructure::clone` (`SegCloneEnv`)
followed by `FromMEnv` (`grow_one` at `cap = 0`, drop cloned state, allocate 17-byte
`"decryption failed"`, and drop coro state). -/
def StageP3VerNeEnv (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st) FromMEnv

/-- Combined Stage P3 entry allocation envelope covering `hOk` (via `FreeOnlyEvs ⊆ FromVPostTdEnv`),
`hErr`, and `hVerNe`. -/
def StageP3Env (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if st.version = msgVer then
    ∃ G₁ : SessionGhost, CloneRel recG G₁ ∧
      StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs
  else
    StageP3VerNeEnv recG st evs

/-- Budget-threaded relocatable `[LibsignalPlacement]` CLI `pollTryDecryptPlacedSpecP` weakened to
`DistinctSid` (`remoteIdentity ≠ some localIdentity ∨ DistinctSid`), dropping `allocFailedIn`
from `onPanic`. -/
def pollTryDecryptPlacedSpecP [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st_b) s =>
    ⌜FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.pollTryDecryptPlacedSpecP
        C (A.atState lim st_b s) ctl uuidParse S).pre x s
  post :=
    (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv).post
  onPanic :=
    (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv).onPanic

/-- Budget-threaded relocatable `[LibsignalPlacement]` `pollTryDecryptPlacedSpecTPTight` for
`StageP3*PlacedStmt`, using `tryDecryptOnPanicTight` (dropping both `S.recvPanics` and
`allocFailedIn`). -/
def pollTryDecryptPlacedSpecTPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { pollTryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st_b) s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LsTokenInit ∗
        (pollTryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv).pre (x, st_b) s
    post := fun (x, st_b) s0 sf =>
      LsTokenInit ∗
        (pollTryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv).post (x, st_b) s0 sf
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S uuidParse x s0 sf }

/-- Budget-threaded relocatable `[LibsignalPlacement]` `cliTryDecryptPqV1_ok` contract on
`dpPollProgPlaced ext` at Block `507`. -/
def CliTryDecryptPqV1PlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : Crypto → SpqrModel → TryDecryptEnvArgs → List AllocEvent → Prop)
    (ext : Crypto → MlKem → String → Option (State → State)) : Prop :=
  ∀ (C : Crypto) (K : MlKem) (ctl : BitVec 64),
    let S := spqrV1 C.F K
    subroutine_ok (dpPollProgPlaced (ext C K))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S (tdEnv C S)))

/-- Budget-threaded relocatable `[LibsignalPlacement]` `StageP3PrevEmptyVRegsPlacedStmt`. -/
def StageP3PrevEmptyVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {st_b : M.σ}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    AllocContractsXCliPlaced A lim ext →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl
          uuidTryParse (spqrV1 C.F K) tdEnv)) →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

/-- Budget-threaded relocatable `[LibsignalPlacement]` `StageP3GenStepsVRegsPlacedStmt`. -/
def StageP3GenStepsVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {st_b : M.σ}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    AllocContractsXCliPlaced A lim ext →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl
          uuidTryParse (spqrV1 C.F K) tdEnv)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr
            prevStatesPtr (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

/-! ## `LibsignalFrozen` Variants -/

def StageP3PrevEmptyVRegsFrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {st_b : M.σ}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    AllocContractsXCliPlaced A lim ext →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl
          uuidTryParse (spqrV1 C.F K) tdEnv)) →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

def StageP3GenStepsVRegsFrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {st_b : M.σ}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    AllocContractsXCliPlaced A lim ext →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A lim ctl
          uuidTryParse (spqrV1 C.F K) tdEnv)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeEnv recG st evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr outPtr
            prevStatesPtr (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
