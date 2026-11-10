/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `OverD3` Stage-P1 and Stage-P3 Envelope Inclusion Statements

Statement interfaces `h7l1_Stmt` (Stage-P1 untrusted and trusted store-kit envelope inclusions into
`AllFixed`) and `h7l6_Stmt` (Stage-P3 `Over` envelope inclusions into
`W4StageP3Prev1WideEnvOf VerNeTightTopEnv` under the `2 MiB` `clearPending` record-length cap).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafStmts

open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (
  VerNeTightTopEnv VerNeTightTopRawEnv W4StageP3Prev1WideEnvOf
)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-- Stage-P1 `OverD3` untrusted (`CliDpPollUntrustedEnv`) and trusted (`CliStageP1OkEnv`)
envelopes at `ReadFileRuleEnvFixed cliIo.rd` and `SessDeserializeCancelEnv` embed into
`W4BinaryStageP1UntrustedEnvAllFixed` and `W4BinaryStageP1OkEnvAllFixed`. -/
def h7l1_Stmt : Prop :=
  ∀ [LibsignalPlacement] (A : RustAlloc) (B : RunBudgets) (g : DecPkGhost)
    (evs : List AllocEvent),
    let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
    (CliDpPollUntrustedEnv (A := A) B ReadEnv SessDeserializeCancelEnv g evs →
      W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs) ∧
    (CliStageP1OkEnv (A := A) B ReadEnv SessDeserializeCancelEnv g evs →
      W4BinaryStageP1OkEnvAllFixed cliIo.rd g.F g.peer g.msg.identityKey evs)

/-- Stage-P3 `OverD3` arms (`StageP3ErrM3Env`, `StageP3OkPrefixM3Env`,
`StageP3VerNePrev1Env VerNeTightTopRawEnv`, and `StageP3Prev1Env (tdEnv W) VerNeTightTopRawEnv`)
embed into `W4StageP3Prev1WideEnvOf VerNeTightTopEnv` whenever
`(encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21`. -/
def h7l6_Stmt : Prop :=
  ∀ (W : CliHooks) (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG : SessionGhost) (st0 : SessionState (List (BitVec 8)))
    (peer me : AddrGhost) (msg : SignalMessage) (coins : List (BitVec 8))
    (s_old : Session (List (BitVec 8)))
    {CloneEnv : List AllocEvent → Prop},
    (∀ e, SegCloneEnv recG st0 e → CloneEnv e) →
    let enc_prev1 := encSession (clearPending s_old)
    (∀ (G₁ : SessionGhost) (whisperG : SignalMessageGhost)
       {TryDecEnv : List AllocEvent → Prop},
      (∀ e,
        tdEnv W (stageP3M3TryDecryptEnvArgs G₁ st0 peer me whisperG msg coins) e →
        TryDecEnv e) →
      ∀ evs,
        (StageP3ErrM3Env (tdEnv W) recG G₁ st0 peer me whisperG msg coins evs ∨
         StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0 peer me whisperG msg coins evs) →
        W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv enc_prev1 evs) ∧
    ((encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 →
      ∀ (TryDecEnv : List AllocEvent → Prop) (evs : List AllocEvent),
        StageP3VerNePrev1Env VerNeTightTopRawEnv recG st0 enc_prev1 evs →
        W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv enc_prev1 evs) ∧
    ((encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 →
      ∀ (whisperG : SignalMessageGhost) (msgVer : BitVec 32) (evs : List AllocEvent),
        StageP3Prev1Env (tdEnv W) VerNeTightTopRawEnv recG st0
          peer me whisperG msg msgVer enc_prev1 coins evs →
        (∃ G₁ : SessionGhost,
          CloneRel recG G₁ ∧
          ∀ {TryDecEnv : List AllocEvent → Prop},
            (∀ e,
              tdEnv W (stageP3M3TryDecryptEnvArgs G₁ st0 peer me whisperG msg coins) e →
              TryDecEnv e) →
            W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv enc_prev1 evs) ∨
        (∀ (TryDecEnv : List AllocEvent → Prop),
          W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv enc_prev1 evs))

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafStmts
