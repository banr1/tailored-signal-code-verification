/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafStmts
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `OverD3` Stage-P1 and Stage-P3 Envelope Inclusion Proofs

Proves `h7l1_Stmt` and `h7l6_Stmt`, upgrading `VerNeTightTopRawEnv` to `VerNeTightTopEnv` under
the `2 MiB` serialized record-length bound on `⟨some (clearPending s_old)⟩`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16

open CryptoGames.LibsignalSession (IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollSessKitPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryIdTrustStepEnvAllFixed W4BinarySessLoadStepEnvAllFixed
  W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (
  OptStageEnv w4StageP3WideEnv_of_err w4StageP3WideEnv_of_okPrefix
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (
  boxedDeallocPred_to_w4BoxedStoreStep rustDealloc8_freeOnly
)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (
  VerNeSessionCancelEnv VerNeSessionCancelRawEnv VerNeTightTopEnv VerNeTightTopRawEnv
  W4StageP3Prev1WideEnvOf w4StageP3Prev1WideEnvOf_of_stageP3VerNePrev1Env
  w4StageP3Prev1WideEnvOf_of_wide
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (deserCancelFineMaxReq)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (
  SessDeserializeCancelEnv sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafStmts (
  h7l1_Stmt h7l6_Stmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

private theorem e2ar_seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) (hb : ∀ e, B₁ e → B₂ e) {evs : List AllocEvent}
    (h : SeqEnv A₁ B₁ evs) : SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl (ha evs h1)
  · exact Or.inr ⟨e₁, e₂, rfl, ha e₁ h1, hb e₂ h2⟩

private theorem e2ar_optLoadDeserEnv_mono
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {D₁ D₂ : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hD : ∀ r e, D₁ r e → D₂ r e)
    (gr : Except Unit (List (BitVec 8))) {evs : List AllocEvent}
    (h : OptLoadDeserEnv Scope D₁ gr evs) :
    OptLoadDeserEnv Scope D₂ gr evs := by
  cases gr with
  | error _ => exact h
  | ok bs =>
    cases bs with
    | nil => exact h
    | cons b0 bsRest =>
      rcases h with ⟨r, henc, hsc, hdes⟩
      exact ⟨r, henc, hsc, hD r evs hdes⟩

private theorem e2ar_loadStep_sessDeser_sub_w4SessLoadAllFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {peer : AddrGhost} {evs : List AllocEvent}
    (h : LoadStepEnv
      (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A F0 peer B (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv)
      StoresGhost.opened.sessions peer.val evs) :
    W4BinarySessLoadStepEnvAllFixed cliIo.rd F0 peer evs :=
  e2ar_seqEnv_mono (fun _ hb => hb)
    (fun _ h2 => e2ar_seqEnv_mono
      (fun _ hp => e2ar_seqEnv_mono (fun _ ha => ha)
        (fun _ hg => e2ar_seqEnv_mono (fun _ hdir => hdir)
          (fun _ hopt => e2ar_seqEnv_mono
            (fun _ ho => e2ar_optLoadDeserEnv_mono
              (fun _ _ hd => sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hd) _ ho)
            (fun _ hf => hf) hopt) hg) hp)
      (fun _ hf => hf) h2)
    (boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)

private theorem e2ar_trustStep_sub_w4IdTrustAllFixed [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) {F0 : FsFiles} {peer : AddrGhost} {remoteIk : IdentityKey}
    {evs : List AllocEvent}
    (h : TrustStepEnv
      (cliPollIdKitPlaced A F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A F0 peer B (ReadFileRuleEnvFixed cliIo.rd))
      StoresGhost.opened.identity peer.val remoteIk .receiving evs) :
    W4BinaryIdTrustStepEnvAllFixed cliIo.rd F0 peer remoteIk evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h

theorem h7w_l1_proved : h7l1_Stmt := by
  intro _ A B g evs
  dsimp only
  refine ⟨?_, ?_⟩
  · intro hUntr
    exact e2ar_seqEnv_mono
      (fun _ hl => e2ar_loadStep_sessDeser_sub_w4SessLoadAllFixed A B hl)
      (fun _ ht => e2ar_seqEnv_mono
        (fun _ htr => e2ar_trustStep_sub_w4IdTrustAllFixed A B htr)
        (fun _ hcl => hcl) ht)
      hUntr
  · intro hOk
    exact e2ar_seqEnv_mono
      (fun _ hl => e2ar_loadStep_sessDeser_sub_w4SessLoadAllFixed A B hl)
      (fun _ htr => Or.inr (e2ar_trustStep_sub_w4IdTrustAllFixed A B htr))
      hOk

/-- Upgrades `VerNeSessionCancelRawEnv (encSession (clearPending s_old))` to the `2 MiB`-record-capped
`VerNeSessionCancelEnv` whenever `(encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21`. -/
theorem h7w_verNeSessionCancelRaw_to_tight
    {s_old : Session (List (BitVec 8))}
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21)
    {evs : List AllocEvent}
    (h : VerNeSessionCancelRawEnv (encSession (clearPending s_old)) evs) :
    VerNeSessionCancelEnv (encSession (clearPending s_old)) evs := by
  rcases h with ⟨s, henc, hdes⟩
  refine ⟨s, henc, ?_, hdes⟩
  have hRecEq : encodeRecord ⟨some s⟩ = encodeRecord ⟨some (clearPending s_old)⟩ := by
    simp [encodeRecord, ← henc]
  rw [hRecEq]
  simpa [deserCancelFineMaxReq] using hCap

/-- Upgrades `VerNeTightTopRawEnv (encSession (clearPending s_old))` to `VerNeTightTopEnv` under
the `2 MiB` record-length cap on `⟨some (clearPending s_old)⟩`. -/
theorem h7w_verNeTightTopRaw_to_tight
    {s_old : Session (List (BitVec 8))}
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21)
    {evs : List AllocEvent}
    (h : VerNeTightTopRawEnv (encSession (clearPending s_old)) evs) :
    VerNeTightTopEnv (encSession (clearPending s_old)) evs :=
  e2ar_seqEnv_mono (fun _ h1 => h1)
    (fun _ h2 => e2ar_seqEnv_mono
      (fun _ h3 => e2ar_seqEnv_mono
        (fun _ hdec => h7w_verNeSessionCancelRaw_to_tight hCap hdec)
        (fun _ hf => hf) h3)
      (fun _ ht => ht) h2)
    h

theorem h7w_l6_proved : h7l6_Stmt := by
  intro W tdEnv recG st0 peer me msg coins s_old CloneEnv hClone
  dsimp only
  have hArm1 : ∀ (G₁ : SessionGhost) (whisperG : SignalMessageGhost)
      {TryDecEnv : List AllocEvent → Prop},
      (∀ e, tdEnv W (stageP3M3TryDecryptEnvArgs G₁ st0 peer me whisperG msg coins) e →
        TryDecEnv e) →
      ∀ evs,
        (StageP3ErrM3Env (tdEnv W) recG G₁ st0 peer me whisperG msg coins evs ∨
         StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0 peer me whisperG msg coins evs) →
        W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv
          (encSession (clearPending s_old)) evs := by
    intro G₁ whisperG TryDecEnv hTd evs hP3
    rcases hP3 with hErr | hOk
    · exact w4StageP3Prev1WideEnvOf_of_wide
        (w4StageP3WideEnv_of_err
          (e2ar_seqEnv_mono hClone (fun _ h => e2ar_seqEnv_mono hTd (fun _ hv => hv) h) hErr))
    · exact w4StageP3Prev1WideEnvOf_of_wide
        (w4StageP3WideEnv_of_okPrefix
          (e2ar_seqEnv_mono hClone (fun _ h => e2ar_seqEnv_mono hTd (fun _ hf => hf) h) hOk))
  have hArm2 : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 →
      ∀ (TryDecEnv : List AllocEvent → Prop) (evs : List AllocEvent),
        StageP3VerNePrev1Env VerNeTightTopRawEnv recG st0 (encSession (clearPending s_old)) evs →
        W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv
          (encSession (clearPending s_old)) evs := by
    intro hCap TryDecEnv evs hVerNe
    exact w4StageP3Prev1WideEnvOf_of_stageP3VerNePrev1Env hClone
      (e2ar_seqEnv_mono (fun _ hc => hc) (fun _ hv => h7w_verNeTightTopRaw_to_tight hCap hv) hVerNe)
  refine ⟨hArm1, hArm2, ?_⟩
  intro hCap whisperG msgVer evs hPrev1
  unfold StageP3Prev1Env at hPrev1
  by_cases hver : st0.version = msgVer
  · simp only [hver, ↓reduceIte] at hPrev1
    rcases hPrev1 with ⟨G₁, hcl, hErr⟩
    exact Or.inl ⟨G₁, hcl, fun {TryDecEnv} hTd => hArm1 G₁ whisperG hTd evs (Or.inl hErr)⟩
  · simp only [hver, ↓reduceIte] at hPrev1
    exact Or.inr fun TryDecEnv => hArm2 hCap TryDecEnv evs hPrev1

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16
