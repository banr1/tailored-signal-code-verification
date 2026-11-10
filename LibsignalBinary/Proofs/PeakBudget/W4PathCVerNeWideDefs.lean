/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux

/-!
# Path-C Stage-P3 Tight `VerNe-prev1` Binary-Kit Slot Envelopes

**Checked by Lean.**

When an existing non-matching current session `s_old` receives an outer v4 `PreKeySignalMessage`
carrying an inner `messageVersion = 3#8` `SignalMessage`, `process_prekey` initializes a fresh v4
Bob session (`sess_out1`) and archives `enc_old = encSession (clearPending s_old)` into
`previous_sessions = [enc_old]`. Subsequent `try_decrypt_from_record` observes `4 ≠ 3` on the
promoted current session and loops over `[enc_old]`, decoding the bare `SessionStructure` wire bytes
`enc_old` and skipping `try_decrypt` (`enc_old.version = 4 ≠ 3`).

This module defines:
1. `VerNeSessionCancelRawEnv` and `VerNeSessionCancelEnv` (`enc = encSession s` paired with
   `SessDeserializeCancelEnv ⟨some s⟩`), with closed `fineCostModel` `PhaseCreditSpec` and
   `PhaseGroupSpec` instances.
2. `VerNeTightTopEnvOf` / `VerNeTightTopRawEnv` / `VerNeTightTopEnv` and `W4StageP3Prev1WideEnvOf` /
   `W4StageP3Prev1WideEnv` (adding the version-mismatch arm alongside `W4StageP3WideEnv`).
3. Path-C and 4-arm binary-kit slot envelopes (`W4BinaryRecvPrekeyPathCWideVerNeEnv*`,
   `W4BinaryRecvPrekeyWideVerNeSlotEnv*`, `realCliDecPkBinaryWideVerNeSlotEnvFixed*`, and
   `realCliDecPkBinaryWideVerNeSlotEnvGuardedFixed*`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs

open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
  (StageP3VerNePrev1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (VerNeS1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (VerNeTailEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryRecvPrekeyParams W4BinaryRecvPrekeyPathAWideEnv W4BinaryRecvPrekeyPathBWideEnv
   W4BinaryRecvPrekeyPathCWideEnv W4BinaryRecvPrekeyWideSlotEnv W4BinaryStageP1OkEnv
   W4BinaryStageP1UntrustedEnv W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathCWideEnv
   W4BinaryStageP4PathCWideEnv W4CloneACDomEnv W4CloneBDomEnv mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked (W4BinaryCallSiteDom)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryRecvPrekeyPathAWideEnvFixed W4BinaryRecvPrekeyPathCWideEnvFixed
   W4BinaryRecvPrekeyWideSlotEnvAllFixed W4BinaryRecvPrekeyWideSlotEnvFixed
   W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
   W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathCWideEnvAllFixed
   W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed
   W4BinaryStageP4PathCWideEnvAllFixed W4BinaryStageP4PathCWideEnvFixed
   realCliDecPkBinaryWideSlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (OptStageEnv W4StageP3WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (W4RecvPrekeyTryDecACEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak sessDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## Tight `SessionStructure` Deserialization Envelopes on Bare `encSession s` Wire Bytes -/

/-- Uncapped bare-`SessionStructure` (`enc = encSession s`) scratch-cancelling decode envelope
pairing `enc` with `SessDeserializeCancelEnv ⟨some s⟩` (`recFieldsQ ⟨some s⟩ = genFieldsQ s`). -/
def VerNeSessionCancelRawEnv (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ s : Session (List (BitVec 8)),
    enc = encSession s ∧
    SessDeserializeCancelEnv ⟨some s⟩ evs

/-- `2 MiB`-record-capped bare-`SessionStructure` (`enc = encSession s`) scratch-cancelling decode
envelope carrying `(encodeRecord ⟨some s⟩).length ≤ deserCancelFineMaxReq` (`2,097,152`), so
`sessDeserializeCancelEnv_fine_phaseCreditSpec` applies directly when `enc.length ≤ 2,097,152`. -/
def VerNeSessionCancelEnv (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ s : Session (List (BitVec 8)),
    enc = encSession s ∧
    (encodeRecord ⟨some s⟩).length ≤ deserCancelFineMaxReq ∧
    SessDeserializeCancelEnv ⟨some s⟩ evs

theorem verNeSessionCancelEnv_sub_raw {enc : List (BitVec 8)} {evs : List AllocEvent}
    (h : VerNeSessionCancelEnv enc evs) : VerNeSessionCancelRawEnv enc evs := by
  rcases h with ⟨s, henc, _, hdes⟩
  exact ⟨s, henc, hdes⟩

/-- Closed `fineCostModel` `PhaseCreditSpec` for `VerNeSessionCancelEnv enc`:
`(cum, live, peak, maxReq) = (16,890,453, 3,211,282, 5,316,629, 2,097,152)`. -/
theorem verNeSessionCancelEnv_fine_phaseCreditSpec (enc : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (VerNeSessionCancelEnv enc)
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq where
  req_align _ hE ev hev := by
    rcases hE with ⟨_, _, hlen, hdes⟩
    exact (sessDeserializeCancelEnv_fine_phaseCreditSpec hlen).req_align _ hdes ev hev
  credit_le st0 {_} hE := by
    rcases hE with ⟨_, _, hlen, hdes⟩
    exact (sessDeserializeCancelEnv_fine_phaseCreditSpec hlen).credit_le st0 hdes

/-- Closed `PhaseGroupSpec` for `VerNeSessionCancelRawEnv enc` (`344,462,092`, `5,257` groups). -/
theorem verNeSessionCancelRawEnv_fine_groupSpec (enc : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (VerNeSessionCancelRawEnv enc) deserCancelFineGrpS where
  groups_le st0 {_} hE := by
    rcases hE with ⟨s, _, hdes⟩
    exact (sessDeserializeCancelEnv_fine_groupSpec ⟨some s⟩).groups_le st0 hdes

/-- Closed `PhaseGroupSpec` for `VerNeSessionCancelEnv enc` (`344,462,092`, `5,257` groups). -/
theorem verNeSessionCancelEnv_fine_groupSpec (enc : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (VerNeSessionCancelEnv enc) deserCancelFineGrpS where
  groups_le st0 {_} hE :=
    (verNeSessionCancelRawEnv_fine_groupSpec enc).groups_le st0 (verNeSessionCancelEnv_sub_raw hE)

/-! ## Parametric & Tight `VerNe-prev1` Stage-P3 Envelopes -/

/-- Parametric `VerNe` post-clone top envelope (`VerNeS1Env` → `DecEnv enc` → `FreeOnlyEvs` →
`VerNeTailEnv`, no `try_decrypt` because `enc_old.version = 4 ≠ msgVer`). -/
def VerNeTightTopEnvOf (DecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv VerNeS1Env (SeqEnv (SeqEnv (DecEnv enc) FreeOnlyEvs) VerNeTailEnv)

/-- `VerNeTightTopEnvOf` specialized to uncapped `VerNeSessionCancelRawEnv`. -/
abbrev VerNeTightTopRawEnv : List (BitVec 8) → List AllocEvent → Prop :=
  VerNeTightTopEnvOf VerNeSessionCancelRawEnv

/-- `VerNeTightTopEnvOf` specialized to `VerNeSessionCancelEnv`. -/
abbrev VerNeTightTopEnv : List (BitVec 8) → List AllocEvent → Prop :=
  VerNeTightTopEnvOf VerNeSessionCancelEnv

/-- Definitional check: `StageP3VerNePrev1Env VerNeTightTopEnv` expands to the exact tight shape. -/
theorem stageP3VerNePrev1Env_tight_eq
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (enc : List (BitVec 8)) :
    StageP3VerNePrev1Env VerNeTightTopEnv recG st enc =
      SeqEnv (SegCloneEnv recG st)
        (SeqEnv VerNeS1Env
          (SeqEnv (SeqEnv (VerNeSessionCancelEnv enc) FreeOnlyEvs) VerNeTailEnv)) :=
  rfl

/-- Path-C Stage-P3 envelope parametric in `verNeEnv`: `W4StageP3WideEnv CloneEnv TryDecEnv` OR
(`MAX`, not sequential) the `1`-previous-session version-mismatch arm
`SeqEnv CloneEnv (verNeEnv enc_prev1)`. -/
def W4StageP3Prev1WideEnvOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (CloneEnv TryDecEnv : List AllocEvent → Prop)
    (enc_prev1 : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  W4StageP3WideEnv CloneEnv TryDecEnv evs ∨
    SeqEnv CloneEnv (verNeEnv enc_prev1) evs

/-- Path-C Stage-P3 envelope specialized to `VerNeTightTopEnv`. -/
abbrev W4StageP3Prev1WideEnv
    (CloneEnv TryDecEnv : List AllocEvent → Prop)
    (enc_prev1 : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  W4StageP3Prev1WideEnvOf VerNeTightTopEnv CloneEnv TryDecEnv enc_prev1 evs

private theorem seqEnv_mono_local {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) (hb : ∀ e, B₁ e → B₂ e) {evs : List AllocEvent}
    (h : SeqEnv A₁ B₁ evs) : SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl (ha evs h1)
  · exact Or.inr ⟨e₁, e₂, rfl, ha e₁ h1, hb e₂ h2⟩

private theorem optStageEnv_mono_local {A₁ A₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) {evs : List AllocEvent}
    (h : OptStageEnv A₁ evs) : OptStageEnv A₂ evs :=
  h.elim Or.inl fun h1 => Or.inr (ha _ h1)

theorem w4StageP3Prev1WideEnvOf_of_wide
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {enc_prev1 : List (BitVec 8)} {evs : List AllocEvent}
    (h : W4StageP3WideEnv CloneEnv TryDecEnv evs) :
    W4StageP3Prev1WideEnvOf verNeEnv CloneEnv TryDecEnv enc_prev1 evs :=
  Or.inl h

theorem w4StageP3Prev1WideEnvOf_of_stageP3VerNePrev1Env
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {enc_prev1 : List (BitVec 8)} {evs : List AllocEvent}
    (hclone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (h : StageP3VerNePrev1Env verNeEnv recG st enc_prev1 evs) :
    W4StageP3Prev1WideEnvOf verNeEnv CloneEnv TryDecEnv enc_prev1 evs :=
  Or.inr (seqEnv_mono_local hclone (fun _ hv => hv) h)

/-! ## Path-C & 4-Arm Binary-Kit `recv-prekey` Slot Envelopes with `VerNe-prev1` -/

/-- Binary-kit Path C (`Over` / `prev1`) Stages P1 → P2 → P3 → P4 envelope with `VerNe-prev1`
Stage-P3 alternative `W4StageP3Prev1WideEnvOf verNeEnv`. -/
def W4BinaryRecvPrekeyPathCWideVerNeEnvOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParams) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACEnv w.base) w.base.enc_prev1))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnv w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

abbrev W4BinaryRecvPrekeyPathCWideVerNeEnv : W4BinaryRecvPrekeyParams → List AllocEvent → Prop :=
  W4BinaryRecvPrekeyPathCWideVerNeEnvOf VerNeTightTopEnv

/-- Binary-kit Path C (`Over` / `prev1`) envelope at `W4BinaryStageP4PathCWideEnvFixed` with
`VerNe-prev1` Stage-P3 alternative `W4StageP3Prev1WideEnvOf verNeEnv`. -/
def W4BinaryRecvPrekeyPathCWideVerNeEnvFixedOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParams) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACEnv w.base) w.base.enc_prev1))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

abbrev W4BinaryRecvPrekeyPathCWideVerNeEnvFixed :
    W4BinaryRecvPrekeyParams → List AllocEvent → Prop :=
  W4BinaryRecvPrekeyPathCWideVerNeEnvFixedOf VerNeTightTopEnv

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope with `VerNe-prev1` on Path C. -/
def W4BinaryRecvPrekeyWideVerNeSlotEnvOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParams) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideEnv w e ∨
      W4BinaryRecvPrekeyPathAWideEnv w e ∨
      W4BinaryRecvPrekeyPathCWideVerNeEnvOf verNeEnv w e)
    FreeOnlyEvs evs

abbrev W4BinaryRecvPrekeyWideVerNeSlotEnv : W4BinaryRecvPrekeyParams → List AllocEvent → Prop :=
  W4BinaryRecvPrekeyWideVerNeSlotEnvOf VerNeTightTopEnv

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope at `W4BinaryKpkMarkStepEnvFixed` on
Paths A and C, with `VerNe-prev1` on Path C. -/
def W4BinaryRecvPrekeyWideVerNeSlotEnvFixedOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParams) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideEnv w e ∨
      W4BinaryRecvPrekeyPathAWideEnvFixed w e ∨
      W4BinaryRecvPrekeyPathCWideVerNeEnvFixedOf verNeEnv w e)
    FreeOnlyEvs evs

abbrev W4BinaryRecvPrekeyWideVerNeSlotEnvFixed :
    W4BinaryRecvPrekeyParams → List AllocEvent → Prop :=
  W4BinaryRecvPrekeyWideVerNeSlotEnvFixedOf VerNeTightTopEnv

/-- Complete 4-arm W4 (`recv-prekey`) slot envelope with `ReadFileRuleEnvFixed` on all store-kit
`Dir::get` steps AND `W4StageP3Prev1WideEnvOf verNeEnv` on Path C Stage P3. -/
def W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixedOf
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParams) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideSlotParams w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.F w.base.x_res w.base.x_spqr))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneACDomEnv (W4RecvPrekeyTryDecACEnv w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3Prev1WideEnvOf verNeEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACEnv w.base) w.base.enc_prev1))
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

abbrev W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixed :
    W4BinaryRecvPrekeyParams → List AllocEvent → Prop :=
  W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixedOf VerNeTightTopEnv

theorem w4BinaryRecvPrekeyWideSlotEnv_sub_verNeOf
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {w : W4BinaryRecvPrekeyParams} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnv w evs) :
    W4BinaryRecvPrekeyWideVerNeSlotEnvOf verNeEnv w evs := by
  rcases h with hf | hs
  · exact Or.inl hf
  · refine Or.inr (seqEnv_mono_local (fun _ he => ?_) (fun _ hf => hf) hs)
    rcases he with hu | hb | ha | hc
    · exact Or.inl hu
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl ha))
    · refine Or.inr (Or.inr (Or.inr ?_))
      unfold W4BinaryRecvPrekeyPathCWideEnv at hc
      unfold W4BinaryRecvPrekeyPathCWideVerNeEnvOf
      exact seqEnv_mono_local (fun _ h1 => h1)
        (fun _ h2 => seqEnv_mono_local (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono_local
            (fun _ hp3 => optStageEnv_mono_local (fun _ hw => Or.inl hw) hp3)
            (fun _ hp4 => hp4) h3) h2) hc

theorem w4BinaryRecvPrekeyWideSlotEnvFixed_sub_verNeFixedOf
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {w : W4BinaryRecvPrekeyParams} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvFixed w evs) :
    W4BinaryRecvPrekeyWideVerNeSlotEnvFixedOf verNeEnv w evs := by
  rcases h with hf | hs
  · exact Or.inl hf
  · refine Or.inr (seqEnv_mono_local (fun _ he => ?_) (fun _ hf => hf) hs)
    rcases he with hu | hb | ha | hc
    · exact Or.inl hu
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl ha))
    · refine Or.inr (Or.inr (Or.inr ?_))
      unfold W4BinaryRecvPrekeyPathCWideEnvFixed at hc
      unfold W4BinaryRecvPrekeyPathCWideVerNeEnvFixedOf
      exact seqEnv_mono_local (fun _ h1 => h1)
        (fun _ h2 => seqEnv_mono_local (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono_local
            (fun _ hp3 => optStageEnv_mono_local (fun _ hw => Or.inl hw) hp3)
            (fun _ hp4 => hp4) h3) h2) hc

theorem w4BinaryRecvPrekeyWideSlotEnvAllFixed_sub_verNeAllFixedOf
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {w : W4BinaryRecvPrekeyParams} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvAllFixed w evs) :
    W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixedOf verNeEnv w evs := by
  rcases h with hf | hs
  · exact Or.inl hf
  · refine Or.inr (seqEnv_mono_local (fun _ he => ?_) (fun _ hf => hf) hs)
    rcases he with hu | hb | ha | hc
    · exact Or.inl hu
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl ha))
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono_local (fun _ h1 => h1)
        (fun _ h2 => seqEnv_mono_local (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono_local
            (fun _ hp3 => optStageEnv_mono_local (fun _ hw => Or.inl hw) hp3)
            (fun _ hp4 => hp4) h3) h2) hc

/-! ## `DecPkGhost`-Level Slot Envelopes, Guarded Variants, & `ghost_congr` -/

/-- Widened binary-kit `W4` (`recv-prekey`) slot envelope (`DecPkGhost → List AllocEvent → Prop`)
at `W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixedOf verNeEnv`. -/
abbrev realCliDecPkBinaryWideVerNeSlotEnvFixedOf [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParams,
    W4BinaryCallSiteDom W.C.F W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideVerNeSlotEnvAllFixedOf verNeEnv w4 evs

abbrev realCliDecPkBinaryWideVerNeSlotEnvFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideVerNeSlotEnvFixedOf VerNeTightTopEnv X W x evs

theorem realCliDecPkBinaryWideVerNeSlotEnvFixedOf_ghost_congr [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideVerNeSlotEnvFixedOf verNeEnv X W x =
      realCliDecPkBinaryWideVerNeSlotEnvFixedOf verNeEnv X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideVerNeSlotEnvFixedOf, hp, hf, hmsg]

theorem realCliDecPkBinaryWideVerNeSlotEnvFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores)
    (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideVerNeSlotEnvFixed X W x =
      realCliDecPkBinaryWideVerNeSlotEnvFixed X W y :=
  realCliDecPkBinaryWideVerNeSlotEnvFixedOf_ghost_congr VerNeTightTopEnv X W x y
    hp hm hs hcp hf hc hmsg

theorem realCliDecPkBinaryWideSlotEnvFixed_sub_verNeFixedOf [LibsignalPlacement]
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvFixed X W x evs) :
    realCliDecPkBinaryWideVerNeSlotEnvFixedOf verNeEnv X W x evs := by
  rcases h with ⟨w4, hdom, hid, hbk, hevs⟩
  exact ⟨w4, hdom, hid, hbk, w4BinaryRecvPrekeyWideSlotEnvAllFixed_sub_verNeAllFixedOf hevs⟩

/-- Input-reachability-guarded wide binary-kit `decrypt_prekey` slot envelope with `VerNe-prev1`:
requires `realCliDecPkBinaryWideVerNeSlotEnvFixedOf verNeEnv X W x evs` whenever
`PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val` holds.

When the guard is false, the envelope reduces to `fun _ => True` (`⊤`), for which
`FitsEnv M lim st (fun _ => True)` is unsatisfiable at finite `lim` (`IfaceBudgetLemmas.lean:378`);
outer `MainOk` consumers discharge `PeerSpqrStateTight640` from `CliPqxdhInputs`. -/
abbrev realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideVerNeSlotEnvFixedOf verNeEnv X W x evs

abbrev realCliDecPkBinaryWideVerNeSlotEnvGuardedFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf VerNeTightTopEnv X W x evs

theorem realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf_ghost_congr [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf verNeEnv X W x =
      realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf verNeEnv X W y := by
  funext evs
  dsimp [realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf]
  rw [hf, hp,
    realCliDecPkBinaryWideVerNeSlotEnvFixedOf_ghost_congr verNeEnv X W x y hp hm hs hcp hf hc hmsg]

theorem realCliDecPkBinaryWideVerNeSlotEnvGuardedFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideVerNeSlotEnvGuardedFixed X W x =
      realCliDecPkBinaryWideVerNeSlotEnvGuardedFixed X W y :=
  realCliDecPkBinaryWideVerNeSlotEnvGuardedFixedOf_ghost_congr VerNeTightTopEnv X W x y
    hp hm hs hcp hf hc hmsg

end LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
