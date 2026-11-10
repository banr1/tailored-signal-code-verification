/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Slots.S1CoinSplitAlgebra
public import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot
public import Symbolic.Proofs.Swarm.CREF.Sanitize
public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure -- shake: keep

/-!
# Coin-Split Lift Definitions and Interface Contracts

Defines the hardware-step certificate `GoodStepCut`, the cut-polymorphic CLI liveness invariant
`CliLiveAtCli`, and the `Prop` interface specifications (`GoodExit0CutSpec`, `InitClearLeakSpec`,
`BridgeAPtSpec`, `BridgeBQuietFailSpec`, `BridgeCCaseASpec`, `BridgeCCaseBSpec`) for lifting clean
model explanations across `CoinSplit` cuts.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureDrawsCoins)
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng)

/-! ## `GoodStepCut` and `NoAdjRng` -/

/-- Single-step hardware-cut shape for an appended block `blk_hw` at call index `k`. -/
inductive GoodStepCut (ok : Nat → Bool) (k : Nat) : List MachineEvent → Prop where
  | leaks {leaks : List MachineEvent} :
      (∀ e ∈ leaks, ∃ x, e = .leak x) →
      GoodStepCut ok k leaks
  | callRecvFail {w : HwBytes} :
      ok k = false →
      GoodStepCut ok k [.recv w]
  | callSendFail {pt : HwBytes} {mid : List MachineEvent} :
      (∀ ev ∈ mid, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt) →
      ok k = false →
      GoodStepCut ok k (.pt pt :: mid)
  | callSendOk {pt : HwBytes} {mid : List MachineEvent} {out_ev : MachineEvent} :
      (∀ ev ∈ mid, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt) →
      eventKind out_ev = .send →
      ok k = true →
      GoodStepCut ok k (.pt pt :: mid ++ [out_ev])
  | callRecvAccept {w : HwBytes} {mid : List MachineEvent} {out_ev : MachineEvent} :
      (mid = [] ∨ ∃ coins, mid = [.rng coins] ∧ coins.length = 32) →
      eventKind out_ev = .accept →
      ok k = true →
      GoodStepCut ok k (.recv w :: mid ++ [out_ev])
  | callInit34 {blob : HwBytes} {ds : List HwBytes} :
      ds.length = 34 →
      ds[0]?.map List.length = some 32 →
      ds[33]?.map List.length = some 32 →
      ok k = true →
      GoodStepCut ok k (.recv blob :: ds.map MachineEvent.rng)

/-- Appending `ys` whose head (if any) is non-`.rng` to `NoAdjRng xs` preserves `NoAdjRng`. -/
theorem noAdjRng_append_of_head_nonRng {xs ys : List MachineEvent}
    (hxs : NoAdjRng xs) (hys : NoAdjRng ys)
    (hhead : ∀ y, ys.head? = some y → eventKind y ≠ .rng) :
    NoAdjRng (xs ++ ys) := by
  induction xs with
  | nil => simpa using hys
  | cons x₁ tl ih =>
    cases tl with
    | nil =>
      cases ys with
      | nil => exact trivial
      | cons y₀ ytl => exact ⟨Or.inr (hhead y₀ rfl), hys⟩
    | cons x₂ tl' =>
      exact ⟨hxs.1, ih hxs.2⟩

/-! ## Cut-polymorphic CLI liveness invariant -/

/-- Cut-polymorphic CLI liveness invariant at `σ_acc`: `NoAdjRng σ_acc`, existence of a clean
`ExplainsCli` witness on `σ_acc`, and `PureCRel ∧ COpkRelC` on every clean `ExplainsCli` cut `τ'`
of `σ_acc`. -/
structure CliLiveAtCli (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (t_clean : CliTurn) (accepted : List HwBytes) (σ_acc : List MachineEvent) : Prop where
  noAdjRng : NoAdjRng σ_acc
  witness : ∃ τ_acc g ms,
    ExplainsCli interp r S who ok σ_acc τ_acc g ms ∧
    ¬ ReadCollision interp r S g ms τ_acc
  cutRel : ∀ τ',
    (∃ g' ms', ExplainsCli interp r S who ok σ_acc τ' g' ms' ∧
      ¬ ReadCollision interp r S g' ms' τ') →
    PureCRel interp r S who ok (t_clean.leakRecords r) t_clean.sent accepted τ' ∧
    COpkRelC interp r S who ok (t_clean.opkUsed r) τ'

theorem explainsCli_toClean {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {σ τ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hex : ExplainsCli interp r S who ok σ τ g ms)
    (hnrc : ¬ ReadCollision interp r S g ms τ) :
    Clean interp r S who ok g ms τ := by
  unfold ExplainsCli OutcomeFaithfulCli Clean ExplainsMoves at *
  tauto

/-- Every inhabited clean `ExplainsCli` cut `τ'` of `σ_acc` satisfies `TopPure.CliLiveAt`. -/
theorem CliLiveAtCli.cliLiveAt_of_cut {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t_clean : CliTurn} {accepted : List HwBytes} {σ_acc τ' : List MachineEvent}
    (hlive : CliLiveAtCli interp r S who ok t_clean accepted σ_acc)
    (hinh : ∃ g' ms', ExplainsCli interp r S who ok σ_acc τ' g' ms' ∧
      ¬ ReadCollision interp r S g' ms' τ') :
    CliLiveAt interp r S who ok t_clean accepted τ' := by
  obtain ⟨g', ms', hex', hnrc'⟩ := hinh
  obtain ⟨hrel, hopk⟩ := hlive.cutRel τ' ⟨g', ms', hex', hnrc'⟩
  exact ⟨⟨g', ms', explainsCli_toClean hex' hnrc'⟩, hrel, hopk⟩

/-! ## Interface specifications -/

/-- Single-step lift from `Clean` on `τ_pre ++ blk_hw` to `ExplainsCli` on `σ_pre ++ blk_cli`
along a `GoodStepCut` block `blk_hw`. -/
def GoodExit0CutSpec : Prop :=
  ∀ {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {σ_pre τ_pre blk_cli blk_hw : List MachineEvent}
    {g₀ g₁ : Ghost} {ms₀ ms_pre δ : List Move},
    ExplainsCli interp r S who ok σ_pre τ_pre g₀ ms₀ →
    CoinSplit blk_cli blk_hw →
    GoodStepCut ok (callStarts τ_pre).length blk_hw →
    (ms_pre = ms₀ ∨ ms_pre = Sanitize.sanitizeMoves (setupTrace r) ms₀) →
    (∀ ts < (runTraceMoves r ms₀).length, ∀ sz, g₁.σ ts sz = g₀.σ ts sz) →
    Clean interp r S who ok g₁ (ms_pre ++ δ) (τ_pre ++ blk_hw) →
    ExplainsCli interp r S who ok (σ_pre ++ blk_cli) (τ_pre ++ blk_hw) g₁ (ms_pre ++ δ) ∧
      ¬ ReadCollision interp r S g₁ (ms_pre ++ δ) (τ_pre ++ blk_hw)

/-- Base `init`, `clearSession`, and `leaks` stepping specification for `CliLiveAtCli`. -/
def InitClearLeakSpec : Prop :=
  (∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics},
      ProtocolSetupWF r → SemReady interp' r S →
      ∀ (who : List Participant) (ok : Nat → Bool),
        CliLiveAtCli interp' r S who ok (CliTurn.init (initDirs interp' r)) [] []) ∧
  (∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
      {who : List Participant} {ok : Nat → Bool}
      {t_clean : CliTurn} {accepted : List HwBytes} {σ_acc : List MachineEvent}
      (p : Participant),
      CliLiveAtCli interp' r S who ok t_clean accepted σ_acc →
      CliLiveAtCli interp' r S who ok (t_clean.clearSession r p) accepted σ_acc) ∧
  (∀ {interp' : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
      {who : List Participant} {ok : Nat → Bool}
      {t_clean : CliTurn} {accepted : List HwBytes} {σ_acc leaks : List MachineEvent},
      ProtocolSetupWF r →
      (∀ e ∈ leaks, ∃ k, KeyInDirsV1 r t_clean k ∧ e = .leak k) →
      CliLiveAtCli interp' r S who ok t_clean accepted σ_acc →
      CliLiveAtCli interp' r S who ok t_clean accepted (σ_acc ++ leaks))

/-- Lifting of a `.pt` `PrefixGhosts` memo collision on `τ₁` to
`CollisionAfterExplainedPrefixMoves` on `σ₁ ++ .pt b :: σ₂` under `NoAdjRng σ₁`. -/
def BridgeAPtSpec : Prop :=
  ∀ {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {σ₁ τ₁ σ₂ : List MachineEvent} {b : HwBytes},
    NoAdjRng σ₁ →
    ExplainsCli interp r S who ok σ₁ τ₁ g ms →
    EventMatchesEntry interp r S g (.pt b) (ptEntryOfNextEncrypt r ms) →
    (∀ g' ∈ PrefixGhosts interp r S who g ms τ₁,
      MemoCollisionOn interp r S g' (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms
        (ptEntryOfNextEncrypt r ms).terms) →
    CollisionAfterExplainedPrefixMoves interp r S who ok (σ₁ ++ .pt b :: σ₂)

/-- Transfer of `PureCRel ∧ COpkRelC` across any `CoinSplit` cut `blk'` of `[e, .rng coins]` on a
failed call (`ok (callStarts τ_pre).length = false`). -/
def BridgeBQuietFailSpec : Prop :=
  ∀ {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {τ_pre blk' : List MachineEvent} {e : MachineEvent} {coins : HwBytes},
    ProtocolSetupWF r →
    (eventKind e = .recv ∨ eventKind e = .pt) →
    CoinSplit [e, .rng coins] blk' →
    ok (callStarts τ_pre).length = false →
    PureCRel interp r S who ok records sent accepted τ_pre →
    COpkRelC interp r S who ok opkUsed τ_pre →
    PureCRel interp r S who ok records sent accepted (τ_pre ++ blk') ∧
      COpkRelC interp r S who ok opkUsed (τ_pre ++ blk')

/-- Binary session-decryption hypotheses for whisper or RPK-promote receive steps. -/
def BinarySessionDecryptOk (interp' : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (accepted sent : List HwBytes) (records : Participant → Option HwBytes)
    (me : Participant) (st st' : PqParty) (d_me : DirectorySnapshot)
    (x : RecordExtras) (g_st : GhostState HwBytes)
    (w inner_wire out : HwBytes) (inner : SignalMessage) (rc : BitVec 256) : Prop :=
  (me = r.alice ∨ me = r.bob) ∧
  PqPartyInv interp' P r accepted me st d_me ∧
  PqxdhPartyInSpecDomain P st ∧
  st.session = some (x, g_st) ∧
  records me = some (encodeRecordUnderExtras (fun _ => x) g_st) ∧
  (encodeRecordUnderExtras (fun _ => x) g_st).length < 2 ^ 32 - 2 ^ 20 ∧
  PqFromHonest sent inner_wire ∧
  SignalMessage.tryFrom protoSignalCodec inner_wire = .ok inner ∧
  ((w = wireWhisperTag :: inner_wire ∧
      pqRecvWhisperModel P st inner_wire rc = some (some (st', out))) ∨
    (∃ q, parsePreKeyWire w = some q ∧ inner_wire = q.message ∧
      PqFieldsMatch x g_st q ∧
      pqRecvMatchingFieldsModel P st x g_st q rc = some (some (st', out))))

/-- Receive-collision extraction when `pureDrawsCoins = false` in the binary but the model cut
`τ₂` draws `.rng` before `.accept out`. -/
def BridgeCCaseASpec : Prop :=
  ∀ {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ_pre τ₂ σ_rest : List MachineEvent} {me : Participant}
    {st st' : PqParty} {d_me : DirectorySnapshot} {x : RecordExtras} {g_st : GhostState HwBytes}
    {w inner_wire out rb : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    {g : Ghost} {ms : List Move} {t_rep : _root_.DY.Bytes} {τ₂_tl : List MachineEvent},
    let interp' := interpOfParams interp P
    let S := compSemOf interp' r
    ExternContractsHoldCli interp →
    ModelAgree interp P →
    ProtocolSetupWF r →
    who[(callStarts τ_pre).length]? = some me →
    PureCRel interp' r S who ok records sent accepted τ_pre →
    Clean interp' r S who ok g ms τ_pre →
    BinarySessionDecryptOk interp' P r accepted sent records me st st' d_me x g_st
      w inner_wire out inner rc →
    pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state inner.senderRatchetKey = false →
    t_rep ∈ recvRepresentations interp' r S g ms inner_wire →
    CoinSplit (.rng (HMAC.keyToBytes32 rc) :: .accept out :: σ_rest) τ₂ →
    τ₂ = .rng rb :: τ₂_tl →
    ModelAcceptsTermAfterCoinSplit interp' r S who ok g ms τ_pre (.recv w) τ₂ t_rep →
    RecvCollision interp' r S g ms t_rep

/-- Receive-collision extraction when `pureDrawsCoins = true` in the binary but the model cut
`τ₂` draws no randomness before `.accept out`. -/
def BridgeCCaseBSpec : Prop :=
  ∀ {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ_pre τ₂ σ_rest : List MachineEvent} {me : Participant}
    {st st' : PqParty} {d_me : DirectorySnapshot} {x : RecordExtras} {g_st : GhostState HwBytes}
    {w inner_wire out : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    {g : Ghost} {ms : List Move} {t_rep : _root_.DY.Bytes} {τ₂_tl : List MachineEvent},
    let interp' := interpOfParams interp P
    let S := compSemOf interp' r
    ExternContractsHoldCli interp →
    ModelAgree interp P →
    ProtocolSetupWF r →
    who[(callStarts τ_pre).length]? = some me →
    PureCRel interp' r S who ok records sent accepted τ_pre →
    Clean interp' r S who ok g ms τ_pre →
    BinarySessionDecryptOk interp' P r accepted sent records me st st' d_me x g_st
      w inner_wire out inner rc →
    pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state inner.senderRatchetKey = true →
    t_rep ∈ recvRepresentations interp' r S g ms inner_wire →
    CoinSplit (.rng (HMAC.keyToBytes32 rc) :: .accept out :: σ_rest) τ₂ →
    τ₂ = .accept out :: τ₂_tl →
    ModelAcceptsTermAfterCoinSplit interp' r S who ok g ms τ_pre (.recv w) τ₂ t_rep →
    RecvCollision interp' r S g ms t_rep

end Symbolic.Swarm.Coinsplit.Lift
