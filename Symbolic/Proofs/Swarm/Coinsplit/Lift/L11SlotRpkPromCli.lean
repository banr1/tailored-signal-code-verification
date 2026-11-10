/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromReject
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromSlot
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperCodec
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2HypsPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2Pure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.EntryPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Fail
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HistOpkPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonPath
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.Coinsplit.Lift.L11SlotRpkPromCliRawKn
import Symbolic.Proofs.Swarm.Coinsplit.Probe.P2CrossRunRecv
import Symbolic.Proofs.Swarm.Coinsplit.Probe.P3SuffixExcuses
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure
import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic -- shake: keep
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.MatchedPrefix -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure -- shake: keep
import VCVio.Prelude.Core -- shake: keep

/-!
# Cut-Polymorphic Session-Promote Pre-Key `recv` Slot Refinement

Proves `SlotRpkPromCliSpec`, lifting the matching-session promote branch
(`EligibleForSessionPromotion rec_ c.stdin`) of `slot_rpk_d3_pqModelRel` to cut-polymorphic
`CliLiveAtCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L11

open Symbolic.Swarm.Coinsplit.Lift
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

private theorem coinSplit_append {σ₁ σ₂ τ₁ τ₂ : List MachineEvent}
    (h₁ : CoinSplit σ₁ τ₁) (h₂ : CoinSplit σ₂ τ₂) : CoinSplit (σ₁ ++ σ₂) (τ₁ ++ τ₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | keep hne _ ih => exact .keep hne ih
  | split hne hflat _ ih => rw [List.cons_append, List.append_assoc]; exact .split hne hflat ih

private theorem coinSplit_append_recv_inv {σ_pre σ₂ τ' : List MachineEvent} {w : HwBytes}
    (hcs : CoinSplit (σ_pre ++ .recv w :: σ₂) τ') :
    ∃ τ'_pre τ₂, τ' = τ'_pre ++ .recv w :: τ₂ ∧ CoinSplit σ_pre τ'_pre ∧ CoinSplit σ₂ τ₂ := by
  induction σ_pre generalizing τ' with
  | nil => cases hcs with | keep _ h₂ => exact ⟨[], _, rfl, .nil, h₂⟩
  | cons e σ_rest ih =>
    cases hcs with
    | keep hne hrest =>
      obtain ⟨τ'_pre, τ₂, rfl, hpre, h₂⟩ := ih hrest
      exact ⟨e :: τ'_pre, τ₂, rfl, .keep hne hpre, h₂⟩
    | @split _ pieces _ _ hne hflat hrest =>
      obtain ⟨τ'_pre, τ₂, rfl, hpre, h₂⟩ := ih hrest
      exact ⟨pieces.map .rng ++ τ'_pre, τ₂, by simp [List.append_assoc], .split hne hflat hpre, h₂⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool} {ms₁ ms₂ : List Move}
    (hof : OutcomeFaithfulCli r ok (ms₁ ++ ms₂)) (hof₁ : OutcomeFaithful r ok ms₁) :
    OutcomeFaithfulCli r ok ms₁ := by
  refine ⟨hof₁, fun i m hget => ?_⟩
  have hi : i < ms₁.length := (List.getElem?_eq_some_iff.mp hget).1
  have h := hof.2 i m (by rw [List.getElem?_append_left hi]; exact hget)
  dsimp only at h ⊢
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi)] at h

private theorem rngLengthsFaithfulCli_prefix {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms₁ ms₂ : List Move}
    (hrng : RngLengthsFaithfulCli interp r S g (ms₁ ++ ms₂)) :
    RngLengthsFaithfulCli interp r S g ms₁ := by
  intro i m hget
  have hi : i < ms₁.length := (List.getElem?_eq_some_iff.mp hget).1
  have h := hrng i m (by rw [List.getElem?_append_left hi]; exact hget)
  dsimp only at h ⊢
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi)] at h

private theorem explainsCli_prefix_of_recv_split {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {σ_pre σ₂ τ'_pre τ₂ : List MachineEvent} {w : HwBytes} {g' : Ghost} {ms' : List Move}
    (hex' : ExplainsCli interp r S who ok (σ_pre ++ .recv w :: σ₂) (τ'_pre ++ .recv w :: τ₂) g' ms')
    (hnrc' : ¬ ReadCollision interp r S g' ms' (τ'_pre ++ .recv w :: τ₂))
    (hcs_pre : CoinSplit σ_pre τ'_pre) :
    ∃ ms₀ δ, ms' = ms₀ ++ δ ∧ ExplainsCli interp r S who ok σ_pre τ'_pre g' ms₀ ∧
      ¬ ReadCollision interp r S g' ms₀ τ'_pre ∧ XplBlock interp r S who g' ms₀ δ τ'_pre (.recv w :: τ₂) := by
  have hc' : Clean interp r S who ok g' ms' (τ'_pre ++ (.recv w :: τ₂)) := explainsCli_toClean hex' hnrc'
  have hhead : ∀ e ∈ (MachineEvent.recv w :: τ₂).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he; subst he; exact Or.inl rfl
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hc'.matched hhead (matchedPrefix_prefix_reachable hc'.matched)
  have hc₀ : Clean interp r S who ok g' ms₀ τ'_pre := clean_prefix (matchedPrefix_length_eq hpre) hc'
  exact ⟨ms₀, δ, rfl, ⟨hcs_pre, hc₀.matched, outcomeFaithfulCli_prefix hex'.2.2.1 hc₀.1.2,
    rngLengthsFaithfulCli_prefix hex'.2.2.2⟩, hc₀.2, ⟨hpre, hc'.matched.2.1, hmatch⟩⟩

private def CliSlotPostCore (NC : List Participant → (Nat → Bool) → Prop)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
    (accepted : List HwBytes) (σ_pre : List MachineEvent) : Prop :=
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let blk_cli := cliEntryEvents c ++ cliExitEvents c code out
  ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
    PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
    ∀ (who : List Participant) (ok : Nat → Bool),
      who[(callStarts σ_pre).length]? = some c.party →
      CliLiveAtCli interp' r S who ok t_clean accepted σ_pre →
      NC who ok →
      (∃ τ_out g ms, CoinSplit (σ_pre ++ blk_cli) τ_out ∧
          MatchedPrefix interp' r S who g ms τ_out) ∧
        (ok (callStarts σ_pre).length = decide (code = 0) →
          CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli))

/-- Cut-local non-collision hypothesis: on exit `0`, `SignalMsgAcceptedOnlyViaCollisionMoves`
fails at the call's own cut for every clean explanation of `σ_pre`. -/
def RpkPromNC (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (c : CliCall) (code : Nat) (out : HwBytes) (q : PreKeyFields)
    (σ_pre : List MachineEvent) (who : List Participant) (ok : Nat → Bool) : Prop :=
  code = 0 →
  ∀ τ₁ g ms, ExplainsCli interp' r S who ok σ_pre τ₁ g ms →
    ¬ ReadCollision interp' r S g ms τ₁ →
    ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g ms σ_pre (.recv c.stdin)
        [.rng c.coins, .accept out] q.message

private def RpkPromNCWeak (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (c : CliCall) (code : Nat) (out : HwBytes) (q : PreKeyFields)
    (σ_pre : List MachineEvent) (who : List Participant) (ok : Nat → Bool) : Prop :=
  code = 0 →
  ∀ τ₁ g ms, ExplainsCli interp' r S who ok σ_pre τ₁ g ms →
    ¬ ReadCollision interp' r S g ms τ₁ →
    KnownBaseKey interp' r S g ms q →
    ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g ms σ_pre (.recv c.stdin)
        [.rng c.coins, .accept out] q.message

private theorem slot_rpk_prom_reject_cli
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r)
    {t : CliTurn} {c : CliCall} {peer : Address} {stB : PqParty}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hDir : PqDirInv (interpOfParams interp P) P r t accepted)
    (hoff : t.bobOff = false)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv peer)
    (hinvB : PqPartyInv (interpOfParams interp P) P r accepted r.bob stB (t.dirs r.bob))
    (s_in : HwBytes) (rc : BitVec 256) :
    CliSlotPostCore (fun _ _ => True) interp P r t t c 1 []
      (filesOf (pqRecvInputs P stB s_in rc).files) accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let blk_cli := cliEntryEvents c ++ cliExitEvents c 1 []
  have hscr : scrub (filesOf (pqRecvInputs P stB s_in rc).files) = t.dirs c.party := by
    rw [hbob, hinvB.dir_eq]
    exact scrub_filesOf_pqInputs_reject P stB _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hafter : CliTurn.after t r c 1 [] (filesOf (pqRecvInputs P stB s_in rc).files) = t :=
    afterD3_eq_self_of_recv_exit1 hcmd hscr
  have hblk_eq : blk_cli = [.recv c.stdin, .rng c.coins] := by
    dsimp [blk_cli]
    rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]
    simp [toCliCallNone, cliEntryEvents, cliExitEvents, hcmd]
  have hcs_blk : CoinSplit blk_cli [.recv c.stdin] := by
    rw [hblk_eq]
    exact CoinSplit.keep (fun _ h => by cases h)
      (CoinSplit.split (pieces := []) (by simp) List.nil_prefix CoinSplit.nil)
  refine ⟨t, accepted, by rw [hafter]; exact pqTurnSim1A_refl hDir hoff,
    fun who ok _hwho hlive _ => ?_⟩
  obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
  have hc₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
  have hcs_out : CoinSplit (σ_pre ++ blk_cli) (τ_acc ++ [.recv c.stdin]) :=
    coinSplit_append hex₀.1 hcs_blk
  refine ⟨?_, fun hok_eq => ?_⟩
  · cases hparse : parsePreKeyWire c.stdin with
    | none =>
      exact ⟨τ_acc ++ [.recv c.stdin], g₀, ms₀ ++ [.reject []], hcs_out,
        Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject c.stdin [] hc₀.matched
          (rpkProm_unparseable_path_fail hparse [] hc₀)⟩
    | some _ =>
      exact ⟨τ_acc ++ [.recv c.stdin], g₀,
        Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []], hcs_out,
        Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject c.stdin []
          (rpkProm_sanitize_clean hc₀).matched (rpkProm_sanitize_path_fail c.stdin [] hc₀)⟩
  · have hok_f : ok (callStarts σ_pre).length = false := by simpa using hok_eq
    have hok_acc : ok (callStarts τ_acc).length = false := by
      rwa [coinSplit_callStarts_length_eq hex₀.1]
    have hnoAdj_blk : NoAdjRng blk_cli := by
      rw [hblk_eq]; exact ⟨Or.inl (by simp [eventKind]), trivial⟩
    have hnoAdj_all : NoAdjRng (σ_pre ++ blk_cli) :=
      noAdjRng_append_of_head_nonRng hlive.noAdjRng hnoAdj_blk (by
        rw [hblk_eq]; intro y hy; simp only [List.head?_cons, Option.some.injEq] at hy; subst hy; simp [eventKind])
    have hwit : ∃ τ_out g₁ ms₁,
        ExplainsCli interp' r S who ok (σ_pre ++ blk_cli) τ_out g₁ ms₁ ∧
        ¬ ReadCollision interp' r S g₁ ms₁ τ_out := by
      cases hparse : parsePreKeyWire c.stdin with
      | none =>
        have hc' := Symbolic.Swarm.Leaves.IC12Stage1MP.clean_snoc_reject c.stdin []
          ⟨hc₀.1, hc₀.2⟩ (rpkProm_unparseable_path_fail hparse [] hc₀) hok_acc
        have hg := hGood hex₀ hcs_blk (.callRecvFail hok_acc) (Or.inl rfl)
          (fun _ _ _ => rfl) ⟨hc'.1, hc'.2⟩
        exact ⟨τ_acc ++ [.recv c.stdin], g₀, ms₀ ++ [.reject []], hg.1, hg.2⟩
      | some _ =>
        have hc_s := rpkProm_sanitize_clean hc₀
        have hc' := Symbolic.Swarm.Leaves.IC12Stage1MP.clean_snoc_reject c.stdin []
          ⟨hc_s.1, hc_s.2⟩ (rpkProm_sanitize_path_fail c.stdin [] hc₀) hok_acc
        have hg := hGood hex₀ hcs_blk (.callRecvFail hok_acc) (Or.inr rfl)
          (fun _ _ _ => rfl) ⟨hc'.1, hc'.2⟩
        exact ⟨τ_acc ++ [.recv c.stdin], g₀,
          Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []], hg.1, hg.2⟩
    refine ⟨hnoAdj_all, hwit, fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
    have hex'_eq : ExplainsCli interp' r S who ok (σ_pre ++ [.recv c.stdin, .rng c.coins]) τ' g' ms' := by
      rwa [← hblk_eq]
    obtain ⟨τ'_pre, τ₂, rfl, hcs_pre, hcs₂⟩ := coinSplit_append_recv_inv hex'_eq.1
    obtain ⟨ms₀', _δ', _, hex_pre, hnrc_pre, _⟩ :=
      explainsCli_prefix_of_recv_split hex'_eq hnrc' hcs_pre
    obtain ⟨hrel_pre, hopk_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms₀', hex_pre, hnrc_pre⟩
    have hok_pre : ok (callStarts τ'_pre).length = false := by
      rwa [coinSplit_callStarts_length_eq hcs_pre]
    exact hB hwf (Or.inl rfl) (CoinSplit.keep (fun _ h => by cases h) hcs₂) hok_pre hrel_pre hopk_pre

private theorem coinSplit_prom_tail (draw : Bool) {coins out : HwBytes}
    (hne : coins ≠ []) :
    CoinSplit [.rng coins, .accept out]
      ((if draw then [MachineEvent.rng coins] else []) ++ [.accept out]) := by
  cases draw
  · exact CoinSplit.split (pieces := []) (by simp) List.nil_prefix
      (CoinSplit.keep (fun _ h => by cases h) CoinSplit.nil)
  · exact CoinSplit.split (pieces := [coins])
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hne)
      (by simp)
      (CoinSplit.keep (fun _ h => by cases h) CoinSplit.nil)

private theorem coinSplit_prom_blk (draw : Bool) {w coins out : HwBytes}
    (hne : coins ≠ []) :
    CoinSplit [.recv w, .rng coins, .accept out]
      (.recv w :: ((if draw then [MachineEvent.rng coins] else []) ++ [.accept out])) :=
  CoinSplit.keep (fun _ h => by cases h) (coinSplit_prom_tail draw hne)

private theorem noAdjRng_prom_accept_blk (w coins out : HwBytes) :
    NoAdjRng [.recv w, .rng coins, .accept out] :=
  ⟨Or.inl (by simp [eventKind]), Or.inr (by simp [eventKind]), trivial⟩

section Accept

cref_open
open _root_.DY.Libsignal.HwEvents (StateAndMessage)
open _root_.DY.Libsignal.Composed

private theorem prom_explains_pin_ok_end
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms : List Move} {acc : List MachineEvent}
    (hf : ExplainsMoves interpretation r S who ok g ms acc) :
    ExplainsMoves interpretation r S who
      (fun k => if k = (callStarts acc).length then true else ok k) g ms acc := by
  refine ⟨hf.1, fun i m hi => ?_⟩
  have hlt : i < ms.length := (List.getElem?_eq_some_iff.mp hi).1
  have hcc_ms : callCount (runVis r ms) = (callStarts acc).length :=
    prom_callCount_of_forall₂ hf.1.2.2.2.2.2
  by_cases hk : callCount (runVis r (ms.take i)) = (callStarts acc).length
  · refine ⟨fun ds hrej => ?_, fun _ => by simp only [hk, ↓reduceIte]⟩
    subst hrej
    have hsplit : ms = ms.take i ++ Move.reject ds :: ms.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i ms, ← List.cons_getElem_drop_succ (h := hlt)]
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
      rw [hi]
    have hvis : runVis r ms =
        runVis r (ms.take i) ++
          (runMoves (Move.reject ds :: ms.drop (i + 1)) (runTraceMoves r (ms.take i))).2 := by
      conv_lhs => rw [hsplit]
      exact Symbolic.Swarm.CREF.TR.runVis_append r (ms.take i) _
    have hcc_pos : 1 ≤
        callCount (runMoves (Move.reject ds :: ms.drop (i + 1)) (runTraceMoves r (ms.take i))).2 := by
      rw [runMoves_cons_snd, Symbolic.Swarm.CREF.callCount_append]
      have h1 : 1 ≤ callCount ((Move.reject ds).vis (runTraceMoves r (ms.take i))) := by
        simp [Move.vis, callCount]
      omega
    have htot := congrArg callCount hvis
    rw [Symbolic.Swarm.CREF.callCount_append, hcc_ms, hk] at htot
    omega
  · obtain ⟨h1, h2⟩ := hf.2 i m hi
    refine ⟨fun ds hrej => ?_, fun hal => ?_⟩
    · simp only [hk, ↓reduceIte]; exact h1 ds hrej
    · simp only [hk, ↓reduceIte]; exact h2 hal

private theorem cBad_promCli_reselect_full {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g₁ : Ghost} {ms₁ : List Move} {σ₁ : List MachineEvent}
    {body coins pt : HwBytes} {pf : PreKeyFields} {t₁ : _root_.DY.Bytes}
    (ht₁ : t₁ ∈ recvRepresentations interp r S g₁ ms₁ pf.message)
    (hnot_exc : ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp r S who ok g₁ ms₁ σ₁
      (.recv (wirePrekey :: body)) [.rng coins, .accept pt] pf.message) :
    ∃ (τ₁' : List MachineEvent) (g' : Ghost) (ms' : List Move) (t' : _root_.DY.Bytes),
      ExplainsCli interp r S who ok σ₁ τ₁' g' ms' ∧
      ¬ ReadCollision interp r S g' ms' τ₁' ∧
      t' ∈ recvRepresentations interp r S g' ms' pf.message ∧
      ¬ RecvCollision interp r S g' ms' t' ∧
      ¬ ReselectCollision interp r S g' ms' t' ∧
      ¬ ((∃ t ∈ recvRepresentations interp r S g' ms' pf.message,
            ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
              (.recv (wirePrekey :: body)) [.rng coins, .accept pt] t) ∧
          ∀ t ∈ recvRepresentations interp r S g' ms' pf.message,
            ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
              (.recv (wirePrekey :: body)) [.rng coins, .accept pt] t →
            RecvCollision interp r S g' ms' t) := by
  refine Classical.byContradiction fun hno => hnot_exc ⟨⟨t₁, ht₁⟩, fun τ₁' g' ms' hex' hnrc' => ?_⟩
  by_cases hac :
      (∃ t ∈ recvRepresentations interp r S g' ms' pf.message,
        ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
          (.recv (wirePrekey :: body)) [.rng coins, .accept pt] t) ∧
      ∀ t ∈ recvRepresentations interp r S g' ms' pf.message,
        ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
          (.recv (wirePrekey :: body)) [.rng coins, .accept pt] t →
        RecvCollision interp r S g' ms' t
  · exact Or.inr hac
  · refine Or.inl fun t' ht' => Classical.byContradiction fun hnc => ?_
    exact hno ⟨τ₁', g', ms', t', hex', hnrc', ht',
      fun hc => hnc (Or.inl hc), fun hrs => hnc (Or.inr hrs), hac⟩

private theorem not_acceptCollision_prom_of_bridgeC
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ₁' : List MachineEvent}
    {stB st' : PqParty} {d_bob : DirectorySnapshot} {x : RecordExtras} {g_st : GhostState HwBytes}
    {body pt : HwBytes} {q : PreKeyFields} {rc : BitVec 256}
    {g' : Ghost} {ms' : List Move}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hwf : ProtocolSetupWF r)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (hwho : who[(callStarts τ₁').length]? = some r.bob)
    (hrel : PureCRel (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok records sent accepted τ₁')
    (hc' : Clean (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok g' ms' τ₁')
    (hbin : BinarySessionDecryptOk (interpOfParams interp P) P r accepted sent records r.bob stB st'
      d_bob x g_st (wirePrekey :: body) q.message pt q.inner rc)
    (hnac_cli : ¬ ((∃ t ∈ recvRepresentations (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) g' ms' q.message,
          ModelAcceptsTermAfterAttackerSendsMoves (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            who ok g' ms' τ₁' (.recv (wirePrekey :: body))
            [.rng (HMAC.keyToBytes32 rc), .accept pt] t) ∧
        ∀ t ∈ recvRepresentations (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) g' ms' q.message,
          ModelAcceptsTermAfterAttackerSendsMoves (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            who ok g' ms' τ₁' (.recv (wirePrekey :: body))
            [.rng (HMAC.keyToBytes32 rc), .accept pt] t →
          RecvCollision (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            g' ms' t)) :
    ¬ AcceptCollision (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
        who ok g' ms' τ₁' (.recv (wirePrekey :: body))
        (rpkPromMid (interpOfParams interp P) x g_st q.inner (HMAC.keyToBytes32 rc) ++
          [.accept pt]) q.message := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let coins := HMAC.keyToBytes32 rc
  have hcoins_len : coins.length = 32 := Slots.keyToBytes32_length rc
  have hcoins_ne : coins ≠ [] := Slots.keyToBytes32_ne_nil rc
  have hcs_drop : CoinSplit [.rng coins, .accept pt] ([] ++ [.accept pt]) :=
    coinSplit_prom_tail false hcoins_ne
  have hcs_full : CoinSplit [.rng coins, .accept pt] ([.rng coins] ++ [.accept pt]) :=
    coinSplit_prom_tail true hcoins_ne
  have hmid_eq : rpkPromMid interp' x g_st q.inner coins =
      (if pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey then
        [.rng coins] else []) := rfl
  rw [hmid_eq]
  rintro ⟨⟨t₁, ht₁, hacc₁⟩, hall_col⟩
  have hcs_mid : CoinSplit [.rng coins, .accept pt]
      ((if pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey then
        [MachineEvent.rng coins] else []) ++ [.accept pt]) :=
    coinSplit_prom_tail _ hcoins_ne
  apply hnac_cli
  refine ⟨⟨t₁, ht₁, _, hcs_mid, hacc₁⟩, fun t₂ ht₂ hacc_cli₂ => ?_⟩
  by_contra hncol₂
  have htwo := (Symbolic.Swarm.Coinsplit.P3.acceptsViaCli_iff_two_mids
    (σ_rest := []) hcoins_len).mp hacc_cli₂
  cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey
  · simp only [hdraw, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hall_col
    rcases htwo with h0 | h32
    · exact hncol₂ (hall_col t₂ ht₂ h0)
    · exact hncol₂ (hCA hext hagree hwf hwho hrel hc' hbin hdraw ht₂ hcs_full rfl h32)
  · simp only [hdraw, ↓reduceIte, List.cons_append, List.nil_append] at hall_col
    rcases htwo with h0 | h32
    · exact hncol₂ (hCB hext hagree hwf hwho hrel hc' hbin hdraw ht₂ hcs_drop rfl h0)
    · exact hncol₂ (hall_col t₂ ht₂ h32)

private theorem prom_make_acceptCall
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc_hw mid : List MachineEvent} {rec_ b rec' pt : HwBytes}
    {pf : PreKeyFields} {sess sess' : Session HwBytes}
    {coins : BitVec 256} {expected : Option HwBytes}
    (hwf : ProtocolSetupWF r)
    (hwho : who[(callStarts acc_hw).length]? = some r.bob)
    (hrec : records r.bob = some rec_)
    (hlen : rec_.length < 2 ^ 32 - 2 ^ 20)
    (hpm : EligibleForSessionPromotion rec_ b)
    (hhon : HonestIdentity interp r b)
    (hpqh : ∀ q₀, parsePreKeyWire b = some q₀ → PqFromHonest sent q₀.message)
    (hclean : ∃ g ms, Clean interp r S who ok g ms acc_hw)
    (hrel : PureCRel interp r S who ok records sent accepted acc_hw)
    (hopk : COpkRelC interp r S who ok opkUsed acc_hw)
    (hout : PromPureAcceptOut interp r rec_ b rec' mid pt pf sess sess' coins expected) :
    PromAcceptCall interp r S who ok (callStarts acc_hw).length ⟨records, sent, accepted, opkUsed⟩
      mid acc_hw rec_ b { state := rec', message := List.replicate 47 0#8 ++ pt }
      pf sess sess' coins expected pt :=
  { entry := prom_entry_hyps_pure hwf ⟨hclean, hrel, hopk⟩ hwho hrec hlen hpm hhon hpqh
    hj := rfl
    out :=
      { hpf := hout.hpf
        hcan_in := hout.hcan_in
        hcoins := hout.hcoins
        hdecOk := hout.hdecOk
        hexec := hout.hexec
        halice := hout.halice
        hpend := hout.hpend
        hkyb := hout.hkyb
        hstate := hout.hstate
        hmsg := rfl
        hwrc := hout.hwrc
        hcanon_out := hout.hcanon_out }
    ver := hout.hver
    nodraw := hout.hnodraw }

set_option maxHeartbeats 400000 in
private theorem prom_cut_tau2_eq_mid
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {e' : PromTurn} {τ'_pre τ₂ mid : List MachineEvent}
    {stB st' : PqParty} {d_bob : DirectorySnapshot} {x : RecordExtras} {g_st : GhostState HwBytes}
    {rec_ body out : HwBytes} {sm : StateAndMessage} {q : PreKeyFields}
    {sess sess' : Session HwBytes} {coins_out rc : BitVec 256} {expected : Option HwBytes}
    {g' : Ghost} {ms'_pre δ : List Move}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hwf : ProtocolSetupWF r)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (hwho : who[(callStarts τ'_pre).length]? = some r.bob)
    (hC_τ' : PromAcceptCall (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok (callStarts τ'_pre).length e' mid τ'_pre rec_ (wirePrekey :: body)
      sm q sess sess' coins_out expected out)
    (hc'_pre : Clean (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok g' ms'_pre τ'_pre)
    (hc_ext : Clean (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok g' (ms'_pre ++ δ) (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)))
    (hB_blk : XplBlock (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who g' ms'_pre δ τ'_pre (.recv (wirePrekey :: body) :: τ₂))
    (hrng_cli : RngLengthsFaithfulCli (interpOfParams interp P) r
      (compSemOf (interpOfParams interp P) r) g' (ms'_pre ++ δ))
    (hcs₂ : CoinSplit [.rng (HMAC.keyToBytes32 rc), .accept out] τ₂)
    (hbin : BinarySessionDecryptOk (interpOfParams interp P) P r e'.accepted e'.sent e'.records
      r.bob stB st' d_bob x g_st (wirePrekey :: body) q.message out q.inner rc) :
    τ₂ = rpkPromMid (interpOfParams interp P) x g_st q.inner (HMAC.keyToBytes32 rc) ++
      [.accept out] := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let coins := HMAC.keyToBytes32 rc
  have hcoins_len : coins.length = 32 := Slots.keyToBytes32_length rc
  have hcoins_ne : coins ≠ [] := Slots.keyToBytes32_ne_nil rc
  have hrel_pre : PureCRel interp' r S who ok e'.records e'.sent e'.accepted τ'_pre :=
    hC_τ'.entry.ready.2.1
  have hτ₂_pieces : ∃ pieces : List HwBytes, τ₂ = pieces.map .rng ++ [.accept out] := by
    cases hcs₂ with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ pieces _ τ_after _ _ hcs_after =>
      cases hcs_after with
      | @keep _ _ τ_nil _ hcs_nil =>
        cases hcs_nil
        exact ⟨pieces, rfl⟩
  obtain ⟨pieces, hτ₂_eq⟩ := hτ₂_pieces
  have hhead : ∀ e ∈ (MachineEvent.recv (wirePrekey :: body) :: τ₂).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hne_blk : (MachineEvent.recv (wirePrekey :: body) :: τ₂) ≠ [] := by simp
  have htail : ∀ e ∈ (MachineEvent.recv (wirePrekey :: body) :: τ₂).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [List.tail_cons, hτ₂_eq, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨bs, _, rfl⟩ | rfl <;> simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨_hs, ha0, hm0⟩, hpost⟩ :=
    xpl_oneMove hB_blk hhead hne_blk htail
  have hrun_pre : (runMoves pre (runTraceMoves r ms'_pre)).1 = runTraceMoves r (ms'_pre ++ pre) :=
    (Symbolic.Swarm.CREF.TR.runTrace_append r ms'_pre pre).symm
  have ha : m.LogsSessionCompletion (runTraceMoves r (ms'_pre ++ pre)) := hrun_pre ▸ ha0
  have hm_vis : List.Forall₂ (EventMatchesEntry interp' r S g')
      (.recv (wirePrekey :: body) :: τ₂) (m.vis (runTraceMoves r (ms'_pre ++ pre))) :=
    hrun_pre ▸ hm0
  obtain ⟨v0, hv0, hv0k, _⟩ := xpl_head_entry hm_vis rfl
  have hrk := xpl_recvHeadKind m (runTraceMoves r (ms'_pre ++ pre)) hv0 hv0k
  have hacc_mem : MachineEvent.accept out ∈
      (MachineEvent.recv (wirePrekey :: body) :: τ₂) := by
    simp [hτ₂_eq]
  obtain ⟨v_acc, hv_acc, hev_acc⟩ := xpl_forall₂_mem_left hm_vis (.accept out) hacc_mem
  have hv_acck : v_acc.kind = .accept := by
    rw [xpl_kind_of_matches hev_acc]; rfl
  obtain ⟨hpre_vis, _⟩ := prom_invisible_nil pre (runTraceMoves r ms'_pre) hpre
  obtain ⟨hpost_vis, _⟩ :=
    prom_invisible_nil post (m.next (runMoves pre (runTraceMoves r ms'_pre)).1) hpost
  have hm_dec : (∃ p sIdx mIdx pqIdx spIdx w, m = .decrypt p sIdx mIdx pqIdx spIdx w) ∨
      (∃ p sIdx mIdx skIdx pqIdx spIdx w, m = .decryptSkipped p sIdx mIdx skIdx pqIdx spIdx w) := by
    cases m with
    | aliceStart a _ _ _ _ _ =>
      rcases xpl_accept_by (p := a) _ _ hv_acc hv_acck (Or.inr rfl) with h | h <;> cases h
    | bobStart b pbk otpk pqpk msgIdx w spIdx opIdx =>
      let mb : Move := .bobStart b pbk otpk pqpk msgIdx w spIdx opIdx
      exfalso
      have hi : (ms'_pre ++ (pre ++ mb :: post))[ms'_pre.length + pre.length]? = some mb := by
        rw [← List.append_assoc, List.getElem?_append_right (by simp)]; simp
      have htake : (ms'_pre ++ (pre ++ mb :: post)).take (ms'_pre.length + pre.length) =
          ms'_pre ++ pre := by
        rw [← List.append_assoc]; exact List.take_left' (by simp)
      have hcc : callCount (runVis r ((ms'_pre ++ (pre ++ mb :: post)).take
          (ms'_pre.length + pre.length))) = (callStarts τ'_pre).length := by
        rw [htake, Symbolic.Swarm.CREF.TR.runVis_append, hpre_vis, List.append_nil]
        exact matchedPrefix_callCount_eq hB_blk.pre
      have hcs_tail : ∀ ps : List HwBytes,
          callStarts (ps.map MachineEvent.rng ++ [.accept out]) = [] := by
        intro ps; induction ps with
        | nil => rfl
        | cons _ _ ih => exact ih
      have hcall : (callStarts (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)))[
          callCount (runVis r ((ms'_pre ++ (pre ++ mb :: post)).take
            (ms'_pre.length + pre.length)))]? = some (.recv (wirePrekey :: body)) := by
        rw [hcc, Symbolic.Swarm.CREF.callStarts_append,
          show callStarts (.recv (wirePrekey :: body) :: τ₂) =
            [.recv (wirePrekey :: body)] by
              rw [hτ₂_eq]; exact congrArg (MachineEvent.recv _ :: ·) (hcs_tail pieces),
          List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
      obtain ⟨ek, hek, heq⟩ := promXpl_hbka_of_acceptCallBy₂ hC_τ' hc'_pre
      have hq1 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt
          (runTraceMoves r ms'_pre) (runTraceMoves r (ms'_pre ++ pre)) := by
        rw [Symbolic.Swarm.CREF.TR.runTrace_append]
        exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ pre
          (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
      have hdone : ∃ ek ∈ bobDoneBaseKeys
          (runTraceMoves r ((ms'_pre ++ (pre ++ mb :: post)).take (ms'_pre.length + pre.length))),
          ecKey (gamma interp' S g' ek) = q.baseKey.take 33 := by
        rw [htake, Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_bobDoneBaseKeys hq1]
        exact ⟨ek, hek, heq⟩
      exact Symbolic.Swarm.CREF.TR.G1.Spine.not_bobStart_of_bobDone
        hc_ext.path hi hcall hC_τ'.out.hpf hdone rfl
    | decrypt p sIdx mIdx pqIdx spIdx w => exact Or.inl ⟨p, sIdx, mIdx, pqIdx, spIdx, w, rfl⟩
    | decryptSkipped p sIdx mIdx skIdx pqIdx spIdx w =>
      exact Or.inr ⟨p, sIdx, mIdx, skIdx, pqIdx, spIdx, w, rfl⟩
    | reject _ =>
      rcases xpl_accept_by (p := r.alice) _ _ hv_acc hv_acck (Or.inl rfl) with h | h <;> cases h
    | _ => exact False.elim hrk
  have hread : isReadMove m = true := by
    rcases hm_dec with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ <;> rfl
  have hexp_nil : exposures (runTraceMoves r (ms'_pre ++ pre))
      (m.next (runTraceMoves r (ms'_pre ++ pre))) = [] := by
    cases hexp : exposures (runTraceMoves r (ms'_pre ++ pre))
        (m.next (runTraceMoves r (ms'_pre ++ pre))) with
    | nil => rfl
    | cons v_leak vtl =>
      have hv_mem_exp : v_leak ∈ exposures (runTraceMoves r (ms'_pre ++ pre))
          (m.next (runTraceMoves r (ms'_pre ++ pre))) := by simp [hexp]
      have hv_mem_vis : v_leak ∈ m.vis (runTraceMoves r (ms'_pre ++ pre)) := by
        rw [xpl_vis_eq]; exact List.mem_append_right _ hv_mem_exp
      obtain ⟨ev_l, hev_l_mem, hev_l_match⟩ := xpl_forall₂_mem_right hm_vis v_leak hv_mem_vis
      have hev_lk : eventKind ev_l = .leak := by
        rw [← xpl_kind_of_matches hev_l_match]
        exact xpl_exposures_kind hv_mem_exp
      simp only [List.mem_cons] at hev_l_mem
      rcases hev_l_mem with rfl | htl_mem
      · simp [eventKind] at hev_lk
      · exact ((htail ev_l htl_mem).2.2 hev_lk).elim
  have hrng_m : ∀ (v : VisEntry) (t : _root_.DY.Bytes),
      v ∈ m.vis (runTraceMoves r (ms'_pre ++ pre)) → v.kind = .rng → v.layout = .single →
      v.terms = [t] → (gamma interp' S g' t).length = 32 := by
    have hidx : (ms'_pre ++ (pre ++ m :: post))[(ms'_pre ++ pre).length]? = some m := by
      rw [← List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    have htake : (ms'_pre ++ (pre ++ m :: post)).take (ms'_pre ++ pre).length =
        ms'_pre ++ pre := by
      rw [← List.append_assoc, List.take_left]
    have h := hrng_cli (ms'_pre ++ pre).length m hidx
    dsimp only at h
    rw [htake] at h
    exact h (List.any_eq_true.mpr ⟨v0, hv0, by rw [hv0k]; rfl⟩)
  have hcs_blk' : CoinSplit [.recv (wirePrekey :: body), .rng coins, .accept out]
      (.recv (wirePrekey :: body) :: τ₂) :=
    .keep (fun _ h => by cases h) hcs₂
  have hdich := (Symbolic.Swarm.Coinsplit.P2.accepted_recv_blk_dichotomy_of_rngLengths
    hcoins_len hrng_m hread ha hexp_nil hcs_blk' hm_vis).1
  have hτ₂_dich : τ₂ = [.accept out] ∨ τ₂ = [.rng coins, .accept out] := by
    rcases hdich with h2 | h3
    · exact Or.inl (List.cons.inj h2).2
    · exact Or.inr (List.cons.inj h3).2
  have hvis_pre2 : runVis r (ms'_pre ++ pre) = runVis r ms'_pre := by
    rw [Symbolic.Swarm.CREF.TR.runVis_append, hpre_vis, List.append_nil]
  have hlen_pre2 : τ'_pre.length = (runVis r (ms'_pre ++ pre)).length :=
    hB_blk.pre.2.2.2.2.2.length_eq.trans (congrArg List.length hvis_pre2).symm
  have hms_assoc1 : ms'_pre ++ (pre ++ m :: post) = (ms'_pre ++ pre) ++ (m :: post) :=
    (List.append_assoc ms'_pre pre (m :: post)).symm
  have hc_ext' : Clean interp' r S who ok g' ((ms'_pre ++ pre) ++ (m :: post))
      (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)) := by
    rwa [← hms_assoc1]
  have hc_pre2 : Clean interp' r S who ok g' (ms'_pre ++ pre) τ'_pre :=
    clean_prefix hlen_pre2 hc_ext'
  have hvis_eq : runVis r ((ms'_pre ++ pre) ++ (m :: post)) =
      runVis r ((ms'_pre ++ pre) ++ [m]) := by
    have hm_post : m :: post = [m] ++ post := rfl
    rw [hm_post, ← List.append_assoc, Symbolic.Swarm.CREF.TR.runVis_append]
    have htr_m : runTraceMoves r ((ms'_pre ++ pre) ++ [m]) =
        m.next (runMoves pre (runTraceMoves r ms'_pre)).1 := by
      rw [Symbolic.Swarm.CREF.TR.runTrace_snoc, hrun_pre]
    rw [htr_m, hpost_vis, List.append_nil]
  have hlen_m : (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)).length =
      (runVis r ((ms'_pre ++ pre) ++ [m])).length :=
    hc_ext'.1.1.2.2.2.2.2.length_eq.trans (congrArg List.length hvis_eq)
  have hc_m : Clean interp' r S who ok g' ((ms'_pre ++ pre) ++ [m])
      (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)) := by
    have hms_assoc2 : ms'_pre ++ (pre ++ m :: post) = ((ms'_pre ++ pre) ++ [m]) ++ post := by
      simp [List.append_assoc]
    have hc_ext'' : Clean interp' r S who ok g' (((ms'_pre ++ pre) ++ [m]) ++ post)
        (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)) := by
      rwa [← hms_assoc2]
    have hc_ext''' : Clean interp' r S who ok g' (((ms'_pre ++ pre) ++ [m]) ++ post)
        ((τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)) ++ []) := by
      rw [List.append_nil]; exact hc_ext''
    exact clean_prefix hlen_m hc_ext'''
  have hdec_vis_none : ∀ sIdx mIdx w,
      (runTraceMoves r (ms'_pre ++ pre)).getMessageSentAt mIdx = none →
      v0 ∈ decVis (runTraceMoves r (ms'_pre ++ pre))
        (m.next (runTraceMoves r (ms'_pre ++ pre))) sIdx mIdx w → False := by
    intro sIdx mIdx w hnone hv
    cases hpt : receivedPlaintext (runTraceMoves r (ms'_pre ++ pre))
        (m.next (runTraceMoves r (ms'_pre ++ pre))) <;>
      simp [decVis, hnone, hpt, rngEntry] at hv
    · obtain ⟨_, _, _, rfl⟩ := hv; cases hv0k
    · rcases hv with ⟨_, _, _, rfl⟩ | rfl <;> cases hv0k
  obtain ⟨msgIdx, hm_idx, t_rep, hget_rep⟩ :
      ∃ msgIdx, m.decryptMsgIdx? = some msgIdx ∧
        ∃ t_rep, (runTraceMoves r (ms'_pre ++ pre)).getMessageSentAt msgIdx = some t_rep := by
    rcases hm_dec with ⟨p, sIdx, mIdx, pqIdx, spIdx, w, rfl⟩ |
        ⟨p, sIdx, mIdx, skIdx, pqIdx, spIdx, w, rfl⟩ <;>
    · cases hget : (runTraceMoves r (ms'_pre ++ pre)).getMessageSentAt mIdx with
      | some t_rep => exact ⟨mIdx, rfl, t_rep, hget⟩
      | none =>
        rw [Move.vis, hexp_nil, List.append_nil] at hv0
        exact (hdec_vis_none sIdx mIdx w hget hv0).elim
  have hrcv_term : rcvMoveTerm (runTraceMoves r (ms'_pre ++ pre)) m = some t_rep :=
    rcvMoveTerm_of_decryptMsgIdx_some hm_idx hget_rep
  have hget_ext :
      (runTraceMoves r ((ms'_pre ++ pre) ++ [].map .attackerSend)).getMessageSentAt msgIdx =
        some t_rep := by
    rw [List.map_nil, List.append_nil]; exact hget_rep
  have hmid_eq : rpkPromMid interp' x g_st q.inner coins =
      (if pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey then
        [.rng coins] else []) := rfl
  rw [hmid_eq]
  have hcs_drop : CoinSplit [.rng coins, .accept out] ([] ++ [.accept out]) :=
    coinSplit_prom_tail false hcoins_ne
  have hcs_full : CoinSplit [.rng coins, .accept out] ([.rng coins] ++ [.accept out]) :=
    coinSplit_prom_tail true hcoins_ne
  rcases hτ₂_dich with rfl | rfl
  · have hc_blk : CleanBy interp' r S who ok g' (ms'_pre ++ (pre ++ m :: post))
        (τ'_pre ++ promAccBlk (wirePrekey :: body) [] out) := hc_ext
    have hB_prom : XplBlock interp' r S who g' ms'_pre (pre ++ m :: post) τ'_pre
        (promAccBlk (wirePrekey :: body) [] out) := hB_blk
    have hcur := prom_currentRead_of_not_dirtyAt₂ interp' hC_τ'.out.hpf hc_blk hB_prom
      hpre hpost (Or.inl rfl)
    have ht_rep : t_rep ∈ recvRepresentations interp' r S g' (ms'_pre ++ pre) q.message := by
      rcases hm_dec with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hcur.2 t_rep hrcv_term
      · exact hcur.2 t_rep hrcv_term
    have hnc_rep : ¬ RecvCollision interp' r S g' (ms'_pre ++ pre) t_rep :=
      prom_not_recvCollision_of_not_dirtyAt₂ interp' hC_τ'.out.hpf hc_blk hB_prom
        hpre (Or.inl rfl) hrcv_term
    have hexpl_m : ExplainsMoves interp' r S who ok g'
        ((ms'_pre ++ pre) ++ [].map .attackerSend ++ [m])
        (τ'_pre ++ .recv (wirePrekey :: body) :: ([MachineEvent.accept out]).take (0 + 1)) := by
      rw [List.map_nil, List.append_nil]; exact hc_m.1
    have hacc_via : ModelAcceptsTermAfterCoinSplit interp' r S who ok g' (ms'_pre ++ pre) τ'_pre
        (.recv (wirePrekey :: body)) [.accept out] t_rep := by
      refine ⟨[], m, msgIdx, 0, out, g', ?_, hm_idx, rfl, fun _ _ => rfl,
        hget_ext, rfl, rfl, hexpl_m⟩
      intro _ hx; cases hx
    cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey
    · rfl
    · exact absurd
        (hCB hext hagree hwf hwho hrel_pre hc_pre2 hbin hdraw ht_rep hcs_drop rfl hacc_via)
        hnc_rep
  · have hc_blk : CleanBy interp' r S who ok g' (ms'_pre ++ (pre ++ m :: post))
        (τ'_pre ++ promAccBlk (wirePrekey :: body) [.rng coins] out) := hc_ext
    have hB_prom : XplBlock interp' r S who g' ms'_pre (pre ++ m :: post) τ'_pre
        (promAccBlk (wirePrekey :: body) [.rng coins] out) := hB_blk
    have hcur := prom_currentRead_of_not_dirtyAt₂ interp' hC_τ'.out.hpf hc_blk hB_prom
      hpre hpost (Or.inr ⟨coins, rfl, hcoins_len⟩)
    have ht_rep : t_rep ∈ recvRepresentations interp' r S g' (ms'_pre ++ pre) q.message := by
      rcases hm_dec with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hcur.2 t_rep hrcv_term
      · exact hcur.2 t_rep hrcv_term
    have hnc_rep : ¬ RecvCollision interp' r S g' (ms'_pre ++ pre) t_rep :=
      prom_not_recvCollision_of_not_dirtyAt₂ interp' hC_τ'.out.hpf hc_blk hB_prom
        hpre (Or.inr ⟨coins, rfl, hcoins_len⟩) hrcv_term
    have hexpl_m : ExplainsMoves interp' r S who ok g'
        ((ms'_pre ++ pre) ++ [].map .attackerSend ++ [m])
        (τ'_pre ++ .recv (wirePrekey :: body) ::
          ([MachineEvent.rng coins, MachineEvent.accept out]).take (1 + 1)) := by
      rw [List.map_nil, List.append_nil]; exact hc_m.1
    have hacc_via : ModelAcceptsTermAfterCoinSplit interp' r S who ok g' (ms'_pre ++ pre) τ'_pre
        (.recv (wirePrekey :: body)) [.rng coins, .accept out] t_rep := by
      refine ⟨[], m, msgIdx, 1, out, g', ?_, hm_idx, rfl, fun _ _ => rfl,
        hget_ext, rfl, ?_, hexpl_m⟩
      · intro _ hx; cases hx
      · simp [eventKind]
    cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_st).state q.inner.senderRatchetKey
    · exact absurd
        (hCA hext hagree hwf hwho hrel_pre hc_pre2 hbin hdraw ht_rep hcs_full rfl hacc_via)
        hnc_rep
    · rfl

set_option maxHeartbeats 400000 in
private theorem slot_rpk_prom_accept_cli
    (hGood : GoodExit0CutSpec)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hwf : ProtocolSetupWF r)
    {t : CliTurn} {c : CliCall} {stB st' : PqParty}
    {x : RecordExtras} {g_st : GhostState HwBytes}
    {rec_ body out : HwBytes} {q : PreKeyFields}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hDir : PqDirInv (interpOfParams interp P) P r t accepted)
    (hoff : t.bobOff = false)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hcoins : c.coins.length = 32)
    (hfb_bob : FilesBounded (t.dirs r.bob))
    (hinvB : PqPartyInv (interpOfParams interp P) P r accepted r.bob stB (t.dirs r.bob))
    (hwfB : PqxdhPartyInSpecDomain P stB)
    (hsess : stB.session = some (x, g_st))
    (hrec_eq : rec_ = encodeRecordUnderExtras (fun _ => x) g_st)
    (hrec_bob : t.records r r.bob = some rec_)
    (hstdin : c.stdin = wirePrekey :: body)
    (hq : parsePreKey body = some q)
    (hfm : PqFieldsMatch x g_st q)
    (hpm : EligibleForSessionPromotion rec_ (wirePrekey :: body))
    (hpqh : ∀ q₀, parsePreKeyWire c.stdin = some q₀ → PqFromHonest t.sent q₀.message)
    (hok_mod : pqRecvMatchingFieldsModel P stB x g_st q (HKDF.bytesToKey32 c.coins) =
      some (some (st', out))) :
    CliSlotPostCore
      (RpkPromNCWeak (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) c 0 out q σ_pre)
      interp P r t t c 0 out
      (filesOf ((pqRecvInputs P stB (wirePrekey :: body) (HKDF.bytesToKey32 c.coins)).files ++
        encodeDir P st'))
      accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let c1 := toCliCallNone c
  let rc := HKDF.bytesToKey32 c.coins
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hmb : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  have hcoins_rc : c.coins = HMAC.keyToBytes32 rc := (keyToBytes32_bytesToKey32 hcoins).symm
  have hlen_rec : rec_.length < 2 ^ 31 := hrec_eq ▸ (hwfB.1 x g_st hsess).2.2
  have hlen_rec_bound : rec_.length < 2 ^ 32 - 2 ^ 20 := Nat.lt_trans hlen_rec (by decide)
  have hpm_c : EligibleForSessionPromotion rec_ c.stdin := hstdin.symm ▸ hpm
  have hnnm3 : ¬ PreKeyNoMatch r t c := by
    rintro ⟨_, _, _, rec₁, hrec₁, hnprom⟩
    cases Option.some.inj (hrec_bob.symm.trans hrec₁); exact hnprom hpm_c
  have hnnm1 : ¬ PreKeyNoMatch r t c1 := by
    rintro ⟨_, _, _, rec₁, hrec₁, hnprom⟩
    cases Option.some.inj (hrec_bob.symm.trans hrec₁); exact hnprom hpm_c
  have hbinv : BobPromDirInv interp' P r stB rec_ :=
    bobPromDirInv_of_pqPartyInv hwf hagree' hinvB hfb_bob hrec_bob
  obtain ⟨s, htrusts, _, hdec, hst'_raw⟩ := pqRecvMatchingFieldsModel_ok_inv hok_mod
  obtain ⟨_, hpeer_eq⟩ := honestIdentity_of_matching_trusts hbinv hq htrusts
  have hst'_eq : st' = { stB with session := some (x, { g_st with session := s }) } := by
    rw [hst'_raw, ← hpeer_eq]
  obtain ⟨_, _, htry, _⟩ := parsePreKey_some_inv hq
  obtain ⟨g₁_pq, hrpq₁, hp₁, hs₁⟩ := rpkProm_reachPq_promote hwfB hsess htry hdec
  have hg_pty : g_st.party = stB.party := (hinvB.session_reach x g_st hsess).2
  have hst'_inv : PqPartyInv interp' P r accepted r.bob st' (filesOf (encodeDir P st')) :=
    { party_eq := by rw [hst'_eq]; exact hinvB.party_eq
      me_eq := by rw [hst'_eq]; exact hinvB.me_eq
      peerId_eq := by rw [hst'_eq]; exact hinvB.peerId_eq
      alice_stores := fun h => absurd h.symm hwf.1
      bob_stores := fun h => by rw [hst'_eq]; exact hinvB.bob_stores h
      session_reach := fun x₀ g₀ hs₀ => by
        rw [hst'_eq] at hs₀ ⊢
        rcases Prod.mk.inj (Option.some.inj hs₀) with ⟨rfl, rfl⟩
        exact ⟨⟨g₁_pq, hrpq₁, hp₁, hs₁⟩, hg_pty⟩
      dir_eq := rfl }
  have hkot : stB.kyberOneTime = [] := (hinvB.bob_stores hwf.1.symm).2.1
  have hsub : ∀ f ∈ encodeDir P stB, ∃ g₀ ∈ encodeDir P st', f.1 = g₀.1 := by
    rw [hst'_eq]; exact encodeDir_sub_of_fields rfl rfl rfl rfl rfl hkot hkot rfl
  let files_acc :=
    filesOf ((pqRecvInputs P stB (wirePrekey :: body) rc).files ++ encodeDir P st')
  have hscr : scrub files_acc = filesOf (encodeDir P st') :=
    scrub_filesOf_pqInputs_accept P stB st' _ [] _ _
      (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
  have hDir' : PqDirInv interp' P r (t.after r c1 0 out files_acc) accepted :=
    pqDirInv_after_accept_same hwf.1 hDir (Or.inr ⟨hbob, hoff⟩) hnnm1 hscr
      (by simpa [c1, toCliCallNone, hbob] using hst'_inv)
  have hbo_after : (t.after r c1 0 out files_acc).bobOff = false := by
    simp [CliTurn.after, hoff, hnnm1]
  have hafter_eq : CliTurn.after t r c 0 out files_acc = t.after r c1 0 out files_acc :=
    afterD3_eq_after_of_not_noMatch hnnm3 hnnm1
  have hleak_bob : t.leakRecords r r.bob = some rec_ := by
    rw [leakRecords_eq_records_of_bobOff_false r hoff, hrec_bob]
  have hst'_after : PqPartyInv interp' P r accepted r.bob st'
      ((t.after r c1 0 out files_acc).dirs r.bob) := by
    simpa [CliTurn.after, c1, toCliCallNone, hbob, hscr] using hst'_inv
  have hleak_after : (t.after r c1 0 out files_acc).leakRecords r =
      fun p => if p = r.bob then
        some (encodeRecordUnderExtras (fun _ => x) { g_st with session := s })
      else t.leakRecords r p := by
    rw [leakRecords_eq_records_of_bobOff_false r hbo_after,
        leakRecords_eq_records_of_bobOff_false r hoff]
    funext p; by_cases hpb : p = r.bob
    · subst hpb; rw [records_of_pqPartyInv hst'_after, hst'_eq]; simp
    · have hpc1 : p ≠ c1.party := by simpa [c1, toCliCallNone, hbob] using hpb
      simp [CliTurn.records, CliTurn.after, hpb, hpc1]
  have hsent_after : (t.after r c1 0 out files_acc).sent = t.sent := by
    simp [CliTurn.after, c1, toCliCallNone, hcmd]
  have hopk_after : (t.after r c1 0 out files_acc).opkUsed r = t.opkUsed r := by
    have hB_pre : PqBobInv interp' P r accepted t.bobOff stB (t.dirs r.bob) := by
      unfold PqBobInv; rw [hoff]; exact hinvB
    have hB_post : PqBobInv interp' P r accepted
        (t.after r c1 0 out files_acc).bobOff st'
        ((t.after r c1 0 out files_acc).dirs r.bob) := by
      unfold PqBobInv; rw [hbo_after]; exact hst'_after
    exact opkUsed_eq_of_pqBobInv_oneTime_eq hwf.1 hB_post hB_pre (by rw [hst'_eq])
  refine ⟨t.after r c1 0 out files_acc, accepted, ?_, fun who ok hwho hlive hnc => ?_⟩
  · change PqTurnSim1A interp' P r (CliTurn.after t r c 0 out files_acc) _ _
    rw [hafter_eq]; exact pqTurnSim1A_refl hDir' hbo_after
  · have hblk_eq : cliEntryEvents c ++ cliExitEvents c 0 out =
        [.recv (wirePrekey :: body), .rng (HMAC.keyToBytes32 rc), .accept out] := by
      rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]
      simp [cliEntryEvents, cliExitEvents, toCliCallNone, hcmd, hstdin, hcoins_rc]
    obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
    have hc₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
    obtain ⟨hrel₀, hopk₀⟩ := hlive.cutRel τ_acc ⟨g₀, ms₀, hex₀, hnrc₀⟩
    have hwho₀ : who[(callStarts τ_acc).length]? = some r.bob := by
      rw [coinSplit_callStarts_length_eq hex₀.1, ← hbob]; exact hwho
    obtain ⟨s', _, coins_out, sess, sess', hst'_eq', _, _, _, hhon_wire, hout⟩ :=
      pqRecvMatchingFieldsModel_accept_eval hmb hbinv hsess hrec_eq hleak_bob
        hrel₀.oooAll hrel₀.bkn hcoins hq hok_mod
    have hs_eq : s' = s := by
      have h1 : st'.session = some (x, { g_st with session := s }) := by rw [hst'_eq]
      have h2 : st'.session = some (x, { g_st with session := s' }) := by rw [hst'_eq']
      exact congrArg GhostState.session (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).2
    let rec' := encodeRecordUnderExtras (fun _ => x) { g_st with session := s' }
    let mid := rpkPromMid interp' x g_st q.inner c.coins
    let e' : PromTurn := ⟨t.leakRecords r, t.sent, accepted, t.opkUsed r⟩
    let sm : StateAndMessage := { state := rec', message := List.replicate 47 0#8 ++ out }
    have hpqh_b : ∀ q₀, parsePreKeyWire (wirePrekey :: body) = some q₀ →
        PqFromHonest t.sent q₀.message := hstdin ▸ hpqh
    have hC₀ := prom_make_acceptCall hwf hwho₀ hleak_bob hlen_rec_bound hpm hhon_wire hpqh_b
      ⟨g₀, ms₀, hc₀⟩ hrel₀ hopk₀ hout
    have hkb₀ : KnownBaseKey interp' r S g₀ ms₀ q := promXpl_knownBaseKey_of_acceptCallBy₂ hC₀ hc₀
    obtain ⟨t₀, ht₀⟩ :=
      prom_recvRepresentations_nonempty_of_parsePreKeyWire interp' r S g₀ ms₀ hout.hpf
    have hnot_exc : ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g₀ ms₀ σ_pre
        (.recv (wirePrekey :: body)) [.rng (HMAC.keyToBytes32 rc), .accept out] q.message := by
      have h0 := hnc rfl τ_acc g₀ ms₀ hex₀ hnrc₀ hkb₀
      rwa [hstdin, hcoins_rc] at h0
    obtain ⟨τ_star, g_star, ms_star, t_star, hex_star, hnrc_star, ht_star, hnc_star,
        hnrs_star, hnac_cli⟩ :=
      cBad_promCli_reselect_full ht₀ hnot_exc
    have hc_star : Clean interp' r S who ok g_star ms_star τ_star :=
      explainsCli_toClean hex_star hnrc_star
    obtain ⟨hrel_star, hopk_star⟩ := hlive.cutRel τ_star ⟨g_star, ms_star, hex_star, hnrc_star⟩
    have hwho_star : who[(callStarts τ_star).length]? = some r.bob := by
      rw [coinSplit_callStarts_length_eq hex_star.1, ← hbob]
      exact hwho
    have hC_star := prom_make_acceptCall hwf hwho_star hleak_bob hlen_rec_bound hpm hhon_wire
      hpqh_b ⟨g_star, ms_star, hc_star⟩ hrel_star hopk_star hout
    have hbin : BinarySessionDecryptOk interp' P r accepted t.sent (t.leakRecords r) r.bob
        stB st' (t.dirs r.bob) x g_st (wirePrekey :: body) q.message out q.inner rc :=
      ⟨Or.inr rfl, hinvB, hwfB, hsess, hrec_eq ▸ hleak_bob, hrec_eq ▸ hlen_rec_bound,
        hpqh_b q hout.hpf, parsePreKeyWire_inner_tryFrom hout.hpf,
        Or.inr ⟨q, hout.hpf, rfl, hfm, hok_mod⟩⟩
    have hmid_rc : mid = rpkPromMid interp' x g_st q.inner (HMAC.keyToBytes32 rc) := by
      dsimp [mid]; rw [hcoins_rc]
    have hnac_mid : ¬ AcceptCollision interp' r S who ok g_star ms_star τ_star
        (.recv (wirePrekey :: body)) (mid ++ [.accept out]) q.message := by
      rw [hmid_rc]
      exact not_acceptCollision_prom_of_bridgeC hext hagree hwf hCA hCB hwho_star hrel_star
        hc_star hbin hnac_cli
    have href_star : RecvExcuseFree interp' r S who ok g_star ms_star τ_star
        (.recv (wirePrekey :: body)) (mid ++ [.accept out]) q.message t_star :=
      ⟨hnrs_star, hnac_mid⟩
    have hw_star := prom_rawKnWitness_at_clean hext' hwf rfl hC_star hc_star ht_star
      hnc_star href_star
    obtain ⟨g₁, _stateIdx, _spqrMsgIdx, pqSalt, t_m, m_step,
        hfr, ht_m, hpq_kn, _hcur, hm_step, hraw⟩ := hw_star
    have hc₁ := cbadG2_cleanBy_transfer hfr hc_star
    have ht₁ := cbadG2_recvRep_of_sigmaFrame hfr hc_star.matched ht_m
    have htag_ne : wirePrekey ≠ wireWhisperTag :=
      prom_tag_ne_wireWhisperTag_of_parsePreKeyWire hout.hpf
    have hmid_ex : mid = [] ∨ ∃ d : HwBytes, mid = [.rng d] :=
      promXpl_mid_cases_of_acceptCallBy₂ hC_star
    have hok_pin : (fun k => if k = (callStarts τ_star).length then true else ok k)
        (callStarts τ_star).length = true := by simp only [↓reduceIte]
    have hExpl_mp := explains_append_decrypt_step
      (prom_explains_pin_ok_end hc₁.explains) ht₁ hwho_star hok_pin hm_step hmid_ex
      (Or.inr ⟨htag_ne, q, hout.hpf, rfl, promXpl_hbka_of_acceptCallBy₂ hC_star hc₁⟩) hraw
    have hcs_blk_mid : CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 out)
        (promAccBlk (wirePrekey :: body) mid out) := by
      rw [hblk_eq]
      change CoinSplit _ (.recv (wirePrekey :: body) :: (mid ++ [.accept out]))
      rw [hmid_rc]
      exact coinSplit_prom_blk _ (Slots.keyToBytes32_ne_nil rc)
    refine ⟨⟨τ_star ++ promAccBlk (wirePrekey :: body) mid out,
      g₁, ms_star ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m_step]),
      coinSplit_append hex_star.1 hcs_blk_mid, hExpl_mp.1⟩, fun hok => ?_⟩
    simp only [decide_true] at hok
    have hok_star : ok (callStarts τ_star).length = true := by
      rw [coinSplit_callStarts_length_eq hex_star.1]; exact hok
    have hnoAdj : NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 out)) := by
      rw [hblk_eq]
      exact noAdjRng_append_of_head_nonRng hlive.noAdjRng
        (noAdjRng_prom_accept_blk _ _ _)
        (fun y hy => by simp at hy; subst hy; simp [eventKind])
    obtain ⟨g₁', hfr', hc₁', hbr⟩ :=
      cBadG2_of_rawWitness hc_star hnac_mid hfr ht_m hpq_kn hwho_star hok_star hm_step hmid_ex
        (Or.inr ⟨htag_ne, q, hout.hpf, rfl, promXpl_hbka_of_acceptCallBy₂ hC_star hc₁⟩) hraw
    obtain ⟨pre_b, post_b, m_b, t_b, hex_b, hpre_vis_b, hpre_nd_b, hpost_nd_b,
        hm_b, hbody_b, hrep_b, hncol_b⟩ := hbr
    have hclean_ext : Clean interp' r S who ok g₁' (ms_star ++ (pre_b ++ m_b :: post_b))
        (τ_star ++ promAccBlk (wirePrekey :: body) mid out) :=
      cleanBy_snoc_decrypt hc₁' hex_b hpre_vis_b hpre_nd_b hpost_nd_b hm_b hbody_b hrep_b hncol_b
    obtain ⟨hex_ext, hnrc_ext⟩ :=
      hGood hex_star hcs_blk_mid (GoodStepCut.callRecvAccept hC_star.hmid rfl hok_star)
        (Or.inl rfl) hfr'.1 hclean_ext
    refine ⟨hnoAdj, ⟨τ_star ++ promAccBlk (wirePrekey :: body) mid out,
      g₁', ms_star ++ (pre_b ++ m_b :: post_b), hex_ext, hnrc_ext⟩,
      fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
    have hex'_eq : ExplainsCli interp' r S who ok
        (σ_pre ++ [.recv (wirePrekey :: body), .rng (HMAC.keyToBytes32 rc), .accept out])
        τ' g' ms' := by
      rwa [← hblk_eq]
    obtain ⟨τ'_pre, τ₂, rfl, hcs_pre, hcs₂⟩ := coinSplit_append_recv_inv hex'_eq.1
    obtain ⟨ms'_pre, δ, rfl, hex'_pre, hnrc'_pre, hB_blk⟩ :=
      explainsCli_prefix_of_recv_split hex'_eq hnrc' hcs_pre
    have hc'_pre : Clean interp' r S who ok g' ms'_pre τ'_pre :=
      explainsCli_toClean hex'_pre hnrc'_pre
    have hc_ext' : Clean interp' r S who ok g' (ms'_pre ++ δ)
        (τ'_pre ++ (.recv (wirePrekey :: body) :: τ₂)) :=
      explainsCli_toClean hex'_eq hnrc'
    obtain ⟨hrel'_pre, hopk'_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
    have hwho_τ' : who[(callStarts τ'_pre).length]? = some r.bob := by
      rw [coinSplit_callStarts_length_eq hcs_pre, ← hbob]
      exact hwho
    have hC_τ' := prom_make_acceptCall hwf hwho_τ' hleak_bob hlen_rec_bound hpm hhon_wire
      hpqh_b ⟨g', ms'_pre, hc'_pre⟩ hrel'_pre hopk'_pre hout
    have hτ₂_eq : τ₂ = mid ++ [.accept out] := by
      rw [hmid_rc]
      exact prom_cut_tau2_eq_mid hext hagree hwf hCA hCB hwho_τ' hC_τ' hc'_pre
        hc_ext' hB_blk hex'_eq.2.2.2 hcs₂ hbin
    subst hτ₂_eq
    have hsel_τ' := prom_decSel_cases_out hC_τ'.out fun hnil =>
      prom_noDrawOK_proved _ e' τ'_pre rec_ (wirePrekey :: body) sm q sess sess' coins_out _ out
        (hnil ▸ hC_τ')
    have hrel_post := prom_accept_cRel hC_τ'
      (prom_newRecBy₂_of_tieAt hC_τ' (prom_rcvDecTie_at_clean hext' hwf rfl hC_τ' hsel_τ'))
      (prom_cHist_step hext' hwf hC_τ')
    have hopk_post := prom_opkUnused_of_cOpkRelC hC_τ'
    change PureCRel interp' r S who ok _ _ _ (τ'_pre ++ promAccBlk (wirePrekey :: body) mid out) ∧
      COpkRelC interp' r S who ok _ (τ'_pre ++ promAccBlk (wirePrekey :: body) mid out)
    rw [hleak_after, hsent_after, hopk_after]
    dsimp only [sm, rec'] at hrel_post
    rw [hs_eq] at hrel_post
    exact ⟨hrel_post, hopk_post⟩

end Accept

private theorem CliSlotPostCore.mono {NC₁ NC₂ : List Participant → (Nat → Bool) → Prop}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (himp : ∀ who ok, NC₁ who ok → NC₂ who ok)
    (h : CliSlotPostCore NC₂ interp P r t t_clean c code out files accepted σ_pre) :
    CliSlotPostCore NC₁ interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨tc', acc', hsim', hstep⟩ := h
  exact ⟨tc', acc', hsim', fun who ok hwho hlive hnc₁ => hstep who ok hwho hlive (himp who ok hnc₁)⟩

private theorem slot_rpk_prom_cli_core
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {rec_ : HwBytes} {q : PreKeyFields}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hrec_bob : t.records r r.bob = some rec_)
    (hq_wire : parsePreKeyWire c.stdin = some q)
    (hpm : EligibleForSessionPromotion rec_ c.stdin)
    (hpqh : ∀ q₀, parsePreKeyWire c.stdin = some q₀ → PqFromHonest t.sent q₀.message)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    CliSlotPostCore
      (RpkPromNCWeak (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) c code out q σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  let interp' := interpOfParams interp P
  have hoff : t.bobOff = false := by
    cases hbo : t.bobOff
    · rfl
    · exact absurd hbob (hbca hbo)
  have htc_eq : t_clean = t := hsim.bobOff_false_eq hoff
  subst t_clean
  have hDir : PqDirInv interp' P r t accepted := hsim.dirInv
  have hfb_bob : FilesBounded (t.dirs r.bob) := hbob ▸ hfb
  obtain ⟨stB, hBobInv⟩ := hDir.2.1
  have hinvB : PqPartyInv interp' P r accepted r.bob stB (t.dirs r.bob) := by
    unfold PqBobInv at hBobInv; rwa [hoff] at hBobInv
  have hwfB : PqxdhPartyInSpecDomain P stB := wfPq_of_pqPartyInv hinvB hfb_bob
  let c1 := toCliCallNone c
  have hin1 : InputsFor c1 (t.dirs c1.party) i := inputsFor_toCliCallNone hbun hin
  have hi_enc : InputsFor c1 (filesOf (encodeDir P stB)) i := by
    rwa [show c1.party = r.bob from hbob, hinvB.dir_eq] at hin1
  let rc := HKDF.bytesToKey32 c.coins
  have hcoins_rc : c1.coins = HMAC.keyToBytes32 rc := (keyToBytes32_bytesToKey32 hcoins).symm
  have hcmd_stB : c1.cmd = .recv (partyAddress stB.party.other) := by
    change c.cmd = .recv (partyAddress stB.party.other)
    rw [hcmd, peerOf_eq_addrE_other, ← hinvB.party_eq]
  have heq_recv : InputsEquiv i (pqRecvInputs P stB c.stdin rc) :=
    inputsEquiv_pqRecvInputs (c := c1) hi_enc hcmd_stB rfl hcoins_rc
  have hp : PqModelPost interp P i (.exited code out files) :=
    PqModelRel.exited_iff.mp hRel
  have hrec_map := hrec_bob
  rw [records_of_pqPartyInv hinvB] at hrec_map
  rcases hsess : stB.session with _ | ⟨x, g_st⟩
  · rw [hsess] at hrec_map; cases hrec_map
  have hrec_eq : rec_ = encodeRecordUnderExtras (fun _ => x) g_st := by
    rw [hsess] at hrec_map
    exact (Option.some.inj hrec_map).symm
  have hstdin_ex : ∃ body, c.stdin = wirePrekey :: body ∧ parsePreKey body = some q := by
    rcases hcs : c.stdin with _ | ⟨tag, body⟩
    · rw [hcs] at hq_wire; cases hq_wire
    · rw [hcs] at hq_wire
      unfold parsePreKeyWire at hq_wire
      dsimp only at hq_wire
      split_ifs at hq_wire with htag
      exact ⟨body, by rw [htag]; rfl, hq_wire⟩
  obtain ⟨body, hstdin, hq⟩ := hstdin_ex
  have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
    rw [hstdin, List.head?_cons, ne_eq, Option.some.injEq]
    unfold wirePrekey wireWhisperTag
    decide
  unfold StdinBounded at hsb
  rw [hcmd] at hsb
  have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
  have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
  have hpm_b : EligibleForSessionPromotion rec_ (wirePrekey :: body) := hstdin ▸ hpm
  by_cases hfm : PqFieldsMatch x g_st q
  · have hobs := hp.recvPrekeyMatching stB x g_st body q rc hwfB hsess hbody_lt hq hfm
      (hstdin ▸ heq_recv)
    rcases exited_eq_pqObserve_iff.mp hobs with
        ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hok_mod, rfl, rfl, rfl⟩
    · exact CliSlotPostCore.mono (fun _ _ _ => trivial)
        (slot_rpk_prom_reject_cli hGood hB hwf hDir hoff hbob hcmd hinvB _ _)
    · exact slot_rpk_prom_accept_cli hGood hCA hCB hext hagree hwf hDir hoff hbob hcmd hcoins
        hfb_bob hinvB hwfB hsess hrec_eq hrec_bob hstdin hq hfm hpm_b hpqh hok_mod
  · have hno_fm : ∀ x₀ g₀, stB.session = some (x₀, g₀) → ¬ PqFieldsMatch x₀ g₀ q := by
      intro x₀ g₀ hs₀
      rw [hsess] at hs₀
      rcases Prod.mk.inj (Option.some.inj hs₀) with ⟨rfl, rfl⟩
      exact hfm
    cases hm : preKeyOfBody? body with
    | none =>
      have hobs := hp.recvPrekeyUntyped stB body q rc hwfB hbody_lt hq hm hno_fm
        (hstdin ▸ heq_recv)
      injection hobs with hcode hout hfiles
      subst hcode hout hfiles
      exact CliSlotPostCore.mono (fun _ _ _ => trivial)
        (slot_rpk_prom_reject_cli hGood hB hwf hDir hoff hbob hcmd hinvB _ _)
    | some m =>
      obtain ⟨q₁, hq₁, hv4, _⟩ := preKeyOfBody?_some_inv hm
      cases Option.some.inj (hq.symm.trans hq₁)
      exact absurd (pqFieldsMatch_of_promoteMatch_v4 hwfB hsess hq hv4 (hrec_eq ▸ hpm_b)) hfm

/-- Generalized matching-session promote `recv` slot returning `Defs.CliSlotPostW` under `RpkPromNC`. -/
theorem slot_rpk_prom_cli_gen
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {rec_ : HwBytes} {q : PreKeyFields}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hrec_bob : t.records r r.bob = some rec_)
    (hq_wire : parsePreKeyWire c.stdin = some q)
    (hpm : EligibleForSessionPromotion rec_ c.stdin)
    (hpqh : ∀ q₀, parsePreKeyWire c.stdin = some q₀ → PqFromHonest t.sent q₀.message)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    Symbolic.Proofs.Swarm.UA.Defs.CliSlotPostW
      (RpkPromNC (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) c code out q σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨tc', acc', hsim', hstep⟩ :=
    slot_rpk_prom_cli_core hGood hB hCA hCB interp P r hext hagree hwf hsim hbob hcmd hbun hcoins
      hsb hfb hbca hrec_bob hq_wire hpm hpqh hin hRel
  refine ⟨tc', acc', hsim', fun who ok hwho hlive hnc hok => ?_⟩
  exact (hstep who ok hwho hlive (fun hc τ₁ g ms hex₁ hnrc₁ _ => hnc hc τ₁ g ms hex₁ hnrc₁)).2 hok

end Symbolic.Swarm.Coinsplit.Lift.L11
