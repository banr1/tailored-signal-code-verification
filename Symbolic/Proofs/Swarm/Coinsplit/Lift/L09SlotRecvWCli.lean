/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptCollisionPickPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperCodec
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperEval
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperReject
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperSlot
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieDispatchPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedEqCliPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2Pure
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.HistStepPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2ProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2Pure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.Coinsplit.Probe.P2CrossRunRecv
import Symbolic.Proofs.Swarm.Coinsplit.Probe.P3SuffixExcuses
import Symbolic.Proofs.Swarm.TRREF.HooksOKXTRPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure -- shake: keep

/-!
# Cut-Polymorphic Whisper `recv` Slot Refinement

Proves `SlotRecvWCliSpec`, lifting `slot_recvW_d3_pqModelRel` from single-cut `CliLiveAt` to
cut-polymorphic `CliLiveAtCli`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.Lift.L09

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureDrawsCoins)
open Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure hiding StEntry TREntry
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng)
open Symbolic.Swarm.Coinsplit.Lift

/-! ## Call-Boundary `CoinSplit` and `ExplainsCli` Prefix Splitting -/

private theorem coinSplit_append {σ₁ σ₂ τ₁ τ₂ : List MachineEvent}
    (h₁ : CoinSplit σ₁ τ₁) (h₂ : CoinSplit σ₂ τ₂) :
    CoinSplit (σ₁ ++ σ₂) (τ₁ ++ τ₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | keep hx _ ih => exact .keep hx ih
  | split hall hpref _ ih =>
    rw [List.append_assoc]
    exact .split hall hpref ih

private theorem coinSplit_append_cons_nonRng {σ₁ σ₂ τ : List MachineEvent} {e : MachineEvent}
    (hne : eventKind e ≠ .rng)
    (hcs : CoinSplit (σ₁ ++ e :: σ₂) τ) :
    ∃ τ₁ τ₂, τ = τ₁ ++ e :: τ₂ ∧ CoinSplit σ₁ τ₁ ∧ CoinSplit σ₂ τ₂ := by
  induction σ₁ generalizing τ with
  | nil =>
    obtain ⟨τ₂, rfl, hcs₂⟩ := (Symbolic.Swarm.Coinsplit.S1.coinSplit_cons_nonRng_iff hne).mp hcs
    exact ⟨[], τ₂, rfl, .nil, hcs₂⟩
  | cons x σ₁' ih =>
    cases hcs with
    | @keep _ _ τ_rest hx hrest =>
      obtain ⟨τ₁, τ₂, rfl, h₁, h₂⟩ := ih hrest
      exact ⟨x :: τ₁, τ₂, rfl, .keep hx h₁, h₂⟩
    | @split bs pieces _ τ_rest hall hpref hrest =>
      obtain ⟨τ₁, τ₂, rfl, h₁, h₂⟩ := ih hrest
      exact ⟨pieces.map .rng ++ τ₁, τ₂, by simp [List.append_assoc], .split hall hpref h₁, h₂⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool} {ms₀ δ : List Move}
    (hof₀ : OutcomeFaithful r ok ms₀)
    (hofc : OutcomeFaithfulCli r ok (ms₀ ++ δ)) :
    OutcomeFaithfulCli r ok ms₀ := by
  refine ⟨hof₀, fun i m hi hvis hok => ?_⟩
  have hi_lt : i < ms₀.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_app : (ms₀ ++ δ)[i]? = some m := by
    rw [List.getElem?_append_left hi_lt]; exact hi
  have htake : (ms₀ ++ δ).take i = ms₀.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hi_lt)
  have h := hofc.2 i m hi_app
  dsimp only at h
  rw [htake] at h
  exact h hvis hok

private theorem rngLengthsFaithfulCli_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ δ : List Move}
    (hrng : RngLengthsFaithfulCli interp r S g (ms₀ ++ δ)) :
    RngLengthsFaithfulCli interp r S g ms₀ := by
  intro i m hi
  have hi_lt : i < ms₀.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_app : (ms₀ ++ δ)[i]? = some m := by
    rw [List.getElem?_append_left hi_lt]; exact hi
  have htake : (ms₀ ++ δ).take i = ms₀.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hi_lt)
  have h := hrng i m hi_app
  dsimp only at h
  rw [htake] at h
  exact h

private theorem explainsCli_clean_split_recv {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {σ_pre σ₂ τ' : List MachineEvent} {w : HwBytes} {g' : Ghost} {ms' : List Move}
    (hex' : ExplainsCli interp r S who ok (σ_pre ++ (.recv w :: σ₂)) τ' g' ms')
    (hnrc' : ¬ ReadCollision interp r S g' ms' τ') :
    ∃ τ'_pre τ₂ ms'_pre δ,
      τ' = τ'_pre ++ (.recv w :: τ₂) ∧
      ms' = ms'_pre ++ δ ∧
      CoinSplit σ_pre τ'_pre ∧
      CoinSplit σ₂ τ₂ ∧
      ExplainsCli interp r S who ok σ_pre τ'_pre g' ms'_pre ∧
      Clean interp r S who ok g' ms'_pre τ'_pre ∧
      Clean interp r S who ok g' (ms'_pre ++ δ) (τ'_pre ++ (.recv w :: τ₂)) ∧
      XplBlock interp r S who g' ms'_pre δ τ'_pre (.recv w :: τ₂) := by
  obtain ⟨τ'_pre, τ₂, rfl, hcs_pre, hcs₂⟩ :=
    coinSplit_append_cons_nonRng (by simp [eventKind]) hex'.1
  have hc_ext : Clean interp r S who ok g' ms' (τ'_pre ++ (.recv w :: τ₂)) :=
    explainsCli_toClean hex' hnrc'
  have hhead : ∀ e ∈ (MachineEvent.recv w :: τ₂).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  obtain ⟨ms'_pre, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hc_ext.matched hhead (matchedPrefix_prefix_reachable hc_ext.matched)
  have hc_pre : Clean interp r S who ok g' ms'_pre τ'_pre :=
    clean_prefix hpre.2.2.2.2.2.length_eq hc_ext
  have hex_pre : ExplainsCli interp r S who ok σ_pre τ'_pre g' ms'_pre :=
    ⟨hcs_pre, hpre, outcomeFaithfulCli_prefix hc_pre.1.2 hex'.2.2.1,
      rngLengthsFaithfulCli_prefix hex'.2.2.2⟩
  exact ⟨τ'_pre, τ₂, ms'_pre, δ, rfl, rfl, hcs_pre, hcs₂, hex_pre, hc_pre, hc_ext,
    ⟨hpre, hc_ext.matched.2.1, hmatch⟩⟩

/-! ## Nonzero-Exit Whisper `recv` Step -/

private def CliSlotPostCore (NC : List Participant → (Nat → Bool) → Prop)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : _root_.DY.Libsignal.Composed.Refinement.Cli.CliCall)
    (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
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

private theorem slot_recvW_cli_nonzero
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : _root_.DY.Libsignal.Composed.Refinement.Cli.CliCall}
    {body out : HwBytes} {code : Nat} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hbca : BobCallAllowed r t c)
    (hcmd : c.cmd = .recv (peerOf r c.party))
    (hstdin : c.stdin = wireWhisperTag :: body)
    (hne : code ≠ 0)
    (hDir' : PqDirInv (interpOfParams interp P) P r
      (t_clean.after r (toCliCallNone c) code out files) accepted)
    (hrec_after : (t_clean.after r (toCliCallNone c) code out files).records r
        (toCliCallNone c).party =
      t_clean.records r (toCliCallNone c).party)
    (hopk' : (t_clean.after r (toCliCallNone c) code out files).opkUsed r =
      t_clean.opkUsed r) :
    CliSlotPostCore (fun _ _ => True) interp P r t t_clean c code out files accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let c1 := toCliCallNone c
  have hcmd1 : c1.cmd = .recv (peerOf r c.party) := hcmd
  have hstdin1 : c1.stdin = wireWhisperTag :: body := hstdin
  have hn3 : ¬ PreKeyNoMatch r t c := fun h => h.2.2.1 (by simp [hstdin])
  have hn1 : ¬ PreKeyNoMatch r t_clean c1 :=
    Slots.not_preKeyNoMatch_of_recvWhisper (c := c1) hstdin1
  have hblk_eq : cliEntryEvents c ++ cliExitEvents c code out =
      [.recv (wireWhisperTag :: body), .rng c.coins] := by
    rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq,
      Slots.cliEntryEvents_recvWhisper hcmd1 hstdin1,
      Slots.cliExitEvents_recvWhisper_nonzero hcmd1 hne out, List.append_nil]
    rfl
  have hcs_blk : CoinSplit (cliEntryEvents c ++ cliExitEvents c code out)
      [.recv (wireWhisperTag :: body)] := by
    rw [hblk_eq]
    exact Slots.coinSplit_recv_drop_rng (wireWhisperTag :: body) c.coins
  refine ⟨t_clean.after r c1 code out files, accepted,
    pqTurnSim1A_caller_after hwf hsim hbca hp hn3 hn1 hDir', fun who ok _hwho hlive _ => ?_⟩
  obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
  have hc₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
  have hcs_out : CoinSplit (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c code out))
      (τ_acc ++ [.recv (wireWhisperTag :: body)]) :=
    coinSplit_append hex₀.1 hcs_blk
  refine ⟨⟨τ_acc ++ [.recv (wireWhisperTag :: body)], g₀, ms₀ ++ [Move.reject []],
    hcs_out, Slots.matchedPrefix_recvWhisper_reject body hc₀.1.1⟩, fun hok => ?_⟩
  have hdec_false : decide (code = 0) = false := decide_eq_false hne
  rw [hdec_false] at hok
  have hnoAdj : NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c code out)) := by
    rw [hblk_eq]
    exact noAdjRng_append_of_head_nonRng hlive.noAdjRng ⟨Or.inl (by simp [eventKind]), trivial⟩
      (fun y hy => by simp at hy; subst hy; simp [eventKind])
  have hok_acc : ok (callStarts τ_acc).length = false := by
    rw [coinSplit_callStarts_length_eq hex₀.1]; exact hok
  have hclean_ext : Clean interp' r S who ok g₀ (ms₀ ++ [Move.reject []])
      (τ_acc ++ [.recv (wireWhisperTag :: body)]) :=
    Slots.clean_recvWhisper_reject body hc₀ hok_acc
  obtain ⟨hex_ext, hnrc_ext⟩ :=
    hGood hex₀ hcs_blk (GoodStepCut.callRecvFail hok_acc) (Or.inl rfl)
      (fun _ _ _ => rfl) hclean_ext
  refine ⟨hnoAdj, ⟨τ_acc ++ [.recv (wireWhisperTag :: body)], g₀, ms₀ ++ [Move.reject []],
    hex_ext, hnrc_ext⟩, fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
  rw [hblk_eq] at hex'
  obtain ⟨τ'_pre, τ₂, ms'_pre, _δ, rfl, _, hcs_pre, hcs₂, hex'_pre, hc'_pre, _, _⟩ :=
    explainsCli_clean_split_recv hex' hnrc'
  obtain ⟨hrel_pre, hopk_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hc'_pre.2⟩
  have hok_τ' : ok (callStarts τ'_pre).length = false := by
    rw [coinSplit_callStarts_length_eq hcs_pre]; exact hok
  have hcs_blk' : CoinSplit [.recv (wireWhisperTag :: body), .rng c.coins]
      (.recv (wireWhisperTag :: body) :: τ₂) :=
    .keep (fun _ h => by cases h) hcs₂
  obtain ⟨hrel_post, hopk_post⟩ :=
    hB hwf (Or.inl rfl) hcs_blk' hok_τ' hrel_pre hopk_pre
  have hlr_fail : (t_clean.after r c1 code out files).leakRecords r = t_clean.leakRecords r :=
    Slots.after_leakRecords_of_recvWhisper_fail hstdin1 hrec_after
  have hsent_fail : (t_clean.after r c1 code out files).sent = t_clean.sent := by
    cases code <;> simp [CliTurn.after, hcmd1]
  rw [hlr_fail, hsent_fail, hopk']
  exact ⟨hrel_post, hopk_post⟩

/-! ## Accepting Whisper `recv` Helpers -/

private theorem a2b_rcvDecTie_noCol
    (interpretation : ExternInterpretation)
    (hceh : ExternCryptoLawsHold interpretation)
    {r₀ : ProtocolSetup} (hwf : ProtocolSetupWF r₀) (hik : Symbolic.Swarm.CREF.TR.IkShape interpretation r₀)
    {S : OpaqueSymbolSemantics} (hS : S = compSemOf interpretation r₀) {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc mid rec body sm)
    (g : Ghost) (ms₀ pre : List Move) (mv : Move) (post : List Move)
    (hc : CleanBy interpretation r₀ S who ok g (ms₀ ++ (pre ++ mv :: post))
      (acc ++ RecvWirePure.rcvAccBlk body mid sm))
    (hc₀ : CleanBy interpretation r₀ S who ok g ms₀ acc)
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ mv :: post) acc
      (RecvWirePure.rcvAccBlk body mid sm))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hdec : DecryptBy p mv)
    (hpost : MovesFrom InvisibleNoEffect (mv.next (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hch₀ : CHistBy interpretation r₀ S g ms₀)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre)) mv = some t →
       ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RecvWirePure.RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body mv)
    (hrel_pre : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) p rec)
    (hns_pre : Symbolic.Swarm.CREF.TR.TRNsBound r₀ (ms₀ ++ pre) sent) :
    Symbolic.Swarm.CREF.TR.PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [mv]) (fun q => if q = p then some sm.state else none) ∧
      Symbolic.Swarm.CREF.TR.TRNsBound r₀ (ms₀ ++ pre ++ [mv]) sent := by
  have hcompat : GhostAndSemMatchSetup interpretation r₀ S g := hB.1.1
  have hrun_pre : ModelRun r₀ (ms₀ ++ pre) := RecvWirePure.a2b_modelRun_pre hB
  have hfresh₀ : Symbolic.Swarm.CREF.TR.TRRecvFreshAll r₀ ms₀ :=
    trRecvFreshAll_of_matchedPrefix interpretation hc₀.matched
  have habs₀ : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g (ms₀ ++ pre) :=
    RecvWirePure.rcv_abs_of_xplBlock interpretation hc.matched hB
  have hat := a2b_recvAtFacts_of_quietPre hpre hch₀.1 hfresh₀
  have hrkAlias : A2bSeedRkAliasRes interpretation r₀ S g (ms₀ ++ pre) acc :=
    a2b_hrkAlias r₀ S g ms₀ pre mv post acc (RecvWirePure.rcvAccBlk body mid sm) hB hpre hch₀ hfresh₀
  have hseed₀ : A2bSkStepSeedEq interpretation r₀ S g (ms₀ ++ pre) acc :=
    a2b_skStepSeedEq_of_shapeRes interpretation hceh r₀ hwf S hS g (ms₀ ++ pre) acc
      hcompat hrun_pre hat (rcv_hcross_pure interpretation) (rcv_hshapeEq_pure interpretation hB) hrkAlias
  have hF : A2bRunFacts interpretation r₀ S g (ms₀ ++ pre) acc :=
    a2b_runFacts_of_cHistBy hpre hch₀ hfresh₀ habs₀ hseed₀
  obtain ⟨hcanon_r0, g_rw, coins, hwho, hwire, hcanon_q, hmid_cases, hcoins_ok, heval_u⟩ :=
    rcv_pending_callEnd_of_pureAccept interpretation hC
  obtain ⟨m, newPqrState, pqrKey, htry, hrecv_spqr, hbr⟩ :=
    evalRecvWireWithCoinsW_branch_cases interpretation body mid sm g_rw coins hwire hmid_cases heval_u
  cases mv
  case decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = p := hdec
    subst hme
    exact a2b_tie_decrypt interpretation hceh r₀ hwf hik S hS g ms₀ pre post acc mid sent me
      stateIdx msgIdx pqIdx spqrMsgIdx wrapped rec body sm hB hpre hpost hnocol hcurR hrel_pre hns_pre hF
      g_rw coins m newPqrState pqrKey hC.hstate_lt hcanon_r0 hwho hwire hcanon_q hcoins_ok heval_u htry
      hrecv_spqr hbr
  case decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = p := hdec
    subst hme
    exact a2b_tie_decryptSkipped interpretation hceh r₀ S hS g ms₀ pre post acc mid sent me
      stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped rec body sm hB hpre hpost hnocol hcurR hrel_pre hns_pre
      hF g_rw coins m newPqrState pqrKey hC.hstate_lt hcanon_r0 hwire hcanon_q heval_u htry hrecv_spqr hbr
  all_goals exact hdec.elim

private theorem pureCRel_and_opk_accept_whisper_noCol
    {interpretation : ExternInterpretation}
    (hExt : ExternContractsHoldCli interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc mid : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r S who ok j p records sent accepted opkUsed acc mid rec body sm) :
    PureCRel interpretation r S who ok
        (fun q => if q = p then some sm.state else records q) sent accepted
        (acc ++ RecvWirePure.rcvAccBlk body mid sm) ∧
      COpkRelC interpretation r S who ok opkUsed (acc ++ RecvWirePure.rcvAccBlk body mid sm) := by
  have hik := Symbolic.Proofs.Swarm.TRREF.Pure.rcv_ikShape_of_cryptoEquations hExt.1 r
  refine rcv_accept_pureCRel_of_parts interpretation hwf hC.hrel hC.hopk hC.hwho hC.hj hC.hp
    hC.hrec hC.hss hC.hmid
    (rcv_oooOK_of_pureAccept interpretation hC)
    (rcv_bkaOK_of_pureAccept interpretation hC)
    (fun g ms₀ δ hc hB h1 hch₀ hrr₀ hns₀ => ?_)
    (fun g ms₀ δ hc hB h1 ⟨hch₀, hrole₀⟩ hrr₀ hns₀ _hrr' => ?_)
  · obtain ⟨pre, m, post, rfl, hpre, hstep, hpost⟩ := h1
    have hc₀ : CleanBy interpretation r S who ok g ms₀ acc :=
      clean_prefix hB.pre.2.2.2.2.2.length_eq hc
    have hne_st : sm.state ≠ [] := rcv_state_ne_nil_of_pureAccept interpretation hC
    have hcur := rcv_currentRead_of_clean_pure interpretation hc hB hpre hpost
    have hq := RecvWirePure.a2b_quietPre hpre
    obtain ⟨hrsi, hns'⟩ := a2b_rcvDecTie_noCol interpretation hExt.1 hwf hik hSeq hC
      g ms₀ pre m post hc hc₀ hB hpre (hstep.2.2 (rcv_accBlk_has_accept body mid sm)) hpost hch₀
      (fun _t ht => rcv_not_recvCollision_of_clean interpretation hc hB hpre hC.hmid ht)
      hcur (PureXplQuiet.quiet_pureCRecRel hq hrr₀) (PureXplQuiet.quiet_trNsBound hq hns₀)
    have hq' := RecvWirePure.a2b_quietPost hpost
    exact ⟨hne_st, PureXplQuiet.quiet_pureCRecRel hq' (Or.inl hrsi), PureXplQuiet.quiet_trNsBound hq' hns'⟩
  · obtain ⟨pre, m, post, rfl, hpre, hstep, hpost⟩ := h1
    have hc₀ : CleanBy interpretation r S who ok g ms₀ acc :=
      clean_prefix hB.pre.2.2.2.2.2.length_eq hc
    have hrun_pre : (runMoves pre (runTraceMoves r ms₀)).1 = runTraceMoves r (ms₀ ++ pre) :=
      (Symbolic.Swarm.CREF.TR.runTrace_append r ms₀ pre).symm
    have hm : DecryptBy p m := hstep.2.2 (rcv_accBlk_has_accept body mid sm)
    have hcur := rcv_currentRead_of_clean_pure interpretation hc hB hpre hpost
    have hq_pre := RecvWirePure.a2b_quietPre hpre
    have hrr_pre := PureXplQuiet.quiet_pureCRecRel hq_pre hrr₀
    obtain ⟨hrsi, _⟩ := a2b_rcvDecTie_noCol interpretation hExt.1 hwf hik hSeq hC
      g ms₀ pre m post hc hc₀ hB hpre hm hpost ⟨hch₀, hrole₀⟩
      (fun _t ht => rcv_not_recvCollision_of_clean interpretation hc hB hpre hC.hmid ht)
      hcur hrr_pre (PureXplQuiet.quiet_trNsBound hq_pre hns₀)
    have hrole_pre : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) := by
      rw [Symbolic.Swarm.CREF.TR.runTrace_append]
      exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole₀
    have hrole_m : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
      rw [Symbolic.Swarm.CREF.TR.runTrace_snoc]; cases m with
      | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
        exact roleSnapshots_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped hrole_pre
      | decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped =>
        exact roleSnapshots_decryptSkipped me stateIdx msgIdx k pqIdx spqrMsgIdx wrapped hrole_pre
      | _ => nomatch hm
    have hrole_pair : ∀ (st₁ st₂ : _root_.DY.Libsignal.TripleRatchet.TRState) (i₁ i₂ : Nat),
        ((runTraceMoves r (ms₀ ++ pre ++ [m])).at? i₁ : Option HStE) = some ⟨⟨p, st₁⟩⟩ →
        ((runTraceMoves r (ms₀ ++ pre ++ [m])).at? i₂ : Option HStE) = some ⟨⟨p, st₂⟩⟩ →
        st₁.initiator = st₂.initiator := fun st₁ st₂ i₁ i₂ h₁ h₂ => by
      rw [hrole_m p st₁ i₁ h₁, hrole_m p st₂ i₂ h₂]
    have hok_rk := rcv_recRecvRkOk_of_pureAccept interpretation hExt.1 hC hch₀ hrr₀
    have hstore := rcvHist_store_of_inv hrsi hrole_pair hok_rk
    have hpost' : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post := by
      rwa [← hrun_pre]
    have hch_pre : CHist interpretation r S g (ms₀ ++ pre) :=
      PureXplQuiet.quiet_cHist (rcvHist_quietPre hpre) hch₀
    have hch_m : CHist interpretation r S g (ms₀ ++ pre ++ [m]) :=
      rcvHist_snoc_of_parts hm hch_pre
        (rcv_skippedInstallByteFresh_step₂ interpretation hC hB hpre hm hpost hcur hrr_pre hrole_pre)
        hstore
    exact PureXplQuiet.quiet_cHist (rcvHist_quietPost hpost') hch_m

private theorem cBad_whisperCli_reselect_full {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g₁ : Ghost} {ms₁ : List Move} {σ₁ : List MachineEvent}
    {body coins pt : HwBytes} {t₁ : _root_.DY.Bytes}
    (ht₁ : t₁ ∈ recvRepresentations interp r S g₁ ms₁ body)
    (hnot_exc : ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp r S who ok g₁ ms₁ σ₁
      (.recv (wireWhisperTag :: body)) [.rng coins, .accept pt] body) :
    ∃ (τ₁' : List MachineEvent) (g' : Ghost) (ms' : List Move) (t' : _root_.DY.Bytes),
      ExplainsCli interp r S who ok σ₁ τ₁' g' ms' ∧
      ¬ ReadCollision interp r S g' ms' τ₁' ∧
      t' ∈ recvRepresentations interp r S g' ms' body ∧
      ¬ RecvCollision interp r S g' ms' t' ∧
      ¬ ReselectCollision interp r S g' ms' t' ∧
      ¬ ((∃ t ∈ recvRepresentations interp r S g' ms' body,
            ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
              (.recv (wireWhisperTag :: body)) [.rng coins, .accept pt] t) ∧
          ∀ t ∈ recvRepresentations interp r S g' ms' body,
            ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
              (.recv (wireWhisperTag :: body)) [.rng coins, .accept pt] t →
            RecvCollision interp r S g' ms' t) := by
  refine Classical.byContradiction fun hno => hnot_exc ⟨⟨t₁, ht₁⟩, fun τ₁' g' ms' hex' hnrc' => ?_⟩
  by_cases hac :
      (∃ t ∈ recvRepresentations interp r S g' ms' body,
        ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
          (.recv (wireWhisperTag :: body)) [.rng coins, .accept pt] t) ∧
      ∀ t ∈ recvRepresentations interp r S g' ms' body,
        ModelAcceptsTermAfterAttackerSendsMoves interp r S who ok g' ms' τ₁'
          (.recv (wireWhisperTag :: body)) [.rng coins, .accept pt] t →
        RecvCollision interp r S g' ms' t
  · exact Or.inr hac
  · refine Or.inl fun t' ht' => Classical.byContradiction fun hnc => ?_
    exact hno ⟨τ₁', g', ms', t', hex', hnrc', ht',
      fun hc => hnc (Or.inl hc), fun hrs => hnc (Or.inr hrs), hac⟩

private theorem not_acceptCollision_mid_of_bridgeC
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ₁' : List MachineEvent} {me : Participant}
    {st st' : PqParty} {d_me : DirectorySnapshot} {x : RecordExtras} {g_sess : GhostState HwBytes}
    {body pt : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    {g' : Ghost} {ms' : List Move}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hwf : ProtocolSetupWF r)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (hwho : who[(callStarts τ₁').length]? = some me)
    (hrel : PureCRel (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok records sent accepted τ₁')
    (hc' : Clean (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok g' ms' τ₁')
    (hbin : BinarySessionDecryptOk (interpOfParams interp P) P r accepted sent records me st st'
      d_me x g_sess (wireWhisperTag :: body) body pt inner rc)
    (hnac_cli : ¬ ((∃ t ∈ recvRepresentations (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) g' ms' body,
          ModelAcceptsTermAfterAttackerSendsMoves (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            who ok g' ms' τ₁' (.recv (wireWhisperTag :: body))
            [.rng (HMAC.keyToBytes32 rc), .accept pt] t) ∧
        ∀ t ∈ recvRepresentations (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) g' ms' body,
          ModelAcceptsTermAfterAttackerSendsMoves (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            who ok g' ms' τ₁' (.recv (wireWhisperTag :: body))
            [.rng (HMAC.keyToBytes32 rc), .accept pt] t →
          RecvCollision (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
            g' ms' t)) :
    ¬ AcceptCollision (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
        who ok g' ms' τ₁' (.recv (wireWhisperTag :: body))
        (Slots.pqRecvWhisperMid (interpOfParams interp P) st body (HMAC.keyToBytes32 rc) ++
          [.accept pt]) body := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let coins := HMAC.keyToBytes32 rc
  have hcoins_len : coins.length = 32 := Slots.keyToBytes32_length rc
  have hcoins_ne : coins ≠ [] := Slots.keyToBytes32_ne_nil rc
  have hcs_drop : CoinSplit [.rng coins, .accept pt] [.accept pt] :=
    .split (pieces := []) (by simp) List.nil_prefix (.keep (fun _ h => by cases h) .nil)
  have hcs_full : CoinSplit [.rng coins, .accept pt] [.rng coins, .accept pt] :=
    .split (pieces := [coins]) (by simp [hcoins_ne]) (by simp)
      (.keep (fun _ h => by cases h) .nil)
  have hmid_eq : Slots.pqRecvWhisperMid interp' st body coins =
      (if pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey then
        [.rng coins] else []) := by
    unfold Slots.pqRecvWhisperMid
    rw [hbin.2.2.2.1, hbin.2.2.2.2.2.2.2.1]
  rw [hmid_eq]
  rintro ⟨⟨t₁, ht₁, hacc₁⟩, hall_col⟩
  have hcs_mid : CoinSplit [.rng coins, .accept pt]
      ((if pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey then
        [MachineEvent.rng coins] else []) ++ [.accept pt]) := by
    split_ifs
    · exact hcs_full
    · exact hcs_drop
  apply hnac_cli
  refine ⟨⟨t₁, ht₁, _, hcs_mid, hacc₁⟩, fun t₂ ht₂ hacc_cli₂ => ?_⟩
  by_contra hncol₂
  have htwo := (Symbolic.Swarm.Coinsplit.P3.acceptsViaCli_iff_two_mids
    (σ_rest := []) hcoins_len).mp hacc_cli₂
  cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey
  · simp only [hdraw, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hall_col
    rcases htwo with h0 | h32
    · exact hncol₂ (hall_col t₂ ht₂ h0)
    · exact hncol₂ (hCA hext hagree hwf hwho hrel hc' hbin hdraw ht₂ hcs_full rfl h32)
  · simp only [hdraw, ↓reduceIte, List.cons_append, List.nil_append] at hall_col
    rcases htwo with h0 | h32
    · exact hncol₂ (hCB hext hagree hwf hwho hrel hc' hbin hdraw ht₂ hcs_drop rfl h0)
    · exact hncol₂ (hall_col t₂ ht₂ h32)

private theorem invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

private theorem whisper_cut_tau2_eq_mid
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes}
    {τ'_pre τ₂ : List MachineEvent} {me : Participant}
    {st st' : PqParty} {d_me : DirectorySnapshot} {x : RecordExtras} {g_sess : GhostState HwBytes}
    {body out : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    {g' : Ghost} {ms'_pre δ : List Move}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hwf : ProtocolSetupWF r)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (hwho : who[(callStarts τ'_pre).length]? = some me)
    (hrel_pre : PureCRel (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok records sent accepted τ'_pre)
    (hc_ext : Clean (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who ok g' (ms'_pre ++ δ) (τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)))
    (hB_blk : XplBlock (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
      who g' ms'_pre δ τ'_pre (.recv (wireWhisperTag :: body) :: τ₂))
    (hrng_cli : RngLengthsFaithfulCli (interpOfParams interp P) r
      (compSemOf (interpOfParams interp P) r) g' (ms'_pre ++ δ))
    (hcs₂ : CoinSplit [.rng (HMAC.keyToBytes32 rc), .accept out] τ₂)
    (hbin : BinarySessionDecryptOk (interpOfParams interp P) P r accepted sent records me st st'
      d_me x g_sess (wireWhisperTag :: body) body out inner rc) :
    τ₂ = Slots.pqRecvWhisperMid (interpOfParams interp P) st body (HMAC.keyToBytes32 rc) ++
      [.accept out] := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let coins := HMAC.keyToBytes32 rc
  have hcoins_len : coins.length = 32 := Slots.keyToBytes32_length rc
  have hcoins_ne : coins ≠ [] := Slots.keyToBytes32_ne_nil rc
  have hτ₂_pieces : ∃ pieces : List HwBytes, τ₂ = pieces.map .rng ++ [.accept out] := by
    cases hcs₂ with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ pieces _ τ_after _ _ hcs_after =>
      cases hcs_after with
      | @keep _ _ τ_nil _ hcs_nil =>
        cases hcs_nil
        exact ⟨pieces, rfl⟩
  obtain ⟨pieces, hτ₂_eq⟩ := hτ₂_pieces
  have hhead : ∀ e ∈ (MachineEvent.recv (wireWhisperTag :: body) :: τ₂).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hne_blk : (MachineEvent.recv (wireWhisperTag :: body) :: τ₂) ≠ [] := by simp
  have htail : ∀ e ∈ (MachineEvent.recv (wireWhisperTag :: body) :: τ₂).tail,
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
      (.recv (wireWhisperTag :: body) :: τ₂) (m.vis (runTraceMoves r (ms'_pre ++ pre))) :=
    hrun_pre ▸ hm0
  obtain ⟨v0, hv0, hv0k, _⟩ := xpl_head_entry hm_vis rfl
  have hrk := xpl_recvHeadKind m (runTraceMoves r (ms'_pre ++ pre)) hv0 hv0k
  have hacc_mem : MachineEvent.accept out ∈
      (MachineEvent.recv (wireWhisperTag :: body) :: τ₂) := by
    simp [hτ₂_eq]
  obtain ⟨v_acc, hv_acc, hev_acc⟩ := xpl_forall₂_mem_left hm_vis (.accept out) hacc_mem
  have hv_acck : v_acc.kind = .accept := by
    rw [xpl_kind_of_matches hev_acc]; rfl
  have hm_dec : (∃ q sIdx mIdx pqIdx spIdx w, m = .decrypt q sIdx mIdx pqIdx spIdx w) ∨
      (∃ q sIdx mIdx skIdx pqIdx spIdx w, m = .decryptSkipped q sIdx mIdx skIdx pqIdx spIdx w) := by
    cases m with
    | aliceStart a _ _ _ _ _ =>
      rcases xpl_accept_by (p := a) _ _ hv_acc hv_acck (Or.inr rfl) with h | h <;> cases h
    | bobStart _ _ _ _ _ _ _ _ => exact (xpl_bobStart_not_whisper hm_vis).elim
    | decrypt q sIdx mIdx pqIdx spIdx w => exact Or.inl ⟨q, sIdx, mIdx, pqIdx, spIdx, w, rfl⟩
    | decryptSkipped q sIdx mIdx skIdx pqIdx spIdx w =>
      exact Or.inr ⟨q, sIdx, mIdx, skIdx, pqIdx, spIdx, w, rfl⟩
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
    have hany : (m.vis (runTraceMoves r (ms'_pre ++ pre))).any (fun v => v.kind == .recv) = true :=
      List.any_eq_true.mpr ⟨v0, hv0, by rw [hv0k]; rfl⟩
    exact h hany
  have hcs_blk' : CoinSplit [.recv (wireWhisperTag :: body), .rng coins, .accept out]
      (.recv (wireWhisperTag :: body) :: τ₂) :=
    .keep (fun _ h => by cases h) hcs₂
  have hdich := (Symbolic.Swarm.Coinsplit.P2.accepted_recv_blk_dichotomy_of_rngLengths
    hcoins_len hrng_m hread ha hexp_nil hcs_blk' hm_vis).1
  have hτ₂_dich : τ₂ = [.accept out] ∨ τ₂ = [.rng coins, .accept out] := by
    rcases hdich with h2 | h3
    · exact Or.inl (List.cons.inj h2).2
    · exact Or.inr (List.cons.inj h3).2
  have hpre_vis : (runMoves pre (runTraceMoves r ms'_pre)).2 = [] :=
    invisible_vis_nil pre _ hpre
  have hpost_vis : (runMoves post (m.next (runMoves pre (runTraceMoves r ms'_pre)).1)).2 = [] :=
    invisible_vis_nil post _ hpost
  have hvis_pre2 : runVis r (ms'_pre ++ pre) = runVis r ms'_pre := by
    rw [Symbolic.Swarm.CREF.TR.runVis_append, hpre_vis, List.append_nil]
  have hlen_pre2 : τ'_pre.length = (runVis r (ms'_pre ++ pre)).length :=
    hB_blk.pre.2.2.2.2.2.length_eq.trans (congrArg List.length hvis_pre2).symm
  have hms_assoc1 : ms'_pre ++ (pre ++ m :: post) = (ms'_pre ++ pre) ++ (m :: post) :=
    (List.append_assoc ms'_pre pre (m :: post)).symm
  have hc_ext' : Clean interp' r S who ok g' ((ms'_pre ++ pre) ++ (m :: post))
      (τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)) := by
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
  have hlen_m : (τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)).length =
      (runVis r ((ms'_pre ++ pre) ++ [m])).length :=
    hc_ext'.1.1.2.2.2.2.2.length_eq.trans (congrArg List.length hvis_eq)
  have hc_m : Clean interp' r S who ok g' ((ms'_pre ++ pre) ++ [m])
      (τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)) := by
    have hms_assoc2 : ms'_pre ++ (pre ++ m :: post) = ((ms'_pre ++ pre) ++ [m]) ++ post := by
      simp [List.append_assoc]
    have hc_ext'' : Clean interp' r S who ok g' (((ms'_pre ++ pre) ++ [m]) ++ post)
        (τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)) := by
      rwa [← hms_assoc2]
    have hc_ext''' : Clean interp' r S who ok g' (((ms'_pre ++ pre) ++ [m]) ++ post)
        ((τ'_pre ++ (.recv (wireWhisperTag :: body) :: τ₂)) ++ []) := by
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
    rcases hm_dec with ⟨q, sIdx, mIdx, pqIdx, spIdx, w, rfl⟩ |
        ⟨q, sIdx, mIdx, skIdx, pqIdx, spIdx, w, rfl⟩ <;>
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
  have hmid_eq : Slots.pqRecvWhisperMid interp' st body coins =
      (if pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey then
        [.rng coins] else []) := by
    unfold Slots.pqRecvWhisperMid
    rw [hbin.2.2.2.1, hbin.2.2.2.2.2.2.2.1]
  rw [hmid_eq]
  have hcs_drop : CoinSplit [.rng coins, .accept out] [.accept out] :=
    .split (pieces := []) (by simp) List.nil_prefix (.keep (fun _ h => by cases h) .nil)
  have hcs_full : CoinSplit [.rng coins, .accept out] [.rng coins, .accept out] :=
    .split (pieces := [coins]) (by simp [hcoins_ne]) (by simp)
      (.keep (fun _ h => by cases h) .nil)
  rcases hτ₂_dich with rfl | rfl
  ·
    let sm : StateAndMessage := ⟨[], out⟩
    have hc_sm : CleanBy interp' r S who ok g' (ms'_pre ++ (pre ++ m :: post))
        (τ'_pre ++ RecvWirePure.rcvAccBlk body [] sm) := hc_ext
    have hB_sm : XplBlock interp' r S who g' ms'_pre (pre ++ m :: post) τ'_pre
        (RecvWirePure.rcvAccBlk body [] sm) := hB_blk
    have hcur := rcv_currentRead_of_clean_pure interp' hc_sm hB_sm hpre hpost
    have ht_rep : t_rep ∈ recvRepresentations interp' r S g' (ms'_pre ++ pre) body := by
      rcases hm_dec with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hcur.2 t_rep hrcv_term
      · exact hcur.2 t_rep hrcv_term
    have hnc_rep : ¬ RecvCollision interp' r S g' (ms'_pre ++ pre) t_rep :=
      rcv_not_recvCollision_of_clean interp' hc_sm hB_sm hpre (Or.inl rfl) hrcv_term
    have hexpl_m : ExplainsMoves interp' r S who ok g'
        ((ms'_pre ++ pre) ++ [].map .attackerSend ++ [m])
        (τ'_pre ++ .recv (wireWhisperTag :: body) :: ([MachineEvent.accept out]).take (0 + 1)) := by
      rw [List.map_nil, List.append_nil]; exact hc_m.1
    have hacc_via : ModelAcceptsTermAfterCoinSplit interp' r S who ok g' (ms'_pre ++ pre) τ'_pre
        (.recv (wireWhisperTag :: body)) [.accept out] t_rep := by
      refine ⟨[], m, msgIdx, 0, out, g', ?_, hm_idx, rfl, fun _ _ => rfl,
        hget_ext, rfl, rfl, hexpl_m⟩
      intro _ hx; cases hx
    cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey
    · rfl
    · exact absurd
        (hCB hext hagree hwf hwho hrel_pre hc_pre2 hbin hdraw ht_rep hcs_drop rfl hacc_via)
        hnc_rep
  ·
    let sm : StateAndMessage := ⟨[], out⟩
    have hc_sm : CleanBy interp' r S who ok g' (ms'_pre ++ (pre ++ m :: post))
        (τ'_pre ++ RecvWirePure.rcvAccBlk body [.rng coins] sm) := hc_ext
    have hB_sm : XplBlock interp' r S who g' ms'_pre (pre ++ m :: post) τ'_pre
        (RecvWirePure.rcvAccBlk body [.rng coins] sm) := hB_blk
    have hcur := rcv_currentRead_of_clean_pure interp' hc_sm hB_sm hpre hpost
    have ht_rep : t_rep ∈ recvRepresentations interp' r S g' (ms'_pre ++ pre) body := by
      rcases hm_dec with ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hcur.2 t_rep hrcv_term
      · exact hcur.2 t_rep hrcv_term
    have hnc_rep : ¬ RecvCollision interp' r S g' (ms'_pre ++ pre) t_rep :=
      rcv_not_recvCollision_of_clean interp' hc_sm hB_sm hpre (Or.inr ⟨coins, hcoins_len, rfl⟩)
        hrcv_term
    have hexpl_m : ExplainsMoves interp' r S who ok g'
        ((ms'_pre ++ pre) ++ [].map .attackerSend ++ [m])
        (τ'_pre ++ .recv (wireWhisperTag :: body) ::
          ([MachineEvent.rng coins, MachineEvent.accept out]).take (1 + 1)) := by
      rw [List.map_nil, List.append_nil]; exact hc_m.1
    have hacc_via : ModelAcceptsTermAfterCoinSplit interp' r S who ok g' (ms'_pre ++ pre) τ'_pre
        (.recv (wireWhisperTag :: body)) [.rng coins, .accept out] t_rep := by
      refine ⟨[], m, msgIdx, 1, out, g', ?_, hm_idx, rfl, fun _ _ => rfl,
        hget_ext, rfl, ?_, hexpl_m⟩
      · intro _ hx; cases hx
      · simp [eventKind]
    cases hdraw : pureDrawsCoins (cryptoOf' interp') (pqSession x g_sess).state inner.senderRatchetKey
    · exact absurd
        (hCA hext hagree hwf hwho hrel_pre hc_pre2 hbin hdraw ht_rep hcs_full rfl hacc_via)
        hnc_rep
    · rfl

/-! ## Main Whisper `recv` Slot Theorems -/

/-- Cut-local non-collision hypothesis: on exit `0`, `SignalMsgAcceptedOnlyViaCollisionMoves`
fails at the call's own cut for every clean explanation of `σ_pre`. -/
def RecvWNC (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (c : _root_.DY.Libsignal.Composed.Refinement.Cli.CliCall) (code : Nat) (out body : HwBytes)
    (σ_pre : List MachineEvent) (who : List Participant) (ok : Nat → Bool) : Prop :=
  code = 0 →
  ∀ τ₁ g ms, ExplainsCli interp' r S who ok σ_pre τ₁ g ms →
    ¬ ReadCollision interp' r S g ms τ₁ →
    ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g ms σ_pre (.recv c.stdin)
        [.rng c.coins, .accept out] body

private theorem slot_recvW_cli_core
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : _root_.DY.Libsignal.Composed.Refinement.Cli.CliCall}
    {i : Inputs} {body : HwBytes} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r c.party))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hstdin : c.stdin = wireWhisperTag :: body)
    (hbody_lt : body.length < 2 ^ 32)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hrec_ne : t.records r c.party ≠ none)
    (hpq : PqFromHonest t.sent body)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    CliSlotPostCore
      (RecvWNC (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) c code out body σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let c1 := toCliCallNone c
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hb' : ModelHookBridge interp' P := modelHookBridge_interpOfParams hagree
  obtain ⟨hd_eq, hrec_eq, hbca1⟩ := clean_dirs_caller_eq hwf hsim hbca hp
  have hrec_ne1 : t_clean.records r c1.party ≠ none := by
    change t_clean.records r c.party ≠ none
    rwa [hrec_eq]
  have hsb1 : StdinBounded c1 := by
    unfold StdinBounded
    simp only [c1, toCliCallNone, hcmd, hstdin]
    refine ⟨fun body₀ hb₀ => (List.cons.inj hb₀).2 ▸ hbody_lt,
      fun hnw => absurd (by simp) hnw, fun q hq => ?_,
      fun _ _ _ _ _ _ _ _ _ _ _ hpw => ?_⟩
    · simp [parsePreKeyWire, wireWhisperTag, _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag] at hq
    · unfold preKeyWire at hpw
      exact absurd (List.cons.inj hpw).1 (by decide)
  have hnext1 : ValidCall interp' r t_clean c1 := by
    refine ⟨by simpa [c1, toCliCallNone, hcmd, coinsLen] using hcoins,
      hsb1, hd_eq.symm ▸ hfb, hbca1, ?_⟩
    dsimp only [c1, toCliCallNone]; rw [hcmd]
    exact ⟨hp, rfl, rfl, Or.inl ⟨hrec_ne1, body, hstdin, hsim.sent_eq.symm ▸ hpq⟩⟩
  have hin1 : InputsFor c1 (t_clean.dirs c1.party) i :=
    hd_eq.symm ▸ inputsFor_toCliCallNone hbun hin
  have hp1 : c1.party = r.alice ∨ c1.party = r.bob := hp
  have hbca1' : BobCallAllowed r t_clean c1 := hbca1
  obtain ⟨hparty_case, st, hinvP⟩ := caller_pqPartyInv_of_allowed hsim.dirInv hbca1' hp1
  have hwf_st : PqxdhPartyInSpecDomain P st := wfPq_of_pqPartyInv hinvP (hd_eq.symm ▸ hfb)
  have hrec_st : t_clean.records r c1.party =
      (st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g) := by
    simpa using records_of_pqPartyInv hinvP
  let rc := CryptoGames.HKDF.bytesToKey32 c1.coins
  have hcoins_rc : c1.coins = HMAC.keyToBytes32 rc :=
    (keyToBytes32_bytesToKey32 hcoins).symm
  have hpeer' : peerOf r c1.party = partyAddress st.party.other := by
    rw [peerOf_eq_addrE_other, ← hinvP.party_eq]
  have hcmd_st : c1.cmd = .recv (partyAddress st.party.other) := hpeer' ▸ hcmd
  have hi' : InputsFor c1 (filesOf (encodeDir P st)) i := by rwa [hinvP.dir_eq] at hin1
  have hstdin_st : c1.stdin = wireWhisper :: body := hstdin
  have heq_in : InputsEquiv i (pqRecvInputs P st (wireWhisper :: body) rc) :=
    hstdin_st ▸ inputsEquiv_pqRecvInputs hi' hcmd_st rfl hcoins_rc
  have hobs_eq := (PqModelRel.exited_iff.mp hRel).recvWhisper st body rc hwf_st hbody_lt heq_in
  have hn3 : ¬ PreKeyNoMatch r t c := fun h => h.2.2.1 (by simp [hstdin])
  have hn1 : ¬ PreKeyNoMatch r t_clean c1 :=
    Slots.not_preKeyNoMatch_of_recvWhisper (c := c1) hstdin
  rcases exited_eq_pqObserve_iff.mp hobs_eq with
      ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, rfl⟩
  ·
    have hscr : scrub (filesOf (pqRecvInputs P st (wireWhisper :: body) rc).files) =
        t_clean.dirs c1.party := by
      rw [hinvP.dir_eq]
      exact scrub_filesOf_pqInputs_reject P st _ [] _ _
        (fun _ h => nomatch h) (fun _ h => nomatch h)
    have hDir' := pqDirInv_after_reject (out := []) hsim.dirInv hscr
    have hdirs_eq : ∀ q,
        (t_clean.after r c1 1 [] (filesOf (pqRecvInputs P st (wireWhisper :: body) rc).files)).dirs q =
          t_clean.dirs q := fun q => by
      by_cases hq : q = c1.party <;> simp [CliTurn.after, hq, hscr]
    obtain ⟨tc', acc', hsim', hstep⟩ :=
      slot_recvW_cli_nonzero hGood hB hwf hsim hp hbca hcmd hstdin Nat.one_ne_zero hDir'
        (by dsimp only [c1] at hdirs_eq; simp only [CliTurn.records, hdirs_eq])
        (by dsimp only [c1] at hdirs_eq; simp only [CliTurn.opkUsed, hdirs_eq])
    exact ⟨tc', acc', hsim', fun who ok hwho hlive _ => hstep who ok hwho hlive trivial⟩
  ·
    let files_acc := filesOf ((pqRecvInputs P st (wireWhisper :: body) rc).files ++ encodeDir P st')
    obtain ⟨hst', hsub⟩ := pqPartyInv_of_pqRecvWhisperModel hinvP hwf_st hmod
    have hscr : scrub files_acc = filesOf (encodeDir P st') :=
      scrub_filesOf_pqInputs_accept P st st' _ [] _ _
        (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
    have hDir' := pqDirInv_after_accept_same (out := out) hwf.1 hsim.dirInv hparty_case hn1 hscr hst'
    have hst'_after : PqPartyInv interp' P r accepted c1.party st'
        ((t_clean.after r c1 0 out files_acc).dirs c1.party) := by
      simpa [CliTurn.after, hscr] using hst'
    have hrec_after : (t_clean.after r c1 0 out files_acc).records r c1.party =
        (st'.session.map fun (x', g') => encodeRecordUnderExtras (fun _ => x') g') := by
      simpa using records_of_pqPartyInv hst'_after
    refine ⟨t_clean.after r c1 0 out files_acc, accepted,
      pqTurnSim1A_caller_after hwf hsim hbca hp hn3 hn1 hDir', fun who ok hwho hlive hnc => ?_⟩
    have hblk_eq : cliEntryEvents c ++ cliExitEvents c 0 out =
        [.recv (wireWhisperTag :: body), .rng (HMAC.keyToBytes32 rc), .accept out] := by
      rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq,
        Slots.cliEntryEvents_recvWhisper (c := c1) hcmd hstdin,
        Slots.cliExitEvents_recvWhisper_zero (c := c1) hcmd out, hcoins_rc]
      rfl
    have hmod_copy := hmod
    unfold pqRecvWhisperModel at hmod_copy
    rcases hsess_st : st.session with _ | ⟨x_st, g_sess_st⟩
    · simp [hsess_st] at hmod_copy
    rw [hsess_st] at hmod_copy
    cases htry_body : SignalMessage.tryFrom protoSignalCodec body with
    | error _ => simp [htry_body] at hmod_copy
    | ok inner =>
      obtain ⟨τ_acc, g₀, ms₀, hex₀, _hnrc₀⟩ := hlive.witness
      obtain ⟨t₀, ht₀⟩ :=
        Symbolic.Swarm.CREF.TR.RecvRep.recvRepresentations_nonempty_of_tryFrom
          interp' r S g₀ ms₀ body inner htry_body
      have hnot_exc : ¬ SignalMsgAcceptedOnlyViaCollisionMoves interp' r S who ok g₀ ms₀ σ_pre
          (.recv (wireWhisperTag :: body)) [.rng (HMAC.keyToBytes32 rc), .accept out] body := by
        have h0 := hnc rfl τ_acc g₀ ms₀ hex₀ _hnrc₀
        rwa [hstdin, show c.coins = HMAC.keyToBytes32 rc from hcoins_rc] at h0
      obtain ⟨τ_star, g_star, ms_star, t_star, hex_star, hnrc_star, ht_star, hnc_star,
          hnrs_star, hnac_cli⟩ :=
        cBad_whisperCli_reselect_full ht₀ hnot_exc
      have hc_star : Clean interp' r S who ok g_star ms_star τ_star :=
        explainsCli_toClean hex_star hnrc_star
      obtain ⟨hrel_star, hopk_star⟩ :=
        hlive.cutRel τ_star ⟨g_star, ms_star, hex_star, hnrc_star⟩
      have hwho_star : who[(callStarts τ_star).length]? = some c.party := by
        rw [coinSplit_callStarts_length_eq hex_star.1]; exact hwho
      have hrec_sync : t_clean.leakRecords r c.party =
          st.session.map (fun xg => encodeRecordUnderExtras (fun _ => xg.1) xg.2) := by
        change t_clean.leakRecords r c1.party = _
        rw [leakRecords_party_eq_of_cliNextCall hnext1, hrec_st]
      have hpq_clean : PqFromHonest t_clean.sent body := hsim.sent_eq.symm ▸ hpq
      have hpre_star : Slots.WhisperSlotPre interp' P r S who ok
          (callStarts τ_star).length c.party st (t_clean.leakRecords r) t_clean.sent accepted
          (t_clean.opkUsed r) τ_star body :=
        { extCli   := hext'
          bridge   := hb'
          wfR      := hwf
          semEq    := rfl
          partyMem := hp
          partyTag := hinvP.party_eq
          wfSt     := hwf_st
          recSync  := hrec_sync
          bodyLen  := hbody_lt
          pqHonest := fun _ => hpq_clean
          callIdx  := rfl
          whoAt    := hwho_star
          cleanPre := ⟨g_star, ms_star, hc_star⟩
          relPre   := hrel_star
          opkPre   := hopk_star }
      obtain ⟨x, g_sess, s', _k, _msg, g_rw, mid₀, coins_eff,
        hsess_eval, hst'_eval, hrec_p, hrec_ne_in, hss, hcanonP, hrec4, hlen31, hlen32_out,
        _hpt_lt, hwrc, htrCanon, hmid_eq0, hmid_cases, _hcs_blk0, hwho_grw, hwire_grw, hrcq_grw,
        hcoins_cases, hdco, heval⟩ :=
        Slots.pqRecvWhisper_accept_eval rc hpre_star hmod
      have hxg_eq : (x_st, g_sess_st) = (x, g_sess) := by
        exact Option.some.inj (hsess_st.symm.trans hsess_eval)
      cases hxg_eq
      let rec_in := encodeRecordUnderExtras (fun _ => x_st) g_sess_st
      let rec_out := encodeRecordUnderExtras (fun _ => x_st) { g_sess_st with session := s' }
      let sm : StateAndMessage := ⟨rec_out, out⟩
      let mid := Slots.pqRecvWhisperMid interp' st body (HMAC.keyToBytes32 rc)
      have hmid_def : mid = mid₀ := hmid_eq0.symm
      have hmid_pure : mid₀ = [] ∨ ∃ rb : HwBytes, rb.length = 32 ∧ mid₀ = [.rng rb] := by
        rcases hmid_cases with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨HMAC.keyToBytes32 rc, Slots.keyToBytes32_length rc, rfl⟩
      have hstate_lt64 : sm.state.length < 2 ^ 64 := by
        dsimp [sm, rec_out] at hlen32_out ⊢; omega
      have hC_star : PureRcvAcceptCall interp' r S who ok (callStarts τ_star).length c.party
          (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r)
          τ_star mid₀ rec_in body sm :=
        { hclean₀    := ⟨g_star, ms_star, hc_star⟩
          hrel       := hrel_star
          hopk       := hopk_star
          hwho       := hwho_star
          hj         := rfl
          hp         := hp
          hrec       := hrec_p
          hne        := hrec_ne_in
          hss        := hss
          hlen       := by dsimp [rec_in] at hlen31 ⊢; omega
          hpq        := hpq_clean
          hcanonP    := hcanonP
          hrec4      := hrec4
          hmid       := hmid_pure
          hstate_lt  := hstate_lt64
          hwc        := hwrc
          hcanon_out := htrCanon
          heval      := ⟨g_rw, coins_eff, hwho_grw, hwire_grw, hrcq_grw,
            hcoins_cases, hdco, heval⟩ }
      have hbin : BinarySessionDecryptOk interp' P r accepted t_clean.sent
          (t_clean.leakRecords r) c.party st st' (t_clean.dirs c.party) x_st g_sess_st
          (wireWhisperTag :: body) body out inner rc :=
        ⟨hp, hinvP, hwf_st, hsess_st, hrec_p, by dsimp [rec_in] at hlen31; omega,
          hpq_clean, htry_body, Or.inl ⟨rfl, hmod⟩⟩
      have hnac_mid : ¬ AcceptCollision interp' r S who ok g_star ms_star τ_star
          (.recv (wireWhisperTag :: body)) (mid₀ ++ [.accept out]) body := by
        rw [← hmid_def]
        exact not_acceptCollision_mid_of_bridgeC hext hagree hwf hCA hCB hwho_star hrel_star
          hc_star hbin hnac_cli
      have href_star : RecvExcuseFree interp' r S who ok g_star ms_star τ_star
          (.recv (wireWhisperTag :: body)) (mid₀ ++ [.accept sm.message]) body t_star :=
        ⟨hnrs_star, hnac_mid⟩
      have hik : Symbolic.Swarm.CREF.TR.IkShape interp' r :=
        Symbolic.Proofs.Swarm.TRREF.Pure.rcv_ikShape_of_externCli hext' r
      have hRes_star := RecvWirePure.slot_reselect_pure interp' hwf rfl g_star ms_star hc_star
      have hPkDNR_star := RecvWirePure.rcv_hPkDNR_of_reselect hext'.1 hwf hc_star
        (RecvWirePure.rcv_honestSkelUniq_of_matchedPrefix hc_star.matched)
        (RecvWirePure.rcv_abs_of_matchedPrefix hc_star.matched) hRes_star
      have hPkDSk_star := RecvWirePure.skipped_pk_dispatch_atK' hext' hwf hc_star
        (RecvWirePure.rcv_skippedNotJunkSeedProvAt_of_notLowAll hc_star.matched.2.1.2.2.1.1
          (hrel_star.hist hc_star).2.1)
        hRes_star
        (hrel_star.hist hc_star).2.2.1
        (RecvWirePure.skippedFreshAliasExclB_of_reach interp' hc_star.matched.2.1.2.2.1.1)
      have hw_star := RecvWirePure.recvWireStepWitness_of_acceptCallBy₂K hext' hwf hik rfl hC_star
        g_star ms_star t_star hc_star ht_star hnc_star href_star
        (RecvWirePure.rcv_hfresh_of_cleanBy interp' hc_star) hPkDNR_star hPkDSk_star
        (RecvWirePure.rcv_abs_of_matchedPrefix hc_star.matched)
      have hcs_blk_mid : CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 out)
          (.recv (wireWhisperTag :: body) :: (mid₀ ++ [.accept out])) := by
        rw [← hmid_def, cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]
        have hc_ne : c1.coins ≠ [] := by rw [hcoins_rc]; exact Slots.keyToBytes32_ne_nil rc
        have hcs0 := Slots.coinSplit_recvWhisper_accept_mid (c := c1) interp' st body out hcmd hstdin hc_ne
        rwa [hcoins_rc] at hcs0
      obtain ⟨g_mp, ms_mp, hmp_out⟩ := matchedPrefix_of_recvDecryptRawWitness hw_star
      refine ⟨⟨τ_star ++ (.recv (wireWhisperTag :: body) :: (mid₀ ++ [.accept out])),
        g_mp, ms_mp, coinSplit_append hex_star.1 hcs_blk_mid, hmp_out⟩, fun hok => ?_⟩
      simp only [decide_true] at hok
      have hok_star : ok (callStarts τ_star).length = true := by
        rw [coinSplit_callStarts_length_eq hex_star.1]; exact hok
      have hnoAdj : NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 out)) := by
        rw [hblk_eq]
        exact noAdjRng_append_of_head_nonRng hlive.noAdjRng
          ⟨Or.inl (by simp [eventKind]), Or.inr (by simp [eventKind]), trivial⟩
          (fun y hy => by simp at hy; subst hy; simp [eventKind])
      obtain ⟨g₁, stateIdx, spqrMsgIdx, pqSalt, t_m, m_step,
          hfr, ht_m, hpq_kn, _hcur, hm_step, hmp₁⟩ := hw_star
      have hraw : RawDecryptMatched interp' r S g₁
          (ms_star ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [m_step]))
          (τ_star ++ .recv (wireWhisperTag :: body) :: (mid₀ ++ [.accept out])) :=
        ⟨hmp₁.1, hmp₁.2.1, hmp₁.2.2.2.2.2⟩
      have hmid_ex : mid₀ = [] ∨ ∃ d, mid₀ = [.rng d] :=
        hmid_pure.imp id fun ⟨d, _, hd⟩ => ⟨d, hd⟩
      obtain ⟨g₁', hfr', hc₁', hbr⟩ :=
        cBadG2_of_rawWitness hc_star hnac_mid hfr ht_m hpq_kn hwho_star hok_star hm_step hmid_ex
          (Or.inl ⟨rfl, rfl, rfl⟩) hraw
      obtain ⟨pre_b, post_b, m_b, t_b, hex_b, hpre_vis_b, hpre_nd_b, hpost_nd_b,
          hm_b, hbody_b, hrep_b, hncol_b⟩ := hbr
      have hclean_ext : Clean interp' r S who ok g₁' (ms_star ++ (pre_b ++ m_b :: post_b))
          (τ_star ++ (.recv (wireWhisperTag :: body) :: (mid₀ ++ [.accept out]))) :=
        cleanBy_snoc_decrypt hc₁' hex_b hpre_vis_b hpre_nd_b hpost_nd_b hm_b hbody_b hrep_b hncol_b
      have hmid_good : mid₀ = [] ∨ ∃ coins, mid₀ = [.rng coins] ∧ coins.length = 32 :=
        hmid_pure.imp id fun ⟨rb, hlen_rb, hrb⟩ => ⟨rb, hrb, hlen_rb⟩
      obtain ⟨hex_ext, hnrc_ext⟩ :=
        hGood hex_star hcs_blk_mid (GoodStepCut.callRecvAccept hmid_good rfl hok_star)
          (Or.inl rfl) hfr'.1 hclean_ext
      refine ⟨hnoAdj, ⟨τ_star ++ (.recv (wireWhisperTag :: body) :: (mid₀ ++ [.accept out])),
        g₁', ms_star ++ (pre_b ++ m_b :: post_b), hex_ext, hnrc_ext⟩,
        fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
      rw [hblk_eq] at hex'
      obtain ⟨τ'_pre, τ₂, ms'_pre, δ, rfl, rfl, hcs_pre, hcs₂, hex'_pre, hc'_pre, hc_ext', hB_blk⟩ :=
        explainsCli_clean_split_recv hex' hnrc'
      obtain ⟨hrel'_pre, hopk'_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hc'_pre.2⟩
      have hwho_τ' : who[(callStarts τ'_pre).length]? = some c.party := by
        rw [coinSplit_callStarts_length_eq hcs_pre]; exact hwho
      have hτ₂_eq : τ₂ = mid₀ ++ [.accept out] := by
        rw [← hmid_def]
        exact whisper_cut_tau2_eq_mid hext hagree hwf hCA hCB hwho_τ' hrel'_pre
          hc_ext' hB_blk hex'.2.2.2 hcs₂ hbin
      subst hτ₂_eq
      have hC_τ' : PureRcvAcceptCall interp' r S who ok (callStarts τ'_pre).length c.party
          (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r)
          τ'_pre mid₀ rec_in body sm :=
        { hclean₀    := ⟨g', ms'_pre, hc'_pre⟩
          hrel       := hrel'_pre
          hopk       := hopk'_pre
          hwho       := hwho_τ'
          hj         := rfl
          hp         := hp
          hrec       := hrec_p
          hne        := hrec_ne_in
          hss        := hss
          hlen       := by dsimp [rec_in] at hlen31 ⊢; omega
          hpq        := hpq_clean
          hcanonP    := hcanonP
          hrec4      := hrec4
          hmid       := hmid_pure
          hstate_lt  := hstate_lt64
          hwc        := hwrc
          hcanon_out := htrCanon
          heval      := ⟨g_rw, coins_eff, hwho_grw, hwire_grw, hrcq_grw,
            hcoins_cases, hdco, heval⟩ }
      obtain ⟨hrel_post, hopk_post⟩ :=
        pureCRel_and_opk_accept_whisper_noCol hext' hwf rfl hC_τ'
      have hlr' : (t_clean.after r c1 0 out files_acc).leakRecords r =
          fun q => if q = c.party then some sm.state else t_clean.leakRecords r q := by
        rw [Slots.after_leakRecords_of_recvWhisper_ok hnext1 hstdin, hrec_after]
        funext q
        simp [hst'_eval, sm, rec_out, c1, toCliCallNone]
      have hsent' : (t_clean.after r c1 0 out files_acc).sent = t_clean.sent := by
        simp [CliTurn.after, hcmd, c1, toCliCallNone]
      have hopk' : (t_clean.after r c1 0 out files_acc).opkUsed r = t_clean.opkUsed r := by
        rcases hparty_case with hpA | ⟨hpB, hbo⟩
        · have hba : r.bob ≠ c1.party := hpA ▸ hwf.1.symm
          simp [CliTurn.opkUsed, CliTurn.after, hba]
        · have hbo' : (t_clean.after r c1 0 out files_acc).bobOff = false := by
            simp [CliTurn.after, hbo, hn1]
          have hB_pre : PqBobInv interp' P r accepted t_clean.bobOff st (t_clean.dirs r.bob) := by
            unfold PqBobInv; rw [hbo]; exact hpB ▸ hinvP
          have hB_post : PqBobInv interp' P r accepted
              (t_clean.after r c1 0 out files_acc).bobOff st'
              ((t_clean.after r c1 0 out files_acc).dirs r.bob) := by
            unfold PqBobInv; rw [hbo']
            simpa [CliTurn.after, hpB, hscr] using (hpB ▸ hst')
          have hot_eq : st'.oneTime = st.oneTime := by rw [hst'_eval]
          exact opkUsed_eq_of_pqBobInv_oneTime_eq hwf.1 hB_post hB_pre hot_eq
      rw [hlr', hsent', hopk']
      exact ⟨hrel_post, hopk_post⟩

/-- Generalized whisper `recv` slot returning `Defs.CliSlotPostW` under `RecvWNC`. -/
theorem slot_recvW_cli_gen
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (hCA : BridgeCCaseASpec)
    (hCB : BridgeCCaseBSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hwf : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : _root_.DY.Libsignal.Composed.Refinement.Cli.CliCall}
    {i : Inputs} {body : HwBytes} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hp : c.party = r.alice ∨ c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r c.party))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hstdin : c.stdin = wireWhisperTag :: body)
    (hbody_lt : body.length < 2 ^ 32)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hrec_ne : t.records r c.party ≠ none)
    (hpq : PqFromHonest t.sent body)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    Symbolic.Proofs.Swarm.UA.Defs.CliSlotPostW
      (RecvWNC (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) c code out body σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨tc', acc', hsim', hstep⟩ :=
    slot_recvW_cli_core hGood hB hCA hCB interp P r hext hagree hwf hsim hp hcmd hbun hcoins
      hstdin hbody_lt hfb hbca hrec_ne hpq hin hRel
  exact ⟨tc', acc', hsim', fun who ok hwho hlive hnc hok => (hstep who ok hwho hlive hnc).2 hok⟩

end Symbolic.Swarm.Coinsplit.Lift.L09
