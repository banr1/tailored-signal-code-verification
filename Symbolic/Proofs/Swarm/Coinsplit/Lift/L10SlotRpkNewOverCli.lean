/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
import DY.Trace.Basic
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptRecRelPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedFreshPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewAccept
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTieBundle
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyOverModel
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBobHistPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecCanonPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecRelT1Pure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecSizePure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureB
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.ExplainOKPure
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Cut-Polymorphic Non-Promote Pre-Key `recv` Slot Refinement

Proves `slot_rpk_new_over_cli_gen` and `slot_rpk_new_over_cli : SlotRpkNewOverCliSpec` for
Bob's non-promote `recv` branches: fresh pre-key session creation, `PreKeyNoMatch` overwrite,
and nonzero-exit rejections.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.Coinsplit.Lift.L10

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open _root_.DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.RpkCli
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng coinSplit_cons_nonRng_iff coinSplit_cons_rng_iff)
open Symbolic.Swarm.Coinsplit.Lift

/-! ## `CoinSplit` and `ExplainsCli` Prefix Decomposition -/

private theorem coinSplit_append_inv {σ₁ σ₂ τ : List MachineEvent}
    (h : CoinSplit (σ₁ ++ σ₂) τ) :
    ∃ τ₁ τ₂, τ = τ₁ ++ τ₂ ∧ CoinSplit σ₁ τ₁ ∧ CoinSplit σ₂ τ₂ := by
  induction σ₁ generalizing τ with
  | nil => exact ⟨[], τ, rfl, .nil, by simpa using h⟩
  | cons x σ₁' ih =>
    simp only [List.cons_append] at h
    cases h with
    | keep hx hcs =>
      obtain ⟨τ₁', τ₂, rfl, h₁, h₂⟩ := ih hcs
      exact ⟨x :: τ₁', τ₂, rfl, .keep hx h₁, h₂⟩
    | split hne hpref hcs =>
      obtain ⟨τ₁', τ₂, rfl, h₁, h₂⟩ := ih hcs
      exact ⟨_ ++ τ₁', τ₂, by simp [List.append_assoc], .split hne hpref h₁, h₂⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool}
    {ms₀ δ : List Move}
    (hof₀ : OutcomeFaithful r ok ms₀)
    (h : OutcomeFaithfulCli r ok (ms₀ ++ δ)) :
    OutcomeFaithfulCli r ok ms₀ := by
  refine ⟨hof₀, fun i m hi hvis hok => ?_⟩
  have hlt : i < ms₀.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi' : (ms₀ ++ δ)[i]? = some m := by rwa [List.getElem?_append_left hlt]
  have htk : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length hlt.le
  simpa only [htk] using h.2 i m hi' (by simpa only [htk] using hvis) (by simpa only [htk] using hok)

private theorem rngLengthsFaithfulCli_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ δ : List Move}
    (h : RngLengthsFaithfulCli interp r S g (ms₀ ++ δ)) :
    RngLengthsFaithfulCli interp r S g ms₀ := by
  intro i m hi
  dsimp only
  intro hrecv v t hv hvk hvl hvt
  have hlt : i < ms₀.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi' : (ms₀ ++ δ)[i]? = some m := by rwa [List.getElem?_append_left hlt]
  have htk : (ms₀ ++ δ).take i = ms₀.take i := List.take_append_of_le_length hlt.le
  exact h i m hi' (by simpa only [htk] using hrecv) v t (by simpa only [htk] using hv) hvk hvl hvt

private theorem explainsCli_prefix_of_split {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {σ_pre blk_cli τ_pre blk' : List MachineEvent} {g : Ghost} {ms : List Move}
    (hcs_pre : CoinSplit σ_pre τ_pre)
    (hhead : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hex : ExplainsCli interp r S who ok (σ_pre ++ blk_cli) (τ_pre ++ blk') g ms)
    (hnrc : ¬ ReadCollision interp r S g ms (τ_pre ++ blk')) :
    ∃ ms₀ δ,
      ms = ms₀ ++ δ ∧
      ExplainsCli interp r S who ok σ_pre τ_pre g ms₀ ∧
      ¬ ReadCollision interp r S g ms₀ τ_pre ∧
      XplBlock interp r S who g ms₀ δ τ_pre blk' := by
  have hc : Clean interp r S who ok g ms (τ_pre ++ blk') := explainsCli_toClean hex hnrc
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hc.matched hhead (matchedPrefix_prefix_reachable hc.matched)
  have hc₀ : Clean interp r S who ok g ms₀ τ_pre :=
    clean_prefix hpre.2.2.2.2.2.length_eq hc
  exact ⟨ms₀, δ, rfl,
    ⟨hcs_pre, hpre, outcomeFaithfulCli_prefix hc₀.1.2 hex.2.2.1,
      rngLengthsFaithfulCli_prefix hex.2.2.2⟩,
    hc₀.2, ⟨hpre, hc.matched.2.1, hmatch⟩⟩

/-! ## CLI-Level Reject Step -/

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
      CliLiveAtCli interp' r S who ok t_clean accepted σ_pre → NC who ok →
      (∃ τ_out g ms, CoinSplit (σ_pre ++ blk_cli) τ_out ∧
          MatchedPrefix interp' r S who g ms τ_out) ∧
        (ok (callStarts σ_pre).length = decide (code = 0) →
          CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli))

private theorem CliSlotPostCore.mono {NC₁ NC₂ : List Participant → (Nat → Bool) → Prop}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {t t_clean : CliTurn}
    {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot} {accepted : List HwBytes}
    {σ_pre : List MachineEvent} (himp : ∀ who ok, NC₁ who ok → NC₂ who ok)
    (h : CliSlotPostCore NC₂ interp P r t t_clean c code out files accepted σ_pre) :
    CliSlotPostCore NC₁ interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨tc', acc', hsim', hstep⟩ := h
  exact ⟨tc', acc', hsim', fun who ok hwho hlive hnc₁ => hstep who ok hwho hlive (himp who ok hnc₁)⟩

/-- Cut-local non-collision hypothesis: on exit `0`, `PreKeyStartCollidesOrRejectsMoves` fails
at the call's own cut for every clean explanation of `σ_pre` on a fresh unknown base key. -/
def RpkNewOverNC (interp' : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (accepted : List HwBytes) (c : CliCall) (code : Nat) (σ_pre : List MachineEvent)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  code = 0 → ∀ pf, parsePreKeyWire c.stdin = some pf → pf.baseKey.take 33 ∉ accepted →
  (∀ g₀ ms₀, ∃ x, x ∈ preKeyRepresentations interp' r S g₀ ms₀ c.stdin) →
  ∀ τ₁ g ms, ExplainsCli interp' r S who ok σ_pre τ₁ g ms →
    ¬ ReadCollision interp' r S g ms τ₁ → ¬ KnownBaseKey interp' r S g ms pf →
    ¬ PreKeyStartCollidesOrRejectsMoves interp' r S who ok g ms σ_pre c.stdin pf

private theorem bob_recv_cli_reject_step (hGood : GoodExit0CutSpec) (hB : BridgeBQuietFailSpec)
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {files : DirectorySnapshot} {accepted : List HwBytes} {σ_pre : List MachineEvent} (hr : ProtocolSetupWF r)
    (hDir : PqDirInv (interpOfParams interp P) P r t accepted) (hoff : t.bobOff = false)
    (hcmd : c.cmd = .recv (peerOf r r.bob)) (hscr : scrub files = t.dirs c.party) :
    CliSlotPostCore (fun _ _ => True) interp P r t t c 1 [] files accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hblk_eq : cliEntryEvents c ++ cliExitEvents c 1 [] = [.recv c.stdin, .rng c.coins] := by
    simp [cliEntryEvents, cliExitEvents, hcmd]
  have hcs_blk : CoinSplit (cliEntryEvents c ++ cliExitEvents c 1 []) [.recv c.stdin] := by
    rw [hblk_eq]
    exact CoinSplit.keep (fun _ h => nomatch h)
      (by simpa using CoinSplit.split (pieces := []) (fun _ h => nomatch h) List.nil_prefix .nil)
  refine ⟨t, accepted, ?_, fun who ok _hwho hlive _ => ?_⟩
  · rw [afterD3_eq_self_of_recv_exit1 hcmd hscr]; exact pqTurnSim1A_refl hDir hoff
  · obtain ⟨τ_pre, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
    have hc₀ : Clean interp' r S who ok g₀ ms₀ τ_pre := explainsCli_toClean hex₀ hnrc₀
    refine ⟨⟨τ_pre ++ [.recv c.stdin], g₀, Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []],
        coinSplit_append hex₀.1 hcs_blk,
        matchedPrefix_snoc_reject c.stdin [] (rpkRel_sanitize_clean hc₀).matched
          (rpkRel_sanitize_path_fail c.stdin [] hc₀)⟩, fun hok_σ => ?_⟩
    have hok_f : ok (callStarts σ_pre).length = false := by simpa using hok_σ
    have hok_τ : ok (callStarts τ_pre).length = false := by
      rwa [coinSplit_callStarts_length_eq hex₀.1]
    have hc₁ : Clean interp' r S who ok g₀
        (Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []]) (τ_pre ++ [.recv c.stdin]) :=
      rpk_clean_reject c.stdin [] hc₀ hok_τ
    refine { noAdjRng := by
               rw [hblk_eq]; exact noAdjRng_append_of_head_nonRng hlive.noAdjRng ⟨Or.inl (by simp [eventKind]), trivial⟩ (by simp [eventKind])
             witness := ⟨τ_pre ++ [.recv c.stdin], g₀, Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []],
               hGood hex₀ hcs_blk (GoodStepCut.callRecvFail hok_τ) (Or.inr rfl) (fun _ _ _ => rfl) hc₁⟩
             cutRel := fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_ }
    obtain ⟨τ'_pre, blk', rfl, hcs_pre, hcs_blk'⟩ := coinSplit_append_inv hex'.1
    rw [hblk_eq] at hcs_blk'
    obtain ⟨_, hblk'_eq, _⟩ := (coinSplit_cons_nonRng_iff (by simp [eventKind])).mp hcs_blk'
    have hhead' : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt := by
      rw [hblk'_eq]; simp [eventKind]
    obtain ⟨ms'_pre, _, _, hex'_pre, hnrc'_pre, _⟩ :=
      explainsCli_prefix_of_split hcs_pre hhead' hex' hnrc'
    obtain ⟨hrel_pre, hopk_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
    have hok_τ' : ok (callStarts τ'_pre).length = false := by
      rwa [coinSplit_callStarts_length_eq hcs_pre]
    exact hB hr (Or.inl rfl) hcs_blk' hok_τ' hrel_pre hopk_pre

private theorem bob_recv_cli_pqInputs_reject_step (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec) {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t : CliTurn} {c : CliCall} {stB : PqParty} {accepted : List HwBytes}
    {σ_pre : List MachineEvent} {NC : List Participant → (Nat → Bool) → Prop} (hr : ProtocolSetupWF r)
    (hDir : PqDirInv (interpOfParams interp P) P r t accepted) (hoff : t.bobOff = false)
    (hbob : c.party = r.bob) (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hinvB : PqPartyInv (interpOfParams interp P) P r accepted r.bob stB (t.dirs r.bob))
    (s_in : HwBytes) (rc : BitVec 256) :
    CliSlotPostCore NC interp P r t t c 1 []
      (filesOf (pqRecvInputs P stB s_in rc).files) accepted σ_pre :=
  CliSlotPostCore.mono (fun _ _ _ => trivial) <|
    bob_recv_cli_reject_step hGood hB hr hDir hoff hcmd <| by
      rw [hbob, hinvB.dir_eq]
      exact scrub_filesOf_pqInputs_reject P stB _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h)

/-! ## Accepting Pre-Key `recv` Cut Pinning and `CliLiveAtCli` Step -/

private theorem recv_accept_blk_eq {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {sent accepted : List HwBytes} {τ_pre blk' : List MachineEvent}
    {b d pt : HwBytes} {pf : PreKeyFields} {g : Ghost} {ms₀ δ : List Move}
    (hparse : parsePreKeyWire b = some pf) (hd_len : d.length = 32)
    (hfresh : ∀ q, parsePreKeyWire b = some q → q.baseKey.take 33 ∉ accepted)
    (hwho : who[(callStarts τ_pre).length]? = some r.bob)
    (hbook : CBook interp r S g ms₀ sent accepted τ_pre)
    (hcs_blk : CoinSplit [.recv b, .rng d, .accept pt] blk')
    (hB : XplBlock interp r S who g ms₀ δ τ_pre blk') (hrf : RoleFaithful r who (ms₀ ++ δ))
    (hpath : PathFaithful interp r S g (ms₀ ++ δ) (τ_pre ++ blk'))
    (hrng : RngLengthsFaithfulCli interp r S g (ms₀ ++ δ)) :
    blk' = [.recv b, .rng d, .accept pt] := by
  obtain ⟨blk₁, rfl, hcs₁⟩ := (coinSplit_cons_nonRng_iff (by simp [eventKind])).mp hcs_blk
  obtain ⟨pieces, blk₂, _hpieces_ne, hpieces_pref, rfl, hcs₂⟩ := coinSplit_cons_rng_iff.mp hcs₁
  obtain ⟨blk₃, rfl, hcs₃⟩ := (coinSplit_cons_nonRng_iff (by simp [eventKind])).mp hcs₂
  cases hcs₃
  set blk₀ : List MachineEvent := .recv b :: (pieces.map MachineEvent.rng ++ [.accept pt])
  have hhead : ∀ e ∈ blk₀.head?, eventKind e = .recv ∨ eventKind e = .pt := by simp [blk₀, eventKind]
  have hne : blk₀ ≠ [] := List.cons_ne_nil _ _
  have htail : ∀ e ∈ blk₀.tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [blk₀, List.tail_cons, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨_, _, rfl⟩ | rfl <;> simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨_hs, _ha, hm⟩, hpost⟩ := xpl_oneMove hB hhead hne htail
  obtain ⟨hpreV, hpreA⟩ := rpkRel_invisible_nil pre (runTraceMoves r ms₀) hpre
  obtain ⟨_hpostV, hpostA⟩ := rpkRel_invisible_nil post _ hpost
  obtain ⟨v₀, hv₀, hvk₀, _⟩ := xpl_head_entry hm (e := .recv b) rfl
  have hrk := xpl_recvHeadKind m _ hv₀ hvk₀
  have hi : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc, List.getElem?_append_right (by simp)]; simp
  have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc]; exact List.take_left' (by simp)
  have hf : DeltaFaithful r.bob (runTraceMoves r ms₀) (pre ++ m :: post) := by
    have hagree : ActorAgrees (moveActor m) (some r.bob) := by
      rw [rpkRel_moveActor_eq_party hrk]
      rcases hp : m.party? with _ | p
      · exact Or.inl rfl
      · refine Or.inr (Or.inr ?_)
        have hrf' := hrf (ms₀.length + pre.length) m p hi hp
        rw [htake, TR.runVis_append, hpreV, List.append_nil,
          Sanitize.callCount_of_forall₂ hB.pre.2.2.2.2.2, hwho] at hrf'
        exact hrf'.symm
    intro a ha; rw [visActorsFrom_append, hpreA, List.nil_append] at ha
    simp only [visActorsFrom, hpostA, List.append_nil] at ha
    rw [List.eq_of_mem_replicate ha]; exact hagree
  have hact : ActorIn r.bob m := actorIn_of_vis_ne_nil hf (vis_ne_nil_of_forall₂ hm hne)
  obtain ⟨w_acc, hw_acc, hew_acc⟩ := xpl_forall₂_mem_left hm (.accept pt) (by simp [blk₀])
  have hwk_acc : w_acc.kind = .accept := by rw [xpl_kind_of_matches hew_acc]; rfl
  have hbd : BobStartBy r.bob m ∨ DecryptBy r.bob m := xpl_accept_by m _ hw_acc hwk_acc hact
  have hnodec : ¬ DecryptBy r.bob m := by
    intro hdec
    have hcc : callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))) =
        (callStarts τ_pre).length := by
      rw [htake, TR.runVis_append, hpreV, List.append_nil]
      exact Sanitize.callCount_of_forall₂ hB.pre.2.2.2.2.2
    have hcs_blk₀ : callStarts blk₀ = [.recv b] := by
      have htail_cs : callStarts (pieces.map MachineEvent.rng ++ [.accept pt]) = [] := by
        rw [CREF.callStarts_append, callStarts_map_rng]; rfl
      change (if eventKind (.recv b) == .recv || eventKind (.recv b) == .pt then
          [.recv b] else []) ++ callStarts (pieces.map MachineEvent.rng ++ [.accept pt]) = [.recv b]
      rw [htail_cs]; rfl
    have hcall : (callStarts (τ_pre ++ blk₀))[
        callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length)))]? =
        some (.recv b) := by
      rw [hcc, CREF.callStarts_append, hcs_blk₀, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
    have hbook_done : ∀ ek ∈ bobDoneBaseKeys
        (runTraceMoves r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))),
        ecKey (gamma interp S g ek) ∈ accepted := by
      rw [htake, XplQuiet.quiet_bobDoneBaseKeys (b2_quietPre hpre)]; exact hbook.2.2.2
    have hnot_true : m.prekeyPath? ≠ some true := by
      intro hpath_m
      obtain ⟨ek, hek, heq⟩ := (hpath (ms₀.length + pre.length) m true b pf
        hi hpath_m hcall hparse).1 rfl
      exact hfresh pf hparse (heq ▸ hbook_done ek hek)
    have hdec_false : ∀ si mi tr',
        v₀ ∈ decVis (runMoves pre (runTraceMoves r ms₀)).1 tr' si mi false ++
          exposures (runMoves pre (runTraceMoves r ms₀)).1 tr' →
        List.Forall₂ (EventMatchesEntry interp r S g) blk₀
          (decVis (runMoves pre (runTraceMoves r ms₀)).1 tr' si mi false ++
            exposures (runMoves pre (runTraceMoves r ms₀)).1 tr') → False := by
      intro si mi tr' hv_d hm_d
      rcases hmsg : (runMoves pre (runTraceMoves r ms₀)).1.getMessageSentAt mi with _ | raw
      · rcases List.mem_append.1 hv_d with hv_d | hv_d
        · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
            List.mem_append, List.mem_map] at hv_d
          rcases hv_d with ⟨_, _, rfl⟩ | hv_d
          · dsimp [rngEntry, trEntry] at hvk₀; rcases hvk₀ with ⟨⟩ | ⟨⟩
          · cases hp : receivedPlaintext (runMoves pre (runTraceMoves r ms₀)).1 tr' <;>
              simp [hp] at hv_d
            subst hv_d; dsimp at hvk₀; rcases hvk₀ with ⟨⟩ | ⟨⟩
        · rw [xpl_exposures_kind hv_d] at hvk₀; rcases hvk₀ with ⟨⟩ | ⟨⟩
      · simp only [blk₀, decVis, hmsg, Option.map_some, Option.toList_some,
          List.cons_append] at hm_d
        cases hm_d with
        | cons hme _ =>
          obtain ⟨t, _, hb⟩ := hme.2
          change b = TripleRatchet.Refinement.wireWhisperTag :: gamma interp S g t at hb
          rw [hb] at hparse
          simp [parsePreKeyWire, TripleRatchet.Refinement.wireWhisperTag,
            PQXDH.Refinement.wirePrekeyTag] at hparse
    cases m with
    | decrypt me si mi pq sp wrapped =>
      cases wrapped
      · rw [xpl_vis_eq] at hv₀ hm; exact hdec_false si mi _ hv₀ hm
      · exact hnot_true rfl
    | decryptSkipped me si mi sk pq sp wrapped =>
      cases wrapped
      · rw [xpl_vis_eq] at hv₀ hm; exact hdec_false si mi _ hv₀ hm
      · exact hnot_true rfl
    | _ => exact False.elim hdec
  have hbs : BobStartBy r.bob m := hbd.resolve_right hnodec
  cases m with
  | bobStart pB a kh regA mh pqIdx spqrMsgIdx shown =>
    have hpB : pB = r.bob := hbs; subst hpB
    set tr := runTraceMoves r (ms₀ ++ pre)
    have htr_eq : (runMoves pre (runTraceMoves r ms₀)).1 = tr := (TR.runTrace_append r ms₀ pre).symm
    rw [htr_eq] at hm hv₀ hw_acc
    set mBob := Move.bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown
    rcases hpt : receivedPlaintext tr (mBob.next tr) with _ | pt_m
    · exact absurd hwk_acc (rpkT_bobStart_noAccept hpt hw_acc)
    · obtain ⟨w_ok⟩ := rpkT_bobStart_inv hpt
      have hnr : newRandoms tr (mBob.next tr) = [(randTerm tr.length 32, 32)] := by
        rw [w_ok.next_eq]; exact rpkT1_newRandoms_bobStartTr _ _ _ _ _ _ _ _ _ _ _
      set v_recv : VisEntry :=
        ⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk r.bob kh tr).toList,
          .preKeyRecv, none⟩
      set v_rng : VisEntry := rngEntry (randTerm tr.length 32)
      set v_acc : VisEntry := ⟨.accept, [pt_m], .single, eventIdx isBobDone tr (mBob.next tr)⟩
      have hvis_eq : mBob.vis tr = ([v_recv, v_rng, v_acc]).take shown := by
        rw [xpl_vis_eq, exposures_nil_of_not_leakKind (m := mBob) rfl (fun h => nomatch h),
          List.append_nil]
        dsimp only [xpl_ownVis, bobVis]; rw [hpt, hnr]; rfl
      have hshown_ge : 3 ≤ shown := by
        rcases shown with _ | _ | _ | shown'
        · rw [hvis_eq] at hw_acc; simp at hw_acc
        · rw [hvis_eq] at hw_acc
          simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hw_acc
          subst hw_acc; cases hwk_acc
        · rw [hvis_eq] at hw_acc
          simp only [List.take_succ_cons, List.take_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hw_acc
          rcases hw_acc with rfl | rfl <;> simp [v_recv, v_rng, rngEntry] at hwk_acc
        · omega
      have hvis_full : mBob.vis tr = [v_recv, v_rng, v_acc] := by
        rw [hvis_eq, List.take_of_length_le (by simp; omega)]
      rw [hvis_full] at hm
      rcases pieces with _ | ⟨p₀, _ | ⟨p₁, ps⟩⟩
      · simp only [blk₀, List.map_nil, List.nil_append] at hm
        cases hm with
        | cons _ hm₁ => cases hm₁ with | cons _ hm₂ => cases hm₂
      · simp only [blk₀, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm
        cases hm with
        | cons _ hm₁ =>
          cases hm₁ with
          | cons hme_rng _ =>
            have hp₀_eq : p₀ = gamma interp S g (randTerm tr.length 32) := by
              have h2 : gamma interp S g (randTerm tr.length 32) = p₀ := by
                simpa [v_rng, rngEntry, trEntry, eventBytes] using hme_rng.2
              exact h2.symm
            have hrng_m := hrng (ms₀.length + pre.length) mBob hi; dsimp only at hrng_m
            rw [htake, show runTraceMoves r (ms₀ ++ pre) = tr from rfl, hvis_full] at hrng_m
            have hlen32 : (gamma interp S g (randTerm tr.length 32)).length = 32 :=
              hrng_m (by simp [v_recv]) v_rng (randTerm tr.length 32) (by simp) rfl rfl rfl
            obtain ⟨rem, hd_eq⟩ := hpieces_pref
            simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hd_eq
            have hrem_len : rem.length = 0 := by
              have hl := congrArg List.length hd_eq
              rw [List.length_append, hp₀_eq, hlen32, hd_len] at hl; omega
            rw [List.eq_nil_of_length_eq_zero hrem_len, List.append_nil] at hd_eq
            subst hd_eq; rfl
      · have hlen := xpl_forall₂_length hm; simp [blk₀] at hlen
  | _ => exact False.elim hbs

private theorem rpk_clean_snoc_attackerSend {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} {t : _root_.DY.Bytes}
    (hc : Clean interpretation r S who ok g ms acc) (ht : t.AttackerKnows (runTraceMoves r ms)) :
    Clean interpretation r S who ok g (ms ++ [.attackerSend t]) acc :=
  clean_attackerSend hc
    (by rw [CREF.runTrace_snoc]; exact b5_attackerSend_reachable hc.matched.2.1.2.2.1.1 t ht)

private theorem rpk_callCount_lt_snoc_attackerSend {r : ProtocolSetup} {ms : List Move}
    {acc : List MachineEvent} {t : _root_.DY.Bytes}
    (hlt : ∀ i (m : Move) promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts acc).length) :
    ∀ i (m : Move) promote, (ms ++ [Move.attackerSend t])[i]? = some m →
      m.prekeyPath? = some promote →
      callCount (runVis r ((ms ++ [Move.attackerSend t]).take i)) < (callStarts acc).length := by
  intro i m promote hi hpath
  rcases Nat.lt_or_ge i ms.length with hlt_i | hge_i
  · rw [List.getElem?_append_left hlt_i] at hi; rw [List.take_append_of_le_length hlt_i.le]
    exact hlt i m promote hi hpath
  · rcases Nat.eq_or_lt_of_le hge_i with rfl | hgt_i
    · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; cases hpath
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

private theorem rpk_clean_snoc_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (hc : Clean interpretation r S who ok g ms acc)
    (hmp_out : MatchedPrefix interpretation r S who g
      (ms ++ [Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3])
      (acc ++ [.recv b, .rng d, .accept pt]))
    (hok : ok (callStarts acc).length = true) :
    Clean interpretation r S who ok g
      (ms ++ [Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3])
      (acc ++ [.recv b, .rng d, .accept pt]) := by
  let mBob := Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3
  have hof_out : OutcomeFaithful r ok (ms ++ [mBob]) := by
    intro i m hi
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      simpa only [List.take_append_of_le_length hlt.le] using hc.1.2 i m hi
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi; dsimp only
        rw [(by simp : (ms ++ [mBob]).take ms.length = ms), matchedPrefix_callCount_eq hc.matched]
        exact ⟨(fun _ hrej => nomatch hrej), fun _ => hok⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  refine ⟨⟨hmp_out, hof_out⟩, not_readCollision_append_of_no_decrypt hc.not_readCollision
    (matchedPrefix_length_eq hc.matched) ?_ (fun _ h => nomatch h)⟩
  intro m hm _; simp only [List.mem_singleton] at hm; subst hm; rfl

private theorem rpk_construct_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent} {b : HwBytes} {sm : StateAndMessage} {p : PreKeyFields}
    {d ct_wire pt : HwBytes} {g' : Ghost} {ms' : List Move} {x' : PreKeyRep}
    (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hA : RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed
      acc b sm p d ct_wire pt)
    (hnkm : ¬ KyberMismatch interpretation r p)
    (hc' : Clean interpretation r S who ok g' ms' acc)
    (hx' : x' ∈ preKeyRepresentations interpretation r S g' ms' b)
    (hnbsc : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms' p x') :
    ∃ (g_out : Ghost) (δ : List Move),
      (∀ ts < (runTraceMoves r ms').length, ∀ sz, g_out.σ ts sz = g'.σ ts sz) ∧
      MatchedPrefix interpretation r S who g_out
        (Sanitize.sanitizeMoves (setupTrace r) ms' ++ δ)
        (acc ++ [.recv b, .rng d, .accept pt]) ∧
      (ok (callStarts acc).length = true →
        Clean interpretation r S who ok g_out
          (Sanitize.sanitizeMoves (setupTrace r) ms' ++ δ)
          (acc ++ [.recv b, .rng d, .accept pt])) := by
  have hSeedAk : RpkSeedAkHyp interpretation r S := rpk_seedAkHyp hext hwf hSeq
  have hNotSpqrMac : RpkNotSpqrMacHyp interpretation r S := rpk_notSpqrMacHyp interpretation r S
  have hC := hA.contract
  have hp : parsePreKeyWire b = some p := hC.parse
  set ms_s := Sanitize.sanitizeMoves (setupTrace r) ms'
  have hc_s : Clean interpretation r S who ok g' ms_s acc := rpkRel_sanitize_clean hc'
  have hlt_s : ∀ i (m : Move) promote, ms_s[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms_s.take i)) < (callStarts acc).length :=
    fun _ _ _ hi hpath => Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hc'.matched hi hpath
  have hx_s : x' ∈ preKeyRepresentations interpretation r S g' ms_s b := by
    rwa [Sanitize.preKeyRepresentations_sanitizeMoves]
  have hnbsc_s : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms_s p x' := by
    rwa [rpk_bobStartCollision_sanitizeMoves]
  have hS_ck : S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interpretation := by
    rw [hSeq]; rfl
  obtain ⟨hek'_gamma, _, msg', hparse', hwire'_gamma, hmac'_gamma, _, hcipher'_gamma, hrk'_gamma,
      hpq'_gamma, hctr'_eq, _⟩ :=
    TR.rep_ek_ct_gamma interpretation r S g' ms_s b p ct_wire x' hp hC.kyber_ct hx_s
  have hctr'_le : msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps := hctr'_eq ▸ hC.counter_le
  have hpq'_ne : gamma interpretation S g' msg'.pqRatchet ≠ [] := hpq'_gamma ▸ hC.pqRatchet_ne_nil
  obtain ⟨_, _, _, salt', seed', hbk', hcmk', hspqr', hbss', _⟩ :=
    bobSaltSeed_some_of_not_implicitReject hC.opk_ok hparse' hctr'_le hpq'_ne
  obtain ⟨hsalt'_gamma, hseed'_gamma, _⟩ :=
    TR.bobSaltSeed_gamma interpretation hext.1 r hwf S g' hc_s.matched.1 opkUsed b p hp hnkm
      ct_wire hC.kyber_ct hC.ct_len hC.opk_ok hC.counter_le hC.pqRatchet_ne_nil
      ms_s x' hx_s msg' salt' seed' hparse' hbss'
  have hlow' := x25519LowOrder_false_of_gamma_notLow interpretation hext.1 S g'
    (hrk'_gamma ▸ hC.ratchetKey_ok)
  have hek_eq : TR.ekBytes p = (p.baseKey.take 33).drop 1 := by simp [TR.ekBytes, List.drop_take]
  have hek'_rw : gamma interpretation S g' x'.ek = (p.baseKey.take 33).drop 1 :=
    hek'_gamma.trans hek_eq
  obtain ⟨hp0, hp2, _⟩ := TR.gamma_setupPublic_0_2_6 interpretation r S g' hc_s.matched.1 hwf.1
  have hmac_T_gamma :
      gamma interpretation S g'
        (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
          (PQXDH.serializedIk (setupPublic r 0))
          (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
        gamma interpretation S g' msg'.mac := by
    rw [TR.gamma_computeMac, TR.gamma_trMsgKeys_macKey, hsalt'_gamma, hseed'_gamma,
      TR.gamma_serializedIk, TR.gamma_serializedIk, hp0, hp2, hwire'_gamma]
    exact (hC.mac_eq S hS_ck).trans hmac'_gamma.symm
  have hguard :=
    rpk_bobTrialGuard_of_contract hext.1 hwf.1 hC hA.ready.2.2 hc_s hx_s hparse'
  have hdec_salt'_seed' :
      interpretation _root_.DY.Libsignal.Refinement.aesCbcDecryptSymbol
        [gamma interpretation S g' msg'.ciphertext,
         gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').cipherKey,
         (gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt := by
    rw [hcipher'_gamma, TR.gamma_trMsgKeys_cipherKey, TR.gamma_trMsgKeys_iv,
      hsalt'_gamma, hseed'_gamma]; exact hC.dec_eq S hS_ck
  have hcmac_len : (gamma interpretation S g' msg'.mac).length = 8 := by
    rw [← hmac_T_gamma, TR.gamma_computeMac]; unfold TR.computeMacBytes
    rw [List.length_take, TR.length_hmacWith]; decide
  have hpt_mac : msg'.mac ∉ plaintextTerms (runVis r ms_s) := by
    simpa using TR.G1.g1_rep_ptAtoms_tr r ms_s [] (fun _ h => nomatch h) hparse'
  obtain ⟨x, msg, salt, seed, pqSalt, m, hx, hcan, hparse, hlow, hbss, hpq_ak, hmac, hdec, hpt⟩ :=
    rpk_exactRep_of_not_bobStartCollision hwf hext.1 hext.2 hNotSpqrMac hSeedAk
      hc_s.matched hp hnkm hC.kyber_ct hC.ct_len
      (hC.opk_ok.imp id fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩) hx_s hnbsc_s hbk' hguard hparse' hcmk' hspqr'
      hbss' (hek'_rw ▸ hC.baseKey_ok.1) (hek'_rw ▸ hC.baseKey_ok.2.1) (hek'_rw ▸ hC.baseKey_ok.2.2)
      hlow' hctr'_le hcmac_len hmac_T_gamma hdec_salt'_seed' hpq'_ne hpt_mac
  let ms₁ := ms_s ++ [Move.attackerSend x.ek]
  let ms₂ := ms₁ ++ [Move.attackerSend x.ct]
  let ms₃ := ms₂ ++ [Move.attackerSend x.msg]
  let ms₄ := ms₃ ++ [Move.attackerSend pqSalt]
  have hx₁ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ek]) hx
  have hx₂ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ct]) hx₁
  have hx₃ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.msg]) hx₂
  have hx₄ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend pqSalt]) hx₃
  have hpq₃ : pqSalt.AttackerKnows (runTraceMoves r ms₃) :=
    _root_.DY.Bytes.AttackerKnows_le _ _ _ (CREF.runTrace_le_append r ms₂ _)
      (_root_.DY.Bytes.AttackerKnows_le _ _ _ (CREF.runTrace_le_append r ms₁ _)
        (_root_.DY.Bytes.AttackerKnows_le _ _ _ (CREF.runTrace_le_append r ms_s _) hpq_ak))
  have hc₁ := rpk_clean_snoc_attackerSend hc_s hx.1
  have hc₂ := rpk_clean_snoc_attackerSend hc₁ hx₁.2.1
  have hc₃ := rpk_clean_snoc_attackerSend hc₂ hx₂.2.2.1
  have hc₄ := rpk_clean_snoc_attackerSend hc₃ hpq₃
  have hlt₄ := rpk_callCount_lt_snoc_attackerSend
    (rpk_callCount_lt_snoc_attackerSend
      (rpk_callCount_lt_snoc_attackerSend
        (rpk_callCount_lt_snoc_attackerSend hlt_s (t := x.ek)) (t := x.ct)) (t := x.msg))
    (t := pqSalt)
  let mh : PQXDH.PreKeyMsgHandles :=
    ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
  let pqIdx : Nat := (runTraceMoves r ms₃).length
  have hek₄ : (runTraceMoves r ms₄).at? mh.ek = some (TR.NetE x.ek) :=
    rpk_at?_some_of_le (CREF.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (CREF.runTrace_le_append r ms₂ _)
        (rpk_at?_some_of_le (CREF.runTrace_le_append r ms₁ _)
          (by rw [CREF.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _)))
  have hct₄ : (runTraceMoves r ms₄).at? mh.ct = some (TR.NetE x.ct) :=
    rpk_at?_some_of_le (CREF.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (CREF.runTrace_le_append r ms₂ _)
        (by rw [CREF.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _))
  have hmsg₄ : (runTraceMoves r ms₄).at? mh.msg = some (TR.NetE x.msg) :=
    rpk_at?_some_of_le (CREF.runTrace_le_append r ms₃ _)
      (by rw [CREF.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _)
  have hpqSalt : (((runTraceMoves r ms₄).append (TR.RndE 32)).append (TR.NetE salt)).at? pqIdx =
      some (TR.NetE pqSalt) :=
    rpk_at?_some_of_le (_root_.DY.Trace.append_le _ _)
      (rpk_at?_some_of_le (_root_.DY.Trace.append_le _ _)
        (by rw [CREF.runTrace_snoc, b5_attackerSend_next]; exact TR.at?_append_self _ _))
  have hno_done : ∀ q, parsePreKeyWire b = some q →
      ¬ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms₄),
        ecKey (gamma interpretation S g' ek) = q.baseKey.take 33 := by
    intro q hq ⟨ek, hek, heq⟩
    exact hA.fresh q hq (heq ▸ (hA.ready.2.1.clean g' ms₄ hc₄).1.2.1.2.2.2 ek hek)
  obtain ⟨opk, _, hmp_out⟩ :=
    rpk_bobStart_of_exactRep_pqSalt_at hwf.1 hc₄.matched hlt₄ hA.who_cs hno_done hp hC.version hx₄
      hcan hparse hlow hbss hpqSalt hmac hdec hpt
      (fun hw hpk => by
        rcases hC.opk_ok with hnone | ⟨_, hu, _⟩
        · rw [hnone] at hpk; cases hpk
        · simpa only [← rpk_setupPublic_8 r hwf.1 hw] using hA.ready.2.2 hw hu g' ms₄ hc₄)
      hek₄ hct₄ hmsg₄
  let g_out : Ghost :=
    { g' with σ := TR.FreshSigma.updateFreshAt g'.σ (runTraceMoves r ms₄).length 32 d }
  let mBob := Move.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1 mh pqIdx (preKeySpqrIndex p) 3
  let δ : List Move :=
    [Move.attackerSend x.ek, Move.attackerSend x.ct, Move.attackerSend x.msg,
     Move.attackerSend pqSalt, mBob]
  have hms_eq : ms₄ ++ [mBob] = ms_s ++ δ := by
    simp only [ms₄, ms₃, ms₂, ms₁, δ, List.append_assoc, List.cons_append, List.nil_append]
  have hfr : CBadSigmaFrame g' g_out (runTraceMoves r ms₄).length :=
    cBadSigmaFrame_updateFreshAt g' (Nat.le_refl _) 32 d
  have hlen_le : (runTraceMoves r ms').length ≤ (runTraceMoves r ms₄).length := by
    have hs_eq : (runTraceMoves r ms').length = (runTraceMoves r ms_s).length := by
      rw [Sanitize.runTrace_sanitizeMoves]
    have h1 : (runTraceMoves r ms₁).length = (runTraceMoves r ms_s).length + 1 := by
      dsimp only [ms₁]; rw [CREF.runTrace_snoc, b5_attackerSend_next]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have h2 : (runTraceMoves r ms₂).length = (runTraceMoves r ms₁).length + 1 := by
      dsimp only [ms₂]; rw [CREF.runTrace_snoc, b5_attackerSend_next]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have h3 : (runTraceMoves r ms₃).length = (runTraceMoves r ms₂).length + 1 := by
      dsimp only [ms₃]; rw [CREF.runTrace_snoc, b5_attackerSend_next]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    have h4 : (runTraceMoves r ms₄).length = (runTraceMoves r ms₃).length + 1 := by
      dsimp only [ms₄]; rw [CREF.runTrace_snoc, b5_attackerSend_next]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  refine ⟨g_out, δ, fun ts hts sz => hfr.1 ts (Nat.lt_of_lt_of_le hts hlen_le) sz,
    hms_eq ▸ hmp_out, fun hok_cs => ?_⟩
  exact hms_eq ▸ rpk_clean_snoc_bobStart (cbadG2_cleanBy_transfer hfr hc₄) hmp_out hok_cs

private theorem rpk_accept_cRel_of_not_kyberMismatch {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {acc : List MachineEvent} {b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {d ct_wire pt : HwBytes} (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hA : RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed
      acc b sm pf d ct_wire pt)
    (hBin : RpkAcceptBin pf sm) (hTie : AcceptD.AcceptTieD interpretation r pf d pt sm)
    (hkm : ¬ KyberMismatch interpretation r pf) :
    PureCRel interpretation r S who ok
      (fun q => if q = r.bob then some sm.state else records q)
      sent (accepted ++ [pf.baseKey.take 33]) (acc ++ [.recv b, .rng d, .accept pt]) := by
  have hrel := hA.ready.2.1
  have hlenA : (pf.baseKey.take 33).length = 33 := by
    have h := hA.contract.baseKey_ok.1; simp only [List.length_drop] at h; omega
  obtain ⟨st'_rec, f248, regIdB, hscope, hinv, hclamp, hsm_rec⟩ := hBin.record
  obtain ⟨rr₀, hN₀, h0₀, hcur₀, -, hkyb₀⟩ :=
    recvPrekey_accept_record hscope hinv hlenA hclamp hsm_rec
  have hbk₀ : rr₀.current.aliceBaseKey = pf.baseKey.take 33 := by rw [hcur₀]; rfl
  have hfields : ∀ {rr : RecordRec}, sm.state = recordBytes rr →
      rr.current.aliceBaseKey = pf.baseKey.take 33 ∧ rr.current.pendingKyberPreKey = none := by
    intro rr hrr
    have hcur : TR.normPendingS rr.current = TR.normPendingS rr₀.current :=
      congrArg RecordRec.current (TR.recordBytes_injective (hN₀.symm.trans hrr).symm)
    have hbk : rr.current.aliceBaseKey = rr₀.current.aliceBaseKey := by
      simpa [TR.normPendingS] using congrArg SessionRec.aliceBaseKey hcur
    have hkyb : (rr.current.pendingKyberPreKey.map fun p => (p.1 ++ p.2, ([] : HwBytes))) = none := by
      have h := congrArg SessionRec.pendingKyberPreKey hcur
      simp only [TR.normPendingS] at h; rw [h, hkyb₀]; rfl
    refine ⟨hbk.trans hbk₀, ?_⟩
    cases hk : rr.current.pendingKyberPreKey with
    | none => rfl
    | some _ => rw [hk] at hkyb; simp at hkyb
  have hooo' : COooAll (fun q => if q = r.bob then some sm.state else records q) :=
    cOOO_step_update hrel.oooAll
      (AcceptD.newOoo_of_acceptTieD hext.1 hwf hA.contract.baseKey_ok.1 hTie)
  have hbka' : BobRecordBaseKeyInAccepted r
      (fun q => if q = r.bob then some sm.state else records q)
      (accepted ++ [pf.baseKey.take 33]) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr
    rw [(hfields hrr).1]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hbkn' : PureBobKyberNone r (fun q => if q = r.bob then some sm.state else records q) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr; exact (hfields hrr).2
  have hcanon : sm.state.length < 2 ^ 32 - 2 ^ 20 → TR.PureTRRecordCanon r r.bob sm.state :=
    AcceptD.recCanon_of_acceptTieD hext.1 hwf r.bob hA.contract.baseKey_ok.1 hTie
  obtain ⟨hlen0, hlow0⟩ := rpkBH_senderRatchetKey_len_notLow hext.1 hTie
  refine ⟨hooo', TR.sendsFit_append hrel.sendsFit (rpk_accept_sendsFit b d pt), hbka', hbkn',
    fun g ms hc => ?_⟩
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre₀, hmatch⟩ :=
    matchedPrefix_split hmp (rpkA2_blockHead b d pt) (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interpretation r S who ok g ms₀ acc := clean_prefix hpre₀.2.2.2.2.2.length_eq hc
  obtain ⟨⟨hrecs₀, ⟨hs₀, hns₀, ha1₀, ha2₀⟩, hch₀, hrole₀⟩, -⟩ := hrel.clean g ms₀ hc₀
  have hB : XplBlock interpretation r S who g ms₀ δ acc [.recv b, .rng d, .accept pt] :=
    ⟨hpre₀, hmp.2.1, hmatch⟩
  have hdf := rpk_deltaFaithful_of_roleFaithful rfl hB hmp.2.2.1 hA.who_cs
  have hrole' := rpk_roleSnapshots_accept hwf hB hdf hrole₀
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, _, hacc⟩, hpost⟩ :=
    xplInv_rpk hB hdf (rpkA2_blockShape b d pt)
  have hnodec := rpk_noDecrypt_of_pathFaithful hA.contract.parse hA.fresh hB hpre hpost
    hmp.2.2.2.1 ⟨hs₀, hns₀, ha1₀, ha2₀⟩
  have hbs : BobStartBy r.bob m := (hacc (rpkA2_blockAccept b d pt)).resolve_right hnodec
  have hbob : ∀ a kh regA mh pqIdx spqrMsgIdx shown,
      m = .bobStart r.bob a kh regA mh pqIdx spqrMsgIdx shown →
      ∃ w : BobStartOk (runTraceMoves r (ms₀ ++ pre)) r.bob a kh regA mh pqIdx spqrMsgIdx,
        RpkRecRel interpretation S g (runTraceMoves r ((ms₀ ++ pre) ++ [m])) r.bob (rpkR_finalSt w)
          sm.state ∧
        TR.TRKeyShape interpretation S g (rpkR_finalSt w) ∧
        gamma interpretation S g w.msg.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    intro a kh regA mh pqIdx spqrMsgIdx shown hm; subst hm
    have ha : a = r.alice := rpk_peer_eq_of_peerFaithful hmp.2.1.2.2.2.2.2.1; subst ha
    obtain ⟨_, ⟨w⟩⟩ := rpkT_bobStart_block hB hpre
    have hrep := rpk_rep_of_readFaithful hB hpre hpost w hmp.2.2.2.2.1
    have hG := rpkT1_glue_of_rep hext.1 hwf hSeq hA.contract.parse hA.contract.d_len
      hA.contract.opk_ok hkm hB hpre w hrep
      (rpk_skipped_fresh hB hpre w ha2₀ hA.contract.parse (hA.fresh pf hA.contract.parse))
    have hrecRel := rpkT1_of_glue hext.1 hTie hA.state_lt shown hG
    have hdhs :
        (gamma interpretation S g (randTerm (runTraceMoves r (ms₀ ++ pre)).length 32)).length = 32 := by
      rw [(rpkT1_rng_eq hB hpre).2]; exact hA.contract.d_len
    have hks : TR.TRKeyShape interpretation S g (rpkR_finalSt w) := by
      refine ⟨hdhs, ?_, ?_, ?_⟩
      · dsimp only [rpkR_finalSt, bobRatchetedSt]
        unfold _root_.DY.Libsignal.TripleRatchet.createChain _root_.DY.X25519.agree _root_.DY.Libsignal.TripleRatchet.kdfRk _root_.DY.Libsignal.TripleRatchet.hkdfBlock1
          _root_.DY.Libsignal.TripleRatchet.hkdfBlock2
        dsimp only; rw [TR.gamma_hmac]; exact TR.length_hmacWith _ _ _
      · dsimp only [rpkR_finalSt, bobRatchetedSt]; rw [TR.gamma_serializedIk]; rfl
      · dsimp only [rpkR_finalSt, bobRatchetedSt]; rw [TR.gamma_serializedIk]; rfl
    have hrk_eq : gamma interpretation S g w.msg.ratchetKey =
        pf.inner.senderRatchetKey.bytes.toList := by
      rw [hG.their]
      exact (Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hG.pkLen).symm
    exact ⟨w, hrecRel, hks, hrk_eq⟩
  have htieRec : TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre ++ [m])
      (fun q => if q = r.bob then some sm.state else none) :=
    rpkR_pureTieRec_reduce hbs hcanon fun a kh regA mh pqIdx spqrMsgIdx shown hm => by
      obtain ⟨w, hrr, hks, -⟩ := hbob a kh regA mh pqIdx spqrMsgIdx shown hm; exact ⟨w, hrr, hks⟩
  have hch_step : TR.CHistStep.CHist interpretation r S g (ms₀ ++ pre ++ [m]) := by
    have hch_pre := XplQuiet.quiet_cHist (b2_quietPre hpre) hch₀
    cases m with
    | bobStart p a kh regA mh pqIdx spqrMsgIdx shown =>
      have hp_bob : p = r.bob := hbs; subst hp_bob
      obtain ⟨w, ⟨_, _, hrel', _, hnd', -⟩, -, hrk_eq⟩ := hbob a kh regA mh pqIdx spqrMsgIdx shown rfl
      have ha : a = r.alice := rpk_peer_eq_of_peerFaithful hmp.2.1.2.2.2.2.2.1; subst ha
      exact rpkBH_cHist_bobStart shown w hch_pre hrel' hnd' (hrk_eq ▸ hlen0) (hrk_eq ▸ hlow0)
    | _ => exact False.elim hbs
  have hch' := XplQuiet.quiet_cHist (b2_quietPost hpost) hch_step
  obtain ⟨ek, hek, hγ⟩ := rpkT_tie_baseKey hA.contract.parse hB hpre hbs
  have hkeys : bobDoneBaseKeys (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) ++ [ek] := by
    rw [XplQuiet.quiet_bobDoneBaseKeys (b2_quietPost hpost), hek,
      XplQuiet.quiet_bobDoneBaseKeys (b2_quietPre hpre)]
  have hbks' : BobRecordBaseKeyInSession interpretation r S g (ms₀ ++ (pre ++ m :: post))
      (fun q => if q = r.bob then some sm.state else records q) := by
    intro rr hrr; simp only [↓reduceIte, Option.some.injEq] at hrr
    rw [(hfields hrr).1]; exact bks_bobStart hwf hA.contract.parse hB hpre hpost hbs hrole'
  refine ⟨⟨fun p bs hpb => ?_, ⟨?_, rpkA2_nsBound hB hpre hpost hbs hns₀, ?_, ?_⟩,
    ⟨hch', hrole'⟩⟩, hbks'⟩
  · by_cases hp : p = r.bob
    · subst hp; simp only [ite_true, Option.some.injEq] at hpb; subst hpb
      exact ⟨Or.inr rfl, fun h => b2_encodeRecord_ne_nil _ (hsm_rec ▸ h),
        Or.inl (XplQuiet.quiet_pureCRecRel (b2_quietPost hpost) (Or.inl htieRec))⟩
    · simp only [hp, ite_false] at hpb; obtain ⟨hmem, hne, hcr⟩ := hrecs₀ p bs hpb
      exact ⟨hmem, hne, rpk_pureCRecRelH_mono (fun _ => rpkA2_frame hwf hB hpre hpost hbs hp) hcr⟩
  · rw [hs₀, rpkA2_sentBodies]
  · rw [hkeys]; intro k hk; rcases List.mem_append.1 hk with hk | hk
    · obtain ⟨ek', hmem, rfl⟩ := ha1₀ k hk; exact ⟨ek', List.mem_append_left _ hmem, rfl⟩
    · rw [List.mem_singleton] at hk
      exact ⟨ek, List.mem_append_right _ (List.mem_singleton_self _), hk.trans hγ.symm⟩
  · rw [hkeys]; intro ek' hek'; rcases List.mem_append.1 hek' with hm | hm
    · exact List.mem_append_left _ (ha2₀ ek' hm)
    · rw [List.mem_singleton] at hm; subst hm; rw [hγ]
      exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem rpkNew_accept_cliLiveAtCli (hGood : GoodExit0CutSpec)
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {t t' : CliTurn} {c : CliCall} {peer : Address}
    {accepted : List HwBytes} {σ_pre : List MachineEvent} {body ct_wire pt : HwBytes}
    {sm : StateAndMessage} {pf : PreKeyFields} (hext : ExternContractsHoldCli interp)
    (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interp r) (hcmd : c.cmd = .recv peer)
    (hstdin : c.stdin = wirePrekey :: body) (hwho : who[(callStarts σ_pre).length]? = some r.bob)
    (hlive : CliLiveAtCli interp r S who ok t accepted σ_pre)
    (hnc : RpkNewOverNC interp r S accepted c 0 σ_pre who ok)
    (hhon : HonestIdentity interp r (wirePrekey :: body))
    (hpqh : ∀ q, parsePreKeyWire (wirePrekey :: body) = some q → PqFromHonest t.sent q.message)
    (hfresh : ∀ q, parsePreKeyWire (wirePrekey :: body) = some q → q.baseKey.take 33 ∉ accepted)
    (hst_lt : sm.state.length < 2 ^ 64)
    (hcontract : RecvAcceptContractPure interp r (t.opkUsed r) (wirePrekey :: body)
      sm pf c.coins ct_wire pt)
    (hBin : RpkAcceptBin pf sm) (hTie : AcceptD.AcceptTieD interp r pf c.coins pt sm)
    (hsent' : t'.sent = t.sent)
    (hleak' : t'.leakRecords r = fun q => if q = r.bob then some sm.state else t.leakRecords r q)
    (hopk' : t'.opkUsed r = (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8))) :
    let blk_cli := cliEntryEvents c ++ cliExitEvents c 0 pt
    (∃ τ_out g ms, CoinSplit (σ_pre ++ blk_cli) τ_out ∧
        MatchedPrefix interp r S who g ms τ_out) ∧
      (ok (callStarts σ_pre).length = decide ((0 : Nat) = 0) →
        CliLiveAtCli interp r S who ok t' (accepted ++ [pf.baseKey.take 33]) (σ_pre ++ blk_cli)) := by
  dsimp only
  set b : HwBytes := wirePrekey :: body; set d : HwBytes := c.coins
  have hblk_cli : cliEntryEvents c ++ cliExitEvents c 0 pt = [.recv b, .rng d, .accept pt] := by
    simp [cliEntryEvents, cliExitEvents, hcmd, hstdin, b, d]
  have hcs_blk : CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 pt) [.recv b, .rng d, .accept pt] := by
    simpa [hstdin, b, d] using
      Slots.coinSplit_rpkNew_accept hcmd (Slots.coins_ne_nil_of_len_32 hcontract.d_len) pt
  have hA_of_cut : ∀ {τ_cut : List MachineEvent},
      (∃ g' ms', ExplainsCli interp r S who ok σ_pre τ_cut g' ms' ∧
        ¬ ReadCollision interp r S g' ms' τ_cut) →
      RpkAcceptHypsPure interp r S who ok (t.leakRecords r) t.sent accepted (t.opkUsed r)
        τ_cut b sm pf d ct_wire pt := fun ⟨g', ms', hex', hnrc'⟩ =>
    { ready := hlive.cliLiveAt_of_cut ⟨g', ms', hex', hnrc'⟩
      who_cs := by rwa [coinSplit_callStarts_length_eq hex'.1]
      hon := hhon, pqh := hpqh, fresh := hfresh, state_lt := hst_lt, contract := hcontract }
  obtain ⟨τ₀, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
  have hc₀ : Clean interp r S who ok g₀ ms₀ τ₀ := explainsCli_toClean hex₀ hnrc₀
  have hA₀ := hA_of_cut ⟨g₀, ms₀, hex₀, hnrc₀⟩
  have hrep₀ : ∃ x, x ∈ preKeyRepresentations interp r S g₀ ms₀ b :=
    rpk_reps_nonempty_of_contract g₀ ms₀ hhon hcontract
  have hnk₀ : ¬ KnownBaseKey interp r S g₀ ms₀ pf := fun ⟨ek, hek, heq⟩ =>
    hfresh pf hcontract.parse (heq ▸ (hA₀.ready.2.1.clean g₀ ms₀ hc₀).1.2.1.2.2.2 ek hek)
  have hnexc : ¬ PreKeyStartCollidesOrRejectsMoves interp r S who ok g₀ ms₀ σ_pre b pf := by
    have h0 := hnc rfl pf (hstdin.symm ▸ hcontract.parse) (hfresh pf hcontract.parse)
      (fun g' ms' => hstdin.symm ▸ rpk_reps_nonempty_of_contract g' ms' hhon hcontract)
      τ₀ g₀ ms₀ hex₀ hnrc₀ hnk₀
    rwa [hstdin] at h0
  have hnkm : ¬ KyberMismatch interp r pf := fun hkm => hnexc ⟨hrep₀, Or.inl hkm⟩
  have hex_star : ∃ τ₁' g' ms' x',
      ExplainsCli interp r S who ok σ_pre τ₁' g' ms' ∧ ¬ ReadCollision interp r S g' ms' τ₁' ∧
      x' ∈ preKeyRepresentations interp r S g' ms' b ∧
      ¬ BobSessionStartCollidesOrImplicitRejects interp r S g' ms' pf x' := by
    by_contra hno
    exact hnexc ⟨hrep₀, Or.inr fun τ₁' g' ms' hex₁ hnrc₁ x' hx₁ =>
      Classical.byContradiction fun hnbsc => hno ⟨τ₁', g', ms', x', hex₁, hnrc₁, hx₁, hnbsc⟩⟩
  obtain ⟨τ_star, g_star, ms_star, x_star, hex_s, hnrc_s, hx_s, hnbsc_s⟩ := hex_star
  obtain ⟨g_out, δ, hfr_out, hmp_out, hclean_out⟩ :=
    rpk_construct_bobStart hext hwf hSeq (hA_of_cut ⟨g_star, ms_star, hex_s, hnrc_s⟩) hnkm
      (explainsCli_toClean hex_s hnrc_s) hx_s hnbsc_s
  refine ⟨⟨τ_star ++ [.recv b, .rng d, .accept pt], g_out,
      Sanitize.sanitizeMoves (setupTrace r) ms_star ++ δ,
      coinSplit_append hex_s.1 hcs_blk, hmp_out⟩, fun hok_σ => ?_⟩
  have hok_t : ok (callStarts σ_pre).length = true := by simpa using hok_σ
  have hok_star : ok (callStarts τ_star).length = true := by
    rwa [coinSplit_callStarts_length_eq hex_s.1]
  have hgsc : GoodStepCut ok (callStarts τ_star).length [.recv b, .rng d, .accept pt] :=
    GoodStepCut.callRecvAccept (w := b) (mid := [.rng d]) (out_ev := .accept pt)
      (Or.inr ⟨d, rfl, hcontract.d_len⟩) rfl hok_star
  obtain ⟨hex_out, hnrc_out⟩ := hGood hex_s hcs_blk hgsc (Or.inr rfl) hfr_out (hclean_out hok_star)
  refine { noAdjRng := by
             rw [hblk_cli]; exact noAdjRng_append_of_head_nonRng hlive.noAdjRng ⟨Or.inl (by simp [eventKind]), ⟨Or.inr (by simp [eventKind]), trivial⟩⟩ (by simp [eventKind])
           witness := ⟨τ_star ++ [.recv b, .rng d, .accept pt], g_out,
             Sanitize.sanitizeMoves (setupTrace r) ms_star ++ δ, hex_out, hnrc_out⟩
           cutRel := fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_ }
  obtain ⟨τ'_pre, blk', rfl, hcs_pre, hcs_blk'⟩ := coinSplit_append_inv hex'.1
  rw [hblk_cli] at hcs_blk'
  obtain ⟨_, hblk'_hd, _⟩ := (coinSplit_cons_nonRng_iff (by simp [eventKind])).mp hcs_blk'
  have hhead' : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    rw [hblk'_hd]; simp [eventKind]
  obtain ⟨ms'_pre, δ', hms'_eq, hex'_pre, hnrc'_pre, hB'⟩ :=
    explainsCli_prefix_of_split hcs_pre hhead' hex' hnrc'
  have hA'_pre := hA_of_cut ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
  have hc'_pre : Clean interp r S who ok g' ms'_pre τ'_pre := explainsCli_toClean hex'_pre hnrc'_pre
  have hbook'_pre := (hA'_pre.ready.2.1.clean g' ms'_pre hc'_pre).1.2.1
  have hmp' : MatchedPrefix interp r S who g' (ms'_pre ++ δ') (τ'_pre ++ blk') := hms'_eq ▸ hex'.2.1
  have hblk'_eq : blk' = [.recv b, .rng d, .accept pt] :=
    recv_accept_blk_eq hcontract.parse hcontract.d_len hfresh hA'_pre.who_cs
      hbook'_pre hcs_blk' hB' hmp'.2.2.1 hmp'.2.2.2.1 (hms'_eq ▸ hex'.2.2.2)
  subst hblk'_eq
  exact ⟨by rw [hleak', hsent']; exact rpk_accept_cRel_of_not_kyberMismatch hext hwf hSeq hA'_pre hBin hTie hnkm,
    by rw [hopk']; exact rpk_accept_cOpk hA'_pre⟩

/-! ## Directory Helpers and Top-Level `slot_rpk_new_over_cli` -/

private theorem opkUsed_clean_after_rpk_accept {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {t : CliTurn}
    {stB st1 st' : PqParty} {m : PreKeyMessageFields} {inner : SignalMessage}
    {k : ResponderPreKeySecrets} {x' : RecordExtras} {g' : GhostState HwBytes}
    {X : UnreachedPqxdhPrimitives} {rc : BitVec 256} {out : HwBytes}
    (hr : ProtocolSetupWF r) (hinvB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    (hB₀ : PqPartyInv interp P r accepted r.bob { stB with session := none }
      (filesOf (encodeDir P { stB with session := none })))
    (hmod : pqRecvPrekeyModel X P { stB with session := none } m rc = some (some (st', out)))
    (hk : preKeysNamedBy { stB with session := none } m = some k)
    (hmk : markKyberUsed { stB with session := none } m = some st1)
    (hst' : st' = { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', g') }) :
    ({ dirs := fun q => if q = r.bob then filesOf (encodeDir P st') else t.dirs q
       sent := t.sent, bobOff := false } : CliTurn).opkUsed r =
      (t.opkUsed r || (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome) := by
  let t_clean' : CliTurn :=
    { dirs := fun q => if q = r.bob then filesOf (encodeDir P st') else t.dirs q
      sent := t.sent, bobOff := false }
  obtain ⟨_, hst'_inv, _⟩ := pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod
  have hst'_turn : PqPartyInv interp P r (accepted ++ [djbKey m.baseKey]) r.bob st'
      (t_clean'.dirs r.bob) := by simpa [t_clean'] using hst'_inv
  have hopk_B := opkUsed_of_pqPartyInv hr.1 hinvB
  have hopk_B' := opkUsed_of_pqPartyInv hr.1 hst'_turn
  let t₀ : CliTurn :=
    { dirs := fun q =>
        if q = r.bob then filesOf (encodeDir P { stB with session := none }) else t.dirs q
      sent := t.sent, bobOff := false }
  have hB₀_turn : PqPartyInv interp P r accepted r.bob { stB with session := none }
      (t₀.dirs r.bob) := by simpa [t₀] using hB₀
  have hk_post := Slots.pqPartyInv_bob_keysFor_inv hr.1 hB₀_turn hk
  obtain ⟨_, _, _, _, h1_ot, _⟩ :=
    Slots.pqPartyInv_bob_markKyberUsed_inv hr.1 hB₀_turn hk_post.spkId_eq hk_post.kpkId_eq hmk
  obtain ⟨_, _, ho_B, _⟩ := hinvB.bob_stores hr.1.symm
  rcases hk_post.opk_cases with ⟨hnone, _⟩ | ⟨hyes, _, hopk_some, _⟩
  · have hp_false : (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome = false := by
      simp [Slots.rpkNew_preKeyFieldsOf, hnone]
    rw [hp_false, Bool.or_false]
    have hot_eq : st'.oneTime = stB.oneTime := by rw [hst']; simp [removeOpk, hnone, h1_ot]
    cases hw : r.withOpk
    · rw [hopk_B'.1 hw, hopk_B.1 hw]
    · rcases ho_B with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
      · cases hno_w.symm.trans hw
      · rw [(hopk_B'.2 hw).1.mpr (hot_eq.trans hot_s), (hopk_B.2 hw).1.mpr hot_s]
      · rw [(hopk_B'.2 hw).2.mpr (hot_eq.trans hot_n), (hopk_B.2 hw).2.mpr hot_n]
  · have hp_true : (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome = true := by
      simp [Slots.rpkNew_preKeyFieldsOf, hopk_some]
    rw [hp_true, Bool.or_true]
    have hot' : st'.oneTime = [(r.opkId, none)] := by
      rw [hst']; dsimp only; simp only [removeOpk, hopk_some, h1_ot]
      rcases ho_B with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
      · cases hno_w.symm.trans hyes
      · simp [hot_s]
      · simp [hot_n]
    exact (hopk_B'.2 hyes).2.mpr hot'

private theorem encodeRecordX_lt_2_63_of_rpkAcceptBin {pf : PreKeyFields} {sm : StateAndMessage}
    (hb : RpkAcceptBin pf sm) : sm.state.length < 2 ^ 63 := by
  obtain ⟨_, _, _, _, hinv, _, hsm⟩ := hb.1
  have henc := hinv.2.2.2.2.2.2
  rw [hsm]; dsimp only [Record.encodeRecord, Option.map_some, Record.msgField]
  exact Nat.lt_of_le_of_lt (TR.Pure.lenField_length_le 1 _) (by omega)

private theorem slot_rpk_new_over_cli_core (hGood : GoodExit0CutSpec) (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted) (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob)) (hbun : c.bundle = []) (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c) (hfb : FilesBounded (t.dirs c.party)) (hbca : BobCallAllowed r t c)
    (hkind : c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none)
    (hpqh : ∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest t.sent q.message)
    (hno_prom : ∀ rec_ q, t.records r r.bob = some rec_ → parsePreKeyWire c.stdin = some q →
      ¬ EligibleForSessionPromotion rec_ c.stdin)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    CliSlotPostCore
      (RpkNewOverNC (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) accepted c code σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  let interp' := interpOfParams interp P
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hBridge : Slots.RpkModelHookBridge interp' P := Slots.rpkModelHookBridge_interpOfParams hagree
  have hmlkem := mlkemOf_interpOfParams interp P
  have hhmac := hmacFnOf_interpOfParams interp P
  have hoff : t.bobOff = false := by
    cases hbo : t.bobOff with | false => rfl | true => exact absurd hbob (hbca hbo)
  have htc_eq : t_clean = t := hsim.bobOff_false_eq hoff; subst t_clean
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
    change c.cmd = .recv (partyAddress stB.party.other); rw [hcmd, peerOf_eq_addrE_other, ← hinvB.party_eq]
  have heq_recv : InputsEquiv i (pqRecvInputs P stB c.stdin rc) :=
    inputsEquiv_pqRecvInputs (c := c1) hi_enc hcmd_stB rfl hcoins_rc
  have hp : PqModelPost interp P i (.exited code out files) := PqModelRel.exited_iff.mp hRel
  unfold StdinBounded at hsb; rw [hcmd] at hsb
  by_cases hw : ∃ body, c.stdin = wireWhisperTag :: body
  · obtain ⟨body, hstdin⟩ := hw
    have hrec_none : t.records r r.bob = none := hkind.resolve_left (by simp [hstdin])
    have hsess_none : stB.session = none := by
      rw [records_of_pqPartyInv hinvB] at hrec_none
      cases hs : stB.session with | none => rfl | some _ => rw [hs] at hrec_none; cases hrec_none
    have hstdin_w : c.stdin = wireWhisper :: body := by rwa [wireWhisper_eq_wireWhisperTag]
    have hobs := hp.recvWhisper stB body rc hwfB (hsb.1 body hstdin) (hstdin_w ▸ heq_recv)
    simp only [pqRecvWhisperModel, hsess_none] at hobs
    injection hobs with hcode hout hfiles; subst hcode hout hfiles
    exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _
  · have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
      intro hh; cases hcs : c.stdin with
      | nil => simp [hcs] at hh
      | cons b tl => simp only [hcs, List.head?_cons, Option.some.injEq] at hh; exact hw ⟨tl, hh ▸ hcs⟩
    have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
    by_cases hpk : ∃ body, c.stdin = wirePrekey :: body
    · obtain ⟨body, hstdin⟩ := hpk
      have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
      have heq_body : InputsEquiv i (pqRecvInputs P stB (wirePrekey :: body) rc) := hstdin ▸ heq_recv
      cases hq : parsePreKey body with
      | none =>
        have hobs := hp.recvPrekeyReject stB body rc hwfB hbody_lt hq heq_body
        injection hobs with hcode hout hfiles; subst hcode hout hfiles
        exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _
      | some q =>
        have hno_fm : ∀ x g, stB.session = some (x, g) → ¬ PqFieldsMatch x g q := by
          intro x g hsess hfm
          have hrec_bob : t.records r r.bob = some (encodeRecordUnderExtras (fun _ => x) g) := by
            rw [records_of_pqPartyInv hinvB, hsess]; rfl
          exact hno_prom _ q (hrec_bob) (by rw [hstdin]; simpa using hq)
            (hstdin.symm ▸ promoteMatch_of_pqFieldsMatch hwfB hsess hq hfm)
        cases hm : preKeyOfBody? body with
        | none =>
          have hobs := hp.recvPrekeyUntyped stB body q rc hwfB hbody_lt hq hm hno_fm heq_body
          injection hobs with hcode hout hfiles; subst hcode hout hfiles
          exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _
        | some m =>
          obtain ⟨q₁, hq₁, hv4, hminner, _, _, _, _, hbk_q, _, _⟩ := preKeyOfBody?_some_inv hm
          cases Option.some.inj (hq.symm.trans hq₁)
          have hp_b : parsePreKeyWire (wirePrekey :: body) = some q := by simpa using hq
          have hmlt : m.inner.length + 2048 < 2 ^ 32 := hminner ▸ hsb.2.2.1 q (hstdin ▸ hp_b)
          cases hsess : stB.session with
          | none =>
            have hvac : ∀ x g, stB.session = some (x, g) → PqSessionMatches x g m := fun _ _ hs => by
              rw [hsess] at hs; cases hs
            have hobs := hp.recvPrekeyParsed (Xof interp' P) stB body m rc hwfB hbody_lt hm hmlt hvac heq_body
            rcases exited_eq_pqObserve_iff.mp hobs with ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, rfl⟩
            · exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _
            · have hrec_none : t.records r r.bob = none := by rw [records_of_pqPartyInv hinvB, hsess]; rfl
              have hnnm3 : ¬ PreKeyNoMatch r t c := fun ⟨_, _, _, _, hsome, _⟩ => by rw [hrec_none] at hsome; cases hsome
              have hnnm1 : ¬ PreKeyNoMatch r t c1 := fun ⟨_, _, _, _, hsome, _⟩ => by rw [hrec_none] at hsome; cases hsome
              have hstB_none_eq : ({ stB with session := none } : PqParty) = stB := by cases stB; cases hsess; rfl
              have hmod' : pqRecvPrekeyModel (Xof interp' P) P { stB with session := none } m rc =
                  some (some (st', out)) := by rwa [hstB_none_eq]
              obtain ⟨_, hst'_inv, hsub⟩ := pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod'
              let files_acc := filesOf ((pqRecvInputs P stB (wirePrekey :: body) rc).files ++ encodeDir P st')
              have hscr : scrub files_acc = filesOf (encodeDir P st') :=
                scrub_filesOf_pqInputs_accept P stB st' _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
              have hbo_after : (t.after r c1 0 out files_acc).bobOff = false := by simp [CliTurn.after, hoff, hnnm1]
              have hafter_eq : CliTurn.after t r c 0 out files_acc = t.after r c1 0 out files_acc :=
                afterD3_eq_after_of_not_noMatch hnnm3 hnnm1
              obtain ⟨stA, hA⟩ := hDir.1
              have hDir' : PqDirInv interp' P r (t.after r c1 0 out files_acc) (accepted ++ [q.baseKey.take 33]) := by
                rw [hbk_q]; refine ⟨⟨stA, by simpa only [CliTurn.after, c1, toCliCallNone, hbob, hr.1, ↓reduceIte] using pqPartyInv_alice_accepted_iff.mp hA⟩,
                  ⟨st', by rw [hbo_after]; unfold PqBobInv; simpa only [Bool.false_eq_true, ↓reduceIte, CliTurn.after, c1, toCliCallNone, hbob, hscr] using hst'_inv⟩,
                  fun p ha hb => by simpa only [CliTurn.after, c1, toCliCallNone, hbob, hb, ↓reduceIte] using hDir.2.2 p ha hb⟩
              obtain ⟨inner, k, x', g', st1, htf, htrust, hk, hdec, hmk, hst'⟩ := Slots.pqRecvPrekeyModel_none_ok_inv hsess hmod
              obtain ⟨_, hhon_m, hfresh_m, hst_lt, hopk_rem, hcontract_m, hBin_m, hTie_m⟩ :=
                Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB hinvB hcoins hmlt htf htrust hk hdec hmk
              have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
              have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract_m
              have hBin := heq_pf.rpkAcceptBin hBin_m; have hTie := heq_pf.acceptTieD hTie_m
              have hhon := heq_pf.honestIdentity hcontract_m.parse hp_b hhon_m
              have hfresh := heq_pf.fresh hcontract_m.parse hp_b hfresh_m
              let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩
              have hB₀_dir : PqPartyInv interp' P r accepted r.bob { stB with session := none }
                  (filesOf (encodeDir P { stB with session := none })) := by rw [hstB_none_eq, ← hinvB.dir_eq]; exact hinvB
              have hopk_clean := opkUsed_clean_after_rpk_accept (inner := inner) hr hinvB hB₀_dir hmod' (hstB_none_eq.symm ▸ hk) (hstB_none_eq.symm ▸ hmk) hst'
              refine ⟨t.after r c1 0 out files_acc, accepted ++ [q.baseKey.take 33],
                by rw [hafter_eq]; exact pqTurnSim1A_refl hDir' hbo_after, fun who ok hwho hlive hnc => ?_⟩
              have hsent_eq : (t.after r c1 0 out files_acc).sent = t.sent := by simp [CliTurn.after, c1, toCliCallNone, hcmd]
              have hst'_after : PqPartyInv interp' P r (accepted ++ [djbKey m.baseKey]) r.bob st' ((t.after r c1 0 out files_acc).dirs r.bob) := by
                simpa [CliTurn.after, c1, toCliCallNone, hbob, hscr] using hst'_inv
              have hleak_eq : (t.after r c1 0 out files_acc).leakRecords r = fun p => if p = r.bob then some sm.state else t.leakRecords r p := by
                rw [leakRecords_eq_records_of_bobOff_false r hbo_after, leakRecords_eq_records_of_bobOff_false r hoff]
                funext p; by_cases hpb : p = r.bob
                · subst hpb; rw [records_of_pqPartyInv hst'_after, hst']; simp [sm]
                · have hpc1 : p ≠ c1.party := by simpa [c1, toCliCallNone, hbob] using hpb
                  simp [CliTurn.records, CliTurn.after, hpb, hpc1]
              have hopk_eq : (t.after r c1 0 out files_acc).opkUsed r = (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8)) := by
                have hdirs_eq : (t.after r c1 0 out files_acc).dirs r.bob = filesOf (encodeDir P st') := by simp [CliTurn.after, c1, toCliCallNone, hbob, hscr]
                have hopk_a : (t.after r c1 0 out files_acc).opkUsed r = ({ dirs := (fun p => if p = r.bob then filesOf (encodeDir P st') else t.dirs p), sent := t.sent, bobOff := false } : CliTurn).opkUsed r :=
                  opkUsed_eq_of_bob_agree fun path _ => by simp [hdirs_eq]
                rw [hopk_a, hopk_rem]; exact hopk_clean
              exact rpkNew_accept_cliLiveAtCli hGood hext' hr rfl hcmd hstdin (hbob ▸ hwho)
                hlive hnc hhon (hstdin ▸ hpqh) hfresh hst_lt hcontract hBin hTie hsent_eq hleak_eq hopk_eq
          | some xg =>
            rcases xg with ⟨x, g⟩
            have hnomatch : ¬ PqSessionMatches x g m := fun hsm => hno_fm x g hsess ((pqFieldsMatch_iff_pqSessionMatches x g hq hm).mpr hsm)
            have hrec_bob : t.records r r.bob = some (encodeRecordUnderExtras (fun _ => x) g) := by rw [records_of_pqPartyInv hinvB, hsess]; rfl
            have hlen_in : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := (hwfB.1 x g hsess).2.2
            have hnprom : ¬ EligibleForSessionPromotion (encodeRecordUnderExtras (fun _ => x) g) c.stdin := by
              rw [hstdin]; exact fun hp_m => hno_fm x g hsess (pqFieldsMatch_of_promoteMatch_v4 hwfB hsess hq hv4 hp_m)
            have hpknm3 : PreKeyNoMatch r t c := ⟨hbob, ⟨peerOf r r.bob, hcmd⟩, hnw_tag, encodeRecordUnderExtras (fun _ => x) g, hrec_bob, hnprom⟩
            obtain ⟨hob_ex, hnmsf⟩ := hp.recvPrekeyParsedNoMatch (Xof interp' P) stB x g body m rc
              hwfB hsess hbody_lt hm hmlt hnomatch heq_body
            rcases observedExcept_exited_iff.mp hob_ex with ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, hag⟩
            · exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _
            · obtain ⟨_, hst'_inv, hsub⟩ := pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod
              have hag_scr := scrub_agreeExcept_pqInputs_accept P stB st'
                (.recv (partyAddress stB.party.other)) [] (HMAC.keyToBytes32 rc) (wirePrekey :: body)
                files hinvB.party_eq (fun _ h => nomatch h) (fun _ h => nomatch h) hsub hag
              let stB₀ : PqParty := { stB with session := none }
              let t₀ : CliTurn := { dirs := (fun p => if p = r.bob then filesOf (encodeDir P stB₀) else t.dirs p), sent := t.sent, bobOff := false }
              have hwfB₀ : PqxdhPartyInSpecDomain P stB₀ := Slots.wfPq_clear_session P hwfB
              have hB₀_dir : PqPartyInv interp' P r accepted r.bob stB₀ (filesOf (encodeDir P stB₀)) :=
                { party_eq := hinvB.party_eq, me_eq := hinvB.me_eq, peerId_eq := hinvB.peerId_eq,
                  alice_stores := fun h => absurd h.symm hr.1, bob_stores := hinvB.bob_stores,
                  session_reach := (fun _ _ hs => nomatch hs), dir_eq := rfl }
              have hB₀ : PqPartyInv interp' P r accepted r.bob stB₀ (t₀.dirs r.bob) := by simpa [t₀] using hB₀_dir
              have hopk₀ : t₀.opkUsed r = t.opkUsed r := by
                have ho₀ := opkUsed_of_pqPartyInv hr.1 hB₀; have hoB := opkUsed_of_pqPartyInv hr.1 hinvB
                obtain ⟨_, _, ho_cases, _⟩ := hinvB.bob_stores hr.1.symm
                cases hw_opk : r.withOpk
                · rw [ho₀.1 hw_opk, hoB.1 hw_opk]
                · rcases ho_cases with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
                  · cases hno_w.symm.trans hw_opk
                  · rw [(ho₀.2 hw_opk).1.mpr hot_s, (hoB.2 hw_opk).1.mpr hot_s]
                  · rw [(ho₀.2 hw_opk).2.mpr hot_n, (hoB.2 hw_opk).2.mpr hot_n]
              obtain ⟨inner, k, x', g', st1, htf, htrust, hk, hdec, hmk, hst'⟩ :=
                Slots.pqRecvPrekeyModel_none_ok_inv (rfl : stB₀.session = none) hmod
              obtain ⟨_, hhon_m, hfresh_m, hst_lt, hopk_rem, hcontract₀, hBin_m, hTie_m⟩ :=
                Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB₀ hB₀
                  hcoins hmlt htf htrust hk hdec hmk
              rw [hopk₀] at hcontract₀
              have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
              have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract₀
              have hBin := heq_pf.rpkAcceptBin hBin_m; have hTie := heq_pf.acceptTieD hTie_m
              have hhon := heq_pf.honestIdentity hcontract₀.parse hp_b hhon_m
              have hfresh := heq_pf.fresh hcontract₀.parse hp_b hfresh_m
              let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩
              have hlen'_63 : (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 63 :=
                encodeRecordX_lt_2_63_of_rpkAcceptBin hBin_m
              let t_clean' : CliTurn := { dirs := (fun p => if p = r.bob then filesOf (encodeDir P st') else t.dirs p), sent := t.sent, bobOff := false }
              obtain ⟨stA, hA⟩ := hDir.1
              have hDir_clean' : PqDirInv interp' P r t_clean' (accepted ++ [q.baseKey.take 33]) := by
                rw [hbk_q]; refine ⟨⟨stA, by simpa only [t_clean', hr.1, ↓reduceIte] using pqPartyInv_alice_accepted_iff.mp hA⟩,
                  ⟨st', by unfold PqBobInv; simpa only [t_clean', Bool.false_eq_true, ↓reduceIte] using hst'_inv⟩,
                  fun p ha hb => by simpa only [t_clean', hb, ↓reduceIte] using hDir.2.2 p ha hb⟩
              have hst'_sess : st'.session = some (x', g') := by rw [hst']
              have hsess_file_bob : files (sessionPathOf r r.bob) = some (noMatchRecordBytes x g x' g') := by
                rw [sessionPathOf_eq_sessionFile, ← hinvB.party_eq]
                exact hnmsf st' out x' g' hmod hst'_sess 0 out files rfl
              have hrec_after_bob : (CliTurn.after t r c 0 out files).records r r.bob =
                  some (noMatchRecordBytes x g x' g') := by
                unfold CliTurn.records; simp only [CliTurn.after, hbob, ↓reduceIte, scrub_sessionPathOf,
                  hsess_file_bob, noMatchRecordBytes_ne_nil]
              have hst'_turn : PqPartyInv interp' P r (accepted ++ [djbKey m.baseKey]) r.bob st' (t_clean'.dirs r.bob) := by
                simpa [t_clean'] using hst'_inv
              have hrec_clean'_bob : t_clean'.leakRecords r r.bob = some (encodeRecordUnderExtras (fun _ => x') g') := by
                rw [leakRecords_eq_records_of_bobOff_false r rfl, records_of_pqPartyInv hst'_turn, hst'_sess]; rfl
              have hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c 0 out files)
                  t_clean' (accepted ++ [q.baseKey.take 33]) :=
                { dirInv := hDir_clean', clean_bobOff := rfl, sent_eq := by simp [t_clean', CliTurn.after, hcmd]
                  dirs_other := fun p hpb => by have hpc : p ≠ c.party := hbob ▸ hpb; simp [t_clean', CliTurn.after, hpb, hpc]
                  bobOff_false_eq := fun hbo' => by
                    have hbo_t : (CliTurn.after t r c 0 out files).bobOff = true := by simp [CliTurn.after, hpknm3]
                    cases hbo_t.symm.trans hbo'
                  bob_nonSession := fun path hsp => by simpa [t_clean', CliTurn.after, hbob] using hag_scr path hsp
                  strip_eq := by
                    funext p; by_cases hpb : p = r.bob
                    · subst hpb; unfold pureStripPrev
                      rw [hrec_after_bob, hrec_clean'_bob, Option.map_some, Option.map_some,
                          pureStripBytes_noMatchRecordBytes hlen_in hlen'_63, pureStripBytes_encodeRecordX hlen'_63]
                    · have hpc : p ≠ c.party := hbob ▸ hpb; unfold pureStripPrev
                      rw [leakRecords_eq_records_of_bobOff_false r (rfl : t_clean'.bobOff = false)]
                      simp [CliTurn.records, CliTurn.after, t_clean', hpb, hpc] }
              have hopk_clean := opkUsed_clean_after_rpk_accept (inner := inner) hr hinvB hB₀_dir hmod hk hmk hst'
              refine ⟨t_clean', accepted ++ [q.baseKey.take 33], hsim', fun who ok hwho hlive hnc => ?_⟩
              have hleak_eq : t_clean'.leakRecords r = fun p => if p = r.bob then some sm.state else t.leakRecords r p := by
                funext p; by_cases hpb : p = r.bob
                · subst hpb; simpa [sm] using hrec_clean'_bob
                · rw [leakRecords_eq_records_of_bobOff_false r (rfl : t_clean'.bobOff = false),
                      leakRecords_eq_records_of_bobOff_false r hoff]; simp [CliTurn.records, t_clean', hpb]
              have hopk_eq : t_clean'.opkUsed r = (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8)) := by
                rw [hopk_rem]; exact hopk_clean
              exact rpkNew_accept_cliLiveAtCli hGood hext' hr rfl hcmd hstdin (hbob ▸ hwho)
                hlive hnc hhon (hstdin ▸ hpqh) hfresh hst_lt hcontract hBin hTie
                (rfl : t_clean'.sent = t.sent) hleak_eq hopk_eq
    · have hnw : c.stdin.head? ≠ some wireWhisper := by rwa [wireWhisper_eq_wireWhisperTag]
      have hnp : c.stdin.head? ≠ some wirePrekey := by
        intro hh; cases hcs : c.stdin with
        | nil => simp [hcs] at hh
        | cons b tl => simp only [hcs, List.head?_cons, Option.some.injEq] at hh; exact hpk ⟨tl, hh ▸ hcs⟩
      have hobs := hp.recvOther stB c.stdin rc hwfB hlen_lt hnw hnp heq_recv
      injection hobs with hcode hout hfiles; subst hcode hout hfiles
      exact bob_recv_cli_pqInputs_reject_step hGood hB hr hDir hoff hbob hcmd hinvB _ _

/-- Generalized non-promote Bob `recv` slot returning `Defs.CliSlotPostW` under `RpkNewOverNC`. -/
theorem slot_rpk_new_over_cli_gen (hGood : GoodExit0CutSpec) (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted) (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob)) (hbun : c.bundle = []) (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c) (hfb : FilesBounded (t.dirs c.party)) (hbca : BobCallAllowed r t c)
    (hkind : c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none)
    (hpqh : ∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest t.sent q.message)
    (hno_prom : ∀ rec_ q, t.records r r.bob = some rec_ → parsePreKeyWire c.stdin = some q →
      ¬ EligibleForSessionPromotion rec_ c.stdin)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    Symbolic.Proofs.Swarm.UA.Defs.CliSlotPostW
      (RpkNewOverNC (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r) accepted c code σ_pre)
      interp P r t t_clean c code out files accepted σ_pre := by
  obtain ⟨tc', acc', hsim', hstep⟩ := slot_rpk_new_over_cli_core hGood hB interp P r hext hagree hr
    hsim hbob hcmd hbun hcoins hsb hfb hbca hkind hpqh hno_prom hin hRel
  exact ⟨tc', acc', hsim', fun who ok hwho hlive hnc hok => (hstep who ok hwho hlive hnc).2 hok⟩

end Symbolic.Swarm.Coinsplit.Lift.L10
