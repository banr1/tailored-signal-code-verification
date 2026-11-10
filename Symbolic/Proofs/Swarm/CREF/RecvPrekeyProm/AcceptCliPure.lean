/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BinPure
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRecv
public import Symbolic.Proofs.Swarm.CREF.Xpl.InvRpk
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNonePure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.AcceptFramePure

/-!
# Promote Accept Bundles and Obligation Interfaces

Defines the accepting promote event block `promAccBlk`, entry and call witnesses (`PromEntryHyps`
and `PromAcceptCall`), and the accept-branch obligation predicates (`PromExplainOK`, `PromNewRecOK`,
`PromHistOK`, `PromOpkOK`, `PromNoDrawOK`), together with `prom_book` and `CReadyPure` entry
extraction.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm

/-! ## Promote accept event block -/

/-- Event block `.recv b :: (mid ++ [.accept pt])` of an accepting promote call. -/
abbrev promAccBlk (b : HwBytes) (mid : List MachineEvent) (pt : HwBytes) : List MachineEvent :=
  .recv b :: (mid ++ [.accept pt])

theorem prom_accMid_kinds {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    ∀ e ∈ mid ++ [.accept pt], eventKind e = .rng ∨ eventKind e = .accept := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> simp [eventKind]

theorem prom_accBlk_shape {b : HwBytes} {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    RpkBlockShape (promAccBlk b mid pt) := by
  refine ⟨⟨b, rfl⟩, fun e he => prom_accMid_kinds hmid e (by simpa using he), ?_⟩
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> simp

theorem prom_accBlk_has_accept (b : HwBytes) (mid : List MachineEvent) (pt : HwBytes) :
    ∃ e ∈ promAccBlk b mid pt, eventKind e = .accept :=
  ⟨.accept pt, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)), rfl⟩

theorem prom_accBlk_sendsFit {b : HwBytes} {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    TR.SendsFit (promAccBlk b mid pt) := by
  intro m hm
  rcases List.mem_cons.mp hm with h | h
  · cases h
  · rcases prom_accMid_kinds hmid _ h with h' | h' <;> cases h'

theorem prom_accBlk_sentBodies {b : HwBytes} {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    TR.sentBodies (promAccBlk b mid pt) = [] := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> rfl

theorem prom_accBlk_callStarts {b : HwBytes} {mid : List MachineEvent} {pt : HwBytes}
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32) :
    callStarts (promAccBlk b mid pt) = [.recv b] := by
  rcases hmid with rfl | ⟨rb, rfl, -⟩ <;> rfl

theorem prom_oneMove_recvStep {r : ProtocolSetup} {ms₀ δ : List Move}
    {b : HwBytes} {mid : List MachineEvent} {pt : HwBytes}
    (hδ : OneMove (RpkStep r.bob (promAccBlk b mid pt)) (runTraceMoves r ms₀) δ)
    (hnoBobStart : ∀ pre m post, δ = pre ++ m :: post →
      MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre →
      ¬ BobStartBy r.bob m) :
    OneMove (RecvStep r.bob (promAccBlk b mid pt)) (runTraceMoves r ms₀) δ := by
  obtain ⟨pre, m, post, rfl, hpre, ⟨hact, _, hacc⟩, hpost⟩ := hδ
  have hdec : DecryptBy r.bob m :=
    (hacc (prom_accBlk_has_accept b mid pt)).resolve_left (hnoBobStart pre m post rfl hpre)
  have hrk : RecvKind m := by
    cases m <;> first | exact hdec | trivial
  exact ⟨pre, m, post, rfl, hpre, ⟨hact, Or.inl hrk, fun _ => hdec⟩, hpost⟩

/-- Preserves `CBook` across a `OneMove (RecvStep r.bob (promAccBlk b mid pt))` block once
`TRNsBound` holds on `ms₀ ++ δ`. -/
theorem prom_book {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {acc mid : List MachineEvent} {b pt : HwBytes} {g : Ghost} {ms₀ δ : List Move}
    {sent accepted : List HwBytes}
    (hδ : OneMove (RecvStep r.bob (promAccBlk b mid pt)) (runTraceMoves r ms₀) δ)
    (hmid : mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32)
    (hb : CBook interpretation r S g ms₀ sent accepted acc)
    (hns' : TR.TRNsBound r (ms₀ ++ δ) sent) :
    CBook interpretation r S g (ms₀ ++ δ) sent accepted (acc ++ promAccBlk b mid pt) := by
  obtain ⟨pre, m, post, rfl, hpre, ⟨hact, hrk, _⟩, hpost⟩ := hδ
  have hq1 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hf : promRcvFrame r.bob (runTraceMoves r (ms₀ ++ pre)) (runTraceMoves r (ms₀ ++ pre ++ [m])) := by
    rw [TR.runTrace_snoc]
    rw [← TR.runTrace_append] at hrk
    exact prom_rcv_next_move hact hrk
  have hq2 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ pre ++ [m] ++ post)) := by
    rw [TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)
  have hbd : bobDoneBaseKeys (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) =
      bobDoneBaseKeys (runTraceMoves r ms₀) := by
    rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
      Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_bobDoneBaseKeys hq2, promRcvFrame_bobDoneBaseKeys hf,
      Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_bobDoneBaseKeys hq1]
  refine ⟨?_, hns', ?_⟩
  · rw [TR.sentBodies_append, prom_accBlk_sentBodies hmid, List.append_nil]
    exact hb.1
  · rw [hbd]
    exact hb.2.2

theorem prom_invisible_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ →
      (runMoves δ tr).2 = [] ∧ visActorsFrom δ tr = []
  | [], _, _ => ⟨rfl, rfl⟩
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    obtain ⟨h1, h2⟩ := prom_invisible_nil δ (m.next tr) hδ
    refine ⟨?_, ?_⟩
    · simp only [runMoves, hv, h1, List.nil_append]
    · simp only [visActorsFrom, hv, h2, List.length_nil, List.replicate_zero, List.nil_append]

/-! ## Entry and accepting-call bundles -/

/-- Entry hypotheses on the session-promotion branch of `session_recv_prekey` under `CReadyPure`. -/
structure PromEntryHyps (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (j : Nat) (e' : PromTurn) (acc : List MachineEvent)
    (rec b : HwBytes) : Prop where
  ready : CReadyPure interpretation r S who ok e'.records e'.sent e'.accepted e'.opkUsed acc
  who_at : who[j]? = some r.bob
  rec_lookup : e'.records r.bob = some rec
  rec_len : rec.length < 2 ^ 32 - 2 ^ 20
  pm : EligibleForSessionPromotion rec b
  canon : TR.PureTRRecordCanon r r.bob rec
  rec4 : ∃ rr : RecordRec, rec = recordBytes rr ∧
    rr.current.sessionVersion = 4#32 ∧ rr.current.receiverChains ≠ [] ∧
    rr.current.senderChain.isSome = true ∧ rr.current.pendingKyberPreKey = none
  sent_eq : e'.sent = TR.sentBodies acc
  hon : HonestIdentity interpretation r b
  pqh : ∀ q, parsePreKeyWire b = some q → PqFromHonest e'.sent q.message

/-- Bundled witness for an accepting promote call under `CReadyPure`. -/
structure PromAcceptCall (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)) : Prop where
  entry : PromEntryHyps interpretation r S who ok j e' acc rec b
  hj : (callStarts acc).length = j
  out : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt
  ver : pf.inner.messageVersion = 4#8
  nodraw : mid = [] →
    pureDrawsCoins
      (Proofs.libsignal.Hooks2.cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = false

abbrev PromAcceptCallBy₂ := PromAcceptCall

theorem PromAcceptCall.hmid {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt) :
    mid = [] ∨ ∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32 := by
  rcases hC.out.hcoins with ⟨_, hnil⟩ | ⟨rb, hmid, hlen, _, _⟩
  · exact Or.inl hnil
  · exact Or.inr ⟨rb, hmid, hlen⟩

/-! ## Accept-branch obligations -/

/-- Explanation obligation on an accepting promote call: yields a `MatchedPrefix` explanation and,
when `ok j = true`, a `Clean` explanation. -/
def PromExplainOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ promAccBlk b mid pt)) ∧
    (ok j = true → ∃ g ms, Clean interpretation r S who ok g ms (acc ++ promAccBlk b mid pt))

/-- Post-state `PureCRecRel` and `TRNsBound` step for a single-move receive block under `Clean`. -/
def PromNewRec (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (p : Participant) (rec st' : HwBytes) (sent : List HwBytes) (acc blk : List MachineEvent) :
    Prop :=
  ∀ g ms₀ δ,
    Clean interpretation r S who ok g (ms₀ ++ δ) (acc ++ blk) →
    XplBlock interpretation r S who g ms₀ δ acc blk →
    OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ →
    CHistRole interpretation r S g ms₀ →
    PureCRecRel interpretation r S g ms₀ p rec →
    TR.TRNsBound r ms₀ sent →
    st' ≠ [] ∧ PureCRecRel interpretation r S g (ms₀ ++ δ) p st' ∧ TR.TRNsBound r (ms₀ ++ δ) sent

abbrev PromNewRecBy₂ := PromNewRec

/-- Post-state record and `TRNsBound` obligation on an accepting promote call. -/
def PromNewRecOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    PromNewRec interpretation r S who ok r.bob rec sm.state e'.sent acc (promAccBlk b mid pt)

abbrev PromNewRecByOK₂ := PromNewRecOK

/-- `CHist` step across a single-move receive block under `Clean`. -/
def PromHistStep (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (p : Participant) (rec st' : HwBytes) (acc blk : List MachineEvent) : Prop :=
  ∀ g ms₀ δ,
    Clean interpretation r S who ok g (ms₀ ++ δ) (acc ++ blk) →
    XplBlock interpretation r S who g ms₀ δ acc blk →
    OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ →
    CHistRole interpretation r S g ms₀ →
    PureCRecRel interpretation r S g ms₀ p rec →
    PureCRecRel interpretation r S g (ms₀ ++ δ) p st' →
    CHist interpretation r S g (ms₀ ++ δ)

/-- `CHist` obligation on an accepting promote call. -/
def PromHistOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    PromHistStep interpretation r S who ok r.bob rec sm.state acc (promAccBlk b mid pt)

/-- `COpkRelC` preservation obligation on an accepting promote call. -/
def PromOpkOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    COpkRelC interpretation r S who ok e'.opkUsed (acc ++ promAccBlk b mid pt)

/-- Obligation that an accepting promote call with `mid = []` has `pureDrawsCoins = false`. -/
def PromNoDrawOK (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCall interpretation r S who ok j e' [] acc rec b sm pf
      sess sess' coins expected pt →
    pureDrawsCoins
      (Proofs.libsignal.Hooks2.cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = false

/-! ## Entry extraction under `CReadyPure` -/

theorem prom_canon_v4_sent_of_clean {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {e' : PromTurn} {acc : List MachineEvent}
    (hwf : ProtocolSetupWF r)
    (hbob : PureBobKyberNone r e'.records)
    (hR : CReadyPure interpretation r S who ok e'.records e'.sent e'.accepted e'.opkUsed acc) :
    ∀ rec, e'.records r.bob = some rec → SingleSession rec → rec.length < 2 ^ 32 - 2 ^ 20 →
    TR.PureTRRecordCanon r r.bob rec ∧
      (∃ rr : RecordRec, rec = recordBytes rr ∧
        rr.current.sessionVersion = 4#32 ∧ rr.current.receiverChains ≠ [] ∧
        rr.current.senderChain.isSome = true ∧ rr.current.pendingKyberPreKey = none) ∧
      e'.sent = TR.sentBodies acc := by
  intro rec hrec hss hlen
  obtain ⟨⟨g₀, ms₀, hc₀⟩, hrel, _⟩ := hR
  obtain ⟨_, _, hcr⟩ := hrel.recs hc₀ r.bob rec hrec
  have hsent : e'.sent = TR.sentBodies acc := (hrel.book hc₀).1
  rcases pureCRecRelH_single hcr hss with htr | ⟨hab, _⟩
  · obtain ⟨_, rr, st, stateIdx, hb, hloc, _, hst_rel, _, hcanon, _, _⟩ := htr r.bob rec (by simp)
    have hcan : TR.PureTRRecordCanon r r.bob rec := hcanon hlen
    obtain ⟨hrc_ne, hpkp⟩ := Symbolic.Swarm.CREF.CliPure.RpkCli.hp3_of_bobKyberNone hbob hrec hb hloc hst_rel
    exact ⟨hcan, ⟨rr, hb, congrArg SessionRec.sessionVersion hst_rel.2, hrc_ne,
      congrArg (fun s => s.senderChain.isSome) hst_rel.2, hpkp⟩, hsent⟩
  · exact False.elim (hwf.1 hab.symm)

/-- Extract `PromEntryHyps` directly from `CReadyPure` and `EligibleForSessionPromotion rec b`. -/
theorem prom_entry_hyps_pure {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {acc : List MachineEvent} {rec b : HwBytes}
    (hwf : ProtocolSetupWF r)
    (hR : CReadyPure interpretation r S who ok e'.records e'.sent e'.accepted e'.opkUsed acc)
    (hwho : who[j]? = some r.bob)
    (hrec : e'.records r.bob = some rec)
    (hlen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hpm : EligibleForSessionPromotion rec b)
    (hhon : HonestIdentity interpretation r b)
    (hpqh : ∀ q, parsePreKeyWire b = some q → PqFromHonest e'.sent q.message) :
    PromEntryHyps interpretation r S who ok j e' acc rec b := by
  have ⟨rr, _, hrec_bytes, hprev_nil, _⟩ := hpm
  obtain ⟨hcanon, hrec4, hsent⟩ :=
    prom_canon_v4_sent_of_clean hwf hR.2.1.bkn hR rec hrec ⟨rr, hrec_bytes, hprev_nil⟩ hlen
  exact ⟨hR, hwho, hrec, hlen, hpm, hcanon, hrec4, hsent, hhon, hpqh⟩

theorem prom_baseKey_in_accepted {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {acc : List MachineEvent} {rec b : HwBytes}
    (hE : PromEntryHyps interpretation r S who ok j e' acc rec b)
    {pf : PreKeyFields} (hpf : parsePreKeyWire b = some pf) :
    pf.baseKey.take 33 ∈ e'.accepted := by
  obtain ⟨rr, pf', hrec_bytes, _, hpf', hbk⟩ := hE.pm
  rw [hpf] at hpf'
  injection hpf' with hpf_eq
  subst hpf_eq
  rw [← hbk]
  exact hE.ready.2.1.bka rr (hrec_bytes ▸ hE.rec_lookup)

end Symbolic.Swarm.CREF.CliPure
