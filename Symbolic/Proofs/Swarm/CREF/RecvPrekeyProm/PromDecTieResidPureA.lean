/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedEqPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkPairUniq
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineLink
import Symbolic.Proofs.Swarm.Leaves.IC14_Stage1Trials
public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Residual Freshness, Cross-Seed Exclusion, and Same-Origin Helpers

Proves `prom_fresh_of_matchedPrefix`, `prom_crossSeedExcl`, `prom_seedShapeEqRes_of_modelRun`, and
the `pdtr_NoDoneEv` preservation lemmas used by `PromDecTieResidPure`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo kdfCk computeMac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

theorem pdtr_prom_resid_modelRun_pre {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

theorem prom_fresh_of_matchedPrefix
    (interpretation : ExternInterpretation)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ : List Move} {acc : List MachineEvent}
    (hmp₀ : MatchedPrefix interpretation r S who g ms₀ acc) :
    TR.TRRecvFreshAll r ms₀ :=
  trRecvFreshAll_of_matchedPrefix interpretation hmp₀

/-- Proves `A2bCrossSeedExcl` via `MacTagForgeryOrCollision`. -/
theorem prom_crossSeedExcl
    (interpretation : ExternInterpretation)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {acc : List MachineEvent} :
    TR.RecvDecStep.A2bCrossSeedExcl interpretation r S g ms acc := by
  intro t ⟨msg, hparse, hver, seed, hseed_mem, salt, st₀, hst₀_av, hfind₀, hmac_eq,
    st, hst_av, c, hc, seed', c', hγrk, hcons, hγ, k, hk, hmacγ⟩
  unfold TR.RecvDecStep.skippedSeedsFor at hseed_mem
  obtain ⟨idx, _hidx_range, hidx_ev⟩ := List.mem_filterMap.mp hseed_mem
  cases hget : (runTraceMoves r ms).getEventAt DY.Libsignal.TripleRatchet.TREvent idx with
  | none => simp [hget] at hidx_ev
  | some ev =>
    rw [hget] at hidx_ev
    cases ev with
    | SkippedKeyStored s pk n seed₀ rIdx src =>
      dsimp only at hidx_ev
      split at hidx_ev
      · next hcond =>
        injection hidx_ev with hseed_eq; subst hseed_eq
        rcases hcond with ⟨rfl, rfl⟩
        have hev : (runTraceMoves r ms).EventLoggedAt
            (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s msg.ratchetKey msg.counter seed₀ rIdx src) idx := by
          rwa [DY.Trace.EventLoggedAt_eq_getEventAt]
        have hctx := Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_mem_of_byteChain_some
          hver hst_av hc hγrk hcons
        have hctx₀ := Symbolic.Swarm.CREF.Stage1Trials.whisperTrials_mem_of_skippedKeyStored
          (interpretation := interpretation) (S := S) (g := g) hver hst₀_av hfind₀ hev rfl
        exact Symbolic.Swarm.CREF.Stage1Trials.RecvCollision.of_ownSaltMacCollision hparse
          (Symbolic.Swarm.CREF.Stage1Trials.MacTagForgeryOrCollision.of_crossSeedTerm_exact
            hctx rfl hk hmacγ hctx₀ rfl hγ hmac_eq)
      · cases hidx_ev
    | _ => cases hidx_ev

/-- Proves `A2bSeedShapeEqRes` on any `ModelRun` via `a2b_sameOrigin_seed_eq_core`. -/
theorem prom_seedShapeEqRes_of_modelRun
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (hrun : ModelRun r₀ ms) :
    TR.RecvDecStep.A2bSeedShapeEqRes interpretation r₀ S g ms acc := by
  intro p stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body
    hst _hcur _hc hfind _hrep _hparse _hver _hnc hsk _hmac_eq hcons _hγ hsh
  have hreach : TR.G1.ReachableTrace (runTraceMoves r₀ ms) := hrun.2.2.1.1
  obtain ⟨p₀, _, _, st₀, c₀, _, _, _,
    _, _, _, hc₀_rk, _hc₀_rIdx, hc₀_seed, _, _, hst₀, _hsinfo₀, hdisj⟩ :=
    TR.RecvDecStep.skippedPkLineage_of_reachable hreach skIdx (st.sessionInfo p) msg.ratchetKey
      msg.counter seed_s rIdx_s srcIdx hsk
  have hc₀_origin : c₀ ∈ st₀.recv ∨ c₀ = TR.G1.freshRecvChain st₀ msg.ratchetKey ∨
      (rIdx_s = 2 ∧ c₀.index = 0) :=
    hdisj.imp id (Or.imp id fun ⟨_, _, hr, hi⟩ => ⟨hr, hi⟩)
  exact (TR.RecvDecStep.a2b_sameOrigin_seed_eq_core interpretation S g hreach
    (TR.G1.Spine.recvLinkStored_of_reachable hreach)
    (fun h₁ h₂ hd => (TR.G1.trStateStoredAt_rk_eq_of_dhs_eq hreach h₁ h₂ hd).1)
    hst hfind hcons hsk hsh hst₀ hc₀_rk hc₀_seed hc₀_origin).1

theorem pdtr_memo_mem_of_computeMac_seed (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed peerIk myIk wire : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g seed).memo) :
    e ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys salt seed).macKey peerIk myIk wire)).memo :=
  TR.RecvDecStep.a2b_memo_mem_computeMac_seed i S g salt seed peerIk myIk wire he

theorem pdtr_pqxdhIkm_tail_eq {a₁ b₁ e₁ a₂ b₂ e₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    {ss₁ ss₂ : DY.Bytes}
    (h : DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ e₁ d₁ ss₁ =
      DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ e₂ d₂ ss₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ e₁ = e₂ := by
  unfold DY.Libsignal.PQXDH.pqxdhIkm at h
  have h1 := (TR.G1.concat_injective h).2
  obtain ⟨ha, h2⟩ := TR.G1.concat_injective h1
  obtain ⟨hb, h3⟩ := TR.G1.concat_injective h2
  obtain ⟨he, _⟩ := TR.G1.concat_injective h3
  exact ⟨ha, hb, he⟩

theorem pdtr_spineRkK_and_ikmHolesK {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop}
    {b : Bool} {v : DY.Bytes} (hv : TR.G1.Spine.SpineRkK K B b v) :
    TR.G1.Spine.SpineRkK K (fun c ikm => B c ikm ∧ TR.G1.Spine.IkmHolesK K ikm) b v := by
  induction hv with
  | hsRk hB hI => exact .hsRk ⟨hB, hI⟩ hI
  | hsCk hB hI => exact .hsCk ⟨hB, hI⟩ hI
  | rkStep1 _ hRk hD ih => exact .rkStep1 ih hRk hD
  | rkStep2 _ hRk hD ih => exact .rkStep2 ih hRk hD
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

section DoneOpkEkAkProof

open DY.Libsignal.PQXDH (PQXDHEvent pqxdhIkm registerIdentity registerCorruptIdentity
  genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK
  compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TREvent KeyComponent KeyDir dhRatchetStep ensureReceiverChain
  logMessageKeyAndStore logSkippedKeys verifyMacAndDecrypt messageEncrypt messageEncryptAbort
  messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped guardTrace)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

def pdtr_DoneOpkEkAk (tr : ExecTrace) : Prop :=
  (∀ a b ikA ikB spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) i →
    ∀ o, opk = some o → o.AttackerKnows tr) ∧
  (∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    ek.AttackerKnows tr)

set_option quotPrecheck false in
local notation "isDoneEv_pdtrpa758" => (fun (ev : PQXDHEvent) => match ev with
  | .AliceDone .. => true
  | .BobDone .. => true
  | _ => false)

def pdtr_NoDoneEv {α : Type} (f : Traceful α) : Prop :=
  ∀ tr ev idx, isDoneEv_pdtrpa758 ev = true → ((f.run tr).2.val).EventLoggedAt ev idx →
    tr.EventLoggedAt ev idx

theorem pdtr_NoDoneEv.pure {α : Type} (x : α) : pdtr_NoDoneEv (Pure.pure x) := by
  intro tr ev idx _ h; rw [DY.Traceful.run_pure] at h; exact h

theorem pdtr_NoDoneEv.failure {α : Type} : pdtr_NoDoneEv (Alternative.failure : Traceful α) := by
  intro tr ev idx _ h; rw [DY.Traceful.run_failure] at h; exact h

theorem pdtr_run_bind_snd_nde {α β : Type} (f : Traceful α) (g : α → Traceful β) (tr : ExecTrace) :
    ((f >>= g).run tr).2.val =
      match (f.run tr).1 with
      | none => (f.run tr).2.val
      | some a => ((g a).run (f.run tr).2.val).2.val := by
  rw [Traceful.run_bind]
  rcases f.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (g a).run tr1.val with ⟨_, _⟩; rfl

theorem pdtr_NoDoneEv.bind {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : pdtr_NoDoneEv f) (hg : ∀ x, pdtr_NoDoneEv (g x)) : pdtr_NoDoneEv (f >>= g) := by
  intro tr ev idx hd h
  rw [pdtr_run_bind_snd_nde] at h
  rcases hrun : (f.run tr).1 with _ | x
  · rw [hrun] at h
    exact hf tr ev idx hd h
  · rw [hrun] at h
    exact hf tr ev idx hd (hg x _ ev idx hd h)

theorem pdtr_NoDoneEv.guardP (p : Prop) [Decidable p] : pdtr_NoDoneEv (_root_.guard p) := by
  unfold _root_.guard; split
  · exact pdtr_NoDoneEv.pure _
  · exact pdtr_NoDoneEv.failure

private theorem noDoneEv_guardTrace_pdtrpa758 (p : ExecTrace → Bool) : pdtr_NoDoneEv (guardTrace p) := by
  intro tr ev idx _ h; unfold guardTrace at h; rw [DY.Traceful.run_mk] at h; exact h

theorem pdtr_noDoneEv_guardOnTrace (p : ExecTrace → Bool) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.guardTrace p) := by
  intro tr ev idx _ h
  unfold DY.Libsignal.PQXDH.guardTrace at h; rw [DY.Traceful.run_mk] at h; exact h

theorem pdtr_noDoneEv_traceLength : pdtr_NoDoneEv DY.Libsignal.TripleRatchet.traceLength := by
  intro tr ev idx _ h
  unfold DY.Libsignal.TripleRatchet.traceLength at h; rw [DY.Traceful.run_mk] at h; exact h

private theorem noDoneEv_getEntry_pdtrpa758 (E : Type) [ExecTraceTypes.Has E] (j : Nat) :
    pdtr_NoDoneEv (DY.getEntry j : Traceful E) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h; rw [Traceful.run_mk] at h; dsimp only at h
  cases (tr.at? j : Option E) <;> exact h

theorem pdtr_noDoneEv_receiveMessage (j : Nat) : pdtr_NoDoneEv (DY.Network.receiveMessage j) := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact pdtr_NoDoneEv.bind (noDoneEv_getEntry_pdtrpa758 _ j) fun _ => pdtr_NoDoneEv.pure _

theorem pdtr_noDoneEv_receiveSignalMsg (j : Nat) :
    pdtr_NoDoneEv (DY.Libsignal.TripleRatchet.receiveSignalMsg j) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage j) fun raw => ?_
  cases parseTrSignalMsg raw
  · exact pdtr_NoDoneEv.failure
  · exact pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ => pdtr_NoDoneEv.pure _

private theorem noDoneEv_getLocalStateTR_pdtrpa758 (p : Participant) (j : Nat) :
    pdtr_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful TRState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact pdtr_NoDoneEv.bind (pdtr_NoDoneEv.bind (noDoneEv_getEntry_pdtrpa758 _ j) fun _ => pdtr_NoDoneEv.pure _)
    fun _ => pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ => pdtr_NoDoneEv.pure _

private theorem noDoneEv_getLocalStatePQ_pdtrpa758 (p : Participant) (j : Nat) :
    pdtr_NoDoneEv (DY.PersistentLocalState.getLocalState p j : Traceful DY.Libsignal.PQXDH.PQXDHState) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1]
  exact pdtr_NoDoneEv.bind (pdtr_NoDoneEv.bind (noDoneEv_getEntry_pdtrpa758 _ j) fun _ => pdtr_NoDoneEv.pure _)
    fun _ => pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ => pdtr_NoDoneEv.pure _

private theorem noDoneEv_getKey_pdtrpa758 (p : Participant) (j : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.getKey p j k) :=
  pdtr_NoDoneEv.bind (noDoneEv_getLocalStatePQ_pdtrpa758 p j) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ => pdtr_NoDoneEv.pure _

private theorem noDoneEv_genRand_pdtrpa758 (n : Nat) : pdtr_NoDoneEv (DY.Random.genRand n) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem pdtr_noDoneEv_sendMessage (m : DY.Bytes) : pdtr_NoDoneEv (DY.Network.sendMessage m) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

theorem pdtr_noDoneEv_logEventTR (e : TREvent) : pdtr_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem pdtr_noDoneEv_logEventC (e : DY.Libsignal.Composed.ComposedEvent) :
    pdtr_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx _ h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  exact eventLoggedAt_append_other h rfl

theorem pdtr_noDoneEv_logEventPQ {e : PQXDHEvent} (he : isDoneEv_pdtrpa758 e = false) :
    pdtr_NoDoneEv (DY.ProtocolEvent.logEvent e) := by
  intro tr ev idx hd h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure] at h
  rcases eventLoggedAt_append_ev_iff.mp h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact h
  · rw [he] at hd; cases hd

private theorem noDoneEv_storeTR_pdtrpa758 (p : Participant) (st : TRState) :
    pdtr_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_storePQ_pdtrpa758 (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    pdtr_NoDoneEv (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr ev idx _ h
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at h
  exact eventLoggedAt_append_other h rfl

private theorem noDoneEv_dhRatchetStep_pdtrpa758 (st : TRState) (pk : DY.Bytes) :
    pdtr_NoDoneEv (dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ => pdtr_NoDoneEv.pure _

theorem pdtr_noDoneEv_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    pdtr_NoDoneEv (ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact pdtr_NoDoneEv.pure _
  · exact pdtr_NoDoneEv.bind (noDoneEv_dhRatchetStep_pdtrpa758 st pk) fun _ => pdtr_NoDoneEv.pure _
  · exact pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    pdtr_NoDoneEv (logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => noDoneEv_storeTR_pdtrpa758 me st

theorem pdtr_noDoneEv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), pdtr_NoDoneEv (logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold logSkippedKeys; exact pdtr_NoDoneEv.pure _
  | ck, n, k + 1 => by
    unfold logSkippedKeys
    exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
      pdtr_noDoneEv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

theorem pdtr_noDoneEv_verifyMacAndDecrypt (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) : pdtr_NoDoneEv (verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold verifyMacAndDecrypt
  refine pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ => ?_
  intro tr ev idx _ h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [DY.Traceful.run_mk] at h
  exact h

theorem pdtr_noDoneEv_messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) :
    pdtr_NoDoneEv (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  exact pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 coinsLen) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage pqIdx) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logMessageKeyAndStore me _ .sender _ _ _ _ _ _) fun _ =>
    pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_messageEncryptAbort (me : Participant) (stateIdx : Nat) :
    pdtr_NoDoneEv (messageEncryptAbort me stateIdx) := by
  unfold messageEncryptAbort
  exact pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ => pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) : pdtr_NoDoneEv (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun st₀ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_ensureReceiverChain st₀ msg.ratchetKey) fun ⟨st, c, _⟩ => ?_
  dsimp only
  split
  · split
    · refine pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ => ?_
      split
      · exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
          pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
          pdtr_NoDoneEv.bind (pdtr_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
          pdtr_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
      · exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logSkippedKeys _ _ _ _ _ _ _) fun _ =>
          pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
          pdtr_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact pdtr_NoDoneEv.failure
  · exact pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_messageDecryptSkipped (me : Participant)
    (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    pdtr_NoDoneEv (messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun st =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveSignalMsg msgIdx) fun msg =>
    pdtr_NoDoneEv.bind (noDoneEv_getEntry_pdtrpa758 _ skippedKeyEventIdx) fun _ => ?_
  split
  · refine pdtr_NoDoneEv.bind (pdtr_NoDoneEv.guardP _) fun _ =>
      pdtr_NoDoneEv.bind (noDoneEv_guardTrace_pdtrpa758 _) fun _ => ?_
    split
    · exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage pqIdx) fun pqSalt =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_verifyMacAndDecrypt st msg pqSalt _) fun _ =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
        pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ =>
        pdtr_noDoneEv_logMessageKeyAndStore me _ .receiver _ _ _ _ _ _
    · exact pdtr_NoDoneEv.failure
  · exact pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_exposeKey (me : Participant) (stateIdx : Nat) (k : KeyComponent) :
    pdtr_NoDoneEv (exposeKey me stateIdx k) := by
  unfold exposeKey
  refine pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun _ => ?_
  cases k with
  | rk => exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _
  | dhs => exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _
  | cks => exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _
  | ckr _ =>
    dsimp only; split
    · exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _
    · exact pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_exposeSpqr (me : Participant) (stateIdx : Nat) :
    pdtr_NoDoneEv (exposeSpqr me stateIdx) := by
  unfold exposeSpqr
  exact pdtr_NoDoneEv.bind (noDoneEv_getLocalStateTR_pdtrpa758 me stateIdx) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_exposeSkipped (skippedKeyEventIdx : Nat) :
    pdtr_NoDoneEv (exposeSkipped skippedKeyEventIdx) := by
  unfold exposeSkipped
  refine pdtr_NoDoneEv.bind (noDoneEv_getEntry_pdtrpa758 _ skippedKeyEventIdx) fun _ => ?_
  split
  · exact pdtr_NoDoneEv.bind (noDoneEv_guardTrace_pdtrpa758 _) fun _ =>
      pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventTR _) fun _ => pdtr_noDoneEv_sendMessage _
  · exact pdtr_NoDoneEv.failure

theorem pdtr_noDoneEv_registerIdentity (p : Participant) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_guardOnTrace _) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ => noDoneEv_storePQ_pdtrpa758 p _

theorem pdtr_noDoneEv_genSignedPrekey (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.genSignedPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 64) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_storePQ_pdtrpa758 b _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ => pdtr_NoDoneEv.pure _

theorem pdtr_noDoneEv_genPQPrekey (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.genPQPrekey b j) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 64) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 64) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_storePQ_pdtrpa758 b _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ => pdtr_NoDoneEv.pure _

theorem pdtr_noDoneEv_genOneTimePrekey (b : Participant) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact pdtr_NoDoneEv.bind (noDoneEv_genRand_pdtrpa758 32) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ =>
    pdtr_NoDoneEv.bind (noDoneEv_storePQ_pdtrpa758 b _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_sendMessage _) fun _ => pdtr_NoDoneEv.pure _

theorem pdtr_noDoneEv_compromiseIK (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (compromiseIK b j) := by
  unfold compromiseIK
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ => pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_compromiseSPK (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (compromiseSPK b j) := by
  unfold compromiseSPK
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ => pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_compromisePQSPK (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (compromisePQSPK b j) := by
  unfold compromisePQSPK
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ => pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_compromiseOPK (b : Participant) (j : Nat) :
    pdtr_NoDoneEv (compromiseOPK b j) := by
  unfold compromiseOPK
  exact pdtr_NoDoneEv.bind (noDoneEv_getKey_pdtrpa758 b j _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_guardOnTrace _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ => pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    pdtr_NoDoneEv (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  exact pdtr_NoDoneEv.bind (pdtr_noDoneEv_guardOnTrace _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage skIdx) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_logEventPQ rfl) fun _ => pdtr_noDoneEv_logEventPQ rfl

theorem pdtr_noDoneEv_breakDH : pdtr_NoDoneEv DY.Libsignal.PQXDH.breakDH :=
  pdtr_noDoneEv_logEventPQ rfl

theorem pdtr_noDoneEv_breakKEM : pdtr_NoDoneEv DY.Libsignal.PQXDH.breakKEM :=
  pdtr_noDoneEv_logEventPQ rfl

theorem pdtr_noDoneEv_invertDH (inp : Nat) : pdtr_NoDoneEv (DY.Libsignal.PQXDH.invertDH inp) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine pdtr_NoDoneEv.bind (pdtr_noDoneEv_guardOnTrace _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage inp) fun pk => ?_
  cases DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key pk)
  · exact pdtr_NoDoneEv.failure
  · exact pdtr_noDoneEv_sendMessage _

theorem pdtr_noDoneEv_invertKEM (inp : Nat) : pdtr_NoDoneEv (DY.Libsignal.PQXDH.invertKEM inp) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine pdtr_NoDoneEv.bind (pdtr_noDoneEv_guardOnTrace _) fun _ =>
    pdtr_NoDoneEv.bind (pdtr_noDoneEv_receiveMessage inp) fun pk =>
      pdtr_NoDoneEv.bind ?_ fun _ => pdtr_noDoneEv_sendMessage _
  intro tr ev idx _ h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rw [DY.Traceful.run_mk] at h
  exact h

end DoneOpkEkAkProof

end Symbolic.Swarm.CREF.CliPure
