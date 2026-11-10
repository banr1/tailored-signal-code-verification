/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyBPureA
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep

/-!
# Ratchet-Key Alias Discharger for Whisper Receive

Proves the `SignedPrekeyPublished` owner invariant `SpkOwnerBob`, deduces that every stored
`TRState` belongs to `r.alice` or `r.bob`, and discharges `A2bSeedRkAliasRes` (`a2b_hrkAlias`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure hiding StEntry TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

variable {interpretation : ExternInterpretation}

def SpkOwnerBob (r : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ b pk i, tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.SignedPrekeyPublished b pk) i →
    b = r.bob

theorem spkOwnerBob_append_other {r : ProtocolSetup} {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none)
    (h : SpkOwnerBob r tr) : SpkOwnerBob r (tr.append e) :=
  fun b pk i hev => h b pk i (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other hnone hev)

theorem spkOwnerBob_pres_logPQ {r : ProtocolSetup} (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hev : ∀ b pk, ev = .SignedPrekeyPublished b pk → b = r.bob) :
    Symbolic.Swarm.COMPOSED.CompTrace.Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h b pk i hl
  rw [(Symbolic.Swarm.CREF.TR.Runs.logEvent tr ev).2] at hl
  rcases Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_same hl with ⟨_, hl'⟩ | ⟨_, heq⟩
  · exact h b pk i hl'
  · exact hev b pk heq

section SpkOwnerWalks

open Symbolic.Swarm.COMPOSED.CompTrace
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState)

theorem spk_pres_sendMessage {r : ProtocolSetup} (m : DY.Bytes) :
    Preserves (SpkOwnerBob r) (Network.sendMessage m) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.TR.Runs.sendMessage tr m).2]
  exact spkOwnerBob_append_other (e := COMPOSED.CompTrace.NetE m) rfl h

theorem spk_pres_genRand {r : ProtocolSetup} (n : Nat) :
    Preserves (SpkOwnerBob r) (Random.genRand n) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.TR.Runs.genRand tr n).2]
  exact spkOwnerBob_append_other (e := COMPOSED.CompTrace.RndE n) rfl h

theorem spk_pres_logTR {r : ProtocolSetup} (ev : TREvent) :
    Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.Runs.logEvent_tr tr ev).2]
  exact spkOwnerBob_append_other (e := TREvE ev) rfl h

theorem spk_pres_logC {r : ProtocolSetup} (ev : ComposedEvent) :
    Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.Runs.logEvent_c tr ev).2]
  exact spkOwnerBob_append_other (e := CEvE ev) rfl h

theorem spk_pres_storeTR {r : ProtocolSetup} (p : Participant) (st : TRState) :
    Preserves (SpkOwnerBob r) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.Runs.storeLocalState_tr tr p st).2]
  exact spkOwnerBob_append_other (e := TRStE p st) rfl h

theorem spk_pres_storePQ {r : ProtocolSetup} (p : Participant) (st : PQXDHState) :
    Preserves (SpkOwnerBob r) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  rw [(Symbolic.Swarm.CREF.TR.Runs.storeLocalState tr p st).2]
  exact spkOwnerBob_append_other (e := PQStE p st) rfl h

theorem spk_pres_prodCasesOn {r : ProtocolSetup} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves (SpkOwnerBob r) (f a b)) :
    Preserves (SpkOwnerBob r) (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

theorem spk_pres_optionCasesOn {r : ProtocolSetup} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : Preserves (SpkOwnerBob r) noneCase)
    (hs : ∀ a, Preserves (SpkOwnerBob r) (someCase a)) :
    Preserves (SpkOwnerBob r) (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

theorem spk_pres_getKey {r : ProtocolSetup} (p : Participant) (h : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

theorem spk_pres_lookupIdentity {r : ProtocolSetup} (p : Participant) (h : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem spk_pres_dhRatchetStep {r : ProtocolSetup} (st : TRState) (pk : DY.Bytes) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (spk_pres_genRand 32) fun _ => Preserves.pure _

theorem spk_pres_ensureReceiverChain {r : ProtocolSetup} (st : TRState) (pk : DY.Bytes) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (spk_pres_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

theorem spk_pres_logSkippedKeys {r : ProtocolSetup} (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | succ k ih =>
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    exact Preserves.bind (spk_pres_logTR _) fun _ => ih _ _

theorem spk_pres_logMessageKeyAndStore {r : ProtocolSetup} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (spk_pres_logTR _) fun _ => spk_pres_storeTR me st

local macro "spk_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply spk_pres_prodCasesOn
  | with_reducible apply spk_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply spk_pres_genRand | with_reducible apply spk_pres_storeTR
  | with_reducible apply spk_pres_storePQ
  | with_reducible apply spk_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply spk_pres_getKey
  | with_reducible apply spk_pres_lookupIdentity | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply spk_pres_dhRatchetStep
  | with_reducible apply spk_pres_ensureReceiverChain
  | with_reducible apply spk_pres_logSkippedKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply spk_pres_logMessageKeyAndStore
  | with_reducible apply spk_pres_logTR | with_reducible apply spk_pres_logC
  | ((with_reducible apply spkOwnerBob_pres_logPQ); (intro _ _ h; cases h; try rfl))
  | split | with_reducible intro))

theorem spk_pres_aliceHandshake {r : ProtocolSetup} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; spk_tac

theorem spk_pres_bobHandshake {r : ProtocolSetup} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; spk_tac

theorem spk_pres_aliceStart {r : ProtocolSetup} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind (spk_pres_aliceHandshake a b idStateIdx regIdxB h) fun _ => ?_
  spk_tac

theorem spk_pres_bobStart {r : ProtocolSetup} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind (spk_pres_bobHandshake b a kh regIdxA mh.ek mh.ct) fun _ => ?_
  spk_tac

theorem spkOwnerBob_setupTrace (r : ProtocolSetup) : SpkOwnerBob r (setupTrace r) := by
  have hnil : SpkOwnerBob r Trace.nil :=
    fun _ _ _ h => False.elim (Symbolic.Swarm.COMPOSED.CompInv.eventLoggedAt_nil h)
  have hpres : Preserves (SpkOwnerBob r) (ProtocolSetup.setupMove r).act := by
    unfold ProtocolSetup.setupMove Move.act setupAct
      DY.Libsignal.PQXDH.registerIdentity
      DY.Libsignal.PQXDH.genSignedPrekey
      DY.Libsignal.PQXDH.genPQPrekey
      DY.Libsignal.PQXDH.genOneTimePrekey
    spk_tac
  exact hpres Trace.nil hnil

theorem spkOwnerBob_move_next {r : ProtocolSetup} (m : Move) (hsetup : m.isSetup = false) :
    Preserves (SpkOwnerBob r) m.act := by
  cases m with
  | setup _ _ _ => cases hsetup
  | aliceStart a b idStateIdx regIdxB bh shown =>
    unfold Move.act
    exact Preserves.bind (spk_pres_aliceStart a b idStateIdx regIdxB bh) fun _ => Preserves.pure _
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    unfold Move.act
    exact Preserves.bind (spk_pres_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) fun _ => Preserves.pure _
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    unfold Move.act DY.Libsignal.TripleRatchet.messageEncrypt; spk_tac
  | encryptAbort me stateIdx =>
    unfold Move.act DY.Libsignal.TripleRatchet.messageEncryptAbort; spk_tac
  | encryptFail me stateIdx coinsLen =>
    unfold Move.act DY.Libsignal.TripleRatchet.messageEncrypt; spk_tac
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; spk_tac
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.act DY.Libsignal.TripleRatchet.messageDecryptSkipped; spk_tac
  | reject draws =>
    unfold Move.act
    exact Preserves.pure _
  | compromiseIK p stateIdx =>
    unfold Move.act DY.Libsignal.PQXDH.compromiseIK; spk_tac
  | compromiseSPK p stateIdx =>
    unfold Move.act DY.Libsignal.PQXDH.compromiseSPK; spk_tac
  | compromisePQSPK p stateIdx =>
    unfold Move.act DY.Libsignal.PQXDH.compromisePQSPK; spk_tac
  | compromiseOPK p stateIdx =>
    unfold Move.act DY.Libsignal.PQXDH.compromiseOPK; spk_tac
  | exposeKey me stateIdx k =>
    unfold Move.act DY.Libsignal.TripleRatchet.exposeKey; spk_tac
  | exposeSpqr me stateIdx =>
    unfold Move.act DY.Libsignal.TripleRatchet.exposeSpqr; spk_tac
  | exposeSkipped skIdx =>
    unfold Move.act DY.Libsignal.TripleRatchet.exposeSkipped; spk_tac
  | attackerSend msg =>
    unfold Move.act; spk_tac
  | brkDH =>
    unfold Move.act DY.Libsignal.PQXDH.breakDH; spk_tac
  | brkKEM =>
    unfold Move.act DY.Libsignal.PQXDH.breakKEM; spk_tac

theorem spkOwnerBob_runMoves {r : ProtocolSetup} :
    ∀ (ms : List Move) (tr : ExecTrace),
      (∀ m ∈ ms, m.isSetup = false) → SpkOwnerBob r tr → SpkOwnerBob r (runMoves ms tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hms, htr =>
    spkOwnerBob_runMoves ms (m.next tr) (fun m' hm' => hms m' (List.mem_cons_of_mem m hm'))
      (spkOwnerBob_move_next m (hms m List.mem_cons_self) tr htr)

theorem spkOwnerBob_runTrace {r : ProtocolSetup} {ms : List Move}
    (hms : ∀ m ∈ ms, m.isSetup = false) : SpkOwnerBob r (runTraceMoves r ms) :=
  spkOwnerBob_runMoves ms (setupTrace r) hms (spkOwnerBob_setupTrace r)

end SpkOwnerWalks

theorem a2b_owner_alice_or_bob
    {r : ProtocolSetup} {ms : List Move} {q : Participant} {stateIdx : Nat} {st : TRState}
    (hrole : RoleSnapshots r (runTraceMoves r ms))
    (hrun : ModelRun r ms)
    (hst : ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run (runTraceMoves r ms)).1 = some st) :
    q = r.alice ∨ q = r.bob := by
  have hat := Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
  have hr : st.initiator = decide (q = r.alice) := hrole q st stateIdx hat
  have hreach : ReachableTrace (runTraceMoves r ms) := hrun.2.2.1.1
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt q st stateIdx (runTraceMoves r ms) :=
    getLocalState_some_iff_trStateStoredAt.mp hst
  obtain ⟨_, _, _, ⟨doneIdx_c, ikm_c, dh₁_c, hs_c, _, _, _⟩, _⟩ :=
    hInv.stateOK q st stateIdx hst_at
  have hrole_c := hs_c.2.2
  cases hinit : st.initiator with
  | true =>
    exact Or.inl (of_decide_eq_true (hr.symm.trans hinit))
  | false =>
    change (st.sessionInfo q).initiator = false at hinit
    simp only [hinit, Bool.false_eq_true, ↓reduceIte] at hrole_c
    obtain ⟨b, a, t_spk, ikB, ikA, spkSk, pqsk, opk, ek, ct, dh4, e,
      _hspk, _hr64, _hne, hevB, hme, _⟩ := hrole_c
    obtain ⟨_, sS, _, _, _, _, _, ⟨t, _, _, _, hpub⟩, _⟩ :=
      (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach).bobDone
        b a _ _ _ _ _ _ _ _ doneIdx_c hevB
    exact Or.inr (hme.trans (spkOwnerBob_runTrace hrun.2.1 b _ (t + 2) hpub))

theorem a2b_hrkAlias_of_shapeNe
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre : List Move) (m : Move) (post : List Move)
    (acc blk : List MachineEvent)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hch₀ : CHistBy interpretation r S g ms₀)
    (hfresh₀ : TR.TRRecvFreshAll r ms₀)
    (hC14_all : A2bRkAliasShapeNeExcl interpretation r S g (ms₀ ++ pre) acc) :
    TR.RecvDecStepTiePure.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc := by
  intro q stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body_in
    hst hcur hc hfind hrep hparse hver hnc hsk hmac_eq hγrk hcons hγ
  have hq := a2b_quietPre hpre
  have hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) :=
    a2b_roleSnapshots_of_quietPre hpre hch₀.2
  have hfresh : TR.TRRecvFreshAll r (ms₀ ++ pre) :=
    a2b_trRecvFreshAll_of_quietExt hq hfresh₀
  have hrun : ModelRun r (ms₀ ++ pre) := a2b_modelRun_pre hB
  have hreach : ReachableTrace (runTraceMoves r (ms₀ ++ pre)) := hrun.2.2.1.1
  have hq_ab : q = r.alice ∨ q = r.bob := a2b_owner_alice_or_bob hrole hrun hst
  obtain ⟨_hcf, hskRel⟩ := hfresh q stateIdx st hq_ab hst hcur
  by_cases hshape :
      (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape
  · exact False.elim (a2b_rkAlias_false_of_shape_eq hreach hskRel hst hc hfind hcons hsk hshape)
  · have hst_avail : st ∈ availableStates r (runTraceMoves r (ms₀ ++ pre)) :=
      Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r (ms₀ ++ pre)
        (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst)
    exact False.elim (hnc (hC14_all t ⟨msg, hparse, hver, seed_s, a2b_mem_skippedSeedsFor hsk,
      TR.RecvDecStepTiePure.a2b_skippedSeed_hmac hreach hsk, pqSalt, st,
      hst_avail, hmac_eq, c, hc, seed_c, c', hfind, hγrk, hcons, hγ, hshape⟩))

theorem a2b_hrkAlias
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre : List Move) (m : Move) (post : List Move)
    (acc blk : List MachineEvent)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hch₀ : CHistBy interpretation r S g ms₀)
    (hfresh₀ : TR.TRRecvFreshAll r ms₀) :
    TR.RecvDecStepTiePure.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc :=
  a2b_hrkAlias_of_shapeNe r S g ms₀ pre m post acc blk hB hpre hch₀ hfresh₀
    (a2b_rkAliasShapeNeExcl r S g (ms₀ ++ pre) acc)

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
