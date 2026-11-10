/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown hiding bytes_rec_gAll
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
private theorem attackerKnows_runMoves (ms : List Move) (tr : ExecTrace) {u : DY.Bytes} (h : u.AttackerKnows tr) : u.AttackerKnows (runMoves ms tr).1 := DY.Bytes.AttackerKnows_le u tr (runMoves ms tr).1 (Symbolic.Swarm.CREF.runMoves_le ms tr) h
theorem ptAtoms_subset_append (r : Records) (ms δ : List Move) : ∀ u ∈ ptAtoms (runVis r ms), u ∈ ptAtoms (runVis r (ms ++ δ)) := by intro u hu; unfold ptAtoms plaintextTerms runVis at hu ⊢; rw [← List.cons_append, CompPrefixInvStruct.runMoves_append_snd]; simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hu ⊢; obtain ⟨v, ⟨hv_mem, hv_k⟩, hu_v⟩ := hu; exact ⟨v, ⟨List.mem_append_left _ hv_mem, hv_k⟩, hu_v⟩
theorem ptAvoidFull_append {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (δ : List Move) {b : HwBytes} {t : DY.Bytes} (h : PtAvoidFull i r S g ms b t) : PtAvoidFull i r S g (ms ++ δ) b t := by
  intro x hx hnpt hinj hnk
  refine h x hx (fun hpt => hnpt (ptAtoms_subset_append r ms δ x.1 hpt)) hinj (fun hk => hnk ?_)
  rw [Symbolic.Swarm.CREF.xpl_runTrace_eq, CompPrefixInvStruct.runMoves_append_fst, ← Symbolic.Swarm.CREF.xpl_runTrace_eq]; exact attackerKnows_runMoves δ (runTraceMoves r ms) hk
open Symbolic.Swarm.COMPOSED.CompInv.CompPresBob (bobInitSt bobRatchetedChain bobRatchetedSt)
def bobOutOf (ikB spk pqsk : DY.Bytes) (opk : Option DY.Bytes) (ikAPk ek ct : DY.Bytes) (keys : DY.Libsignal.PQXDH.HandshakeKeys) : DY.Libsignal.PQXDH.BobHandshakeOut := { ikB := DY.DiffieHellman.dhPk ikB, ikA := ikAPk, spk := DY.DiffieHellman.dhPk spk, pqpk := DY.PQKem.kemPk pqsk, opk := opk.map DY.DiffieHellman.dhPk, ek, ct, spkSk := spk, keys }
def bobStartPreSkipTr (tr : ExecTrace) (b a : Participant) (o : DY.Libsignal.PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) : ExecTrace :=
  let dhs := randTerm tr.length 32
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey dhs
  let tr_send := (tr.append (TR.RndE 32)).append (TR.NetE key)
  let tr_opk := match o.opk with | some opkPk => tr_send.append (TR.EvE (.OPKUsed b opkPk)) | none => tr_send
  let doneIdx := tr_opk.length
  (((tr_opk.append (TR.EvE (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DY.DiffieHellman.dhPk st.dhs)))).append (TREvE (.HonestDH (st.sinfo b) st.dhs (st.rIdx - 2)))).append (CEvE (.HandshakeSession (st.sinfo b) doneIdx))
def bobFinalSt (tr : ExecTrace) (a : Participant)
    {b : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : DY.Libsignal.TripleRatchet.TRState :=
  let st := bobRatchetedSt a (DY.DiffieHellman.dhPk w.ikB) w.ikAPk w.keys w.spk w.msg.ratchetKey (randTerm tr.length 32)
  { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv w.c', spqr := w.spqr' }
def bobStartSkipTr (tr : ExecTrace) (b a : Participant)
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : ExecTrace :=
  let o := bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk w.msg.ratchetKey (randTerm tr.length 32)
  let c := bobRatchetedChain o.keys w.msg.ratchetKey o.spkSk
  let tr_hs := bobStartPreSkipTr tr b a o w.msg w.key
  let skipped := w.msg.counter.toNat - c.index.toNat
  ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sinfo b) w.msg.ratchetKey c.rIdx (tr_hs.length + skipped + 2) c.chainKey c.index skipped).run tr_hs).2.val
def bobStartTr (tr : ExecTrace) (b a : Participant)
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : ExecTrace :=
  let o := bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk w.msg.ratchetKey (randTerm tr.length 32)
  let c := bobRatchetedChain o.keys w.msg.ratchetKey o.spkSk
  let tr_hs := bobStartPreSkipTr tr b a o w.msg w.key
  let skipped := w.msg.counter.toNat - c.index.toNat
  let childIdx := tr_hs.length + skipped + 2
  let tr_recv := (bobStartSkipTr tr b a w).append (TREvE (.Received b st.peer w.msg.ratchetKey w.msg.counter w.m))
  (tr_recv.append (TREvE (.MessageKey (st.sinfo b) .receiver w.seed w.pqSalt w.msg.counter c.rIdx childIdx))).append (TRStE b (bobFinalSt tr a w))
private theorem runs_lookupIdentity {tr : ExecTrace} {p : Participant} {regIdx : Nat} {ikPk vkPk : DY.Bytes} {honest : Bool} (hreg : tr.at? regIdx = some (TR.EvE (.IdentityRegistered p ikPk vkPk honest))) : TR.Runs (DY.Libsignal.PQXDH.lookupIdentity p regIdx) tr (ikPk, vkPk) tr := by unfold DY.Libsignal.PQXDH.lookupIdentity; exact TR.Runs.bind (TR.Runs.getEntry hreg) (TR.Runs.bind (TR.Runs.guard _ rfl) (TR.Runs.pure _ _))
private theorem runs_receiveMessage {tr : ExecTrace} {idx : Nat} {b : DY.Bytes} (hnet : tr.at? idx = some (TR.NetE b)) : TR.Runs (DY.Network.receiveMessage idx) tr b tr := by
  rw [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact TR.Runs.bind (TR.Runs.getEntry hnet) (TR.Runs.pure _ _)
private theorem runs_bobHandshake {tr : ExecTrace} {b a : Participant} {h : DY.Libsignal.PQXDH.BobKeyHandles} {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : DY.Bytes} {opk : Option DY.Bytes} {honest : Bool} {keys : DY.Libsignal.PQXDH.HandshakeKeys} (hik : tr.at? h.ik = some (TR.StE b { kind := .identity, sk := ikB })) (hspk : tr.at? h.spk = some (TR.StE b { kind := .signedPrekey, sk := spk })) (hpq : tr.at? h.pqspk = some (TR.StE b { kind := .pqPrekey, sk := pqsk })) (hopk : StOpt tr b h.opk opk) (hreg : tr.at? regA = some (TR.EvE (.IdentityRegistered a ikAPk vkA honest))) (hek : tr.at? ekH = some (TR.NetE ek)) (hct : tr.at? ctH = some (TR.NetE ct)) (hcan : DY.Libsignal.PQXDH.isCanonicalKey ek = true) (hagree : DY.Libsignal.PQXDH.bobAgreement ikB spk pqsk opk ikAPk ek ct = some keys) : TR.Runs (DY.Libsignal.PQXDH.bobHandshake b a h regA ekH ctH) tr (bobOutOf ikB spk pqsk opk ikAPk ek ct keys) tr := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine TR.Runs.bind (TR.Runs.getKey hik) (TR.Runs.bind (TR.Runs.getKey hspk) (TR.Runs.bind (TR.Runs.getKey hpq) ?_))
  rcases hoi : h.opk with _ | i <;> rcases opk with _ | o <;> rw [hoi] at hopk <;> dsimp only [StOpt] at hopk
  · dsimp only; refine TR.Runs.bind (TR.Runs.pure _ _) (TR.Runs.bind (runs_lookupIdentity hreg)
      (TR.Runs.bind (runs_receiveMessage hek) (TR.Runs.bind (runs_receiveMessage hct) (TR.Runs.bind (TR.Runs.guard _ hcan) ?_))))
    rw [hagree]; exact TR.Runs.pure _ _
  · dsimp only; refine TR.Runs.bind (TR.Runs.getKey hopk) (TR.Runs.bind (TR.Runs.pure _ _)
      (TR.Runs.bind (runs_lookupIdentity hreg) (TR.Runs.bind (runs_receiveMessage hek)
      (TR.Runs.bind (runs_receiveMessage hct) (TR.Runs.bind (TR.Runs.guard _ hcan) ?_)))))
    rw [hagree]; exact TR.Runs.pure _ _
private theorem runs_receiveSignalMsg {tr : ExecTrace} {msgH : Nat} {raw : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} (hnet : tr.at? msgH = some (TR.NetE raw)) (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg) (hver : msg.version = DY.Libsignal.TripleRatchet.messageVersion) : TR.Runs (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) tr msg tr := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; refine TR.Runs.bind (runs_receiveMessage hnet) ?_
  rw [hparse]; dsimp only; exact TR.Runs.bind (TR.Runs.guard _ hver) (TR.Runs.pure _ _)
private theorem runs_ensureReceiverChain_bobInitSt {tr : ExecTrace} {a : Participant} {ikB ikA : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {sS rt : DY.Bytes} (hlo : DY.Libsignal.TripleRatchet.x25519LowOrder rt = false) : TR.Runs (DY.Libsignal.TripleRatchet.ensureReceiverChain (bobInitSt a ikB ikA keys sS rt) rt) tr (bobRatchetedSt a ikB ikA keys sS rt (randTerm tr.length 32), bobRatchetedChain keys rt sS, true) (tr.append (TR.RndE 32)) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor DY.Libsignal.TripleRatchet.findRecvChain
  dsimp only [bobInitSt, List.find?_nil]; simp only [hlo, Bool.false_eq_true, ↓reduceIte]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  have hlo' : (!DY.Libsignal.TripleRatchet.x25519LowOrder rt) = true := by simp [hlo]
  exact TR.Runs.bind (TR.Runs.bind (TR.Runs.guard _ hlo') (TR.Runs.bind (TR.Runs.genRand tr 32) (TR.Runs.pure _ _))) (TR.Runs.pure _ _)
private theorem runs_verifyMacAndDecrypt {tr : ExecTrace} {st : DY.Libsignal.TripleRatchet.TRState} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {pqSalt seed m : DY.Bytes} (hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire) (hdec : DY.Libsignal.PQXDH.errToOption (DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m) : TR.Runs (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) tr m tr := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt; refine TR.Runs.bind (TR.Runs.guard _ hmac) ?_
  exact ⟨by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.monadLift_err_fst_eq, hdec],
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.monadLift_err_snd_eq _ _⟩
theorem bobStart_next_eq {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {sh : Nat} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx sh).next tr = bobStartTr tr b a w := by
  let o := bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk w.msg.ratchetKey (randTerm tr.length 32)
  let c := bobRatchetedChain o.keys w.msg.ratchetKey o.spkSk
  let tr_hs := bobStartPreSkipTr tr b a o w.msg w.key
  let tr_skip := bobStartSkipTr tr b a w
  let tr_recv := tr_skip.append (TREvE (.Received b st.peer w.msg.ratchetKey w.msg.counter w.m))
  suffices hrun : TR.Runs (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx) tr
      (tr_recv.length + 1) (bobStartTr tr b a w) by
    unfold Move.next Move.act; rw [run_bind_snd, hrun.1, hrun.2]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd () _
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine TR.Runs.bind (runs_bobHandshake w.hik w.hspk w.hpq w.hopk w.hreg w.hek w.hct w.hcan w.hagree) (TR.Runs.bind (runs_receiveSignalMsg w.hmsg w.hparse w.hver) (TR.Runs.bind (runs_ensureReceiverChain_bobInitSt w.hlow) ?_))
  dsimp only [o, bobOutOf]; rw [w.hcons, w.hspqr]; dsimp only
  refine TR.Runs.bind (TR.Runs.sendMessage _ w.key) (TR.Runs.bind (runs_receiveMessage w.hpqSalt) (TR.Runs.bind (runs_verifyMacAndDecrypt w.hmac w.hdec) ?_))
  have hlog_skip : ∀ (t : ExecTrace) (src : Nat), TR.Runs (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sinfo b) w.msg.ratchetKey c.rIdx src c.chainKey c.index (w.msg.counter.toNat - c.index.toNat)) t () ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sinfo b) w.msg.ratchetKey c.rIdx src c.chainKey c.index (w.msg.counter.toNat - c.index.toNat)).run t).2.val :=
    fun _ _ => ⟨Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.run_logSkippedKeys_fst _ _ _ _ _ _ _ _, rfl⟩
  have hlog_tr : ∀ (t : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent), TR.Runs (DY.ProtocolEvent.logEvent ev) t () (t.append (TREvE ev)) :=
    fun t _ => by rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]; exact TR.Runs.bind (TR.Runs.appendEntry t _) (TR.Runs.pure _ _)
  have hlog_c : ∀ (t : ExecTrace) (ev : CEvent), TR.Runs (DY.ProtocolEvent.logEvent ev) t () (t.append (CEvE ev)) :=
    fun t _ => by rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]; exact TR.Runs.bind (TR.Runs.appendEntry t _) (TR.Runs.pure _ _)
  have hlen : ∀ (t : ExecTrace), TR.Runs DY.Libsignal.TripleRatchet.traceLength t t.length t :=
    fun _ => by unfold TR.Runs DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩
  have hstore_tr : ∀ (t : ExecTrace) (st' : DY.Libsignal.TripleRatchet.TRState), TR.Runs (DY.PersistentLocalState.storeLocalState b st') t t.length (t.append (TRStE b st')) :=
    fun t st' => by rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]; exact TR.Runs.appendEntry t (TRStE b st')
  have hlmk : ∀ (t : ExecTrace) (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) (st' : DY.Libsignal.TripleRatchet.TRState),
      TR.Runs (DY.Libsignal.TripleRatchet.logMessageKeyAndStore b s dir seed pqSalt n rIdx p st') t (t.length + 1)
        ((t.append (TREvE (.MessageKey s dir seed pqSalt n rIdx p))).append (TRStE b st')) :=
    fun t s dir seed pqSalt n rIdx p st' => by
      unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
      refine TR.Runs.bind (hlog_tr t _) ?_
      have hl : (t.append (TREvE (.MessageKey s dir seed pqSalt n rIdx p))).length = t.length + 1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq _ _
      exact Eq.ndrec (motive := fun k => TR.Runs (DY.PersistentLocalState.storeLocalState b st') _ k _) (hstore_tr _ st') hl
  dsimp only [tr_recv, tr_skip, tr_hs, o]; unfold bobStartTr bobStartSkipTr bobStartPreSkipTr bobFinalSt bobOutOf
  rcases hopk_eq : w.opk with _ | o_opk
  · simp only [Option.map]
    exact TR.Runs.bind (hlen _) (TR.Runs.bind (TR.Runs.logEvent _ _) (TR.Runs.bind (hlog_tr _ _) (TR.Runs.bind (hlog_tr _ _) (TR.Runs.bind (hlog_c _ _) (TR.Runs.bind (hlen _) (TR.Runs.bind (hlog_skip _ _) (TR.Runs.bind (hlog_tr _ _) (hlmk _ _ _ _ _ _ _ _ _))))))))
  · simp only [Option.map]
    have hused' : (!DY.Libsignal.PQXDH.opkUsedB ((tr.append (TR.RndE 32)).append (TR.NetE w.key)) b
        (DY.DiffieHellman.dhPk o_opk)) = true := by simp [w.hused o_opk hopk_eq]
    exact TR.Runs.bind (TR.Runs.requireTracePredicate hused') (TR.Runs.bind (TR.Runs.logEvent _ _) (TR.Runs.bind (hlen _) (TR.Runs.bind (TR.Runs.logEvent _ _) (TR.Runs.bind (hlog_tr _ _) (TR.Runs.bind (hlog_tr _ _) (TR.Runs.bind (hlog_c _ _) (TR.Runs.bind (hlen _) (TR.Runs.bind (hlog_skip _ _) (TR.Runs.bind (hlog_tr _ _) (hlmk _ _ _ _ _ _ _ _ _))))))))))
theorem at?_append_other_eq' {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E'] (tr : ExecTrace) (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E') = none) (j : Nat) : ((tr.append e).at? j : Option E') = (tr.at? j : Option E') := by
  by_cases hj : j < tr.length
  · exact Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.at?_append_of_lt tr e hj
  · by_cases hjeq : j = tr.length
    · subst hjeq
      rw [Symbolic.Swarm.CREF.at?_append_length, hnone, Symbolic.Swarm.CREF.at?_ge_length tr (Nat.le_refl _)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]
theorem at?_append_same_eq' {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) (j : Nat) : ((tr.append e).at? j : Option E) = if j = tr.length then some e else (tr.at? j : Option E) := by
  by_cases hj : j = tr.length
  · subst hj; simp only [↓reduceIte]; exact Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.at?_append_here tr e
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < tr.length
    · exact Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.at?_append_of_lt tr e hlt
    · rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]
theorem at?_other_logSkippedKeys {E : Type} [ExecTraceTypes.Has E]
    (hnone : ∀ ev : DY.Libsignal.TripleRatchet.TREvent, (TraceEntryHas.proj (TraceEntryHas.inj (TREvE ev) : ExecTrace.Entry) : Option E) = none)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (count : Nat) (ck : DY.Bytes) (idx : UInt32) (t : ExecTrace) (j : Nat), ((((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck idx count).run t).2.val).at? j : Option E) = (t.at? j : Option E)
  | 0, _, _, _, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd]
  | count + 1, ck, idx, t, j => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.run_logEvent_bind_snd (Ev := DY.Libsignal.TripleRatchet.TREvent), at?_other_logSkippedKeys hnone s pk rIdx src count _ _ _ j]
    exact at?_append_other_eq' t (TREvE _) (hnone _) j
theorem length_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (count : Nat) (ck : DY.Bytes) (idx : UInt32) (t : ExecTrace), (((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck idx count).run t).2.val).length = t.length + count
  | 0, _, _, _ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.traceful_run_pure_snd, Nat.add_zero]
  | count + 1, ck, idx, t => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.run_logEvent_bind_snd (Ev := DY.Libsignal.TripleRatchet.TREvent), length_logSkippedKeys s pk rIdx src count, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
theorem at?_pqSt_bobStartTr {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) (j : Nat) : ((bobStartTr tr b a w).at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry) := by
  unfold bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf; dsimp only
  rw [at?_append_other_eq' _ (TRStE _ _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl,
      at?_other_logSkippedKeys (fun _ => rfl), at?_append_other_eq' _ (CEvE _) rfl,
      at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TR.EvE _) rfl]
  rcases w.opk with _ | _ <;> dsimp only [Option.map]
  · rw [at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_other_eq' _ (TR.RndE _) rfl]
  · rw [at?_append_other_eq' _ (TR.EvE _) rfl, at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_other_eq' _ (TR.RndE _) rfl]
theorem at?_trSt_bobStartTr {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) (j : Nat) : ((bobStartTr tr b a w).at? j : Option TRStEntry) = if j = (bobStartTr tr b a w).length - 1 then some (TRStE b (bobFinalSt tr a w)) else (tr.at? j : Option TRStEntry) := by
  have hlen : ∀ (t : ExecTrace) (st' : DY.Libsignal.TripleRatchet.TRState),
      (t.append (TRStE b st')).length - 1 = t.length := fun t st' => by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
  unfold bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf; dsimp only
  rw [hlen, at?_append_same_eq', at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl,
      at?_other_logSkippedKeys (fun _ => rfl), at?_append_other_eq' _ (CEvE _) rfl,
      at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TR.EvE _) rfl]
  rcases w.opk with _ | _ <;> dsimp only [Option.map]
  · rw [at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_other_eq' _ (TR.RndE _) rfl]
  · rw [at?_append_other_eq' _ (TR.EvE _) rfl, at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_other_eq' _ (TR.RndE _) rfl]
theorem at?_rnd_bobStartTr {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) (j : Nat) : ((bobStartTr tr b a w).at? j : Option DY.Random.ExecEntryT) = if j = tr.length then some (TR.RndE 32) else (tr.at? j : Option DY.Random.ExecEntryT) := by
  unfold bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf; dsimp only
  rw [at?_append_other_eq' _ (TRStE _ _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl,
      at?_other_logSkippedKeys (fun _ => rfl), at?_append_other_eq' _ (CEvE _) rfl,
      at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TR.EvE _) rfl]
  rcases w.opk with _ | _ <;> dsimp only [Option.map]
  · rw [at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_same_eq']
  · rw [at?_append_other_eq' _ (TR.EvE _) rfl, at?_append_other_eq' _ (TR.NetE _) rfl, at?_append_same_eq']
theorem length_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant) (o : DY.Libsignal.PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) : tr.length < (bobStartPreSkipTr tr b a o msg key).length := by
  unfold bobStartPreSkipTr
  cases o.opk <;> dsimp only <;> (simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega)
theorem length_lt_bobStartTr {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : tr.length < (bobStartTr tr b a w).length := by
  have hpre := length_bobStartPreSkipTr tr b a (bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys) w.msg w.key; have hskip : (bobStartSkipTr tr b a w).length = (bobStartPreSkipTr tr b a (bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys) w.msg w.key).length + (w.msg.counter.toNat - (bobRatchetedChain w.keys w.msg.ratchetKey w.spk).index.toNat) := length_logSkippedKeys _ _ _ _ _ _ _ _; unfold bobStartTr; dsimp only; simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega
theorem storedStates_bobStartTr {r : Records} {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r (bobStartTr tr b a w)) : ls ∈ storedStates r tr ∨ ls = ⟨b, bobFinalSt tr a w⟩ := by
  rw [mem_storedStates_iff] at hls; obtain ⟨j, hge, hlt, hat⟩ := hls; rw [at?_trSt_bobStartTr w j] at hat
  split at hat
  · injection hat with heq; injection heq with hls_eq; exact Or.inr hls_eq.symm
  · have hj_tr : j < tr.length := by
      have h1 := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr j; rwa [hat] at h1
    exact Or.inl (mem_storedStates_iff.mpr ⟨j, hge, hj_tr, hat⟩)
theorem gamma_rng_of_bobVis_forall2 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr tr' : ExecTrace} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {opkPk : Option DY.Bytes} {sh : Nat} {w_wire c_rng pt_acc : HwBytes} (hsh : 3 ≤ sh) (hlt : tr.length < tr'.length) (hrnd : (tr'.at? tr.length : Option DY.Random.ExecEntryT) = some (TR.RndE 32)) (hm : List.Forall₂ (EventMatchesEntry i r S g) [.recv w_wire, .rng c_rng, .accept pt_acc] ((bobVis tr tr' mh opkPk).take sh)) : gamma i S g (randTerm tr.length 32) = c_rng := by
  obtain ⟨k, hk⟩ : ∃ k, tr'.length - tr.length = k + 1 := ⟨tr'.length - tr.length - 1, by omega⟩
  obtain ⟨m, hm_sh⟩ : ∃ m, sh = m + 2 := ⟨sh - 2, by omega⟩
  unfold bobVis newRandoms newIndices at hm; rw [hk, List.range'_succ, List.filterMap_cons, hrnd] at hm; simp only [Option.map_some, List.map_cons, List.cons_append] at hm; rw [hm_sh, List.take_succ_cons, List.take_succ_cons] at hm
  rcases hm with (_ | ⟨_, _ | ⟨hrng, _⟩⟩)
  exact (List.cons.inj hrng.2).1
theorem attackerKnows_ratchetKey_of_parseTrSignalMsg {tr : ExecTrace} {raw : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} (hraw : raw.AttackerKnows tr) (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg) : msg.ratchetKey.AttackerKnows tr := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse; dsimp only [bind, Option.bind] at hparse
  rcases hsp : Concat.split raw (raw.length - DY.Trunc.trunc8Length) with _ | ⟨wire, mac⟩ <;> rw [hsp] at hparse
  · cases hparse
  · dsimp only at hparse
    rcases hfw : DY.TrWire.trWireMsgFields? wire with _ | x <;> rw [hfw] at hparse
    · cases hparse
    · injection hparse with hmsg; subst hmsg
      have hsp_ak := Concat.attacker_knows_split raw (raw.length - DY.Trunc.trunc8Length) tr hraw; rw [hsp] at hsp_ak; have hw := hsp_ak.1; rw [DY.TrWire.trWireMsg_of_fields? hfw] at hw; exact (DY.TrWire.attacker_knows_trWireMsg_args x.version x.senderRatchetKey x.counter x.previousCounter x.ciphertext x.pqRatchet x.encodingVariation tr hw).1
theorem ptAvoidFull_createChain {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {rk pk sk : DY.Bytes} (hb : b.length < 32) (hrk : PtAvoidFull compI0 r S g ms b rk) (hpk : PtAvoidFull compI0 r S g ms b (DY.X25519.x25519Key pk)) (hsk : PtAvoidFull compI0 r S g ms b sk) : PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hprk := ptAvoidFull_hmac hb hrk (ptAvoidFull_dh_compI0 hb hpk hsk); have hinfo : PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := ptAvoidFull_lit _; exact ⟨ptAvoidFull_hkdfBlock1 hb hprk hinfo, ptAvoidFull_hkdfBlock2 hb hprk hinfo⟩
theorem ptAvoidFull_chainKeyAt
    {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hb : b.length < 32) :
    ∀ (steps : Nat) {ck : DY.Bytes}, PtAvoidFull compI0 r S g ms b ck → PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.chainKeyAt ck steps)
  | 0, _, hck => hck
  | steps + 1, _, hck => ptAvoidFull_chainKeyAt hb steps (ptAvoidFull_kdfCk_fst hb hck)
theorem ptAvoidFull_consumeMessageKey_chainKey {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {c c' : DY.Libsignal.TripleRatchet.RecvChain} {counter : UInt32} {seed : DY.Bytes} (hb : b.length < 32) (hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c counter = some (seed, c')) (hck : PtAvoidFull compI0 r S g ms b c.chainKey) : c'.ratchetKey = c.ratchetKey ∧ PtAvoidFull compI0 r S g ms b c'.chainKey := by
  unfold DY.Libsignal.TripleRatchet.consumeMessageKey at hcons; split at hcons
  · cases hcons
  · split at hcons
    · cases hcons
    · split at hcons
      · cases hcons
      · injection hcons with hpair; have h2 := congrArg Prod.snd hpair; dsimp only at h2; subst h2
        exact ⟨rfl, ptAvoidFull_kdfCk_fst hb (ptAvoidFull_chainKeyAt hb _ hck)⟩
theorem ptAvoidFull_bobHandshakeKeys_and_chain {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr : ExecTrace} {p a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr p a kh regA mh pqIdx spqrMsgIdx) (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb32 : b.length < 32) (hmr : ModelRun r ms) (hle : tr ≤ runTraceMoves r ms) (hbase : ∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u) : PtAvoidFull compI0 r S g ms b w.ikB ∧ PtAvoidFull compI0 r S g ms b w.spk ∧ PtAvoidFull compI0 r S g ms b w.ikAPk ∧ PtAvoidFull compI0 r S g ms b w.msg.ratchetKey ∧ PtAvoidFull compI0 r S g ms b w.msg.pqRatchet ∧ PtAvoidFull compI0 r S g ms b w.keys.rk ∧ PtAvoidFull compI0 r S g ms b w.keys.ck ∧ PtAvoidFull compI0 r S g ms b w.keys.pqr ∧ PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.createChain w.keys.rk w.msg.ratchetKey w.spk).1 ∧ PtAvoidFull compI0 r S g ms b (DY.Libsignal.TripleRatchet.createChain w.keys.rk w.msg.ratchetKey w.spk).2 := by
  have hsec := runPQSecretsGood_of_no_setup hcompat hwf hb32 hmr; have hpki := runPKIGood_of_no_setup hcompat hwf hb32 hmr.2.1
  have hbase_tr : ∀ u : DY.Bytes, tr.BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u :=
    fun u hu => hbase u (baseAttackerKnows_le hle hu)
  have hikB : PtAvoidFull compI0 r S g ms b w.ikB := hsec p _ _ (pqxdhStoredAt_mono hle w.hik); have hspk : PtAvoidFull compI0 r S g ms b w.spk := hsec p _ _ (pqxdhStoredAt_mono hle w.hspk)
  have hopkG : ∀ o, w.opk = some o → PtAvoidFull compI0 r S g ms b o := by
    intro o ho; have hst := w.hopk; rw [ho] at hst
    rcases hkh : kh.opk with _ | idx <;> rw [hkh] at hst
    · cases hst
    · exact hsec p _ _ (pqxdhStoredAt_mono hle hst)
  have hikA := hpki a w.ikAPk w.vkA w.honest regA (CompTrace.eventLoggedAt_mono hle ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 ..).mpr w.hreg)); have hekG := ptAvoidFull_of_attackerKnows_le hle hbase_tr (NetMsgAt.attackerKnows w.hek); have hctG := ptAvoidFull_of_attackerKnows_le hle hbase_tr (NetMsgAt.attackerKnows w.hct); have hraw_ak : w.raw.AttackerKnows tr := NetMsgAt.attackerKnows w.hmsg; have hrkG := ptAvoidFull_of_attackerKnows_le hle hbase_tr (attackerKnows_ratchetKey_of_parseTrSignalMsg hraw_ak w.hparse)
  have hpqG := ptAvoidFull_of_attackerKnows_le hle hbase_tr (attackerKnows_pqRatchet_of_parseTrSignalMsg hraw_ak w.hparse)
  have hpqsk : PtAvoidFull compI0 r S g ms b w.pqsk := hsec p _ _ (pqxdhStoredAt_mono hle w.hpq)
  have hkeys : PtAvoidFull compI0 r S g ms b w.keys.rk ∧ PtAvoidFull compI0 r S g ms b w.keys.ck ∧ PtAvoidFull compI0 r S g ms b w.keys.pqr :=
    ptAvoidFull_bobAgreement_keys hb32 hikB hspk hpqsk hopkG hikA hekG hctG w.hagree
  have hcc1 := ptAvoidFull_createChain hb32 hkeys.1 (ptAvoidFull_x25519Key hrkG) hspk; exact ⟨hikB, hspk, hikA, hrkG, hpqG, hkeys.1, hkeys.2.1, hkeys.2.2, hcc1.1, hcc1.2⟩
theorem ptAvoidFull_spqrRecvState_of {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {st m : DY.Bytes} {idx : UInt32} {res : DY.Bytes × DY.Bytes} (hrecv : DY.Spqr.spqrRecv st m idx = some res) (hst : PtAvoidFull i r S g ms b st) (hm : PtAvoidFull i r S g ms b m) : PtAvoidFull i r S g ms b res.1 := by
  unfold DY.Spqr.spqrRecv at hrecv; split at hrecv
  · cases hrecv
  · cases hv : st.view? DY.Spqr.InitState.SubF with
    | none => rw [hv] at hrecv; injection hrecv with hrecv'; subst hrecv'; exact memoOK_spqrRecvState_pack hst hm
    | some x =>
      rw [hv] at hrecv; rcases x with ⟨authKey, params⟩; dsimp only at hrecv
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir => rw [hd] at hrecv; injection hrecv with hrecv'; subst hrecv'; dsimp only; exact memoOK_spqrRecvState_pack hst hm
theorem ptAvoidFull_bobFinalSt {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr : ExecTrace} {p a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk tr p a kh regA mh pqIdx spqrMsgIdx) (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb32 : b.length < 32) (hmr : ModelRun r ms) (hle : tr ≤ runTraceMoves r ms) (hbase : ∀ u : DY.Bytes, (runTraceMoves r ms).BaseAttackerKnows u → PtAvoidFull compI0 r S g ms b u) (hdhs : PtAvoidFull compI0 r S g ms b (randTerm tr.length 32)) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨p, bobFinalSt tr a w⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  obtain ⟨hikB, _, hikA, hrkG, hpqG, hrk0, _, hpqr, hcc1_rk, hcc1_ck⟩ := ptAvoidFull_bobHandshakeKeys_and_chain w hcompat hwf hb32 hmr hle hbase; have hmyIk := ptAvoidFull_encodeEC (ptAvoidFull_dhPk_compI0 hb32 hikB); have hpeerIk := ptAvoidFull_encodeEC hikA; have hsid := ptAvoidFull_concat (ptAvoidFull_x25519Key hrkG) hrk0; have hcc2 := ptAvoidFull_createChain hb32 hcc1_rk (ptAvoidFull_x25519Key hrkG) hdhs
  have hspqr' := ptAvoidFull_spqrRecvState_of w.hspqr (ptAvoidFull_spqrInit hpqr (ptAvoidFull_literalToBytes _)) hpqG; obtain ⟨hc'_rk, hc'_ck⟩ := ptAvoidFull_consumeMessageKey_chainKey hb32 w.hcons hcc1_ck
  have hc'_ratchet : PtAvoidFull compI0 r S g ms b w.c'.ratchetKey := by rw [hc'_rk]; exact hrkG
  have hset : DY.Libsignal.TripleRatchet.setRecvChain [bobRatchetedChain w.keys w.msg.ratchetKey w.spk] w.c' = [w.c'] := by unfold DY.Libsignal.TripleRatchet.setRecvChain; simp [hc'_rk]
  exact ptAvoidFull_serialize_local_tr (ls := (⟨p, bobFinalSt tr a w⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) hmyIk hpeerIk hcc2.1 hdhs hcc2.2 hsid hspqr'
    (by intro d hd; change d ∈ DY.Libsignal.TripleRatchet.setRecvChain [bobRatchetedChain w.keys w.msg.ratchetKey w.spk] w.c' at hd
        rw [hset, List.mem_singleton] at hd; subst hd; exact ⟨hc'_ratchet, hc'_ck⟩)
attribute [local irreducible] DY.Libsignal.Composed.reachability in
theorem bundle_pin_of_reachable {r : Records} {ms_pre : List Move} {b : Participant} {ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes} {honest : Bool} {regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms_pre, m.isSetup = false) (hreach : (runTraceMoves r ms_pre).Reachable DY.Libsignal.Composed.reachability) (hnoleak : ∀ v ∈ runVis r ms_pre, v.kind ≠ .leak) (hnb : CompSetupSecrecy.NoBrk r ms_pre) (hregB : (runTraceMoves r ms_pre).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regB) (hspkSig : NetMsgAt spkSig hb.spkSig (runTraceMoves r ms_pre)) (hpqSig : NetMsgAt pqpkSig hb.pqpkSig (runTraceMoves r ms_pre)) (hv1 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true) (hv2 : DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true) : regB = 6 ∧ b = r.bob ∧ ikB = setupPublic r 2 ∧ vkB = setupPublic r 3 ∧ honest = true ∧ spk = setupPublic r 4 ∧ pqpk = setupPublic r 6 := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach; have hbok := Symbolic.Swarm.COMPOSED.CompInv.bundleOK_of_verify hinv hregB hspkSig.attackerKnows hpqSig.attackerKnows hv1 hv2 (Nat.le_refl _); have hnon := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms_pre hns; have hno := CompSetupSecrecy.not_compromised_or_brokenDH_of_no_leak hNe hns hnoleak hnb
  rcases hbok with ⟨sB, sS, sQ, _, _, hS, rfl, hQ, rfl⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩
  · obtain ⟨rfl, _, hspk_eq⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hS
    obtain ⟨_, _, hpq_eq⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hQ; have hreg_setup := hnon _ regB rfl hregB
    rcases CompPrefixInvBundle.setupTrace_eventLoggedAt_identityRegistered hNe hreg_setup with
      ⟨_, hb_eq, _, _, _⟩ | ⟨rfl, _, hikB_eq, hvkB_eq, hhon_eq⟩
    · exact absurd hb_eq.symm hNe
    · exact ⟨rfl, rfl, hikB_eq, hvkB_eq, hhon_eq, hspk_eq, hpq_eq⟩
  · exact absurd ⟨j, hj⟩ (hno.1 b ikB)
  · exact absurd ⟨j, hj⟩ hno.2.2.2.2.1
attribute [local irreducible] DY.Libsignal.Composed.reachability in
theorem pia_bundle_inv_of_reachable
    {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms_pre : List Move} {tr : ExecTrace} {a b : Participant} {idS regB : Nat}
    {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {bun : HwBytes} {rs : List MachineEvent}
    (hNe : r.alice ≠ r.bob) (htr : tr = runTraceMoves r ms_pre) (hns : ∀ m ∈ ms_pre, m.isSetup = false)
    (hreach : (runTraceMoves r ms_pre).Reachable DY.Libsignal.Composed.reachability)
    (hnoleak : ∀ v ∈ runVis r ms_pre, v.kind ≠ .leak)
    (hnb : CompSetupSecrecy.NoBrk r ms_pre)
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idS regB hb shown).next tr)).isSome = true)
    (hm_vis : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr ((Move.aliceStart a b idS regB hb shown).next tr) hb))
    (hbun4 : bun[4]? ≠ some 1#8) :
    let m := Move.aliceStart a b idS regB hb shown
    regB = 6 ∧ b = r.bob ∧ hb.opk = none ∧ bun[4]? = some 0#8 ∧
    ∃ (ikA : DY.Bytes), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧
      m.next tr = CompPrefixInvAlice.iniAliceStartTr tr a r.bob
        (CompPrefixInvAlice.iniAliceOut tr ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
  obtain ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest, hstA, hregB, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hopk, _, _, hnext⟩ := CompPrefixInvAlice.aliceStart_inv_of_isAliceDone hdone; obtain ⟨hhb_opk, hopk_eq, _, hbun0⟩ := CompPrefixInvAlice.hb_opk_eq_none_of_bun_byte4 hspk hspkSig hpq hpqSig hopk hm_vis hbun4
  obtain ⟨hregB_eq, hb_eq, hikB_eq, _, _, hspk_eq, hpq_eq⟩ := bundle_pin_of_reachable hNe hns hreach hnoleak hnb (htr ▸ hregB) (htr ▸ hspkSig) (htr ▸ hpqSig) hv1 hv2; subst hb_eq; rw [hikB_eq, hspk_eq, hpq_eq, hopk_eq] at hnext; have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach; have hkind : Symbolic.Swarm.COMPOSED.CompInv.IKAt (runTraceMoves r ms_pre) a ikA := hinv.stOK a { kind := .identity, sk := ikA } idS (htr ▸ hstA)
  have hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1 := by
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨_, hik_eq, _⟩ | ⟨_, hik_eq, _⟩ <;> [exact .inl hik_eq; exact .inr hik_eq]
  exact ⟨hregB_eq, rfl, hhb_opk, hbun0, ikA, hid, hnext⟩
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a
