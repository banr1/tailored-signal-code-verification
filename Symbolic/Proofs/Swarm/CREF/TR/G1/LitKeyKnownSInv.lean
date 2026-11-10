/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnown
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import Symbolic.Proofs.Swarm.COMPOSED.CompTrDHS
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.R3FoundSkippedSeedDecTR
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Reachability of `SInvTR`

Proves `depthTR_reachable` and `sinvTR_reachable`, establishing the `SInvTR` invariant for
chain keys and skipped keys on non-honest ratchet keys across all reachable composed traces.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles)
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyComponent KeyDir hmac createChain kdfCk
  chainKeyAt consumeMessageKey findRecvChain setRecvChain recvChainFor x25519LowOrder)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED.CompTermAlgebra

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Root-key depth invariant -/

/-- Root-key depth matches `2 * st.rIdx + 2` on every stored state in the composed model. -/
def DepthTR (tr : ExecTrace) : Prop :=
  ∀ p st i, TRStateStoredAt p st i tr → saltDepth st.rk = 2 * st.rIdx + 2

theorem depthTR_reachable {tr : ExecTrace} (hreach : ReachableTrace tr) : DepthTR tr := by
  intro p st i hst
  obtain ⟨_, _, _, ⟨_, ikm, _, _, hrk, _, _⟩, _⟩ := (compScheduleInv_reachable hreach).stateOK p st i hst
  rw [hrk.saltDepth_eq, saltDepth_pqxdhKdf_rk]
  omega

/-! ## `SInvTR` frame steps and reachability -/

private abbrev RecvEntryOK (tr : ExecTrace) (c : RecvChain) : Prop :=
  ChainOKTR tr c.ratchetKey c.chainKey ∨
    ∃ ikA ikB pqpk opk t e,
      c.chainKey = (DY.Libsignal.PQXDH.aliceAgreement ikA (randTerm t 32) ikB c.ratchetKey pqpk opk e).2.ck

private theorem RecvEntryOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {c : RecvChain}
    (h : RecvEntryOK tr c) : RecvEntryOK tr' c :=
  h.imp (fun hok => hok.mono hle) id

private def PreservesFrom (tr₀ : ExecTrace) (Inv : ExecTrace → Prop) {α : Type}
    (m : Traceful α) : Prop :=
  ∀ tr, tr₀ ≤ tr → Inv tr → Inv (m.run tr).2.val

private theorem PreservesFrom.bind {tr₀ : ExecTrace} {Inv : ExecTrace → Prop} {α β : Type}
    {m : Traceful α} {f : α → Traceful β}
    (hm : PreservesFrom tr₀ Inv m) (hf : ∀ a, PreservesFrom tr₀ Inv (f a)) :
    PreservesFrom tr₀ Inv (m >>= f) := by
  intro tr hle hInv
  rw [run_bind_snd]
  have h1 : Inv (m.run tr).2.val := hm tr hle hInv
  have hle1 : tr₀ ≤ (m.run tr).2.val := Trace.le_trans _ _ _ hle (m.run tr).2.property
  cases (m.run tr).1 with
  | none => exact h1
  | some a => exact hf a (m.run tr).2.val hle1 h1

private theorem PreservesFrom.bind' {tr₀ : ExecTrace} {Inv : ExecTrace → Prop} {α β : Type}
    {m : Traceful α} {f : α → Traceful β}
    (hm : Preserves Inv m) (hf : ∀ a, PreservesFrom tr₀ Inv (f a)) :
    PreservesFrom tr₀ Inv (m >>= f) :=
  PreservesFrom.bind (fun tr _ hInv => hm tr hInv) hf

private theorem lks_sinv_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (h : SInvTR tr) : SInvTR (tr.append e) where
  recv p st i hst c hc :=
    RecvEntryOK.mono (Trace.append_le tr e) (h.recv p st i (trStateStoredAt_append_other hnone_st hst) c hc)
  skip s pk n seed rIdx src j hev := by
    obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j (eventLoggedAt_append_other hnone_tr hev)
    exact ⟨ck, h1, h2.mono (Trace.append_le tr e)⟩
  cks p st i hst := h.cks p st i (trStateStoredAt_append_other hnone_st hst)

private theorem lks_inertOnNonTR : TrDHS.InertOnNonTR SInvTR where
  append_net _ _ h := lks_sinv_append_other rfl rfl h
  append_rnd _ _ h := lks_sinv_append_other rfl rfl h
  append_pqxEv _ _ h := lks_sinv_append_other rfl rfl h
  append_cEv _ _ h := lks_sinv_append_other rfl rfl h
  append_pqxSt _ _ _ h := lks_sinv_append_other rfl rfl h

private theorem lks_sinv_append_tr {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src)
    (h : SInvTR tr) : SInvTR (tr.append (TREvE ev)) where
  recv p st i hst c hc :=
    RecvEntryOK.mono (Trace.append_le tr _)
      (h.recv p st i (trStateStoredAt_append_other (e := TREvE ev) rfl hst) c hc)
  skip s pk n seed rIdx src j hl := by
    rcases eventLoggedAt_append_same hl with ⟨_, hl⟩ | ⟨_, heq⟩
    · obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j hl
      exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
    · exact absurd heq (hev s pk n seed rIdx src)
  cks p st i hst :=
    h.cks p st i (trStateStoredAt_append_other (e := TREvE ev) rfl hst)

private theorem lks_sinv_append_st {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hrecv : ∀ c ∈ st₀.recv, RecvEntryOK tr c) (hcks : CksOKTR st₀)
    (h : SInvTR tr) :
    SInvTR (tr.append (TRStE p₀ st₀)) where
  recv p st i hst c hc := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, _, rfl⟩
    · exact RecvEntryOK.mono (Trace.append_le tr _) (h.recv p st i hst c hc)
    · exact RecvEntryOK.mono (Trace.append_le tr _) (hrecv c hc)
  skip s pk n seed rIdx src j hl := by
    obtain ⟨ck, h1, h2⟩ := h.skip s pk n seed rIdx src j
      (eventLoggedAt_append_other (e := TRStE p₀ st₀) rfl hl)
    exact ⟨ck, h1, h2.mono (Trace.append_le tr _)⟩
  cks p st i hst := by
    rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, _, rfl⟩
    · exact h.cks p st i hst
    · exact hcks

private theorem lks_cksOK_kdfCk {st : TRState} {spqr' : _} (hcks : CksOKTR st) :
    CksOKTR { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := spqr' } := by
  rcases hcks with ⟨i, n, k, hck⟩ | ⟨rk, pk, k, hck, hrk⟩
  · exact .inl ⟨i, n, k + 1, by dsimp only; rw [hck, chainKeyAt_succ_eq_kdfCk_fst]⟩
  · exact .inr ⟨rk, pk, k + 1, by dsimp only; rw [hck, chainKeyAt_succ_eq_kdfCk_fst], hrk⟩

private theorem Preserves.lks_genRand (n : Nat) :
    Preserves SInvTR (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact lks_sinv_append_other rfl rfl h

private theorem Preserves.lks_sendMessage (m : DY.Bytes) :
    Preserves SInvTR (Network.sendMessage m) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  exact lks_sinv_append_other rfl rfl h

private theorem Preserves.lks_logEvent (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src) :
    Preserves SInvTR (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact lks_sinv_append_tr hev h

private theorem PreservesFrom.lks_storeLocalState {tr₀ : ExecTrace} (p : Participant) (st : TRState)
    (hrecv₀ : ∀ c ∈ st.recv, RecvEntryOK tr₀ c) (hcks : CksOKTR st) :
    PreservesFrom tr₀ SInvTR (PersistentLocalState.storeLocalState p st) := by
  intro tr hle hInv
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact lks_sinv_append_st (fun c hc => (hrecv₀ c hc).mono hle) hcks hInv

private theorem PreservesFrom.lks_logMessageKeyAndStore {tr₀ : ExecTrace} (me : Participant)
    (s : SessionInfo) (dir : KeyDir) (mk pqSalt : DY.Bytes) (n : UInt32)
    (rIdx parentStateIdx : Nat) (st : TRState)
    (hrecv₀ : ∀ c ∈ st.recv, RecvEntryOK tr₀ c) (hcks : CksOKTR st) :
    PreservesFrom tr₀ SInvTR
      (logMessageKeyAndStore me s dir mk pqSalt n rIdx parentStateIdx st) := by
  unfold logMessageKeyAndStore
  refine PreservesFrom.bind' (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ => ?_
  exact PreservesFrom.lks_storeLocalState me st hrecv₀ hcks

private theorem lks_run_sendMessage_bind_snd {α : Type} (msg : DY.Bytes) (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val = ((f tr.length).run (tr.append (NetE msg))).2.val := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  rfl

private theorem Preserves.lks_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    Preserves SInvTR (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hInv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv (lks_sinv_append_other rfl rfl hInv)
    fun ikA ikB vkB spk spkSig pqpk pqpkSig opk honest _ _ _ _ _ _ _ _ _ _ _ => ?_
  let o := aliceOut tr ikA ikB spk pqpk opk
  let tr1 := tr.append (RndE 32)
  let tr2 := tr1.append (RndE 32)
  let dhsA := randTerm tr2.length 32
  let tr3 := tr2.append (RndE 32)
  let tr4 := tr3.append (NetE o.ek)
  let tr5 := tr4.append (NetE o.ct)
  let doneIdx := tr5.length
  let evDone := PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys
  let tr6 := tr5.append (PQEvE evDone)
  let tr7 := tr6.append (TREvE (.InitSession a b (DiffieHellman.dhPk dhsA) o.spk))
  let stA : TRState := {
    peer := b, myIk := DY.Libsignal.PQXDH.serializedIk o.ikA,
    peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB,
    rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
    cks := (createChain o.keys.rk o.spk dhsA).2, ns := 0, pn := 0,
    sid := Concat.concat (DiffieHellman.dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := DY.Spqr.spqrInit o.keys.pqr spqrA2B }
  let tr8 := tr7.append (CEvE (.HandshakeSession (stA.sessionInfo a) doneIdx))
  have hInv6 : SInvTR tr6 :=
    lks_sinv_append_other rfl rfl (lks_sinv_append_other rfl rfl (lks_sinv_append_other rfl rfl
      (lks_sinv_append_other rfl rfl (lks_sinv_append_other rfl rfl (lks_sinv_append_other rfl rfl hInv)))))
  have hInv7 : SInvTR tr7 := lks_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) hInv6
  have hInv8 : SInvTR tr8 := lks_sinv_append_other rfl rfl hInv7
  have hrecv : ∀ c ∈ stA.recv, RecvEntryOK tr8 c := by
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact .inr ⟨ikA, ikB, pqpk, opk, tr.length, randTerm (tr.length + 1) 32, rfl⟩
  have hcks : CksOKTR stA := .inr ⟨o.keys.rk, o.spk, 0, rfl, rfl⟩
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    DY.Libsignal.TripleRatchet.traceLength, Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact lks_sinv_append_st hrecv hcks hInv8

private theorem lks_spk_ne_dhs {tr : ExecTrace} (hreach : ReachableTrace tr)
    {b : Participant} {spkSk : DY.Bytes} {idx : Nat}
    (hspk : PQXDHStoredAt tr b { kind := .signedPrekey, sk := spkSk } idx) :
    ∃ t_spk, spkSk = randTerm t_spk 32 ∧
      ∀ p st i, TRStateStoredAt p st i tr → st.dhs ≠ randTerm t_spk 32 := by
  have hInv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hreach
  obtain ⟨t_spk, hspk_eq, _, hr64, _⟩ := hInv.stOK b { kind := .signedPrekey, sk := spkSk } idx hspk
  refine ⟨t_spk, hspk_eq, fun p st i hst hdhs => ?_⟩
  obtain ⟨_, _, _, _, _, hrat, _⟩ := hInv.trStOK p st i hst
  rcases hrat with ⟨t', ht', _, _, _, _, _, _, _, _, _, _, _, _, _, hn3, _, _⟩ | ⟨t', msg, ht', _, hn⟩
  · have ht : t_spk = t' + 2 := (Symbolic.Swarm.COMPOSED.CompInv.rnd_inj (hdhs.symm.trans ht')).1
    have hidx : t' + 3 = t_spk + 1 := by omega
    rw [hidx] at hn3
    exact Symbolic.Swarm.COMPOSED.CompInv.HsClassHelpers.randAt_not_netAt hr64 hn3
  · have ht : t_spk = t' := (Symbolic.Swarm.COMPOSED.CompInv.rnd_inj (hdhs.symm.trans ht')).1
    subst ht
    exact Symbolic.Swarm.COMPOSED.CompInv.HsClassHelpers.randAt_not_netAt hr64 hn

private theorem lks_bind_guardOnTrace_at {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace) (hInv : SInvTR tr)
    (hf : p tr = true → SInvTR ((f ()).run tr).2.val) :
    SInvTR (((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.guardTrace; rw [run_bind_snd, Traceful.run_mk]; dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; exact hInv

private theorem sinvTR_bobStart (hCk : CkKnownCasesTRP)
    (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) (hreach : ReachableTrace tr) (hInv : SInvTR tr) :
    SInvTR ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hInv
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ hspk_st _ _ _ _ _ _ _ => ?_
  obtain ⟨t_spk, hspk_eq, hne_dhs⟩ := lks_spk_ne_dhs hreach hspk_st
  rw [run_bind_snd]
  have htr1 : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr).2.val = tr :=
    Preserves.receiveSignalMsg (Inv := fun t => t = tr) mh.msg tr rfl
  rcases hrm : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr).1 with _ | msg
  · rw [htr1]; exact hInv
  obtain ⟨raw, hraw_ak, hparse⟩ := rdec_receiveSignalMsg_some hrm
  dsimp only
  rw [htr1]
  let st0 : TRState := {
    peer := a, myIk := DY.Libsignal.PQXDH.serializedIk (DiffieHellman.dhPk ikB),
    peerIk := DY.Libsignal.PQXDH.serializedIk ikA,
    rk := keys.rk, dhs := spkSk, cks := keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) keys.rk,
    initiator := false, rIdx := 0, recv := [],
    spqr := DY.Spqr.spqrInit keys.pqr spqrB2A }
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  cases hfind : findRecvChain st0.recv msg.ratchetKey with
  | some c => cases hfind
  | none =>
    dsimp only
    by_cases hlo : x25519LowOrder msg.ratchetKey = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]
      simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]
      exact hInv
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
      have hlo_false : x25519LowOrder msg.ratchetKey = false := by
        cases h : x25519LowOrder msg.ratchetKey <;> simp_all
      have hlo' : (!x25519LowOrder msg.ratchetKey) = true := by simp [hlo_false]
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h,
        run_bind_assoc_snd, run_bind_assoc_snd, run_pure_bind_snd,
        run_bind_assoc_snd, run_genRand_bind_snd, run_pure_bind_snd, run_pure_bind_snd]
      let tr2 := tr.append (RndE 32)
      have hle02 : tr ≤ tr2 := Trace.append_le tr (RndE 32)
      have hInv2 : SInvTR tr2 := lks_sinv_append_other rfl rfl hInv
      let dhs' := randTerm tr.length 32
      let rk1 := (createChain keys.rk msg.ratchetKey spkSk).1
      let ckr := (createChain keys.rk msg.ratchetKey spkSk).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1
      let cks := (createChain rk1 msg.ratchetKey dhs').2
      let c : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := 2 }
      let st : TRState := { st0 with rk := rk2, dhs := dhs', cks := cks, ns := 0, pn := 0, rIdx := 2, recv := [c] }
      rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
      · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hInv2
      dsimp only
      obtain ⟨hseed, hc'k, hc'r⟩ := rdec_consumeMessageKey_eq hcons
      rcases DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hInv2
      dsimp only
      rw [lks_run_sendMessage_bind_snd]
      let tr3 := tr2.append (NetE key)
      have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 (NetE key)
      have hInv3 : SInvTR tr3 := lks_sinv_append_other rfl rfl hInv2
      refine bind_receiveMessage_at pqIdx tr3 hInv3 fun pqSalt _ _ => ?_
      rw [run_bind_snd, verifyMacAndDecrypt_trace]
      rcases hvm : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run tr3).1 with _ | m
      · exact hInv3
      have hmac := rdec_verifyMacAndDecrypt_some hvm
      have hgood : GoodTR tr msg.ratchetKey ckr := by
        intro hj
        have hpk_ak : msg.ratchetKey.AttackerKnows tr := rdec_ratchetKey_known_of_parse hraw_ak hparse
        have hseed' : seed = (kdfCk (chainKeyAt (createChain keys.rk msg.ratchetKey (randTerm t_spk 32)).2
            (msg.counter.toNat - 0))).2 := by
          dsimp [c, ckr] at hseed
          rw [← hspk_eq]
          exact hseed
        rw [hseed'] at hmac
        have hseed_ak := seed_known_of_forgedMac_tr hreach hraw_ak hparse hmac hj
        have hbase_ak := rdec_freshSeed_of_ne_dhs hCk hreach hInv hne_dhs hj _ hseed_ak
        dsimp [ckr]
        rw [hspk_eq]
        exact ⟨hpk_ak, hbase_ak⟩
      have hc0 : ChainOKTR tr msg.ratchetKey c.chainKey :=
        ⟨ckr, 0, rfl, hgood, .inr (.inl ⟨keys.rk, t_spk, by dsimp [ckr]; rw [hspk_eq]⟩)⟩
      have hc'0 : ChainOKTR tr c'.ratchetKey c'.chainKey := by
        rw [hc'k, hc'r]
        exact rdec_chainOK_kdfCk_fst (rdec_chainOK_chainKeyAt hc0 _)
      dsimp only
      have h_commit_opk : ∀ (t4 : ExecTrace), tr2 ≤ t4 → SInvTR t4 →
          SInvTR ((do
            let doneIdx ← traceLength
            ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
              (DiffieHellman.dhPk spkSk) (DY.PQKem.kemPk pqsk) (opkSk.map DiffieHellman.dhPk)
              ek ct keys)
            if true = true then
              ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
              ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← traceLength) + skipped + 2
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t4).2.val := by
        intro t4 hle24 hInv4
        let doneIdx := t4.length
        let evDone := PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
          (DiffieHellman.dhPk spkSk) (DY.PQKem.kemPk pqsk) (opkSk.map DiffieHellman.dhPk)
          ek ct keys
        let t5 := t4.append (PQEvE evDone)
        let t6 := t5.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
        let t7 := t6.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
        let t8 := t7.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
        have hInv5 : SInvTR t5 := lks_sinv_append_other rfl rfl hInv4
        have hInv6 : SInvTR t6 := lks_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) hInv5
        have hInv7 : SInvTR t7 := lks_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) hInv6
        have hInv8 : SInvTR t8 := lks_sinv_append_other rfl rfl hInv7
        have hle48 : t4 ≤ t8 :=
          Trace.le_trans _ _ _ (Trace.append_le t4 _)
            (Trace.le_trans _ _ _ (Trace.append_le t5 _)
              (Trace.le_trans _ _ _ (Trace.append_le t6 _) (Trace.append_le t7 _)))
        have hle08 : tr ≤ t8 := Trace.le_trans _ _ _ hle02 (Trace.le_trans _ _ _ hle24 hle48)
        have hc8 : ChainOKTR t8 msg.ratchetKey c.chainKey := hc0.mono hle08
        have hc'8 : ChainOKTR t8 c'.ratchetKey c'.chainKey := hc'0.mono hle08
        let skipped := msg.counter.toNat - c.index.toNat
        let childIdx := t8.length + skipped + 2
        have h_pre_eq : ((do
            let doneIdx ← traceLength
            ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
              (DiffieHellman.dhPk spkSk) (DY.PQKem.kemPk pqsk) (opkSk.map DiffieHellman.dhPk)
              ek ct keys)
            if true = true then
              ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
              ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← traceLength) + skipped + 2
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t4).2.val =
          ((do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t8).2.val := by
          simp only [↓reduceIte, DY.Libsignal.TripleRatchet.traceLength,
            Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
            Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
          rfl
        rw [h_pre_eq, run_bind_snd, rdec_logSkippedKeys_fst]
        dsimp only
        let t9 := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped).run t8).2.val
        have hle89 : t8 ≤ t9 := rdec_logSkippedKeys_le _ _ _ _ _ _ _ t8
        have hInv9 : SInvTR t9 := rdec_sinv_logSkippedKeys _ _ _ _ _ _ _ t8 hInv8 hc8
        let t10 := t9.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
        have hle910 : t9 ≤ t10 := Trace.append_le t9 _
        have hInv10 : SInvTR t10 := lks_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) hInv9
        let evMK := TREvent.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        let t11 := t10.append (TREvE evMK)
        have hle1011 : t10 ≤ t11 := Trace.append_le t10 _
        have hInv11 : SInvTR t11 := lks_sinv_append_tr (fun _ _ _ _ _ _ h => nomatch h) hInv10
        have hle811 : t8 ≤ t11 := Trace.le_trans _ _ _ hle89 (Trace.le_trans _ _ _ hle910 hle1011)
        have hcks : CksOKTR { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
          .inr ⟨rk1, msg.ratchetKey, 0, rfl, rfl⟩
        simp only [DY.Libsignal.TripleRatchet.logMessageKeyAndStore,
          Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1,
          Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
        refine lks_sinv_append_st (p₀ := b)
          (st₀ := { st with recv := setRecvChain st.recv c', spqr := spqr' })
          (fun x hx => ?_) hcks hInv11
        rcases rdec_mem_setRecvChain hx with rfl | hx
        · exact .inl (hc'8.mono hle811)
        · rw [List.mem_singleton] at hx
          subst hx
          exact .inl (hc8.mono hle811)
      rcases opkSk with _ | o
      · exact h_commit_opk tr3 hle23 hInv3
      · dsimp only [Option.map]
        refine lks_bind_guardOnTrace_at _ tr3 hInv3 fun _ => ?_
        have h_opk_step : ∀ (f : PUnit → Traceful Nat),
            ((ProtocolEvent.logEvent (PQXDHEvent.OPKUsed b (DiffieHellman.dhPk o)) >>= f).run tr3).2.val =
              ((f ()).run (tr3.append (PQEvE (.OPKUsed b (DiffieHellman.dhPk o))))).2.val := by
          intro f
          simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
            Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
          rfl
        rw [h_opk_step]
        exact h_commit_opk (tr3.append (PQEvE (.OPKUsed b (DiffieHellman.dhPk o))))
          (Trace.le_trans _ _ _ hle23 (Trace.append_le tr3 _)) (lks_sinv_append_other rfl rfl hInv3)

private theorem Preserves.lks_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves SInvTR (messageEncrypt me stH coinsLen pqIdx) := by
  unfold messageEncrypt
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hrecv₀ : ∀ c ∈ st.recv, RecvEntryOK tr₀ c := hInv₀.recv me st stH hst₀
  have hcks₀ : CksOKTR st := hInv₀.cks me st stH hst₀
  refine (PreservesFrom.bind' (Preserves.guardP _) fun _ => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  refine PreservesFrom.bind' (Preserves.lks_genRand 32) fun _ => ?_
  refine PreservesFrom.bind' (Preserves.lks_genRand coinsLen) fun _ => ?_
  refine PreservesFrom.bind' (Preserves.lks_sendMessage _) fun _ => ?_
  refine PreservesFrom.bind' (Preserves.receiveMessage pqIdx) fun _ => ?_
  refine PreservesFrom.bind' (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ => ?_
  exact PreservesFrom.bind
    (PreservesFrom.lks_logMessageKeyAndStore me _ .sender _ _ _ _ _ _ hrecv₀ (lks_cksOK_kdfCk hcks₀))
    fun _ tr _ hInv => Preserves.lks_sendMessage _ tr hInv

private theorem Preserves.lks_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves SInvTR (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hrecv₀ : ∀ c ∈ st.recv, RecvEntryOK tr₀ c := hInv₀.recv me st stH hst₀
  have hcks₀ : CksOKTR st := hInv₀.cks me st stH hst₀
  refine (PreservesFrom.bind' (Preserves.receiveSignalMsg _) fun msg => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  refine PreservesFrom.bind' (Preserves.getEntry evH) fun e => ?_
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    refine PreservesFrom.bind' (Preserves.guardP _) fun _ => ?_
    refine PreservesFrom.bind' (Preserves.guardTrace _) fun _ => ?_
    split
    · next spqr' key _ =>
      refine PreservesFrom.bind' (Preserves.lks_sendMessage key) fun _ => ?_
      refine PreservesFrom.bind' (Preserves.receiveMessage pqIdx) fun _ => ?_
      refine PreservesFrom.bind' (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ => ?_
      refine PreservesFrom.bind' (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ => ?_
      refine PreservesFrom.bind' (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ => ?_
      exact PreservesFrom.lks_logMessageKeyAndStore me s .receiver seed _ n rIdx stH { st with spqr := spqr' } hrecv₀ hcks₀
    · exact fun _ _ => Preserves.failure _
  | _ => exact fun _ _ => Preserves.failure _

private theorem Preserves.lks_exposeKey (me : Participant) (stH : Nat) (k : KeyComponent) :
    Preserves SInvTR (exposeKey me stH k) := by
  unfold exposeKey
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ _ => ?_
  cases k with
  | rk =>
    exact (Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
      Preserves.lks_sendMessage _) tr₀ hInv₀
  | dhs =>
    exact (Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
      Preserves.lks_sendMessage _) tr₀ hInv₀
  | cks =>
    exact (Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
      Preserves.lks_sendMessage _) tr₀ hInv₀
  | ckr pk =>
    dsimp only; cases findRecvChain st.recv pk with
    | none => simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hInv₀
    | some _ =>
      exact (Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
        Preserves.lks_sendMessage _) tr₀ hInv₀

private theorem Preserves.lks_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves SInvTR (exposeSpqr me stH) := by
  unfold exposeSpqr
  refine Preserves.bind_getLocalState_tr me stH fun _ tr₀ hInv₀ _ => ?_
  exact (Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
    Preserves.lks_sendMessage _) tr₀ hInv₀

private theorem Preserves.lks_exposeSkipped (evH : Nat) :
    Preserves SInvTR (exposeSkipped evH) := by
  unfold exposeSkipped
  refine Preserves.bind (Preserves.getEntry evH) fun e tr₀ hInv₀ => ?_
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored _ _ _ _ _ _ =>
    dsimp only
    refine (Preserves.bind (Preserves.guardTrace _) fun _ => ?_) tr₀ hInv₀
    exact Preserves.bind (Preserves.lks_logEvent _ (fun _ _ _ _ _ _ h => by cases h)) fun _ =>
      Preserves.lks_sendMessage _
  | _ => simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; exact hInv₀

/-- Every reachable composed trace satisfies `SInvTR`. -/
theorem sinvTR_reachable (hCk : CkKnownCasesTRP) {tr : ExecTrace} (hreach : ReachableTrace tr) :
    SInvTR tr := by
  induction hreach with
  | Base =>
    refine ⟨fun _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ h => ?_⟩ <;>
    · simp -failIfUnchanged only [TRStateStoredAt,
        Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1,
        DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte] at h
      cases h
  | Step input hPre ht ih =>
    rcases input with ⟨⟨i, hi⟩, inp⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · exact Preserves.lks_sendMessage inp _ ih
    · exact lks_inertOnNonTR.preserves_registerIdentity inp _ ih
    · rcases inp with ⟨p, skIdx⟩; exact lks_inertOnNonTR.preserves_registerCorruptIdentity p skIdx _ ih
    · rcases inp with ⟨b, idStateIdx⟩; exact lks_inertOnNonTR.preserves_genSignedPrekey b idStateIdx _ ih
    · rcases inp with ⟨b, idStateIdx⟩; exact lks_inertOnNonTR.preserves_genPQPrekey b idStateIdx _ ih
    · exact lks_inertOnNonTR.preserves_genOneTimePrekey inp _ ih
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact Preserves.lks_aliceStart a b idStateIdx regIdxB bh _ ih
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact sinvTR_bobStart hCk b a kh regIdxA mh pqIdx spqrMsgIdx _ ht ih
    · rcases inp with ⟨me, stH, coinsLen, pqIdx⟩
      exact Preserves.lks_messageEncrypt me stH coinsLen pqIdx _ ih
    · rcases inp with ⟨me, stH⟩; exact lks_inertOnNonTR.preserves_messageEncryptAbort me stH _ ih
    · rcases inp with ⟨me, stH, msgH, pqIdx, spqrMsgIdx⟩
      exact sinvTR_messageDecrypt hCk me stH msgH pqIdx spqrMsgIdx _ ht ih (depthTR_reachable ht)
    · rcases inp with ⟨me, stH, msgH, evH, pqIdx, spqrMsgIdx⟩
      exact Preserves.lks_messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx _ ih
    · rcases inp with ⟨me, stH, k⟩; exact Preserves.lks_exposeKey me stH k _ ih
    · rcases inp with ⟨me, stH⟩; exact Preserves.lks_exposeSpqr me stH _ ih
    · exact Preserves.lks_exposeSkipped inp _ ih
    · rcases inp with ⟨p, stateIdx⟩; exact lks_inertOnNonTR.preserves_compromiseIK p stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact lks_inertOnNonTR.preserves_compromiseSPK b stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact lks_inertOnNonTR.preserves_compromisePQSPK b stateIdx _ ih
    · rcases inp with ⟨b, stateIdx⟩; exact lks_inertOnNonTR.preserves_compromiseOPK b stateIdx _ ih
    · exact lks_inertOnNonTR.preserves_breakDH _ ih
    · exact lks_inertOnNonTR.preserves_breakKEM _ ih
    · exact lks_inertOnNonTR.preserves_invertDH inp _ ih
    · exact lks_inertOnNonTR.preserves_invertKEM inp _ ih
    · omega

end Symbolic.Swarm.CREF.TR.G1
