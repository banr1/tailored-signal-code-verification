/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedNotJunkFixPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSkelLocal
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRkCore
public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkKDefs
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedProvBPureA
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkBobGuard
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkRootTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSep
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkInvCons
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Skipped-Key Ratchet-Index Invariant and Fresh-Alias Exclusion

Proves reachability of `spb_ProvRIdx2Inv`, spine membership and skeleton uniqueness for
`SkippedKeyStored` seeds, and `skippedFreshAliasExclB_of_reach`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain recvChainFor
  consumeMessageKey chainKeyAt kdfCk createChain)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry logSkippedKeysTr decTailTr run_bind_fst run_bind_snd at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add logSkippedKeysTr_length at?_eq_none_of_le
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.COMPOSED.CompTrace hiding run_bind_fst run_bind_snd NetE
open Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS (InertOnNonTR)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.TripleRatchet (spqrB2A logSkippedKeys logMessageKeyAndStore verifyMacAndDecrypt)
open Symbolic.Swarm.CREF.TR.RecvDec (StEntry)
open Symbolic.Swarm.CREF.TR.RecvDecStep (prov_bind_getLocalState_tr prov_bind_ensureReceiverChain_tr
  mem_recv_of_recvChainFor_false)

section ProvRIdx2Proof

private theorem provRIdx2Inv_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves spb_ProvRIdx2Inv (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  have hlen_bind : ∀ {α : Type} (f : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= f).run t).2.val = ((f t.length).run t).2.val := by
    intro _ f t
    have hl : (DY.Libsignal.TripleRatchet.traceLength : Traceful Nat).run t =
        (some t.length, ⟨t, Trace.le_refl t⟩) := by
      unfold DY.Libsignal.TripleRatchet.traceLength; erw [DY.Traceful.run_mk]
    rw [DY.Traceful.run_bind, hl]
  have hlog_pq_bind : ∀ {α : Type} (ev : DY.Libsignal.PQXDH.PQXDHEvent) (f : Unit → Traceful α) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev >>= f).run t).2.val = ((f ()).run (t.append (PQEvE ev))).2.val := by
    intro _ ev f t
    have he : (ProtocolEvent.logEvent ev : Traceful Unit).run t =
        (some (), ⟨t.append (PQEvE ev), Trace.append_le t _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    rw [DY.Traceful.run_bind, he]
  have hlog_tr_bind : ∀ {α : Type} (ev : TREvent) (f : Unit → Traceful α) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev >>= f).run t).2.val = ((f ()).run (t.append (TREvE ev))).2.val := by
    intro _ ev f t
    have he : (ProtocolEvent.logEvent ev : Traceful Unit).run t =
        (some (), ⟨t.append (TREvE ev), Trace.append_le t _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    rw [DY.Traceful.run_bind, he]
  have hlog_c_bind : ∀ {α : Type} (ev : DY.Libsignal.Composed.ComposedEvent) (f : Unit → Traceful α) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev >>= f).run t).2.val = ((f ()).run (t.append (CEvE ev))).2.val := by
    intro _ ev f t
    have he : (ProtocolEvent.logEvent ev : Traceful Unit).run t =
        (some (), ⟨t.append (CEvE ev), Trace.append_le t _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    rw [DY.Traceful.run_bind, he]
  refine InertOnNonTR.bind_bobHandshake b a kh regIdxA mh.ek mh.ct tr₀ hInv₀ fun o => ?_
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, spb_receiveSignalMsg_trace_rIdx2]
  rcases hrcv : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr₀).1 with _ | msg; · exact hInv₀
  dsimp only
  let st0 : TRState := {
    peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
    dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit o.keys.pqr spqrB2A }
  refine prov_bind_ensureReceiverChain_tr (Inv := spb_ProvRIdx2Inv) st0 msg.ratchetKey tr₀ hInv₀
    (fun c hc_find => nomatch mem_recv_of_recvChainFor_false hc_find) (fun _ _ => ?_)
  dsimp only
  let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₀.length 32
  let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st0.rk msg.ratchetKey st0.dhs).2, index := 0, rIdx := st0.rIdx + 2 }
  let st : TRState := { st0 with
    rk := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
    cks := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).2, ns := 0,
    pn := if st0.ns = 0 then 0 else st0.ns - 1, rIdx := st0.rIdx + 2,
    recv := (st0.recv ++ [c1]).drop ((st0.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
  let tr₁ := tr₀.append (Random.ExecEntryT.mk 32)
  have hInv₁ : spb_ProvRIdx2Inv tr₁ := spb_provRIdx2Inv_append_other rfl rfl hInv₀
  rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; exact Preserves.failure tr₁ hInv₁
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; exact Preserves.failure tr₁ hInv₁
  dsimp only; let tr₂ := tr₁.append (Network.ExecEntryT.mk key)
  have hInv₂ : spb_ProvRIdx2Inv tr₂ := spb_provRIdx2Inv_append_other rfl rfl hInv₁
  rw [spb_run_sendMessage_bind_snd_rIdx2, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, spb_receiveMessage_trace_rIdx2]
  rcases ((Network.receiveMessage pqIdx).run tr₂).1 with _ | pqSalt; · exact hInv₂
  dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, verifyMacAndDecrypt_trace]
  rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₂
  have huniq_st : spb_RecvKeysUnique st.recv := spb_recvKeysUnique_singleton c1
  have hTail : ∀ (t : ExecTrace) (opkOpt : Option DY.Bytes), spb_ProvRIdx2Inv t →
      spb_ProvRIdx2Inv ((do
        let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
        ProtocolEvent.logEvent (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk opkOpt o.ek o.ct o.keys)
        if true = true then
          ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs))
          ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
        ProtocolEvent.logEvent (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
        let skipped := msg.counter.toNat - c1.index.toNat
        let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
        DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c1.rIdx childIdx c1.chainKey c1.index skipped
        ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
        DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
          msg.counter c1.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t).2.val := by
    intro t4 opkOpt hInv4
    let t5 := t4.append (PQEvE (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk opkOpt o.ek o.ct o.keys))
    let t6 := t5.append (TREvE (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs)))
    let t7 := t6.append (TREvE (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
    let t8 := t7.append (CEvE (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (st.sessionInfo b) t4.length))
    have hInv8 : spb_ProvRIdx2Inv t8 :=
      spb_provRIdx2Inv_append_other rfl rfl (spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun)
        (spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun) (spb_provRIdx2Inv_append_other rfl rfl hInv4)))
    let childIdx := t8.length + (msg.counter.toNat - c1.index.toNat) + 2
    rw [hlen_bind, hlog_pq_bind]
    simp only [↓reduceIte]
    rw [hlog_tr_bind, hlog_tr_bind, hlog_c_bind, hlen_bind]
    change spb_ProvRIdx2Inv ((do
      let _ ← logSkippedKeys (st.sessionInfo b) msg.ratchetKey c1.rIdx childIdx c1.chainKey c1.index (msg.counter.toNat - c1.index.toNat)
      let _ ← DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter
        c1.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } : Traceful Nat).run t8).2.val
    rw [spb_decTailTr_run_rIdx2]
    exact spb_provRIdx2Inv_decTailTr_bob hInv8 huniq_st rfl
  cases o.opk with
  | none => exact hTail tr₂ none hInv₂
  | some opkPk =>
    dsimp only [Option.map]
    have hguard : ((DY.Libsignal.PQXDH.guardTrace fun tr => !DY.Libsignal.PQXDH.opkUsedB tr b opkPk).run tr₂).2.val = tr₂ :=
      Preserves.requireTracePredicate (Inv := fun t => t = tr₂) _ tr₂ rfl
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
    rcases ((DY.Libsignal.PQXDH.guardTrace fun tr => !DY.Libsignal.PQXDH.opkUsedB tr b opkPk).run tr₂).1 with _ | _
    · rw [hguard]; exact hInv₂
    · dsimp only; rw [hguard, hlog_pq_bind]
      exact hTail (tr₂.append (PQEvE (.OPKUsed b opkPk))) (some opkPk) (spb_provRIdx2Inv_append_other rfl rfl hInv₂)

private theorem provRIdx2Inv_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves spb_ProvRIdx2Inv (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  have hlog_tr_bind : ∀ {α : Type} (ev : TREvent) (f : Unit → Traceful α) (t : ExecTrace),
      ((ProtocolEvent.logEvent ev >>= f).run t).2.val = ((f ()).run (t.append (TREvE ev))).2.val := by
    intro _ ev f t
    have he : (ProtocolEvent.logEvent ev : Traceful Unit).run t =
        (some (), ⟨t.append (TREvE ev), Trace.append_le t _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
        Symbolic.DYBridge.DY.appendEntry_eq_1]
      erw [DY.Traceful.run_mk]; dsimp only; erw [DY.Traceful.run_pure]
    rw [DY.Traceful.run_bind, he]
  refine prov_bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  have huniq₀ : spb_RecvKeysUnique st₀.recv := hInv₀.1 me st₀ stH hst₀
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, spb_receiveSignalMsg_trace_rIdx2]
  rcases hrcv : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH).run tr₀).1 with _ | msg; · exact hInv₀
  dsimp only
  refine prov_bind_ensureReceiverChain_tr (Inv := spb_ProvRIdx2Inv) st₀ msg.ratchetKey tr₀ hInv₀
    (fun c hc_find => ?_) (fun hfind hlow => ?_)
  · dsimp only; rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; exact Preserves.failure tr₀ hInv₀
    dsimp only; rcases Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; exact Preserves.failure tr₀ hInv₀
    dsimp only; let tr₁ := tr₀.append (Network.ExecEntryT.mk key)
    have hInv₁ : spb_ProvRIdx2Inv tr₁ := spb_provRIdx2Inv_append_other rfl rfl hInv₀
    rw [spb_run_sendMessage_bind_snd_rIdx2, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, spb_receiveMessage_trace_rIdx2]
    rcases ((Network.receiveMessage pqIdx).run tr₁).1 with _ | pqSalt; · exact hInv₁
    dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, verifyMacAndDecrypt_trace]
    rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₁
    change spb_ProvRIdx2Inv ((do
      let _ ← logSkippedKeys (st₀.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index (msg.counter.toNat - c.index.toNat)
      let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st₀.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st₀.sessionInfo me) .receiver seed pqSalt msg.counter
        c.rIdx stH { st₀ with recv := setRecvChain st₀.recv c', spqr := spqr' } : Traceful Nat).run tr₁).2.val
    rw [spb_decTailTr_run_rIdx2]
    exact spb_provRIdx2Inv_decTailTr hInv₁ (trStateStoredAt_mono (Trace.append_le tr₀ _) hst₀) huniq₀ hc_find hcons
  · dsimp only; let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₀.length 32
    let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2, index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := { st₀ with
      rk := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
      cks := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).2, ns := 0,
      pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
      recv := (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
    let tr₁ := tr₀.append (Random.ExecEntryT.mk 32)
    have hInv₁ : spb_ProvRIdx2Inv tr₁ := spb_provRIdx2Inv_append_other rfl rfl hInv₀
    rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; exact Preserves.failure tr₁ hInv₁
    dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; exact Preserves.failure tr₁ hInv₁
    dsimp only; let tr₂ := tr₁.append (Network.ExecEntryT.mk key)
    have hInv₂ : spb_ProvRIdx2Inv tr₂ := spb_provRIdx2Inv_append_other rfl rfl hInv₁
    rw [spb_run_sendMessage_bind_snd_rIdx2, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, spb_receiveMessage_trace_rIdx2]
    rcases ((Network.receiveMessage pqIdx).run tr₂).1 with _ | pqSalt; · exact hInv₂
    dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, verifyMacAndDecrypt_trace]
    rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₂
    let tr₃ := tr₂.append (TREvE (TREvent.DHRatchet me st.peer msg.ratchetKey (dhPk st.dhs)))
    let tr₄ := tr₃.append (TREvE (TREvent.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2)))
    have hInv₄ : spb_ProvRIdx2Inv tr₄ := spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun) (spb_provRIdx2Inv_append_tr (by intro _ _ _ _ _ _; nofun) hInv₂)
    have hle04 : tr₀ ≤ tr₄ :=
      Trace.le_trans _ _ _ (Trace.append_le tr₀ _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
    have huniq_st : spb_RecvKeysUnique st.recv :=
      spb_recvKeysUnique_drop _ (spb_recvKeysUnique_append_singleton huniq₀ hfind)
    simp only [↓reduceIte]
    rw [hlog_tr_bind, hlog_tr_bind]
    change spb_ProvRIdx2Inv ((do
      let _ ← logSkippedKeys (st.sessionInfo me) msg.ratchetKey c1.rIdx stH c1.chainKey c1.index (msg.counter.toNat - c1.index.toNat)
      let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter
        c1.rIdx stH { st with recv := setRecvChain st.recv c', spqr := spqr' } : Traceful Nat).run tr₄).2.val
    rw [spb_decTailTr_run_rIdx2]
    have hrc_c1 : recvChainFor st₀.toDRState msg.ratchetKey = some (c1, true) := by
      unfold recvChainFor; rw [hfind]; simp [hlow, c1]
    exact spb_provRIdx2Inv_decTailTr hInv₄ (trStateStoredAt_mono hle04 hst₀) huniq_st hrc_c1 hcons

private theorem provRIdx2Inv_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves spb_ProvRIdx2Inv (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  have hsend : ∀ m : DY.Bytes, Preserves spb_ProvRIdx2Inv (DY.Network.sendMessage m) := by
    intro _ _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  have hrnd : ∀ n : Nat, Preserves spb_ProvRIdx2Inv (DY.Random.genRand n) := by
    intro _ _ h
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  have hlog_tr_other : ∀ (ev : TREvent),
      (∀ s pk n seed rIdx src, ev ≠ .SkippedKeyStored s pk n seed rIdx src) →
      Preserves spb_ProvRIdx2Inv (DY.ProtocolEvent.logEvent ev) := by
    intro ev hne _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_tr hne h
  refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have huniq := hInv₀.1 me st stH hst₀
  refine (?_ : Preserves spb_ProvRIdx2Inv _) tr₀ hInv₀
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (hrnd 32) fun _ =>
    Preserves.bind (hrnd coinsLen) fun _ =>
    Preserves.bind (hsend _) fun _ =>
    Preserves.bind (Preserves.receiveMessage pqIdx) fun _ =>
    Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ =>
    Preserves.bind (spb_provRIdx2Inv_logMessageKeyAndStore me _ .sender _ _ _ _ _ _ rfl huniq) fun _ =>
      hsend _

private theorem provRIdx2Inv_reachable {tr : ExecTrace} (hreach : tr.Reachable reachability) : spb_ProvRIdx2Inv tr := by
  have hsend : ∀ m : DY.Bytes, Preserves spb_ProvRIdx2Inv (DY.Network.sendMessage m) := by
    intro _ _ h
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact spb_provRIdx2Inv_append_other rfl rfl h
  have hlog_tr_other : ∀ (ev : TREvent),
      (∀ s pk n seed rIdx src, ev ≠ .SkippedKeyStored s pk n seed rIdx src) →
      Preserves spb_ProvRIdx2Inv (DY.ProtocolEvent.logEvent ev) := by
    intro ev hne _ h
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, DY.Traceful.run_bind,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk, DY.Traceful.run_pure]
    exact spb_provRIdx2Inv_append_tr hne h
  exact spb_provRIdx2Inv_inertOnNonTR.reachable_induction spb_provRIdx2Inv_nil
    spb_provRIdx2Inv_aliceStart provRIdx2Inv_bobStart
    provRIdx2Inv_messageEncrypt
    provRIdx2Inv_messageDecrypt
    (fun me stH msgH evH pqIdx spqrMsgIdx => by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
      refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
      have huniq := hInv₀.1 me st stH hst₀
      refine (?_ : Preserves spb_ProvRIdx2Inv _) tr₀ hInv₀
      refine Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg => Preserves.bind (Preserves.getEntry evH) fun e => ?_
      rcases e with ⟨ev⟩; cases ev with
      | SkippedKeyStored s pk n seed rIdx _ =>
        dsimp only; refine Preserves.bind (Preserves.guardP _) fun _ => Preserves.bind (Preserves.guardTrace _) fun _ => ?_
        split
        · next spqr' key _ =>
          exact Preserves.bind (hsend key) fun _ =>
            Preserves.bind (Preserves.receiveMessage pqIdx) fun _ => Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
            Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ =>
            Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ =>
            spb_provRIdx2Inv_logMessageKeyAndStore me s .receiver seed _ n rIdx stH { st with spqr := spqr' } rfl huniq
        · exact Preserves.failure
      | _ => exact Preserves.failure)
    (fun me stH k => by
      unfold DY.Libsignal.TripleRatchet.exposeKey
      refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ _ => ?_
      cases k with
      | rk | dhs | cks =>
        exact (Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ => hsend _) tr₀ hInv₀
      | ckr pk =>
        dsimp only
        split
        · exact (Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ => hsend _) tr₀ hInv₀
        · exact Preserves.failure tr₀ hInv₀)
    (fun me stH => prov_bind_getLocalState_tr me stH fun _ tr₀ hInv₀ _ =>
      (Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ => hsend _) tr₀ hInv₀)
    (fun evH => Preserves.bind (Preserves.getEntry (E := TREntry) evH) fun ⟨ev⟩ tr₀ hInv₀ => by
      cases ev with
      | SkippedKeyStored _ _ _ _ _ _ =>
        dsimp only; refine (Preserves.bind (Preserves.guardTrace _) fun _ => ?_) tr₀ hInv₀
        exact Preserves.bind (hlog_tr_other _ (by intro _ _ _ _ _ _; nofun)) fun _ => hsend _
      | _ => dsimp only; exact Preserves.failure tr₀ hInv₀)
    hreach

end ProvRIdx2Proof

theorem rIdx_eq_two_of_provB
    {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {s : SessionInfo} {pk seed : DY.Bytes} {n : UInt32} {rIdx srcIdx skIdx : Nat}
    {p_src : Participant} {st_src : TRState} {c₀ : RecvChain}
    (hlog : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx srcIdx) skIdx)
    (hst_src : TR.G1.TRStateStoredAt p_src st_src srcIdx tr)
    (hc₀_mem : c₀ ∈ st_src.recv)
    (hrk₀ : c₀.ratchetKey = pk)
    (hlt : n < c₀.index) :
    rIdx = 2 := by
  have hInv := provRIdx2Inv_reachable hreach
  rcases hInv.2 s pk n seed rIdx srcIdx skIdx hlog with
    ⟨p₀, st₀, c, fresh, seed', c₀', hst₀, hrc, hcons⟩ | hrIdx2
  · have hst_eq : st₀ = st_src := by
      unfold TR.G1.TRStateStoredAt at hst₀ hst_src
      rw [hst_src] at hst₀
      injection hst₀ with hst₀
      cases hst₀; rfl
    subst hst_eq
    have huniq := hInv.1 p_src st₀ srcIdx hst_src
    unfold recvChainFor at hrc
    cases hfind : findRecvChain st₀.recv pk with
    | none =>
      have hnone : st₀.recv.find? (fun x => x.ratchetKey == pk) = none := hfind
      exact absurd (beq_iff_eq.mpr hrk₀) (List.find?_eq_none.mp hnone c₀ hc₀_mem)
    | some c_found =>
      simp only [hfind] at hrc
      injection hrc with hrc; injection hrc with hc_eq _
      subst c_found
      obtain ⟨hc_mem, hc_rk⟩ := TR.G1.mem_recv_of_findRecvChain_eq_some hfind
      have hc_eq_c₀ : c = c₀ := huniq c hc_mem c₀ hc₀_mem (hc_rk.trans hrk₀.symm)
      subst hc_eq_c₀
      unfold consumeMessageKey at hcons
      split at hcons
      · cases hcons
      · rename_i hge; exact absurd hlt hge
  · exact hrIdx2

theorem trStateStoredAt_of_mem_availableStates_provB {r₀ : ProtocolSetup} {tr : ExecTrace} {st : TRState}
    (hst : st ∈ availableStates r₀ tr) :
    ∃ p i, TR.G1.TRStateStoredAt p st i tr := by
  unfold availableStates storedStates DY.ExecTrace.getLocalStateAt at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  exact ⟨e.st.participant, j, hat⟩

/-- Honest skeleton uniqueness for a `SkippedKeyStored` seed `mkSeed`. -/
theorem honestSkelUniq_skipped
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move)
    (p₀ : Participant) (st_s st₀ : TRState) (msg₀ : TRSignalMsg)
    (mkSeed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g (runTraceMoves r₀ ms))
    (hst_s : st_s ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p₀) msg₀.ratchetKey msg₀.counter mkSeed rIdx srcIdx) skIdx)
    (hsh : (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
      (gamma' interpretation S g mkSeed).shape) :
    (kdfCk st_s.cks).2 = mkSeed := by
  obtain ⟨p_s, i_s, hst_s_at⟩ := trStateStoredAt_of_mem_availableStates_provB hst_s
  obtain ⟨rk1, k, j, hcks, hrk⟩ := TR.G1.stCksIsCreateChain_of_stored hreach hst_s_at
  have hX : TR.G1.Spine.RootX (runTraceMoves r₀ ms) (createChain rk1 k st_s.dhs).2 :=
    .inl ⟨p_s, st_s, i_s, j, hst_s_at, hcks, rk1, k, rfl, hrk⟩
  have hckOut : TR.G1.Spine.ckOut true (chainKeyAt (createChain rk1 k st_s.dhs).2 j) =
      (kdfCk st_s.cks).2 := by
    rw [← hcks]; rfl
  have hRkTwin : TR.G1.Spine.RkTwinStmt interpretation S g (runTraceMoves r₀ ms) :=
    TR.G1.Spine.rkTwin interpretation S g hreach
      (TR.G1.Spine.aliceBobTwin_of_reachable interpretation S g hreach hKem32)
  have hRootTwin : TR.G1.Spine.RootTwinStmt interpretation S g (runTraceMoves r₀ ms) :=
    TR.G1.Spine.rootTwin interpretation S g hreach hKem32 hRkTwin
  have heq := TR.G1.Spine.twin_root interpretation S g hreach hRootTwin hX j true
    (good_of_skippedKeyStored hreach hlog)
    (fun _ he => he) (fun _ he => he)
    (by rw [hckOut]; exact hsh)
  rw [← hckOut]; exact heq

/-- Every `SkippedKeyStored` seed `mkSeed` on a reachable trace is a role-`false` `SpineRkK` term. -/
theorem spineRkK_of_skippedKeyStored
    (r₀ : ProtocolSetup) (ms : List Move) {s : SessionInfo} {pk mkSeed : DY.Bytes}
    {n : UInt32} {rIdx srcIdx skIdx : Nat}
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hlog : (runTraceMoves r₀ ms).EventLoggedAt (TREvent.SkippedKeyStored s pk n mkSeed rIdx srcIdx) skIdx) :
    TR.G1.Spine.SpineRkK (·.AttackerKnows (runTraceMoves r₀ ms))
      (TR.G1.Spine.LoggedIkmRk (runTraceMoves r₀ ms)) false mkSeed := by
  have hprov := provEvTR_reachable hreach s pk n mkSeed rIdx srcIdx skIdx hlog
  rcases hprov.2.2 with ⟨p_src, st_src, c₀, bc, c₁, hst_src, _, hrc, hcmk⟩ |
      ⟨p_src, st_src, c₀, hst_src, hsinf, hinit, hc₀_mem, hrk₀, hrIdx₀, hlt⟩
  · have hst_avail : st_src ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
      TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms hst_src
    have hc₀_sp : TR.G1.Spine.SpineRkK (·.AttackerKnows (runTraceMoves r₀ ms))
        (TR.G1.Spine.LoggedIkmRk (runTraceMoves r₀ ms)) false c₀.chainKey :=
      TR.G1.Spine.spineRkK_recvChainFor (TR.G1.Spine.spStateRkK_runTrace hst_avail)
        (TR.G1.Spine.attackerKnows_x25519Key hprov.1) hrc
    rw [(TR.G1.consumeMessageKey_eq_spine hcmk).1]
    exact .ckStep2 (spineRkK_chainKeyAt _ hc₀_sp)
  · have hrIdx2 : rIdx = 2 := rIdx_eq_two_of_provB hreach hlog hst_src hc₀_mem hrk₀ hlt
    have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
    obtain ⟨_, _, _, ⟨doneIdx₁, ikm₁, dh₁₁, hses₁, _, _, hrecv₁⟩, _⟩ :=
      hInv.stateOK p_src st_src srcIdx hst_src
    obtain ⟨_, _, _, ck₀₁, hroot₁, hck₁⟩ := hrecv₁ c₀ hc₀_mem
    obtain ⟨_, _, doneIdx₂, ikm₂, dh₁₂, ck₀₂, hses₂, hroot₂, hmk⟩ :=
      hInv.eventOK (TREvent.SkippedKeyStored s pk n mkSeed rIdx srcIdx) ⟨skIdx, hlog⟩
    have hs_init : s.initiator = false := by
      rw [← hsinf]; exact hinit
    obtain ⟨hikm_eq, hdh_eq⟩ := spb_compSessionAt_resp_ikm_dh_eq (hsinf ▸ hses₁) hses₂ hs_init
    have hck₀_eq : ck₀₂ = ck₀₁ := by
      rw [hrIdx₀, hrIdx2] at hroot₁
      rw [hrIdx2] at hroot₂
      dsimp only [Symbolic.Swarm.COMPOSED.CompRatchet.CompChainRootFrom1] at hroot₁ hroot₂
      rw [hroot₁, hroot₂, hikm_eq, hdh_eq]
    have hst_avail : st_src ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
      TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms hst_src
    have hc₀_sp : TR.G1.Spine.SpineRkK (·.AttackerKnows (runTraceMoves r₀ ms))
        (TR.G1.Spine.LoggedIkmRk (runTraceMoves r₀ ms)) false c₀.chainKey :=
      TR.G1.Spine.spineRkK_recvChain_runTrace hst_avail hc₀_mem
    rw [hck₁] at hc₀_sp
    have hck₀_sp := spineRkK_of_chainKeyAt c₀.index.toNat hc₀_sp
    rw [hmk, hck₀_eq]
    exact .ckStep2 (spineRkK_chainKeyAt _ hck₀_sp)

open Symbolic.Swarm.COMPOSED.CompRatchet in
/-- Proves `SkippedFreshAliasExclB` on reachable traces via `rIdx_eq_two_of_provB` and `saltDepth`. -/
theorem skippedFreshAliasExclB_of_reach
    (interpretation : ExternInterpretation)
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ : List Move} {τ₁ : List MachineEvent}
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability) :
    SkippedFreshAliasExclB interpretation r₀ S g ms₁ τ₁ := by
  intro p _stateIdx₀ _body m st₀ st_prov _t₀ pk seed _k_own msg₀ rIdx srcIdx skIdx c₀ _c_ex
    _htry _ht₀ _hparse₀ hver₀ hctr₀ _hNotCol₀ _hst₀ hst_prov _hik_eq hseed_pk _hk_def hlog _hγ_pk
    _hMacBytes hrcf _hfind _hrk_ne _hJunk _hVar _hrkK _hSeedNK
    ⟨p₀, st₀_src, c_src, hst₀_src_at, _hsinfo_src, _hinit_false, hc_src, hc_src_rk, _hc_src_rIdx, hlt⟩
  have hrIdx2 : rIdx = 2 := rIdx_eq_two_of_provB hreach hlog hst₀_src_at hc_src hc_src_rk hlt
  have hrs := hseed_pk { msg₀ with ratchetKey := pk } hver₀ rfl rfl
  unfold recvSeed at hrs
  simp only [hver₀, ↓reduceIte, hrcf, hctr₀] at hrs
  obtain ⟨⟨seed', c₀'⟩, hcons, hseed_eq⟩ := Option.map_eq_some_iff.mp hrs
  dsimp only at hseed_eq; subst seed'
  have hc₀_ck_idx : c₀.chainKey = (createChain st_prov.rk pk st_prov.dhs).2 ∧ c₀.index = 0 := by
    unfold DY.Libsignal.TripleRatchet.recvChainFor at hrcf
    cases hfc : findRecvChain st_prov.recv pk with
    | none =>
      simp only [hfc] at hrcf
      split at hrcf
      · cases hrcf
      · injection hrcf with hp; injection hp with hc _; subst hc; exact ⟨rfl, rfl⟩
    | some c =>
      simp only [hfc] at hrcf; injection hrcf with hp; injection hp with _ hb; cases hb
  have hseed_prov : seed = (kdfCk (chainKeyAt (createChain st_prov.rk pk st_prov.dhs).2
      (UInt32.ofBitVec m.counter).toNat)).2 := by
    have hsp := (TR.G1.consumeMessageKey_eq_spine hcons).1
    rw [hc₀_ck_idx.1, hc₀_ck_idx.2] at hsp
    exact hsp
  have hInv := compScheduleInv_reachable hreach
  obtain ⟨p_prov, j_prov, hst_prov_at⟩ := TR.G1.trStateStoredAt_of_mem_availableStates hst_prov
  obtain ⟨hrIdx_pos, _, _, ⟨_, ikm_p, dh₁_p, _, hrk_p, _, _⟩, _⟩ :=
    hInv.stateOK p_prov st_prov j_prov hst_prov_at
  obtain ⟨_, _, _, ikm_e, dh₁_e, ck₀_e, _, hroot_e, hseed_e⟩ :=
    hInv.eventOK (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx)
      ⟨skIdx, hlog⟩
  have hsd_prov : saltDepth seed = 5 + 2 * st_prov.rIdx + (UInt32.ofBitVec m.counter).toNat := by
    have hrk_sd := hrk_p.saltDepth_eq
    simp only [saltDepth_pqxdhKdf_rk] at hrk_sd
    rw [hseed_prov, saltDepth_kdfCk_snd, saltDepth_chainKeyAt, saltDepth_createChain_snd, hrk_sd]
    omega
  have hsd_ev : saltDepth seed = 5 + (UInt32.ofBitVec m.counter).toNat := by
    have hck_sd := hroot_e.saltDepth_eq
    rw [hrIdx2] at hck_sd
    rw [hseed_e, saltDepth_kdfCk_snd, saltDepth_chainKeyAt, hck_sd]
    omega
  omega

end Symbolic.Swarm.CREF.CliPure
