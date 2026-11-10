/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedEqPure
import DY.Bytes.Basic
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
import DY.EquationalTheory.Concat
import Symbolic.Specifications.Model.EquationalTheory.Kem
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SlotsZ6FramePure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTieResidPureA
import Symbolic.Proofs.Swarm.CREF.TR.G1.HmacWireMemo
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkBobGuard
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkRootTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSep
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkTwin
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineLink
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Residual Seed-Exclusion Assembly for Promote Record-State Tie

Proves `prom_abs_of_xplBlock` and combines the five residual seed-exclusion obligations in
`prom_tieResid_at_clean`.
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
open DY.Libsignal.TripleRatchet (createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  pqxdhIkm pqxdhKdf agree serializedIk)
open DY.Libsignal.TripleRatchet (TREvent spqrA2B)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED.CompPresPQXDH

section DoneOpkEkAkProof

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

private theorem doneOpkEkAk_nil_pdtrp3b3 : pdtr_DoneOpkEkAk Trace.nil :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at h,
   fun _ _ _ _ _ _ _ _ _ _ _ h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at h⟩

private theorem pdtr_DoneOpkEkAk.append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (hd : pdtr_DoneOpkEkAk tr) (e : E)
    (hne : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none) :
    pdtr_DoneOpkEkAk (tr.append e) :=
  ⟨fun a b ikA ikB spk pqpk opk ek ct keys i hev o ho =>
    DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le tr e)
      (hd.1 a b ikA ikB spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev hne) o ho),
   fun b a ikB ikA spk pqpk opk ek ct keys i hev =>
    DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le tr e)
      (hd.2 b a ikB ikA spk pqpk opk ek ct keys i (eventLoggedAt_append_other hev hne))⟩

private theorem doneOpkEkAk_of_noDoneEv_pdtrp3b3 {α : Type} {f : Traceful α} (hf : pdtr_NoDoneEv f)
    (tr : ExecTrace) (h : pdtr_DoneOpkEkAk tr) : pdtr_DoneOpkEkAk (f.run tr).2.val :=
  ⟨fun a b ikA ikB spk pqpk opk ek ct keys i hev o ho =>
    DY.Bytes.AttackerKnows_le _ _ _ (f.run tr).2.property
      (h.1 a b ikA ikB spk pqpk opk ek ct keys i (hf tr _ i rfl hev) o ho),
   fun b a ikB ikA spk pqpk opk ek ct keys i hev =>
    DY.Bytes.AttackerKnows_le _ _ _ (f.run tr).2.property
      (h.2 b a ikB ikA spk pqpk opk ek ct keys i (hf tr _ i rfl hev))⟩

private def PreservesBobEk_pdtrp3b3 (ek₀ : DY.Bytes) {α : Type} (f : Traceful α) : Prop :=
  ∀ tr, ek₀.AttackerKnows tr → pdtr_DoneOpkEkAk tr → pdtr_DoneOpkEkAk (f.run tr).2.val

private theorem PreservesBobEk_pdtrp3b3.of_noDoneEv {ek₀ : DY.Bytes} {α : Type} {f : Traceful α}
    (hf : pdtr_NoDoneEv f) : PreservesBobEk_pdtrp3b3 ek₀ f :=
  fun tr _ hd => doneOpkEkAk_of_noDoneEv_pdtrp3b3 hf tr hd

private theorem PreservesBobEk_pdtrp3b3.bind {ek₀ : DY.Bytes} {α β : Type} {f : Traceful α} {g : α → Traceful β}
    (hf : PreservesBobEk_pdtrp3b3 ek₀ f) (hg : ∀ x, PreservesBobEk_pdtrp3b3 ek₀ (g x)) :
    PreservesBobEk_pdtrp3b3 ek₀ (f >>= g) := by
  intro tr hek hd
  rw [pdtr_run_bind_snd_nde]
  rcases hrun : (f.run tr).1 with _ | x
  · exact hf tr hek hd
  · exact hg x (f.run tr).2.val
      (DY.Bytes.AttackerKnows_le _ _ _ (f.run tr).2.property hek)
      (hf tr hek hd)

private theorem preservesBobEk_logBobDone_pdtrp3b3 (b a : Participant)
    (ikB ikA spk pqpk : DY.Bytes) (opk : Option DY.Bytes)
    (ek₀ ct : DY.Bytes) (keys : HandshakeKeys) :
    PreservesBobEk_pdtrp3b3 ek₀ (DY.ProtocolEvent.logEvent
      (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek₀ ct keys)) := by
  intro tr hek hd
  have hle := (DY.ProtocolEvent.logEvent
    (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek₀ ct keys)).run tr |>.2.property
  have htr : ((DY.ProtocolEvent.logEvent
      (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek₀ ct keys)).run tr).2.val =
      tr.append ({ ev := PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek₀ ct keys } :
        DY.ProtocolEvent.ExecEntryT PQXDHEvent) := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
    rfl
  refine ⟨fun a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hev o ho => ?_,
          fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => ?_⟩
  · rw [htr] at hev
    rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev'⟩ | ⟨_, hEq⟩
    · exact DY.Bytes.AttackerKnows_le _ _ _ hle
        (hd.1 a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hev' o ho)
    · cases hEq
  · rw [htr] at hev
    rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev'⟩ | ⟨_, hEq⟩
    · exact DY.Bytes.AttackerKnows_le _ _ _ hle
        (hd.2 b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev')
    · injection hEq with _ _ _ _ _ _ _ hekEq _ _
      subst hekEq
      exact DY.Bytes.AttackerKnows_le _ _ _ hle hek

private theorem doneOpkEkAk_preserves_aliceStart_pdtrp3b3 (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) (tr : ExecTrace) (hd : pdtr_DoneOpkEkAk tr) :
    pdtr_DoneOpkEkAk ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hd
    (hd.append_other (CompTrace.RndE 32) rfl)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ hopk _ _ => ?_
  let hs := CompTrace.aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (CompTrace.RndE 32)
  let tr2 := tr1.append (CompTrace.RndE 32)
  let dhsA := Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0, sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk, initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (CompTrace.RndE 32)
  let tr4 := tr3.append (CompTrace.NetE hs.ek)
  let tr5 := tr4.append (CompTrace.NetE hs.ct)
  let evA := PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys
  let tr6 := tr5.append (CompTrace.PQEvE evA)
  let tr7 := tr6.append (CompTrace.TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    DY.Libsignal.TripleRatchet.traceLength,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  change pdtr_DoneOpkEkAk ((tr7.append (CompTrace.CEvE
    (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))).append
    (CompTrace.TRStE a stA))
  have hd5 : pdtr_DoneOpkEkAk tr5 :=
    ((((hd.append_other _ rfl).append_other _ rfl).append_other _ rfl).append_other _ rfl).append_other _ rfl
  have hle06 : tr ≤ tr6 :=
    Trace.le_trans _ _ _ (Trace.append_le tr _)
      (Trace.le_trans _ _ _ (Trace.append_le tr1 _)
        (Trace.le_trans _ _ _ (Trace.append_le tr2 _)
          (Trace.le_trans _ _ _ (Trace.append_le tr3 _)
            (Trace.le_trans _ _ _ (Trace.append_le tr4 _) (Trace.append_le tr5 _)))))
  have hle56 : tr5 ≤ tr6 := Trace.append_le tr5 _
  have hd6 : pdtr_DoneOpkEkAk tr6 :=
    ⟨fun a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hev o ho => by
      rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev5⟩ | ⟨_, hEq⟩
      · exact DY.Bytes.AttackerKnows_le _ _ _ hle56
          (hd5.1 a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys' i hev5 o ho)
      · dsimp only [evA, hs, CompTrace.aliceOut] at hEq
        injection hEq with _ _ _ _ _ _ hopkEq _ _ _
        subst hopkEq
        obtain ⟨_, _, hn⟩ := hopk o ho
        exact DY.Bytes.AttackerKnows_le _ _ _ hle06
          (DY.Bytes.AttackerKnows.prove_from_base o tr hn.baseAttackerKnows),
     fun b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev => by
      rcases eventLoggedAt_append_ev_iff.mp hev with ⟨_, hev5⟩ | ⟨_, hEq⟩
      · exact DY.Bytes.AttackerKnows_le _ _ _ hle56
          (hd5.2 b' a' ikB' ikA' spk' pqpk' opk' ek' ct' keys' i hev5)
      · dsimp only [evA] at hEq; cases hEq⟩
  exact ((hd6.append_other _ rfl).append_other _ rfl).append_other _ rfl

private theorem doneOpkEkAk_preserves_bobStart_pdtrp3b3 (b a : Participant)
    (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) (hd : pdtr_DoneOpkEkAk tr) :
    pdtr_DoneOpkEkAk ((DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hd
    fun sB sS sQ o ikA _ ek ct _ keys _ _ _ _ _ hekNet _ _ _ => ?_
  have hekAk : ek.AttackerKnows tr :=
    DY.Bytes.AttackerKnows.prove_from_base ek tr hekNet.baseAttackerKnows
  suffices hP : PreservesBobEk_pdtrp3b3 ek _ from hP tr hekAk hd
  refine PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_receiveSignalMsg mh.msg)) fun msg =>
    PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_ensureReceiverChain _ msg.ratchetKey)) fun ⟨st, _, _⟩ => ?_
  dsimp only
  split
  · split
    · refine PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_sendMessage _)) fun _ =>
        PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_receiveMessage pqIdx)) fun pqSalt =>
        PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_verifyMacAndDecrypt st msg pqSalt _)) fun _ => ?_
      split
      all_goals first
        | refine PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_guardOnTrace _)) fun _ =>
            PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logEventPQ rfl)) fun _ => ?_
        | skip
      all_goals refine PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv pdtr_noDoneEv_traceLength) fun _ =>
        PreservesBobEk_pdtrp3b3.bind (preservesBobEk_logBobDone_pdtrp3b3 b a _ _ _ _ _ ek ct keys) fun _ => ?_
      all_goals split
      all_goals first
        | refine PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logEventTR _)) fun _ =>
            PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logEventTR _)) fun _ => ?_
        | skip
      all_goals exact PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logEventC _)) fun _ =>
        PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv pdtr_noDoneEv_traceLength) fun _ =>
        PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
        PreservesBobEk_pdtrp3b3.bind (PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logEventTR _)) fun _ =>
        PreservesBobEk_pdtrp3b3.of_noDoneEv (pdtr_noDoneEv_logMessageKeyAndStore b _ .receiver _ _ _ _ _ _)
    · exact PreservesBobEk_pdtrp3b3.of_noDoneEv pdtr_NoDoneEv.failure
  · exact PreservesBobEk_pdtrp3b3.of_noDoneEv pdtr_NoDoneEv.failure

private theorem doneOpkEkAk_of_reachable_pdtrp3b3 {tr : ExecTrace} (hr : TR.G1.ReachableTrace tr) :
    pdtr_DoneOpkEkAk tr := by
  induction hr with
  | Base => exact doneOpkEkAk_nil_pdtrp3b3
  | Step input _ _ hd =>
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_sendMessage inp) _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_registerIdentity inp) _ hd
    · rcases inp with ⟨p, skIdx⟩; exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_registerCorruptIdentity p skIdx) _ hd
    · rcases inp with ⟨b, idStateIdx⟩; exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_genSignedPrekey b idStateIdx) _ hd
    · rcases inp with ⟨b, idStateIdx⟩; exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_genPQPrekey b idStateIdx) _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_genOneTimePrekey inp) _ hd
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩
      exact doneOpkEkAk_preserves_aliceStart_pdtrp3b3 a b idStateIdx regIdxB bh _ hd
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩
      exact doneOpkEkAk_preserves_bobStart_pdtrp3b3 b a kh regIdxA mh pqIdx spqrMsgIdx _ hd
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_messageEncrypt me stateIdx coinsLen pqIdx) _ hd
    · rcases inp with ⟨me, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_messageEncryptAbort me stateIdx) _ hd
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) _ hd
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx) _ hd
    · rcases inp with ⟨me, stateIdx, k⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_exposeKey me stateIdx k) _ hd
    · rcases inp with ⟨me, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_exposeSpqr me stateIdx) _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_exposeSkipped inp) _ hd
    · rcases inp with ⟨p, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_compromiseIK p stateIdx) _ hd
    · rcases inp with ⟨b, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_compromiseSPK b stateIdx) _ hd
    · rcases inp with ⟨b, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_compromisePQSPK b stateIdx) _ hd
    · rcases inp with ⟨b, stateIdx⟩
      exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_compromiseOPK b stateIdx) _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 pdtr_noDoneEv_breakDH _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 pdtr_noDoneEv_breakKEM _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_invertDH inp) _ hd
    · exact doneOpkEkAk_of_noDoneEv_pdtrp3b3 (pdtr_noDoneEv_invertKEM inp) _ hd
    · omega

private theorem pqxdhKdf_inj_ikm_pdtrp3b3 {x y : DY.Bytes} (h : pqxdhKdf x = pqxdhKdf y) : x = y := by
  have h1 : (pqxdhKdf x).rk = (pqxdhKdf y).rk := congrArg HandshakeKeys.rk h
  exact (TR.G1.kdfExtract_injective (TR.G1.kdfExtract_injective h1).1).2

unseal DY.Bytes in
private theorem kemLeaf_ne_concat_pdtrp3b3 {ss l r : DY.Bytes}
    (hk : TR.G1.ShapeModKem.KemLeaf ss) : ss ≠ Concat.concat l r := by
  rcases hk with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩ <;>
    exact fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

private theorem pqxdhIkm_opt_ss_eq_of_kemLeaf_pdtrp3b3
    {a₁ b₁ e₁ a₂ b₂ e₂ ss₁ ss₂ : DY.Bytes} {d₁ d₂ : Option DY.Bytes}
    (hk₁ : TR.G1.ShapeModKem.KemLeaf ss₁) (hk₂ : TR.G1.ShapeModKem.KemLeaf ss₂)
    (h : DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ e₁ d₁ ss₁ =
      DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ e₂ d₂ ss₂) :
    d₁ = d₂ ∧ ss₁ = ss₂ := by
  unfold DY.Libsignal.PQXDH.pqxdhIkm at h
  have htail := (TR.G1.concat_injective (TR.G1.concat_injective (TR.G1.concat_injective (TR.G1.concat_injective h).2).2).2).2
  cases d₁ <;> cases d₂
  · exact ⟨rfl, htail⟩
  · exact False.elim (kemLeaf_ne_concat_pdtrp3b3 hk₁ htail)
  · exact False.elim (kemLeaf_ne_concat_pdtrp3b3 hk₂ htail.symm)
  · exact ⟨congrArg some (TR.G1.concat_injective htail).1, (TR.G1.concat_injective htail).2⟩

private theorem ikmHolesKemK_of_loggedIkmRk_pdtrp3b3 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hT : TR.G1.ReachableTrace T) (hKem32 : TR.G1.Spine.AliceKemLen32 i S g T)
    {c : Bool} {ikm : DY.Bytes}
    (h : TR.G1.Spine.LoggedIkmRk T c ikm ∧ TR.G1.Spine.IkmHolesK (·.AttackerKnows T) ikm) :
    TR.G1.Spine.IkmHolesKemK i S g T ikm := by
  have hinv := spqrInv_of_reachable _ hT
  have hdok := doneOpkEkAk_of_reachable_pdtrp3b3 hT
  obtain ⟨⟨ev, hlog, hd⟩, ⟨a₁, b₁, e₁, d₁, ss₁, hikm₁, ha₁, hb₁, he₁, hd₁⟩⟩ := h
  obtain ⟨j, hev⟩ := TR.G1.Spine.loggedPQEv_iff_eventLogged.mp hlog
  cases c with
  | false =>
    cases ev
    case AliceDone a b ikA ikB spk pqpk opk ek ct keys =>
      obtain ⟨pk, e, a₀, b₀, e₀, d₀, hct, hikm₀, hkeys₀, _, _, _, _⟩ := hd
      obtain ⟨haEq, hbEq, heEq⟩ := pdtr_pqxdhIkm_tail_eq (hikm₀.symm.trans hikm₁)
      subst haEq hbEq heEq
      obtain ⟨t, sA, rfl, _, _, _, _, hag, _⟩ :=
        hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys j hev
      have hct' : ct = (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).1 := congrArg Prod.fst hag
      obtain ⟨hpkEq, heEntEq⟩ := Stage1Kyber.kemEncap_fst_inj (hct.symm.trans hct')
      subst hpkEq heEntEq
      have hikm' : keys = pqxdhKdf (pqxdhIkm (agree spk sA) (agree ikB (randTerm t 32))
          (agree spk (randTerm t 32)) (opk.map (agree · (randTerm t 32)))
          (DY.PQKem.kemEncap pk (randTerm (t + 1) 32)).2) := congrArg Prod.snd hag
      have hd₀Eq : d₀ = opk.map (agree · (randTerm t 32)) :=
        (pqxdhIkm_opt_ss_eq_of_kemLeaf_pdtrp3b3 (.inl ⟨_, _, rfl⟩) (.inl ⟨_, _, rfl⟩)
          (pqxdhKdf_inj_ikm_pdtrp3b3 (hikm₀ ▸ hkeys₀.symm.trans hikm'))).1
      refine ⟨a₀, b₀, e₀, d₀, (DY.PQKem.kemEncap pk (randTerm (t + 1) 32)).2,
        hikm₀, ha₁, hb₁, he₁, ?_,
        TR.G1.Spine.kemKnownFromTwin_of_aliceDone i S g hT hKem32 hev⟩
      intro v hv
      rw [hd₀Eq] at hv
      obtain ⟨o, hopk, rfl⟩ := Option.map_eq_some_iff.mp hv
      exact TR.G1.Spine.dhHoleK_agree t
        (hdok.1 a b ikA ikB spk pk opk ek ct keys (t + 5) hev o hopk)
    all_goals exact False.elim hd
  | true =>
    cases ev
    case BobDone b a ikB ikA spk pqpk opk ek ct keys =>
      obtain ⟨ss₀, a₀, b₀, e₀, d₀, hleaf₀, hikm₀, hkeys₀, _, _, _, _⟩ := hd
      obtain ⟨haEq, hbEq, heEq⟩ := pdtr_pqxdhIkm_tail_eq (hikm₀.symm.trans hikm₁)
      subst haEq hbEq heEq
      obtain ⟨sB, sS, sQ, o, ss, _, _, _, _, ⟨tQ, hsQ, _⟩, hpqpkEq, hopkAt, _, _, hssEq, hkeysEq, _, _⟩ :=
        hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys j hev
      have hleaf : TR.G1.ShapeModKem.KemLeaf ss := by
        subst hssEq
        rcases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sQ ct) with _ | s
        · exact .inr ⟨sQ, ct, rfl⟩
        · obtain ⟨e', _, rfl⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hdec
          exact .inl ⟨_, e', rfl⟩
      obtain ⟨hd₀Eq, hss₀Eq⟩ := pqxdhIkm_opt_ss_eq_of_kemLeaf_pdtrp3b3 hleaf₀ hleaf
        (pqxdhKdf_inj_ikm_pdtrp3b3 (hikm₀ ▸ hkeys₀.symm.trans hkeysEq))
      subst hss₀Eq hssEq
      have hBobAk := TR.G1.Spine.bobDone_ct_pqpk_attackerKnows_of_reachable hT hev
      have hpqAk : (DY.PQKem.kemPk sQ).AttackerKnows T := by
        rw [← hpqpkEq]
        exact hBobAk.2
      refine ⟨a₀, b₀, e₀, d₀, _,
        hikm₀, ha₁, hb₁, he₁, ?_,
        TR.G1.Spine.kemKnownFromTwin_bobKemShare i S g hT hKem32 hsQ hBobAk.1 hpqAk⟩
      intro v hv
      rw [hd₀Eq] at hv
      obtain ⟨x, ho, rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨t, rfl, _⟩ := hopkAt x ho
      exact TR.G1.Spine.dhHoleK_agree t
        (hdok.2 b a ikB ikA spk pqpk opk ek ct keys j hev)
    all_goals exact False.elim hd

end DoneOpkEkAkProof

private theorem g1cAttackerBuiltSeedExcl'_of_seedSepAK_and_kem32_pdtrp3b3
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) {Q : DY.Bytes → Prop}
    (hQ : TR.G1.Spine.SeedSepAKRun interpretation r₀ S g ms Q)
    (hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g (runTraceMoves r₀ ms)) :
    TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms := by
  intro b t₀ msg₀ st₀ mkSeed k_own hreach ht₀ hparse₀ _hnc hst₀ hseed hnk hCase
  have hrkAK : msg₀.ratchetKey.AttackerKnows (runTraceMoves r₀ ms) :=
    (TR.attackerKnows_ratchetKey_and_wire_of_parseTrSignalMsg ht₀.1 hparse₀).1
  obtain ⟨salt₁, inp₀, _hsalt₁, _hgam, hmac₀, hinp_ak, hsh⟩ := hCase
  obtain ⟨_salt₀, seed₀, _hsalt₀_ak, hseed₀_ak, _hsalt₀_sh, hseed₀_sh, _hprk_memo, hmemo₀⟩ :=
    TR.G1.hmac_wire_attackerKnows_inv_memo interpretation r₀ S g ms hreach t₀ msg₀ hparse₀ st₀ salt₁
      mkSeed st₀.peerIk st₀.myIk inp₀ hseed hmac₀ hinp_ak hsh
  have hv := pdtr_spineRkK_and_ikmHolesK (TR.G1.Spine.spineRkK_recvSeed_runTrace hst₀ hrkAK hseed)
  exact TR.G1.Spine.false_of_oneSidedPeelAK interpretation S g hreach hQ.down
    (fun h => ikmHolesKemK_of_loggedIkmRk_pdtrp3b3 interpretation S g hreach hKem32 h)
    (hQ.sep _ _) hv (hQ.seed hst₀ hseed) hnk hseed₀_ak hmemo₀
    (fun e he => pdtr_memo_mem_of_computeMac_seed interpretation S g salt₁ mkSeed st₀.peerIk st₀.myIk
      msg₀.wire he)
    hseed₀_sh

/-- `G1cAttackerBuiltSeedExcl'` holds on `ms₀ ++ pre` for any `XplBlock` under a `MatchedPrefix`. -/
theorem prom_abs_of_xplBlock
    (interpretation : ExternInterpretation)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc blk : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g (ms₀ ++ (pre ++ m :: post)) (acc ++ blk))
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk) :
    TR.G1.G1cAttackerBuiltSeedExcl' interpretation r S g (ms₀ ++ pre) := by
  have hrun_pre : ModelRun r (ms₀ ++ pre) := pdtr_prom_resid_modelRun_pre hB
  have hT : (runTraceMoves r (ms₀ ++ pre)).Reachable
      DY.Libsignal.Composed.reachability := hrun_pre.2.2.1.1
  have hKem32_full := TR.G1.Spine.aliceKemLen32_of_matchedPrefix hmp
  have hKem32 : TR.G1.Spine.AliceKemLen32 interpretation S g (runTraceMoves r (ms₀ ++ pre)) := by
    intro t a b ikA ikB spk pqpk opk ek ct keys hev
    have hle : runTraceMoves r (ms₀ ++ pre) ≤ runTraceMoves r (ms₀ ++ (pre ++ m :: post)) := by
      rw [← List.append_assoc, TR.runTrace_append (ms₁ := ms₀ ++ pre)]
      exact TR.le_runMoves_fst (m :: post) (runTraceMoves r (ms₀ ++ pre))
    exact hKem32_full t a b ikA ikB spk pqpk opk ek ct keys
      (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_mono hle hev)
  have hLink : TR.G1.Spine.RecvLinkStored (runTraceMoves r (ms₀ ++ pre)) :=
    TR.G1.Spine.recvLinkStored_of_reachable hT
  have hRkTwin : TR.G1.Spine.RkTwinStmt interpretation S g (runTraceMoves r (ms₀ ++ pre)) :=
    TR.G1.Spine.rkTwin interpretation S g hT
      (TR.G1.Spine.aliceBobTwin_of_reachable interpretation S g hT hKem32)
  have hRkTwinStored : TR.G1.Spine.RkTwinStoredStmt interpretation S g (runTraceMoves r (ms₀ ++ pre)) :=
    TR.G1.Spine.rkTwinStored interpretation S g hT
  have hRootTwin : TR.G1.Spine.RootTwinStmt interpretation S g (runTraceMoves r (ms₀ ++ pre)) :=
    TR.G1.Spine.rootTwin interpretation S g hT hKem32 hRkTwin
  have hQ := TR.G1.Spine.seedSepAKRun_of interpretation r S g (ms₀ ++ pre)
    hT hLink hRkTwin hRkTwinStored hRootTwin
  exact g1cAttackerBuiltSeedExcl'_of_seedSepAK_and_kem32_pdtrp3b3 interpretation r S g (ms₀ ++ pre) hQ hKem32

/-- Assembles the five residual seed facts consumed by `prom_rcvDecTie_at` from `MatchedPrefix`,
`XplBlock`, and `A2bSeedRkAliasRes`. -/
theorem prom_tieResid_at_clean
    (interpretation : ExternInterpretation)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc blk : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g (ms₀ ++ (pre ++ m :: post)) (acc ++ blk))
    (hmp₀ : MatchedPrefix interpretation r S who g ms₀ acc)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hrkAlias : TR.RecvDecStep.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc) :
    TR.TRRecvFreshAll r ms₀ ∧
      TR.G1.G1cAttackerBuiltSeedExcl' interpretation r S g (ms₀ ++ pre) ∧
      TR.RecvDecStep.A2bCrossSeedExcl interpretation r S g (ms₀ ++ pre) acc ∧
      TR.RecvDecStep.A2bSeedShapeEqRes interpretation r S g (ms₀ ++ pre) acc ∧
      TR.RecvDecStep.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc :=
  ⟨prom_fresh_of_matchedPrefix interpretation hmp₀,
   prom_abs_of_xplBlock interpretation hmp hB,
   prom_crossSeedExcl interpretation,
   prom_seedShapeEqRes_of_modelRun interpretation r S g (ms₀ ++ pre) acc
     (pdtr_prom_resid_modelRun_pre hB),
   hrkAlias⟩

end Symbolic.Swarm.CREF.CliPure
