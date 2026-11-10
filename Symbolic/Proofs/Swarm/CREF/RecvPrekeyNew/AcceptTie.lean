/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
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
public import Symbolic.Proofs.Swarm.CREF.Xpl.Faithful
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.Steps
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.TR.Ghosts -- shake: keep
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
# `bobStart` Inversion, Base-Key Tie, and Stored Snapshot

Defines `BobStartOk` for the witnesses of a successful `bobStart` step, inverts a `bobStart` step
that yields a received plaintext (`rpkT_bobStart_inv` and `rpkT_bobStart_block`), ties the appended
`BobDone` base key to the wire base key (`rpkT_tie_baseKey`), and characterizes the `TRState`
entries stored along `bobStartTr` (`rpkR_finalSt` and `rpkBH_trStateStoredAt_bobStartTr`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR (StE EvE NetE RndE runTrace_append runTrace_snoc)
open Symbolic.Swarm.CREF.TR.G1 (TRStateStoredAt)
open DY.Libsignal.TripleRatchet (TRState TREvent SessionInfo kdfCk logSkippedKeys)

/-- The witnesses of a successful `bobStart b a kh regA mh pqIdx spqrMsgIdx` on `tr`: exactly the
hypotheses of `Runs.bobStart`. -/
structure BobStartOk (tr : ExecTrace) (b a : Participant) (kh : PQXDH.BobKeyHandles)
    (regA : Nat) (mh : PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) where
  ikB : DY.Bytes
  spk : DY.Bytes
  pqsk : DY.Bytes
  ikAPk : DY.Bytes
  vkA : DY.Bytes
  ek : DY.Bytes
  ct : DY.Bytes
  raw : DY.Bytes
  spqr' : DY.Bytes
  key : DY.Bytes
  seed : DY.Bytes
  pqSalt : DY.Bytes
  m : DY.Bytes
  opk : Option DY.Bytes
  honest : Bool
  keys : PQXDH.HandshakeKeys
  msg : DY.Libsignal.TripleRatchet.TRSignalMsg
  c' : DY.Libsignal.TripleRatchet.RecvChain
  hik : tr.at? kh.ik = some (StE b { kind := .identity, sk := ikB })
  hspk : tr.at? kh.spk = some (StE b { kind := .signedPrekey, sk := spk })
  hpq : tr.at? kh.pqspk = some (StE b { kind := .pqPrekey, sk := pqsk })
  hopk : StOpt tr b kh.opk opk
  hreg : tr.at? regA = some (EvE (.IdentityRegistered a ikAPk vkA honest))
  hek : tr.at? mh.ek = some (NetE ek)
  hct : tr.at? mh.ct = some (NetE ct)
  hcan : PQXDH.isCanonicalKey ek = true
  hagree : PQXDH.bobAgreement ikB spk pqsk opk ikAPk ek ct = some keys
  hmsg : tr.at? mh.msg = some (NetE raw)
  hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg
  hver : msg.version = DY.Libsignal.TripleRatchet.messageVersion
  hlow : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey = false
  hcons : DY.Libsignal.TripleRatchet.consumeMessageKey
    (bobRatchetedChain keys msg.ratchetKey spk) msg.counter = some (seed, c')
  hspqr : DY.Spqr.spqrRecv
    (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
      (randTerm tr.length 32)).spqr msg.pqRatchet spqrMsgIdx = some (spqr', key)
  hpqSalt : ((tr.append (RndE 32)).append (NetE key)).at? pqIdx = some (NetE pqSalt)
  hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
    (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
      (randTerm tr.length 32)).peerIk
    (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
      (randTerm tr.length 32)).myIk msg.wire
  hdec : PQXDH.errToOption (DY.SymEnc.symDec
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
    (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m
  hused : ∀ o, opk = some o →
    PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b (DY.DiffieHellman.dhPk o) = false

abbrev BobStartOk.out {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : PQXDH.BobHandshakeOut :=
  bobOut w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys

theorem BobStartOk.next_eq {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) (shown : Nat) :
    (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr =
      bobStartTr tr b a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m := by
  have h := Runs.bobStart w.hik w.hspk w.hpq w.hopk w.hreg w.hek w.hct w.hcan w.hagree w.hmsg
    w.hparse w.hver w.hlow w.hcons w.hspqr w.hpqSalt w.hmac w.hdec w.hused
  unfold Move.next Move.act
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, h.1, h.2]
  dsimp only
  rw [DY.Traceful.run_pure]

theorem rpkT_at?_of_getMessageSentAt {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.getMessageSentAt i = some b) : tr.at? i = some (NetE b) := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h
  rcases hat : (tr.at? i : Option DY.Network.ExecEntryT) with _ | ⟨m⟩
  · rw [hat] at h; cases h
  · rw [hat] at h; injection h with h; subst h; rfl

theorem rpkT_receiveMessage_fst (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, Traceful.run_mk]
  rcases (tr.at? idx : Option DY.Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem rpkT_receiveSignalMsg_some {msgIdx : Nat} {tr : ExecTrace}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).1 = some msg) :
    ∃ t, tr.at? msgIdx = some (NetE t) ∧
      DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg ∧
      msg.version = DY.Libsignal.TripleRatchet.messageVersion := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, rpkT_receiveMessage_fst,
    Symbolic.Swarm.COMPOSED.CompTrace.receiveMessage_snd] at h
  rcases hmsg : tr.getMessageSentAt msgIdx with _ | t
  · rw [hmsg] at h; cases h
  · rw [hmsg] at h; dsimp only at h
    rcases hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg t with _ | m
    · rw [hp, DY.Traceful.run_failure] at h; cases h
    · rw [hp] at h; dsimp only at h
      by_cases hv : m.version = DY.Libsignal.TripleRatchet.messageVersion
      · simp only [_root_.guard, hv, ↓reduceIte, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
          DY.Traceful.run_pure] at h
        injection h with h; subst h; exact ⟨t, rpkT_at?_of_getMessageSentAt hmsg, hp, hv⟩
      · simp only [_root_.guard, hv, ↓reduceIte, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
          DY.Traceful.run_failure] at h; cases h

theorem rpkT_verifyMacAndDecrypt_some {st : DY.Libsignal.TripleRatchet.TRState}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {pqSalt seed ptTerm : DY.Bytes}
    {tr : ExecTrace}
    (h : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).1 =
      some ptTerm) :
    msg.mac = DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some ptTerm := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at h
  by_cases hm : msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [_root_.guard, hm, ↓reduceIte, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
      Traceful.run_pure] at h
    refine ⟨hm, ?_⟩
    dsimp only [liftM, monadLift, MonadLift.monadLift] at h
    rw [DY.Traceful.run_mk] at h
    rcases hdec : DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext with _ | pt <;>
      rw [hdec] at h
    · cases h
    · injection h with h; subst h; rfl
  · simp only [_root_.guard, hm, ↓reduceIte, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
      DY.Traceful.run_failure] at h; cases h

/-- A `bobStart` step with a received plaintext ran successfully. -/
theorem rpkT_bobStart_inv {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {shown : Nat} {pt : DY.Bytes}
    (hpt : receivedPlaintext tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) =
      some pt) :
    Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) := by
  suffices H : ∀ pt', receivedPlaintext tr
      ((DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx).run tr).2.val =
        some pt' → Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) by
    refine H pt ?_
    unfold Move.next Move.act at hpt
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd] at hpt
    rcases hr : ((DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx
      spqrMsgIdx).run tr).1 with _ | n
    · rw [hr] at hpt; exact hpt
    · rw [hr] at hpt; dsimp only at hpt; rw [DY.Traceful.run_pure] at hpt; exact hpt
  have hnone : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (e : E),
      tr.length ≤ t.length → receivedPlaintext tr t = none →
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) = none →
      receivedPlaintext tr (t.append e) = none := by
    intro E _ t e hle h0 hproj
    rw [receivedPlaintext_append_of_proj hle e hproj, h0]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at
    (Inv := fun t => ∀ pt', receivedPlaintext tr t = some pt' →
      Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx))
    b a kh regA mh.ek mh.ct tr (fun pt' h => by rw [receivedPlaintext_self] at h; cases h)
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys hik hspk hpq hopk hreg hek hct hcan
      hagree => ?_
  intro pt' hpt'
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
    Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr)
      mh.msg tr rfl] at hpt'
  rcases hmsg0 : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr).1 with _ | msg
  · rw [hmsg0, receivedPlaintext_self] at hpt'; cases hpt'
  rw [hmsg0] at hpt'; dsimp only at hpt'
  obtain ⟨raw, hmsg, hparse, hver⟩ := rpkT_receiveSignalMsg_some hmsg0
  rcases hlow : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey with _ | _
  swap
  · have hens0 : ((DY.Libsignal.TripleRatchet.ensureReceiverChain
        (bobInitSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey)
        msg.ratchetKey).run tr).1 = none ∧
        ((DY.Libsignal.TripleRatchet.ensureReceiverChain
        (bobInitSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey)
        msg.ratchetKey).run tr).2.val = tr := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
      unfold DY.Libsignal.TripleRatchet.recvChainFor DY.Libsignal.TripleRatchet.findRecvChain
      dsimp only [bobInitSt, List.find?_nil]
      simp only [hlow, ↓reduceIte, DY.Traceful.run_failure]
      exact ⟨trivial, trivial⟩
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd] at hpt'
    erw [hens0.1, hens0.2] at hpt'
    dsimp only at hpt'
    rw [receivedPlaintext_self] at hpt'; cases hpt'
  have hens := Runs.ensureReceiverChain_bobInitSt (tr := tr) (a := a) (ikB := DY.DiffieHellman.dhPk ikB)
    (ikA := ikA) (keys := keys) (sS := spkSk) hlow
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd] at hpt'
  erw [hens.1, hens.2] at hpt'
  dsimp only at hpt'
  have hle1 : tr.length ≤ (tr.append (RndE 32)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hr0 : receivedPlaintext tr (tr.append (RndE 32)) = none :=
    hnone tr _ (Nat.le_refl _) (receivedPlaintext_self tr) rfl
  rcases hcons : DY.Libsignal.TripleRatchet.consumeMessageKey
      (bobRatchetedChain keys msg.ratchetKey spkSk) msg.counter with _ | ⟨seed, c'⟩
  · rw [hcons, DY.Traceful.run_failure, hr0] at hpt'; cases hpt'
  rw [hcons] at hpt'; dsimp only at hpt'
  rcases hsp : DY.Spqr.spqrRecv
      (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey
        (randTerm tr.length 32)).spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · rw [hsp, DY.Traceful.run_failure, hr0] at hpt'; cases hpt'
  rw [hsp] at hpt'; dsimp only at hpt'
  have hk0 : receivedPlaintext tr ((tr.append (RndE 32)).append (NetE key)) = none :=
    hnone _ _ hle1 hr0 rfl
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk] at hpt'
  dsimp only at hpt'
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
    Symbolic.Swarm.COMPOSED.CompTrace.receiveMessage_snd] at hpt'
  rcases hpq0 : ((DY.Network.receiveMessage pqIdx).run
      ((tr.append (RndE 32)).append (NetE key))).1 with _ | pqSalt
  · rw [hpq0, hk0] at hpt'; cases hpt'
  rw [hpq0] at hpt'; dsimp only at hpt'
  rw [rpkT_receiveMessage_fst] at hpq0
  have hpqSalt := rpkT_at?_of_getMessageSentAt hpq0
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
    Symbolic.Swarm.COMPOSED.CompTrace.verifyMacAndDecrypt_trace] at hpt'
  rcases hv0 : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
      (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey
        (randTerm tr.length 32)) msg pqSalt seed).run
      ((tr.append (RndE 32)).append (NetE key))).1 with _ | m
  · rw [hv0, hk0] at hpt'; cases hpt'
  rw [hv0] at hpt'; dsimp only at hpt'
  obtain ⟨hmac, hdec⟩ := rpkT_verifyMacAndDecrypt_some hv0
  have hreg' : tr.at? regA = some (EvE (.IdentityRegistered a ikA vkA honest)) := by
    rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hreg
  rcases opkSk with _ | o
  · refine ⟨(BobStartOk.mk ikB spkSk pqsk ikA vkA ek ct raw spqr' key seed pqSalt m none honest
      keys msg c' hik hspk hpq ?_ hreg' hek hct hcan hagree hmsg hparse hver hlow hcons hsp hpqSalt
      hmac hdec (fun _ h => by cases h) : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)⟩
    rcases hopk with ⟨h1, -⟩ | ⟨idx, o, -, h2, -⟩
    · rw [h1]; trivial
    · cases h2
  · rcases hu : PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b
        (DY.DiffieHellman.dhPk o) with _ | _
    · refine ⟨(BobStartOk.mk ikB spkSk pqsk ikA vkA ek ct raw spqr' key seed pqSalt m (some o)
        honest keys msg c' hik hspk hpq ?_ hreg' hek hct hcan hagree hmsg hparse hver hlow hcons hsp
        hpqSalt hmac hdec (fun o' h => by cases h; exact hu) :
        BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)⟩
      rcases hopk with ⟨-, h2⟩ | ⟨idx, o', h1, h2, h3⟩
      · cases h2
      · cases h2; rw [h1]; exact h3
    · exfalso
      dsimp only [Option.map] at hpt'
      have hg1 : ((PQXDH.guardTrace fun t => !PQXDH.opkUsedB t b
          (DY.DiffieHellman.dhPk o)).run ((tr.append (RndE 32)).append (NetE key))).1 = none := by
        unfold PQXDH.guardTrace; simp [Traceful.run_mk, hu]
      have hg2 : ((PQXDH.guardTrace fun t => !PQXDH.opkUsedB t b
          (DY.DiffieHellman.dhPk o)).run ((tr.append (RndE 32)).append (NetE key))).2.val =
          ((tr.append (RndE 32)).append (NetE key)) := by
        unfold PQXDH.guardTrace; rw [Traceful.run_mk]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hg1, hg2] at hpt'
      dsimp only at hpt'
      rw [hk0] at hpt'; cases hpt'

/-! ## Block visibility inversion -/

theorem rpkT_invisible_vis_nil :
    ∀ (δ : List Move) (tr : ExecTrace), MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hv, _⟩, hδ⟩ => by
    rw [runMoves_cons_snd, hv, rpkT_invisible_vis_nil δ (m.next tr) hδ, List.nil_append]

theorem rpkT_forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], .nil, _, ha => by cases ha
  | x :: _, y :: _, .cons hxy h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self .., hxy⟩
    · obtain ⟨b, hb, hab⟩ := rpkT_forall₂_mem_left h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem rpkT_bobStart_noAccept {tr : ExecTrace} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat}
    {spqrMsgIdx : UInt32} {shown : Nat}
    (hnone : receivedPlaintext tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) =
      none)
    {v : VisEntry} (hv : v ∈ (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr) :
    v.kind ≠ .accept := by
  rw [xpl_vis_eq, List.mem_append] at hv
  rcases hv with hv | hv
  · have hv' := List.mem_of_mem_take hv
    simp only [bobVis, hnone, Option.map_none, Option.toList_none, List.append_nil,
      List.mem_cons, List.mem_map] at hv'
    rcases hv' with rfl | ⟨_, _, rfl⟩ <;> simp [rngEntry]
  · rw [xpl_exposures_kind hv]; simp

theorem rpkT_block_vis {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc : List MachineEvent} {b d pt : HwBytes}
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hne : m.vis (runTraceMoves r (ms₀ ++ pre)) ≠ []) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) [.recv b, .rng d, .accept pt]
      (m.vis (runTraceMoves r (ms₀ ++ pre))) := by
  obtain ⟨_, hs, ⟨_, hanc0⟩, _, _⟩ := hB.run
  have htr : runTraceMoves r (ms₀ ++ pre) = (runMoves pre (runTraceMoves r ms₀)).1 := runTrace_append r ms₀ pre
  have hanc' := xpl_movesAnchored_append_right (ms₀ ++ pre) (m :: post) (setupTrace r)
    (by simpa only [List.append_assoc] using hanc0.1)
  rw [← xpl_runTrace_eq] at hanc'
  have hm := hB.matched
  rw [b5_runMoves_append_snd, rpkT_invisible_vis_nil pre _ hpre, List.nil_append, ← htr] at hm
  have htail : ∀ e ∈ ([.recv b, .rng d, .accept pt] : List MachineEvent).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
  obtain ⟨pre', m', post', heq, hpre', ⟨_, _, hQ⟩, _⟩ := xpl_oneMove_aux (m :: post)
    (runTraceMoves r (ms₀ ++ pre)) _
    (xpl_movesFrom_of _ _ (fun x hx => hs x (by simp [hx])) hanc') hm (List.cons_ne_nil _ _) htail
  cases pre' with
  | nil =>
    cases heq
    simpa [runMoves] using hQ
  | cons x pre'' =>
    cases heq
    exact absurd hpre'.1.1 hne

/-- If `Move.bobStart` follows an `InvisibleNoEffect` prefix in an explanation of
`[.recv b, .rng d, .accept pt]`, it ran successfully (`BobStartOk`) and its visible entries match
the whole block. -/
theorem rpkT_bobStart_block {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {p a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    List.Forall₂ (EventMatchesEntry interpretation r S g) [.recv b, .rng d, .accept pt]
        ((Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown).vis (runTraceMoves r (ms₀ ++ pre))) ∧
      Nonempty (BobStartOk (runTraceMoves r (ms₀ ++ pre)) p a kh regA mh pqIdx spqrMsgIdx) := by
  have hne : (Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown).vis (runTraceMoves r (ms₀ ++ pre)) ≠
      [] := by
    obtain ⟨_, _, ⟨_, hanc0⟩, _, _⟩ := hB.run
    have hanc' := xpl_movesAnchored_append_right (ms₀ ++ pre)
      (Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) (setupTrace r)
      (by simpa only [List.append_assoc] using hanc0.1)
    rw [← xpl_runTrace_eq] at hanc'
    have h1 : 1 ≤ shown := hanc'.1.1
    rw [xpl_vis_eq]
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩
    simp [xpl_ownVis, bobVis]
  have hF := rpkT_block_vis hB hpre hne
  refine ⟨hF, ?_⟩
  rcases hpt : receivedPlaintext (runTraceMoves r (ms₀ ++ pre))
      ((Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown).next (runTraceMoves r (ms₀ ++ pre)))
    with _ | pt'
  · exfalso
    obtain ⟨v, hv, hev⟩ := rpkT_forall₂_mem_left hF (.accept pt) (by simp)
    exact rpkT_bobStart_noAccept hpt hv (xpl_kind_of_matches hev)
  · exact rpkT_bobStart_inv hpt

/-! ## `BobDone` base-key tie -/

def rpkT_bdKey (tr : ExecTrace) (i : Nat) : Option DY.Bytes :=
  match tr.getEventAt PQXDH.PQXDHEvent i with
  | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
  | _ => none

theorem rpkT_bobDoneBaseKeys_eq (tr : ExecTrace) :
    bobDoneBaseKeys tr = (List.range tr.length).filterMap (rpkT_bdKey tr) := rfl

theorem rpkT_bobDoneBaseKeys_append {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E) :
    bobDoneBaseKeys (tr.append x) =
      bobDoneBaseKeys tr ++ (rpkT_bdKey (tr.append x) tr.length).toList := by
  rw [rpkT_bobDoneBaseKeys_eq, rpkT_bobDoneBaseKeys_eq, length_append', List.range_succ,
    List.filterMap_append]
  congr 1
  refine List.filterMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  unfold rpkT_bdKey
  rw [getEventAt_append_lt _ tr x hi]

theorem rpkT_bdKey_append_other {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (hx : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none) :
    rpkT_bdKey (tr.append x) tr.length = none := by
  (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1])
  rw [at?_append_length, hx]

theorem rpkT_bobDoneBaseKeys_append_other {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace)
    (x : E)
    (hx : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none) :
    bobDoneBaseKeys (tr.append x) = bobDoneBaseKeys tr := by
  rw [rpkT_bobDoneBaseKeys_append, rpkT_bdKey_append_other tr x hx, Option.toList_none,
    List.append_nil]

theorem rpkT_bobDoneBaseKeys_append_pq (tr : ExecTrace) (ev : PQXDH.PQXDHEvent) :
    bobDoneBaseKeys (tr.append (EvE ev)) = bobDoneBaseKeys tr ++
      (match ev with
        | .BobDone _ _ _ _ _ _ _ ek _ _ => [ek]
        | _ => []) := by
  rw [rpkT_bobDoneBaseKeys_append]
  congr 1
  (unfold rpkT_bdKey; simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1])
  rw [at?_append_self']
  cases ev <;> rfl

theorem rpkT_logSkippedKeys_bobDoneBaseKeys (L : List DY.Bytes)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (idx : UInt32) (k : Nat),
      Symbolic.Swarm.COMPOSED.CompTrace.Preserves (fun t => bobDoneBaseKeys t = L)
        (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck idx k)
  | _, _, 0 => Symbolic.Swarm.COMPOSED.CompTrace.Preserves.pure ()
  | ck, idx, k + 1 => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    refine Symbolic.Swarm.COMPOSED.CompTrace.Preserves.bind ?_ fun _ =>
      rpkT_logSkippedKeys_bobDoneBaseKeys L s pk rIdx src _ _ k
    intro t ht
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
    rw [rpkT_bobDoneBaseKeys_append_other t _ rfl, ht]

theorem rpkT_bobDoneBaseKeys_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    bobDoneBaseKeys (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) =
      bobDoneBaseKeys tr ++ [o.ek] := by
  have hpre : bobDoneBaseKeys (bobStartPreSkipTr tr b a o msg key) =
      bobDoneBaseKeys tr ++ [o.ek] := by
    unfold bobStartPreSkipTr
    dsimp only
    rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl, rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl, rpkT_bobDoneBaseKeys_append_pq]
    dsimp only
    cases o.opk with
    | none =>
      dsimp only
      rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl, rpkT_bobDoneBaseKeys_append_other _ _ rfl]
    | some opkPk =>
      dsimp only
      rw [rpkT_bobDoneBaseKeys_append_pq, rpkT_bobDoneBaseKeys_append_other _ _ rfl,
        rpkT_bobDoneBaseKeys_append_other _ _ rfl, List.append_nil]
  unfold bobStartTr
  dsimp only
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl, rpkT_bobDoneBaseKeys_append_other _ _ rfl,
    rpkT_bobDoneBaseKeys_append_other _ _ rfl]
  exact rpkT_logSkippedKeys_bobDoneBaseKeys _ _ _ _ _ _ _ _ _ hpre

theorem rpkT_getMessageSentAt_of_at? {tr : ExecTrace} {i : Nat} {x : DY.Bytes}
    (h : tr.at? i = some (NetE x)) : tr.getMessageSentAt i = some x := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  rw [h]

theorem rpkT_bobStart_shown_pos {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {acc blk : List MachineEvent}
    {p a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat}
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) acc blk) :
    1 ≤ shown := by
  obtain ⟨_, _, ⟨_, hanc0⟩, _, _⟩ := hB.run
  have hanc' := xpl_movesAnchored_append_right (ms₀ ++ pre)
    (Move.bobStart p a kh regA mh pqIdx spqrMsgIdx shown :: post) (setupTrace r)
    (by simpa only [List.append_assoc] using hanc0.1)
  exact hanc'.1.1

theorem rpkT_bobStart_gamma {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {p a : Participant} {kh : PQXDH.BobKeyHandles} {regA : Nat}
    {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {k : Nat}
    {b d pt : HwBytes} (w : BobStartOk tr p a kh regA mh pqIdx spqrMsgIdx)
    (hF : List.Forall₂ (EventMatchesEntry interpretation r S g) [.recv b, .rng d, .accept pt]
      ((Move.bobStart p a kh regA mh pqIdx spqrMsgIdx (k + 1)).vis tr))
    {q : Composed.Refinement.PreKeyFields} (hq : parsePreKeyWire b = some q) :
    ecKey (gamma interpretation S g w.ek) = q.baseKey.take 33 := by
  rw [xpl_vis_eq] at hF
  simp only [xpl_ownVis, bobVis, List.take_succ_cons, List.cons_append] at hF
  obtain ⟨⟨_, hrecv⟩, -⟩ := List.forall₂_cons.1 hF
  have hrec : received tr [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
    simp only [received, List.filterMap_cons, List.filterMap_nil,
      rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
      rpkT_getMessageSentAt_of_at? w.hmsg]
  change PreKeyRecvOpkMatches interpretation r S g b
    (received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk p kh tr).toList) at hrecv
  rw [hrec] at hrecv
  have hm : PreKeyRecvMatches interpretation r S g b [w.ek, w.ct, w.raw] := by
    rcases ho : bobOpkPk p kh tr with _ | o <;> rw [ho] at hrecv
    · exact (show PreKeyRecvMatches interpretation r S g b [w.ek, w.ct, w.raw] ∧ OpkNamed r b false
        from hrecv).1
    · exact (show PreKeyRecvMatches interpretation r S g b [w.ek, w.ct, w.raw] ∧ OpkNamed r b true
        from hrecv).1
  obtain ⟨q', hq', hbk, -⟩ := hm
  rw [hq] at hq'
  cases hq'
  exact hbk.symm

/-- Bob's `bobStart` move explaining the accepting block appends one `BobDone` base key `ek` whose
concretized compressed key matches `q.baseKey.take 33`. -/
theorem rpkT_tie_baseKey {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc : List MachineEvent} {b d pt : HwBytes} {q : Composed.Refinement.PreKeyFields}
    (hq : parsePreKeyWire b = some q)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc
      [.recv b, .rng d, .accept pt])
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) (hbs : BobStartBy r.bob m) :
    ∃ ek, bobDoneBaseKeys (runTraceMoves r (ms₀ ++ pre ++ [m])) =
        bobDoneBaseKeys (runTraceMoves r (ms₀ ++ pre)) ++ [ek] ∧
      ecKey (gamma interpretation S g ek) = q.baseKey.take 33 := by
  cases m with
  | bobStart p a kh regA mh pqIdx spqrMsgIdx shown =>
    obtain ⟨hF, ⟨w⟩⟩ := rpkT_bobStart_block hB hpre
    obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by have := rpkT_bobStart_shown_pos hB; omega⟩
    refine ⟨w.ek, ?_, rpkT_bobStart_gamma w hF hq⟩
    rw [runTrace_snoc, w.next_eq]
    exact rpkT_bobDoneBaseKeys_bobStartTr _ _ _ _ _ _ _ _ _ _ _
  | _ => exact False.elim hbs

/-! ## Stored `TRState` snapshot at the end of `bobStartTr` -/

/-- Bob's stored `TRState` snapshot at the end of `bobStartTr`. -/
abbrev rpkR_finalSt {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) : TRState :=
  let st := bobRatchetedSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey
    (randTerm tr.length 32)
  { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv w.c', spqr := w.spqr' }

theorem rpkR_bobStartTr_last {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) :
    ∃ tr₀ : ExecTrace,
      bobStartTr tr b a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m =
        tr₀.append (Symbolic.Swarm.COMPOSED.CompTrace.TRStE b (rpkR_finalSt w)) :=
  ⟨_, rfl⟩

private abbrev StEntryTie :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)
private abbrev TREntryTie := DY.ProtocolEvent.ExecEntryT TREvent

private theorem rpkT_at?_eq_none_of_le {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) {i : Nat}
    (hi : tr.length ≤ i) : (tr.at? i : Option E) = none := by
  have h : ¬ i < tr.length := by omega
  simp only [DY.Trace.at?, h, ↓reduceDIte]

private theorem rpkT_at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append e) i hi (DY.Trace.append_le tr e)]

private theorem rpkT_at?_append_non_entry {E1 E2 : Type} [ExecTraceTypes.Has E1]
    [ExecTraceTypes.Has E2] (tr : ExecTrace) (e : E1)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) = none)
    (i : Nat) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  by_cases hlt : i < tr.length
  · exact rpkT_at?_append_of_lt tr e hlt
  · by_cases heq : i = tr.length
    · subst heq
      rw [at?_append_length, hnone, rpkT_at?_eq_none_of_le tr (Nat.le_refl _)]
    · rw [rpkT_at?_eq_none_of_le (tr.append e)
            (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                  Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
          rpkT_at?_eq_none_of_le tr (by omega)]

private theorem rpkT_logSkippedKeys_len_and_stEntry (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx src ck n k).run tr).2.val.length = tr.length + k ∧
      ∀ i, (((logSkippedKeys s pk rIdx src ck n k).run tr).2.val.at? i : Option StEntryTie) =
        (tr.at? i : Option StEntryTie) := by
  induction k generalizing ck n tr with
  | zero =>
    unfold logSkippedKeys
    rw [DY.Traceful.run_pure]
    exact ⟨(Nat.add_zero _).symm, fun _ => rfl⟩
  | succ k ih =>
    unfold logSkippedKeys
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
    have hlog1 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)).run tr).1 = some () := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure]
    have hlog2 : ((DY.ProtocolEvent.logEvent
        (TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src)).run tr).2.val =
        tr.append (⟨TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src⟩ : TREntryTie) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure]
    rw [hlog1, hlog2]
    dsimp only
    obtain ⟨hlen, hat⟩ := ih (kdfCk ck).1 (n + 1) _
    refine ⟨?_, fun i => ?_⟩
    · rw [hlen]
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    · rw [hat i, rpkT_at?_append_non_entry _ _ rfl]

theorem rpkBH_at?_stEntry_preSkip (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) (i : Nat) :
    ((bobStartPreSkipTr tr b a o msg key).at? i : Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) =
      (tr.at? i : Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) := by
  unfold bobStartPreSkipTr
  dsimp only
  rw [rpkT_at?_append_non_entry _ _ rfl, rpkT_at?_append_non_entry _ _ rfl,
    rpkT_at?_append_non_entry _ _ rfl, rpkT_at?_append_non_entry _ _ rfl]
  cases o.opk with
  | none =>
    dsimp only
    rw [rpkT_at?_append_non_entry _ _ rfl, rpkT_at?_append_non_entry _ _ rfl]
  | some opkPk =>
    dsimp only
    rw [rpkT_at?_append_non_entry _ _ rfl, rpkT_at?_append_non_entry _ _ rfl,
      rpkT_at?_append_non_entry _ _ rfl]

/-- Every `TRStateStoredAt` in `bobStartTr` either comes from `tr` at index `< tr.length` or is the
final snapshot `rpkR_finalSt w`. -/
theorem rpkBH_trStateStoredAt_bobStartTr {tr : ExecTrace} {b a : Participant}
    {kh : PQXDH.BobKeyHandles} {regA : Nat} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx)
    {p : Participant} {st : TRState} {i : Nat}
    (hst : TRStateStoredAt p st i
      (bobStartTr tr b a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m)) :
    (i < tr.length ∧ TRStateStoredAt p st i tr) ∨
      (i = (bobStartPreSkipTr tr b a w.out w.msg w.key).length +
          (w.msg.counter.toNat -
            (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).index.toNat) + 2 ∧
        p = b ∧ st = rpkR_finalSt w) := by
  let c := bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk
  let st_r := bobRatchetedSt a w.out.ikB w.out.ikA w.out.keys w.out.spkSk w.msg.ratchetKey
    (randTerm tr.length 32)
  let tr_hs := bobStartPreSkipTr tr b a w.out w.msg w.key
  let skipped := w.msg.counter.toNat - c.index.toNat
  let childIdx := tr_hs.length + skipped + 2
  let tr_skip := ((logSkippedKeys (st_r.sessionInfo b) w.msg.ratchetKey
    c.rIdx childIdx c.chainKey c.index skipped).run tr_hs).2.val
  let tr_recv := tr_skip.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
    (.Received b st_r.peer w.msg.ratchetKey w.msg.counter w.m))
  let tr_mk := tr_recv.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
    (.MessageKey (st_r.sessionInfo b) .receiver w.seed w.pqSalt w.msg.counter c.rIdx
      childIdx))
  obtain ⟨hlen_skip, hat_skip⟩ := rpkT_logSkippedKeys_len_and_stEntry (st_r.sessionInfo b)
    w.msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr_hs
  have hlen_skip' : tr_skip.length = tr_hs.length + skipped := hlen_skip
  have hlen_mk : tr_mk.length = childIdx := by
    simp only [tr_mk, tr_recv, childIdx, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  change ((tr_mk.append (Symbolic.Swarm.COMPOSED.CompTrace.TRStE b (rpkR_finalSt w))).at? i :
    Option StEntryTie) = some ⟨⟨p, st⟩⟩ at hst
  by_cases hlt : i < tr_mk.length
  · left
    rw [rpkT_at?_append_of_lt tr_mk _ hlt] at hst
    dsimp only [tr_mk, tr_recv] at hst
    rw [rpkT_at?_append_non_entry _ _ rfl, rpkT_at?_append_non_entry _ _ rfl] at hst
    dsimp only [tr_skip] at hst
    rw [hat_skip i, rpkBH_at?_stEntry_preSkip] at hst
    have hi_tr : i < tr.length := by
      have := DY.Trace.at?_eq_some_implies_length_le (EntryT := StEntryTie) tr i
      rwa [hst] at this
    exact ⟨hi_tr, hst⟩
  · by_cases heq : i = tr_mk.length
    · right
      rw [heq, DY.Trace.at?_append] at hst
      injection hst with h1; injection h1 with h2; injection h2 with hp hst_eq
      exact ⟨heq.trans hlen_mk, hp.symm, hst_eq.symm⟩
    · rw [rpkT_at?_eq_none_of_le _
            (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                  Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hst
      cases hst

end Symbolic.Swarm.CREF
