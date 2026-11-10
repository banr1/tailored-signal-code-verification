/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompPcsClosed
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
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
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
# Composed DH-Share Origin Invariant

Proves preservation of `CompDhsOriginInv` across all transitions of `Composed.reachability`
(`compDhsOriginInv_reachable`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain KeyComponent createChain kdfCk findRecvChain
  setRecvChain recvChainFor consumeMessageKey x25519LowOrder maxReceiverChains u32Max computeMac)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  BobHandshakeOut pqxdhKdf serializedIk bobAgreement guardTrace opkUsedB registerIdentity
  registerCorruptIdentity genSignedPrekey genPQPrekey genOneTimePrekey compromiseIK compromiseSPK
  compromisePQSPK compromiseOPK breakDH breakKEM invertDH invertKEM)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg trMsgKeys spqrA2B spqrB2A
  parseTrSignalMsg receiveSignalMsg ensureReceiverChain dhRatchetStep logSkippedKeys
  logMessageKeyAndStore skippedKeyUsedB receiverKeyUsedB messageEncrypt messageEncryptAbort
  messageDecrypt messageDecryptSkipped exposeKey exposeSpqr exposeSkipped traceLength)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompTrace

open CompDhsHelpers

/-- `true` on `TREvent` constructors that do not affect `IsCompDhsOf` or `SkippedKeyStored`. -/
def isTrInert (ev : TREvent) : Bool :=
  match ev with
  | .HonestDH _ _ _ | .ExposedDHs _ _ _ | .SkippedKeyStored _ _ _ _ _ _ => false
  | _ => true

theorem isCompDhsOf_append_tr_inertB {tr : ExecTrace} {ev : TREvent}
    (hinert : isTrInert ev = true)
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append (TREvE ev)) dhs s rIdx) : IsCompDhsOf tr dhs s rIdx :=
  isCompDhsOf_append_tr_inert
    (fun _ _ _ heq => by subst heq; cases hinert)
    (fun _ _ _ heq => by subst heq; cases hinert)
    h

theorem CompDhsOriginInv.append_tr_inert {tr : ExecTrace} {ev : TREvent}
    (hinert : isTrInert ev = true)
    (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (TREvE ev)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_tr_inertB hinert h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => by
      rcases (eventLogged_append_same_iff (tr := tr) (ev₀ := ev)).mp h with h₀ | heq
      · exact .inl h₀
      · subst heq; cases hinert)
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_trEv tr ev b).mp h))

theorem CompDhsOriginInv.append_skippedKeyStored {tr : ExecTrace}
    (s : SessionInfo) (pk : Bytes) (n : UInt32) (ck : Bytes) (rIdx src : Nat)
    (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (TREvE (.SkippedKeyStored s pk n (kdfCk ck).2 rIdx src))) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_tr_inert (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun s' pk' n' seed' rIdx' src' h => by
      rcases (eventLogged_append_same_iff (tr := tr)).mp h with h₀ | heq
      · exact .inl h₀
      · injection heq with _ _ _ hseed _ _
        subst hseed
        exact .inr (.kdf _ _))
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_trEv tr _ b).mp h))

theorem CompDhsOriginInv.append_exposedDHs {tr : ExecTrace}
    {s₀ : SessionInfo} {dhs₀ : Bytes} {r₀ : Nat}
    (hex : IsCompDhsOf tr dhs₀ s₀ r₀) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (TREvE (.ExposedDHs s₀ dhs₀ r₀))) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_exposedDHs hex h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => by
      rcases (eventLogged_append_same_iff (tr := tr)).mp h with h₀ | heq
      · exact .inl h₀
      · cases heq)
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_trEv tr _ b).mp h))

theorem CompDhsOriginInv.append_trSt_existing {tr : ExecTrace}
    {me : Participant} {st₀ : TRState}
    (hdhs₀ : IsCompDhsOf tr st₀.dhs (st₀.sessionInfo me) st₀.rIdx)
    (hst₀ : TRStateClosed (tr.append (TRStE me st₀)) st₀)
    (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (TRStE me st₀)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun dhs s rIdx h => by
      rcases isCompDhsOf_append_trSt h with h₀ | ⟨rfl, rfl, rfl⟩
      · exact h₀
      · exact hdhs₀)
    (fun p st idx h => by
      rcases trStateStoredAt_append_same h with ⟨_, h₀⟩ | ⟨_, rfl, rfl⟩
      · exact .inl h₀
      · exact .inr hst₀)
    (fun _ _ _ _ _ _ h => .inl ((eventLogged_append_other_iff rfl).mp h))
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_trSt tr me st₀ b).mp h))

private theorem brokenDHB_eq_true_imp_eventLogged {tr : ExecTrace}
    (h : DY.Libsignal.PQXDH.brokenDHB tr = true) :
    tr.EventLogged PQXDHEvent.BrokenDH := by
  unfold DY.Libsignal.PQXDH.brokenDHB at h; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h
  rw [List.any_eq_true] at h
  obtain ⟨i, _, hi⟩ := h
  rcases hat : (tr.at? i : Option PQXDHEntry) with _ | ⟨⟨ev⟩⟩
  · rw [hat] at hi; cases hi
  · rw [hat] at hi; dsimp only at hi
    cases ev with
    | BrokenDH => exact ⟨i, by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact hat⟩
    | _ => cases hi

private theorem run_failure_end {Inv : ExecTrace → Prop} {α : Type} {tr : ExecTrace}
    (h : Inv tr) : Inv ((failure : Traceful α).run tr).2.val := by
  rw [Traceful.run_failure]; exact h

private theorem run_failure_at {Inv : ExecTrace → Prop} {α β : Type} {f : α → Traceful β}
    {tr : ExecTrace} (h : Inv tr) : Inv ((failure >>= f).run tr).2.val := by
  rw [Traceful.run_bind, Traceful.run_failure]; exact h

private theorem run_pure_end {Inv : ExecTrace → Prop} {α : Type} {a : α} {tr : ExecTrace}
    (h : Inv tr) : Inv ((pure a : Traceful α).run tr).2.val := by
  rw [Traceful.run_pure]; exact h

private theorem logEvent_run_eq {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev).run tr).1 = some () ∧
    ((ProtocolEvent.logEvent ev).run tr).2.val =
      tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact ⟨trivial, trivial⟩

private theorem run_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev) {tr : ExecTrace}
    (hf : Inv (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev))) :
    Inv ((ProtocolEvent.logEvent ev).run tr).2.val := by
  rw [(logEvent_run_eq ev tr).2]; exact hf

private theorem run_bind_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {α : Type} (ev : Ev)
    {f : Unit → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f ()).run (tr.append ({ ev := ev } : ProtocolEvent.ExecEntryT Ev))).2.val) :
    Inv ((ProtocolEvent.logEvent ev >>= f).run tr).2.val := by
  rw [run_bind_snd, (logEvent_run_eq ev tr).1, (logEvent_run_eq ev tr).2]
  exact hf

private theorem run_sendMessage {Inv : ExecTrace → Prop} (msg : Bytes) {tr : ExecTrace}
    (hf : Inv (tr.append (NetE msg))) :
    Inv ((Network.sendMessage msg).run tr).2.val := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_mk]
  exact hf

private theorem run_storeLocalState {Inv : ExecTrace → Prop} {St : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT St)]
    (p : Participant) (st : St) {tr : ExecTrace}
    (hf : Inv (tr.append (PersistentGlobalState.State.ExecEntryT.mk
      ({ participant := p, state := st } : PersistentLocalState.LocalState St)))) :
    Inv ((PersistentLocalState.storeLocalState p st).run tr).2.val := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hf

private theorem run_bind_storeLocalState {Inv : ExecTrace → Prop} {St : Type}
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT St)] {α : Type}
    (p : Participant) (st : St) {f : Nat → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f tr.length).run (tr.append (PersistentGlobalState.State.ExecEntryT.mk
      ({ participant := p, state := st } : PersistentLocalState.LocalState St)))).2.val) :
    Inv ((PersistentLocalState.storeLocalState p st >>= f).run tr).2.val := by
  rw [run_bind_snd, Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hf

private theorem run_bind_traceLength {Inv : ExecTrace → Prop} {α : Type}
    {f : Nat → Traceful α} {tr : ExecTrace}
    (hf : Inv ((f tr.length).run tr).2.val) :
    Inv ((traceLength >>= f).run tr).2.val := by
  unfold traceLength; rw [run_bind_snd, Traceful.run_mk]; exact hf

private theorem run_logMessageKeyAndStore {Inv : ExecTrace → Prop}
    (me : Participant) (s : SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx parIdx : Nat) (st' : TRState)
    {tr : ExecTrace}
    (hf : Inv ((tr.append (TREvE (.MessageKey s dir seed pqSalt n rIdx parIdx))).append (TRStE me st'))) :
    Inv ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parIdx st').run tr).2.val := by
  unfold logMessageKeyAndStore
  exact run_bind_logEvent _ (run_storeLocalState me st' hf)

private theorem run_bind_logMessageKeyAndStore {Inv : ExecTrace → Prop} {α : Type}
    (me : Participant) (s : SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : Bytes) (n : UInt32) (rIdx parIdx : Nat) (st' : TRState)
    {f : Nat → Traceful α} {tr : ExecTrace}
    (hf : let tr₁ := tr.append (TREvE (.MessageKey s dir seed pqSalt n rIdx parIdx))
      Inv ((f tr₁.length).run (tr₁.append (TRStE me st'))).2.val) :
    Inv ((logMessageKeyAndStore me s dir seed pqSalt n rIdx parIdx st' >>= f).run tr).2.val := by
  unfold logMessageKeyAndStore
  rw [run_bind_assoc_snd]
  exact run_bind_logEvent _ (run_bind_storeLocalState _ st' hf)

private theorem bind_guardOnTrace_at {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv ((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val := by
  rw [run_bind_snd, guardOnTrace_snd]
  unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; exact hInv

private theorem bobAgreement_eq_some_imp_pqxdhKdf
    {ikB spk pqsk : Bytes} {opk : Option Bytes} {ikA ek ct : Bytes} {keys : HandshakeKeys}
    (h : bobAgreement ikB spk pqsk opk ikA ek ct = some keys) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  unfold bobAgreement at h
  change some (pqxdhKdf _) = some keys at h
  injection h with h'
  exact ⟨_, h'.symm⟩

private theorem consumeMessageKey_chainKey_closed {tr : ExecTrace} {c c' : RecvChain}
    {counter : UInt32} {seed : Bytes}
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    CompPcsClosed tr c'.chainKey := by
  unfold consumeMessageKey at hcons
  split at hcons; · cases hcons
  · split at hcons; · cases hcons
    · split at hcons; · cases hcons
      · cases hcons
        exact .kdf _ _

private theorem setRecvChain_closed {tr : ExecTrace} {recv : List RecvChain} {c' : RecvChain}
    (hrecv : ∀ x ∈ recv, CompPcsClosed tr x.chainKey)
    (hc' : CompPcsClosed tr c'.chainKey) :
    ∀ x ∈ setRecvChain recv c', CompPcsClosed tr x.chainKey := by
  intro x hx
  unfold setRecvChain at hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  split
  · exact hc'
  · exact hrecv y hy

private theorem bind_receiveSignalMsg_pcs {Inv : ExecTrace → Prop} {α : Type}
    (msgH : Nat) {f : TRSignalMsg → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hbase : ∀ b, tr.BaseAttackerKnows b → CompPcsClosed tr b)
    (hf : ∀ msg, CompPcsClosed tr msg.pqRatchet → Inv ((f msg).run tr).2.val) :
    Inv ((receiveSignalMsg msgH >>= f).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [run_bind_assoc_snd]
  refine bind_receiveMessage_at msgH tr hInv fun raw hraw _ => ?_
  rcases hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw with _ | msg
  · exact run_failure_at hInv
  · dsimp only
    rw [run_bind_assoc_snd]
    refine bind_guardP_at _ tr hInv fun _ => ?_
    rw [run_pure_bind_snd]
    exact hf msg (CompPcsClosed.parseTrSignalMsg_fields (hbase raw hraw.baseAttackerKnows) hp).2.2.2.2

private theorem bind_ensureReceiverChain_pcs {Inv : ExecTrace → Prop} {α : Type}
    (st₀ : TRState) (pk : Bytes) (tr₀ : ExecTrace) (hInv₀ : Inv tr₀)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hf_hit : ∀ c, findRecvChain st₀.recv pk = some c →
      Inv (((f (st₀, c, false)).run tr₀).2.val))
    (hf_miss :
      findRecvChain st₀.recv pk = none →
      x25519LowOrder pk = false →
      let dhs' := mkRand tr₀.length 32
      let rk1 := (createChain st₀.rk pk st₀.dhs).1
      let ckr := (createChain st₀.rk pk st₀.dhs).2
      let rk2 := (createChain rk1 pk dhs').1
      let cks := (createChain rk1 pk dhs').2
      let c : RecvChain := { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := st₀.rIdx + 2 }
      let st : TRState := {
        st₀ with rk := rk2, dhs := dhs', cks := cks, ns := 0,
                 pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
                 recv := (st₀.recv ++ [c]).drop ((st₀.recv.length + 1) - maxReceiverChains) }
      Inv (((f (st, c, true)).run (tr₀.append (RndE 32))).2.val)) :
    Inv (((ensureReceiverChain st₀ pk >>= f).run tr₀).2.val) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  cases hfind : findRecvChain st₀.recv pk with
  | some c =>
    dsimp only; rw [run_pure_bind_snd]
    exact hf_hit c hfind
  | none =>
    dsimp only
    by_cases hlo : x25519LowOrder pk = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]; exact run_failure_at hInv₀
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
      have hlo' : (!x25519LowOrder pk) = true := by cases h : x25519LowOrder pk <;> simp_all
      have hlo_f : x25519LowOrder pk = false := by cases h : x25519LowOrder pk <;> simp_all
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
      simp only [run_bind_assoc_snd, run_pure_bind_snd, run_genRand_bind_snd]
      exact hf_miss hfind hlo_f

private theorem Preserves.pcs_registerIdentity (p : Participant) :
    Preserves CompDhsOriginInv (registerIdentity p) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine run_bind_guardOnTrace _ tr₀ hInv₀ ?_
  refine run_bind_genRand 32 tr₀ ?_
  let ik := mkRand tr₀.length 32
  let tr₁ := tr₀.append (RndE 32)
  have hInv₁ := hInv₀.append_rnd 32
  have hik₁ : CompPcsClosed tr₁ ik := hInv₀.fresh_rand_closed 32
  let evId := PQXDHEvent.IdentityRegistered p (dhPk ik) (DY.Signature.vk ik) true
  let tr₂ := tr₁.append (PQEvE evId)
  have hInv₂ := hInv₁.append_pqEv evId
  have hik₂ : CompPcsClosed tr₂ ik := hik₁.mono_append_other rfl rfl
  let tr₃ := tr₂.append (NetE (dhPk ik))
  have hInv₃ := hInv₂.append_net (.dhPk ik)
  have hik₃ : CompPcsClosed tr₃ ik := hik₂.mono_append_other rfl rfl
  let tr₄ := tr₃.append (NetE (DY.Signature.vk ik))
  have hInv₄ := hInv₃.append_net (.vk ik)
  have hik₄ : CompPcsClosed tr₄ ik := hik₃.mono_append_other rfl rfl
  refine run_bind_logEvent evId ?_
  refine run_bind_sendMessage (dhPk ik) tr₂ ?_
  refine run_bind_sendMessage (DY.Signature.vk ik) tr₃ ?_
  exact run_storeLocalState p _
    (hInv₄.append_pqSt p { kind := .identity, sk := ik } hik₄)

private theorem Preserves.pcs_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves CompDhsOriginInv (registerCorruptIdentity p skIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine run_bind_guardOnTrace _ tr₀ hInv₀ ?_
  exact run_bind_receiveMessage skIdx tr₀ hInv₀ fun _ =>
    run_bind_logEvent _ (run_logEvent _ ((hInv₀.append_pqEv _).append_pqEv _))

private theorem Preserves.pcs_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompDhsOriginInv (genSignedPrekey b idStateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine bind_getKey_at b idStateIdx .identity tr₀ hInv₀ fun ik _ => ?_
  refine run_bind_genRand 32 tr₀ ?_
  let spk := mkRand tr₀.length 32
  let tr₁ := tr₀.append (RndE 32)
  have hInv₁ := hInv₀.append_rnd 32
  have hspk₁ : CompPcsClosed tr₁ spk := hInv₀.fresh_rand_closed 32
  refine run_bind_genRand 64 tr₁ ?_
  let tr₂ := tr₁.append (RndE 64)
  have hInv₂ := hInv₁.append_rnd 64
  have hspk₂ : CompPcsClosed tr₂ spk := hspk₁.mono_append_other rfl rfl
  let evSpk := PQXDHEvent.SignedPrekeyPublished b (dhPk spk)
  let tr₃ := tr₂.append (PQEvE evSpk)
  have hInv₃ := hInv₂.append_pqEv evSpk
  have hspk₃ : CompPcsClosed tr₃ spk := hspk₂.mono_append_other rfl rfl
  let tr₄ := tr₃.append (PQStE b { kind := .signedPrekey, sk := spk })
  have hInv₄ := hInv₃.append_pqSt b { kind := .signedPrekey, sk := spk } hspk₃
  let tr₅ := tr₄.append (NetE (dhPk spk))
  have hInv₅ := hInv₄.append_net (.dhPk spk)
  refine run_bind_logEvent evSpk ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage (dhPk spk) tr₄ ?_
  refine run_bind_sendMessage _ tr₅ ?_
  exact run_pure_end (hInv₅.append_net (.sign _ _ _))

private theorem Preserves.pcs_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompDhsOriginInv (genPQPrekey b idStateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine bind_getKey_at b idStateIdx .identity tr₀ hInv₀ fun ik _ => ?_
  refine run_bind_genRand 64 tr₀ ?_
  let pqsk := mkRand tr₀.length 64
  let tr₁ := tr₀.append (RndE 64)
  have hInv₁ := hInv₀.append_rnd 64
  have hpqsk₁ : CompPcsClosed tr₁ pqsk := hInv₀.fresh_rand_closed 64
  refine run_bind_genRand 64 tr₁ ?_
  let tr₂ := tr₁.append (RndE 64)
  have hInv₂ := hInv₁.append_rnd 64
  have hpqsk₂ : CompPcsClosed tr₂ pqsk := hpqsk₁.mono_append_other rfl rfl
  let evPq := PQXDHEvent.PQPrekeyPublished b (PQKem.kemPk pqsk)
  let tr₃ := tr₂.append (PQEvE evPq)
  have hInv₃ := hInv₂.append_pqEv evPq
  have hpqsk₃ : CompPcsClosed tr₃ pqsk := hpqsk₂.mono_append_other rfl rfl
  let tr₄ := tr₃.append (PQStE b { kind := .pqPrekey, sk := pqsk })
  have hInv₄ := hInv₃.append_pqSt b { kind := .pqPrekey, sk := pqsk } hpqsk₃
  have hpqsk₄ : CompPcsClosed tr₄ pqsk := hpqsk₃.mono_append_other rfl rfl
  let tr₅ := tr₄.append (NetE (PQKem.kemPk pqsk))
  have hInv₅ := hInv₄.append_net_of (.kemPk hpqsk₄)
  refine run_bind_logEvent evPq ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage (PQKem.kemPk pqsk) tr₄ ?_
  refine run_bind_sendMessage _ tr₅ ?_
  exact run_pure_end (hInv₅.append_net (.sign _ _ _))

private theorem Preserves.pcs_genOneTimePrekey (b : Participant) :
    Preserves CompDhsOriginInv (genOneTimePrekey b) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine run_bind_genRand 32 tr₀ ?_
  let opk := mkRand tr₀.length 32
  let tr₁ := tr₀.append (RndE 32)
  have hInv₁ := hInv₀.append_rnd 32
  have hopk₁ : CompPcsClosed tr₁ opk := hInv₀.fresh_rand_closed 32
  let evOpk := PQXDHEvent.OneTimePrekeyPublished b (dhPk opk)
  let tr₂ := tr₁.append (PQEvE evOpk)
  have hInv₂ := hInv₁.append_pqEv evOpk
  have hopk₂ : CompPcsClosed tr₂ opk := hopk₁.mono_append_other rfl rfl
  let tr₃ := tr₂.append (PQStE b { kind := .oneTimePrekey, sk := opk })
  have hInv₃ := hInv₂.append_pqSt b { kind := .oneTimePrekey, sk := opk } hopk₂
  refine run_bind_logEvent evOpk ?_
  refine run_bind_storeLocalState b _ ?_
  refine run_bind_sendMessage (dhPk opk) tr₃ ?_
  exact run_pure_end (hInv₃.append_net (.dhPk _))

private theorem Preserves.pcs_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves CompDhsOriginInv (compromiseIK p stateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.compromiseIK
  refine bind_getKey_at p stateIdx .identity tr₀ hInv₀ fun ik hst => ?_
  have hik : CompPcsClosed tr₀ ik := hInv₀.pqxSt_ok p _ stateIdx hst
  exact run_bind_logEvent _ (run_sendMessage _
    ((hInv₀.append_pqEv _).append_net_of (hik.mono_append_other rfl rfl)))

private theorem Preserves.pcs_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompDhsOriginInv (compromiseSPK b stateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr₀ hInv₀ fun spk hst => ?_
  have hspk : CompPcsClosed tr₀ spk := hInv₀.pqxSt_ok b _ stateIdx hst
  exact run_bind_logEvent _ (run_sendMessage _
    ((hInv₀.append_pqEv _).append_net_of (hspk.mono_append_other rfl rfl)))

private theorem Preserves.pcs_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompDhsOriginInv (compromisePQSPK b stateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr₀ hInv₀ fun pqsk hst => ?_
  have hpqsk : CompPcsClosed tr₀ pqsk := hInv₀.pqxSt_ok b _ stateIdx hst
  exact run_bind_logEvent _ (run_sendMessage _
    ((hInv₀.append_pqEv _).append_net_of (hpqsk.mono_append_other rfl rfl)))

private theorem Preserves.pcs_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves CompDhsOriginInv (compromiseOPK b stateIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr₀ hInv₀ fun opk hst => ?_
  refine bind_guardOnTrace_at (fun tr => !DY.Libsignal.PQXDH.opkUsedB tr b (DY.DiffieHellman.dhPk opk)) tr₀ hInv₀ fun _ => ?_
  have hopk : CompPcsClosed tr₀ opk := hInv₀.pqxSt_ok b _ stateIdx hst
  exact run_bind_logEvent _ (run_sendMessage _
    ((hInv₀.append_pqEv _).append_net_of (hopk.mono_append_other rfl rfl)))

private theorem Preserves.pcs_breakDH : Preserves CompDhsOriginInv breakDH := by
  intro _ hInv; unfold DY.Libsignal.PQXDH.breakDH; exact run_logEvent _ (hInv.append_pqEv _)

private theorem Preserves.pcs_breakKEM : Preserves CompDhsOriginInv breakKEM := by
  intro _ hInv; unfold DY.Libsignal.PQXDH.breakKEM; exact run_logEvent _ (hInv.append_pqEv _)

private theorem Preserves.pcs_invertDH (pkIdx : Nat) :
    Preserves CompDhsOriginInv (invertDH pkIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.invertDH
  refine bind_guardOnTrace_at DY.Libsignal.PQXDH.brokenDHB tr₀ hInv₀ fun hbrkB => ?_
  have hbrk : tr₀.EventLogged PQXDHEvent.BrokenDH := brokenDHB_eq_true_imp_eventLogged hbrkB
  refine run_bind_receiveMessage pkIdx tr₀ hInv₀ fun pk => ?_
  rcases DY.Libsignal.PQXDH.extractDhSecretKey (DY.X25519.normalizeX25519Key pk) with _ | sk
  · dsimp only; exact run_failure_end hInv₀
  · dsimp only; exact run_sendMessage sk (hInv₀.append_net_of (.brokenDH hbrk sk))

private theorem Preserves.pcs_invertKEM (pkIdx : Nat) :
    Preserves CompDhsOriginInv (invertKEM pkIdx) := by
  intro tr₀ hInv₀
  unfold DY.Libsignal.PQXDH.invertKEM
  refine run_bind_guardOnTrace DY.Libsignal.PQXDH.brokenKEMB tr₀ hInv₀ ?_
  refine bind_receiveMessage_at pkIdx tr₀ hInv₀ fun pk hpk _ => ?_
  rcases hinv : PQKem.invertKemPublicKey pk with _ | sk
  · dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
    rw [run_bind_snd, Traceful.run_mk]
    exact hInv₀
  · have heq : pk = PQKem.kemPk sk := kemPkInvert_eq_some_iff.mp hinv
    have hpk_closed : CompPcsClosed tr₀ (PQKem.kemPk sk) :=
      heq ▸ hInv₀.base_ok pk hpk.baseAttackerKnows
    dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
    rw [run_bind_snd, Traceful.run_mk]
    exact run_sendMessage sk (hInv₀.append_net_of (CompPcsClosed.inv_kemPk hpk_closed))

private theorem Preserves.pcs_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves CompDhsOriginInv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind
    (fun _ hInv => by
      simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact hInv.append_rnd 32)
    fun _ => Preserves.failure

private theorem Preserves.pcs_exposeKey (me : Participant) (stH : Nat) (kc : KeyComponent) :
    Preserves CompDhsOriginInv (exposeKey me stH kc) := by
  unfold exposeKey
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  obtain ⟨_, hrk, hcks, hrecv, _⟩ := hInv₀.trSt_ok me st stH hst₀
  cases kc with
  | rk =>
    dsimp only
    let tr₁ := tr₀.append (TREvE (.ExposedRK (st.sessionInfo me) st.rk st.rIdx))
    have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_tr_inert rfl
    have hrk₁ : CompPcsClosed tr₁ st.rk :=
      hrk.mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
        .inl (isCompDhsOf_append_tr_inertB rfl h)
    exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hrk₁))
  | cks =>
    dsimp only
    let tr₁ := tr₀.append (TREvE (.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx))
    have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_tr_inert rfl
    have hcks₁ : CompPcsClosed tr₁ st.cks :=
      hcks.mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
        .inl (isCompDhsOf_append_tr_inertB rfl h)
    exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hcks₁))
  | ckr pk =>
    dsimp only
    cases hfind : findRecvChain st.recv pk with
    | none => dsimp only; exact run_failure_end hInv₀
    | some c =>
      dsimp only
      have hc : c ∈ st.recv := (findRecvChain_some hfind).1
      let tr₁ := tr₀.append (TREvE (.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
      have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_tr_inert rfl
      have hck₁ : CompPcsClosed tr₁ c.chainKey :=
        (hrecv c hc).mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
          .inl (isCompDhsOf_append_tr_inertB rfl h)
      exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hck₁))
  | dhs =>
    dsimp only
    have hdhs₀ : IsCompDhsOf tr₀ st.dhs (st.sessionInfo me) st.rIdx :=
      .inl ⟨st, stH, hst₀, rfl, rfl, rfl⟩
    obtain ⟨t, hrnd, hdhs_eq⟩ := hInv₀.dhs_rand _ _ _ hdhs₀
    let tr₁ := tr₀.append (TREvE (.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx))
    have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_exposedDHs hdhs₀
    have hexp₁ : tr₁.EventLogged (TREvent.ExposedDHs (st.sessionInfo me) (mkRand t 32) st.rIdx) :=
      hdhs_eq ▸ eventLogged_here tr₀ (TREvent.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
    have hdhs₁ : CompPcsClosed tr₁ st.dhs :=
      hdhs_eq ▸ .rand ⟨randAt_mono (Trace.append_le tr₀ _) hrnd,
        .inr (.inl ⟨st.sessionInfo me, st.rIdx, hexp₁⟩)⟩
    exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hdhs₁))

private theorem Preserves.pcs_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves CompDhsOriginInv (exposeSpqr me stH) := by
  unfold exposeSpqr
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hspqr := (hInv₀.trSt_ok me st stH hst₀).2.2.2.2
  let tr₁ := tr₀.append (TREvE (.ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx))
  have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_tr_inert rfl
  have hspqr₁ : CompPcsClosed tr₁ st.spqr :=
    hspqr.mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
      .inl (isCompDhsOf_append_tr_inertB rfl h)
  exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hspqr₁))

private theorem Preserves.pcs_exposeSkipped (idx : Nat) :
    Preserves CompDhsOriginInv (exposeSkipped idx) := by
  unfold exposeSkipped; intro tr₀ hInv₀
  refine bind_getEntry_tr_eq idx tr₀ hInv₀ fun ev hev => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only
    have hseed := hInv₀.skipped_ok s pk n seed rIdx src hev
    refine run_bind_guardTrace (fun tr => !receiverKeyUsedB tr s seed n rIdx) tr₀ hInv₀ ?_
    let tr₁ := tr₀.append (TREvE (.ExposedMK s seed n rIdx))
    have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_tr_inert rfl
    have hseed₁ : CompPcsClosed tr₁ seed :=
      hseed.mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
        .inl (isCompDhsOf_append_tr_inertB rfl h)
    exact run_bind_logEvent _ (run_sendMessage _ (hInv₁.append_net_of hseed₁))
  | _ => dsimp only; exact run_failure_end hInv₀

private theorem Preserves.pcs_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : BundleHandles) :
    Preserves CompDhsOriginInv (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr₀ hInv₀ (hInv₀.append_rnd 32)
    fun ikA ikB vkB spk spkSig pqpk pqpkSig opk honest _ _ _ _ _ _ _ _ _ _ _ => ?_
  let o := aliceOut tr₀ ikA ikB spk pqpk opk
  let tr₁ := (tr₀.append (RndE 32)).append (RndE 32)
  have hInv₁ : CompDhsOriginInv tr₁ := (hInv₀.append_rnd 32).append_rnd 32
  refine run_bind_genRand 32 tr₁ ?_
  let dhsA := mkRand tr₁.length 32
  let tr₂ := tr₁.append (RndE 32)
  refine run_bind_sendMessage o.ek tr₂ ?_
  let tr₃ := tr₂.append (NetE o.ek)
  refine run_bind_sendMessage o.ct tr₃ ?_
  let tr₄ := tr₃.append (NetE o.ct)
  let doneIdx := tr₄.length
  let evAlice := PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys
  let tr₅ := tr₄.append (PQEvE evAlice)
  let evInit := TREvent.InitSession a b (dhPk dhsA) o.spk
  let tr₆ := tr₅.append (TREvE evInit)
  let stA : TRState := {
    peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
    rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
    cks := (createChain o.keys.rk o.spk dhsA).2,
    ns := 0, pn := 0, sid := Concat.concat (dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit o.keys.pqr spqrA2B }
  let tr₇ := tr₆.append (CEvE (.HandshakeSession (stA.sessionInfo a) doneIdx))
  let tr₈ := tr₇.append (TRStE a stA)
  refine run_bind_traceLength ?_
  refine run_bind_logEvent evAlice ?_
  refine run_bind_logEvent evInit ?_
  refine run_bind_logEvent (ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx) ?_
  refine run_storeLocalState a stA ?_
  change CompDhsOriginInv tr₈
  have hle₂₈ : tr₂ ≤ tr₈ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₂ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₃ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₄ _)
          (Trace.le_trans _ _ _ (Trace.append_le tr₅ _)
            (Trace.le_trans _ _ _ (Trace.append_le tr₆ _) (Trace.append_le tr₇ _)))))
  have hle₁₈ : tr₁ ≤ tr₈ := Trace.le_trans _ _ _ (Trace.append_le tr₁ _) hle₂₈
  have hrnd₈ : RandAt tr₈ tr₁.length 32 := randAt_mono hle₂₈ (randAt_here tr₁ 32)
  refine hInv₁.preserve_fresh hle₁₈ tr₁.length (stA.sessionInfo a) 1 (Nat.le_refl _) hrnd₈
    (fun dhs s rIdx h => ?_) (fun p st idx h => ?_) (fun s pk n seed rIdx src h => ?_)
    (fun p st idx h => ?_) (fun msg h => ?_)
  · rcases isCompDhsOf_append_trSt h with h₇ | ⟨rfl, rfl, rfl⟩
    · have h₆ := isCompDhsOf_append_other rfl rfl h₇
      have h₅ := isCompDhsOf_append_tr_inertB rfl h₆
      have h₄ := isCompDhsOf_append_other rfl rfl h₅
      have h₃ := isCompDhsOf_append_other rfl rfl h₄
      have h₂ := isCompDhsOf_append_other rfl rfl h₃
      exact .inl (isCompDhsOf_append_other rfl rfl h₂)
    · exact .inr ⟨rfl, rfl, rfl⟩
  · rcases trStateStoredAt_append_same h with ⟨_, h₇⟩ | ⟨_, rfl, rfl⟩
    · have h₆ := trStateStoredAt_append_other rfl h₇
      have h₅ := trStateStoredAt_append_other rfl h₆
      have h₄ := trStateStoredAt_append_other rfl h₅
      have h₃ := trStateStoredAt_append_other rfl h₄
      have h₂ := trStateStoredAt_append_other rfl h₃
      exact .inl (trStateStoredAt_append_other rfl h₂)
    · refine .inr ⟨Nat.le_refl 1, .kdf _ _, .kdf _ _, fun c hc => ?_, .spqrInit (.kdf _ _) (.literal _)⟩
      dsimp [stA] at hc
      rw [List.mem_singleton] at hc
      subst hc
      exact .kdf _ _
  · have h₇ := (eventLogged_append_other_iff (tr := tr₇) rfl).mp h
    have h₆ := (eventLogged_append_other_iff (tr := tr₆) rfl).mp h₇
    rcases (eventLogged_append_same_iff (tr := tr₅) (ev₀ := evInit)).mp h₆ with h₅ | heq
    · have h₄ := (eventLogged_append_other_iff (tr := tr₄) rfl).mp h₅
      have h₃ := (eventLogged_append_other_iff (tr := tr₃) rfl).mp h₄
      have h₂ := (eventLogged_append_other_iff (tr := tr₂) rfl).mp h₃
      exact .inl ((eventLogged_append_other_iff (tr := tr₁) rfl).mp h₂)
    · nomatch heq
  · have h₇ := pqxdhStoredAt_append_other rfl h
    have h₆ := pqxdhStoredAt_append_other rfl h₇
    have h₅ := pqxdhStoredAt_append_other rfl h₆
    have h₄ := pqxdhStoredAt_append_other rfl h₅
    have h₃ := pqxdhStoredAt_append_other rfl h₄
    have h₂ := pqxdhStoredAt_append_other rfl h₃
    exact .inl (pqxdhStoredAt_append_other rfl h₂)
  · have h₇ := (baseAttackerKnows_append_trSt tr₇ a stA msg).mp h
    have h₆ := (baseAttackerKnows_append_cEv tr₆ _ msg).mp h₇
    have h₅ := (baseAttackerKnows_append_trEv tr₅ _ msg).mp h₆
    have h₄ := (baseAttackerKnows_append_pqEv tr₄ _ msg).mp h₅
    rcases (baseAttackerKnows_append_net tr₃ o.ct msg).mp h₄ with rfl | h₃
    · exact .inr (.kemEncap _ _)
    · rcases (baseAttackerKnows_append_net tr₂ o.ek msg).mp h₃ with rfl | h₂
      · exact .inr (.dhPk _)
      · exact .inl ((baseAttackerKnows_append_rnd tr₁ 32 msg).mp h₂)

private theorem Preserves.pcs_messageEncrypt (me : Participant) (stH coinsSz pqIdx : Nat) :
    Preserves CompDhsOriginInv (messageEncrypt me stH coinsSz pqIdx) := by
  unfold messageEncrypt
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hdhs₀ : IsCompDhsOf tr₀ st.dhs (st.sessionInfo me) st.rIdx :=
    .inl ⟨st, stH, hst₀, rfl, rfl, rfl⟩
  have hst_closed₀ : TRStateClosed tr₀ st := hInv₀.trSt_ok me st stH hst₀
  refine bind_guardP_at (st.ns ≠ u32Max) tr₀ hInv₀ fun _ => ?_
  refine run_bind_genRand 32 tr₀ ?_
  let m := mkRand tr₀.length 32
  let tr₁ := tr₀.append (RndE 32)
  have hInv₁ := hInv₀.append_rnd 32
  have hm₁ : CompPcsClosed tr₁ m := hInv₀.fresh_rand_closed 32
  refine run_bind_genRand coinsSz tr₁ ?_
  let coins := mkRand tr₁.length coinsSz
  let tr₂ := tr₁.append (RndE coinsSz)
  have hInv₂ := hInv₁.append_rnd coinsSz
  have hm₂ : CompPcsClosed tr₂ m := hm₁.mono_append_other rfl rfl
  have hcoins₂ : CompPcsClosed tr₂ coins := hInv₁.fresh_rand_closed coinsSz
  let key := (Spqr.spqrSend st.spqr coins).2.1
  refine run_bind_sendMessage key tr₂ ?_
  let tr₃ := tr₂.append (NetE key)
  have hInv₃ : CompDhsOriginInv tr₃ := hInv₂.append_net (CompPcsClosed.spqrSendKey_of st.spqr coins)
  have hm₃ : CompPcsClosed tr₃ m := hm₂.mono_append_other rfl rfl
  have hcoins₃ : CompPcsClosed tr₃ coins := hcoins₂.mono_append_other rfl rfl
  refine run_bind_receiveMessage pqIdx tr₃ hInv₃ fun pqSalt => ?_
  let evSent := TREvent.Sent me st.peer (dhPk st.dhs) st.ns m
  let tr₄ := tr₃.append (TREvE evSent)
  have hInv₄ : CompDhsOriginInv tr₄ := hInv₃.append_tr_inert rfl
  let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1,
                                 spqr := (Spqr.spqrSend st.spqr coins).1 }
  let evMK := TREvent.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt
    st.ns st.rIdx stH
  let tr₅ := tr₄.append (TREvE evMK)
  have hInv₅ : CompDhsOriginInv tr₅ := hInv₄.append_tr_inert rfl
  let tr₆ := tr₅.append (TRStE me st')
  have hle₀₅ : tr₀ ≤ tr₅ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₀ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₂ _)
          (Trace.le_trans _ _ _ (Trace.append_le tr₃ _) (Trace.append_le tr₄ _))))
  have hle₀₆ : tr₀ ≤ tr₆ := Trace.le_trans _ _ _ hle₀₅ (Trace.append_le tr₅ _)
  have hle₃₆ : tr₃ ≤ tr₆ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₃ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₄ _) (Trace.append_le tr₅ _))
  have hdhs_same₃₆ : ∀ dhs s rIdx, IsCompDhsOf tr₆ dhs s rIdx → IsCompDhsOf tr₃ dhs s rIdx := by
    intro dhs s rIdx h
    rcases isCompDhsOf_append_trSt h with h₅ | ⟨rfl, rfl, rfl⟩
    · have h₄ := isCompDhsOf_append_tr_inertB rfl h₅
      exact isCompDhsOf_append_tr_inertB rfl h₄
    · exact hdhs₀.mono (Trace.le_trans _ _ _ (Trace.append_le tr₀ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.append_le tr₂ _)))
  have hdhs_same₀₆ : ∀ dhs s rIdx, IsCompDhsOf tr₆ dhs s rIdx → IsCompDhsOf tr₀ dhs s rIdx := by
    intro dhs s rIdx h
    have h₃ := hdhs_same₃₆ dhs s rIdx h
    have h₂ := isCompDhsOf_append_other rfl rfl h₃
    have h₁ := isCompDhsOf_append_other rfl rfl h₂
    exact isCompDhsOf_append_other rfl rfl h₁
  have hst₀_₆ : TRStateClosed tr₆ st :=
    hst_closed₀.mono_of_fresh hle₀₆ fun dhs s rIdx h => .inl (hdhs_same₀₆ dhs s rIdx h)
  have hcoins₆ : CompPcsClosed tr₆ coins :=
    hcoins₃.mono_of_fresh hle₃₆ fun dhs s rIdx h => .inl (hdhs_same₃₆ dhs s rIdx h)
  have hm₆ : CompPcsClosed tr₆ m :=
    hm₃.mono_of_fresh hle₃₆ fun dhs s rIdx h => .inl (hdhs_same₃₆ dhs s rIdx h)
  have hst'₆ : TRStateClosed tr₆ st' :=
    ⟨hst₀_₆.1, hst₀_₆.2.1, .kdf _ _, hst₀_₆.2.2.2.1,
     .spqrSendState hst₀_₆.2.2.2.2 hcoins₆⟩
  have hInv₆ : CompDhsOriginInv tr₆ :=
    hInv₅.append_trSt_existing (hdhs₀.mono hle₀₅) hst'₆
  let keys := trMsgKeys pqSalt (kdfCk st.cks).2
  let pqMsg := (Spqr.spqrSend st.spqr coins).2.2
  let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (DY.SymEnc.symEnc keys.cipherKey keys.iv m) pqMsg
  let mac := DY.Libsignal.TripleRatchet.computeMac keys.macKey st.myIk st.peerIk wire
  have hwire₆ : CompPcsClosed tr₆ wire :=
    .trWireMsg (.dhPk _) (.symEnc hm₆) (.spqrSendMsg _ _)
  have hmac₆ : CompPcsClosed tr₆ mac := .trunc8 _
  refine run_bind_logEvent evSent ?_
  refine run_bind_logMessageKeyAndStore _ _ _ _ _ _ _ _ _ ?_
  exact run_sendMessage _ (hInv₆.append_net_of (.concat hwire₆ hmac₆))

private theorem Preserves.pcs_logSkippedKeys (s : SessionInfo) (pk : Bytes) (rIdx origIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat),
      Preserves CompDhsOriginInv (logSkippedKeys s pk rIdx origIdx ck n k)
  | _, _, 0, _, hInv => by unfold logSkippedKeys; exact run_pure_end hInv
  | ck, n, k + 1, tr, hInv => by
    unfold logSkippedKeys
    exact run_bind_logEvent _ (Preserves.pcs_logSkippedKeys s pk rIdx origIdx (kdfCk ck).1 (n + 1) k
      (tr.append (TREvE (.SkippedKeyStored s pk n (kdfCk ck).2 rIdx origIdx)))
      (hInv.append_skippedKeyStored s pk n ck rIdx origIdx))

private theorem logSkippedKeys_isCompDhsOf (s : SessionInfo) (pk : Bytes) (rIdx origIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      let tr' := ((logSkippedKeys s pk rIdx origIdx ck n k).run tr).2.val
      tr ≤ tr' ∧ (∀ dhs s' r', IsCompDhsOf tr' dhs s' r' → IsCompDhsOf tr dhs s' r')
  | _, _, 0, tr => by
    dsimp only; unfold logSkippedKeys; rw [Traceful.run_pure]
    exact ⟨Trace.le_refl tr, fun _ _ _ h => h⟩
  | ck, n, k + 1, tr => by
    dsimp only; unfold logSkippedKeys
    rw [run_bind_snd, (logEvent_run_eq _ _).1, (logEvent_run_eq _ _).2]
    dsimp only
    let tr₁ := tr.append (TREvE (.SkippedKeyStored s pk n (kdfCk ck).2 rIdx origIdx))
    obtain ⟨hle₁, hdhs₁⟩ := logSkippedKeys_isCompDhsOf s pk rIdx origIdx (kdfCk ck).1 (n + 1) k tr₁
    refine ⟨Trace.le_trans _ _ _ (Trace.append_le tr _) hle₁, fun dhs s' r' h => ?_⟩
    exact isCompDhsOf_append_tr_inert (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (hdhs₁ dhs s' r' h)

private theorem pcs_decrypt_tail (me : Participant) (origIdx parIdx : Nat)
    (msg : TRSignalMsg) (st : TRState) (c c' : RecvChain) (seed pqSalt m spqr' : Bytes)
    (tr : ExecTrace)
    (hInv : CompDhsOriginInv tr)
    (hdhs : IsCompDhsOf tr st.dhs (st.sessionInfo me) st.rIdx)
    (hrIdx_pos : 1 ≤ st.rIdx)
    (hrk : CompPcsClosed tr st.rk)
    (hcks : CompPcsClosed tr st.cks)
    (hrecv : ∀ x ∈ st.recv, CompPcsClosed tr x.chainKey)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr' : CompPcsClosed tr spqr') :
    CompDhsOriginInv ((do
      logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx origIdx c.chainKey c.index
        (msg.counter.toNat - c.index.toNat)
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx parIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val := by
  let skipped := msg.counter.toNat - c.index.toNat
  let stOut : TRState := { st with recv := setRecvChain st.recv c', spqr := spqr' }
  obtain ⟨hfst_sk, _, _, _, _⟩ :=
    logSkippedKeys_spec (st.sessionInfo me) msg.ratchetKey c.rIdx origIdx c.chainKey
      c.chainKey c.index skipped tr ⟨0, rfl⟩
  rw [run_bind_snd, hfst_sk]
  dsimp only
  let tr_sk := ((logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx origIdx c.chainKey c.index
      skipped).run tr).2.val
  have hInv_sk : CompDhsOriginInv tr_sk :=
    Preserves.pcs_logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx origIdx c.chainKey c.index
      skipped tr hInv
  obtain ⟨hle_sk, hdhs_sk⟩ :=
    logSkippedKeys_isCompDhsOf (st.sessionInfo me) msg.ratchetKey c.rIdx origIdx c.chainKey c.index
      skipped tr
  let evRec := TREvent.Received me st.peer msg.ratchetKey msg.counter m
  let tr_rec := tr_sk.append (TREvE evRec)
  have hInv_rec : CompDhsOriginInv tr_rec := hInv_sk.append_tr_inert rfl
  let evMK := TREvent.MessageKey (st.sessionInfo me) .receiver seed pqSalt msg.counter
    c.rIdx parIdx
  let tr_mk := tr_rec.append (TREvE evMK)
  have hInv_mk : CompDhsOriginInv tr_mk := hInv_rec.append_tr_inert rfl
  let tr_final := tr_mk.append (TRStE me stOut)
  have hle_mk : tr ≤ tr_mk :=
    Trace.le_trans _ _ _ hle_sk
      (Trace.le_trans _ _ _ (Trace.append_le tr_sk _) (Trace.append_le tr_rec _))
  have hle_final : tr ≤ tr_final := Trace.le_trans _ _ _ hle_mk (Trace.append_le tr_mk _)
  have hdhs_mk : IsCompDhsOf tr_mk stOut.dhs (stOut.sessionInfo me) stOut.rIdx :=
    hdhs.mono hle_mk
  have hfresh_final : ∀ dhs s' r', IsCompDhsOf tr_final dhs s' r' →
      IsCompDhsOf tr dhs s' r' ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz := by
    intro dhs s' r' h
    rcases isCompDhsOf_append_trSt h with h_mk | ⟨rfl, rfl, rfl⟩
    · have h_rec := isCompDhsOf_append_tr_inertB rfl h_mk
      have h_sk := isCompDhsOf_append_tr_inertB rfl h_rec
      exact .inl (hdhs_sk dhs s' r' h_sk)
    · exact .inl hdhs
  have hstOut_closed : TRStateClosed tr_final stOut :=
    ⟨hrIdx_pos,
     hrk.mono_of_fresh hle_final hfresh_final,
     hcks.mono_of_fresh hle_final hfresh_final,
     setRecvChain_closed (fun x hx => (hrecv x hx).mono_of_fresh hle_final hfresh_final)
       (consumeMessageKey_chainKey_closed hcons),
     hspqr'.mono_of_fresh hle_final hfresh_final⟩
  refine run_bind_logEvent evRec ?_
  exact run_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
    (hInv_mk.append_trSt_existing hdhs_mk hstOut_closed)

private theorem Preserves.pcs_bobStart (b a : Participant) (kh : BobKeyHandles)
    (regIdxA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompDhsOriginInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr₀ hInv₀
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys _ _ _ _ _ _ _ _ hagree => ?_
  obtain ⟨ikm, rfl⟩ := bobAgreement_eq_some_imp_pqxdhKdf hagree
  let o : BobHandshakeOut := {
    ikB := dhPk ikB, ikA, spk := dhPk spkSk, pqpk := PQKem.kemPk pqsk,
    opk := opkSk.map dhPk, ek, ct, spkSk, keys := pqxdhKdf ikm }
  refine bind_receiveSignalMsg_pcs mh.msg tr₀ hInv₀ hInv₀.base_ok fun msg hpq₀ => ?_
  let st0 : TRState := {
    peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
    dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit o.keys.pqr spqrB2A }
  refine bind_ensureReceiverChain_empty st0 msg.ratchetKey tr₀ rfl rfl rfl hInv₀ ?_
  dsimp only
  let dhs' := mkRand tr₀.length 32
  let rk1 := (createChain o.keys.rk msg.ratchetKey o.spkSk).1
  let ckr := (createChain o.keys.rk msg.ratchetKey o.spkSk).2
  let rk2 := (createChain rk1 msg.ratchetKey dhs').1
  let cks := (createChain rk1 msg.ratchetKey dhs').2
  let c : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := 2 }
  let st : TRState := { st0 with rk := rk2, dhs := dhs', cks := cks, ns := 0, pn := 0,
                                 rIdx := 2, recv := [c] }
  let tr₁ := tr₀.append (RndE 32)
  have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_rnd 32
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; exact run_failure_end hInv₁
  · dsimp only
    rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact run_failure_end hInv₁
    · dsimp only
      refine run_bind_sendMessage key tr₁ ?_
      let tr₂ := tr₁.append (NetE key)
      have hInv₂ : CompDhsOriginInv tr₂ := hInv₁.append_net (CompPcsClosed.spqrRecvKey_of hspqr)
      refine run_bind_receiveMessage pqIdx tr₂ hInv₂ fun pqSalt => ?_
      refine run_bind_verifyMacAndDecrypt st msg pqSalt seed tr₂ hInv₂ fun m => ?_
      have hCommit : ∀ tr₃ : ExecTrace,
          tr₂ ≤ tr₃ →
          (∀ dhs s' r', IsCompDhsOf tr₃ dhs s' r' → IsCompDhsOf tr₂ dhs s' r') →
          (∀ p st' idx, StateStoredAt p st' idx tr₃ → StateStoredAt p st' idx tr₂) →
          (∀ s' pk' n' seed' rIdx' src',
            tr₃.EventLogged (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') →
            tr₂.EventLogged (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src')) →
          (∀ p st' idx, PQXDHStoredAt tr₃ p st' idx → PQXDHStoredAt tr₂ p st' idx) →
          (∀ b', tr₃.BaseAttackerKnows b' → tr₂.BaseAttackerKnows b') →
          CompDhsOriginInv ((do
            let doneIdx ← traceLength
            ProtocolEvent.logEvent (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
            if true = true then
              ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs))
              ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let skipped := msg.counter.toNat - c.index.toNat
            let childIdx := (← traceLength) + skipped + 2
            logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
            ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx childIdx
              { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr₃).2.val := by
        intro tr₃ hle₂₃ hdhs₂₃ hst₂₃ hsk₂₃ hpqx₂₃ hbase₂₃
        let doneIdx := tr₃.length
        let evBob := PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys
        let tr₄ := tr₃.append (PQEvE evBob)
        let evDH := TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs)
        let tr₅ := tr₄.append (TREvE evDH)
        let evHon := TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)
        let tr₆ := tr₅.append (TREvE evHon)
        let tr₇ := tr₆.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
        have hle₁₇ : tr₁ ≤ tr₇ :=
          Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
            (Trace.le_trans _ _ _ hle₂₃
              (Trace.le_trans _ _ _ (Trace.append_le tr₃ _)
                (Trace.le_trans _ _ _ (Trace.append_le tr₄ _)
                  (Trace.le_trans _ _ _ (Trace.append_le tr₅ _) (Trace.append_le tr₆ _)))))
        have hle₀₇ : tr₀ ≤ tr₇ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) hle₁₇
        have hrnd₇ : RandAt tr₇ tr₀.length 32 := randAt_mono hle₁₇ (randAt_here tr₀ 32)
        have hdhs₀₇ : ∀ dhs s' r', IsCompDhsOf tr₇ dhs s' r' →
            IsCompDhsOf tr₀ dhs s' r' ∨ (dhs = mkRand tr₀.length 32 ∧ s' = st.sessionInfo b ∧ r' = 2) := by
          intro dhs s' r' h
          have h₆ := isCompDhsOf_append_other rfl rfl h
          rcases isCompDhsOf_append_honestDH h₆ with h₅ | ⟨rfl, rfl, rfl⟩
          · have h₄ := isCompDhsOf_append_tr_inertB rfl h₅
            have h₃ := isCompDhsOf_append_other rfl rfl h₄
            have h₂ := hdhs₂₃ dhs s' r' h₃
            have h₁ := isCompDhsOf_append_other rfl rfl h₂
            exact .inl (isCompDhsOf_append_other rfl rfl h₁)
          · exact .inr ⟨rfl, rfl, rfl⟩
        have hInv₇ : CompDhsOriginInv tr₇ :=
          hInv₀.preserve_fresh hle₀₇ tr₀.length (st.sessionInfo b) 2 (Nat.le_refl _) hrnd₇ hdhs₀₇
            (fun p st' idx h => by
              have h₆ := trStateStoredAt_append_other rfl h
              have h₅ := trStateStoredAt_append_other rfl h₆
              have h₄ := trStateStoredAt_append_other rfl h₅
              have h₃ := trStateStoredAt_append_other rfl h₄
              have h₂ := hst₂₃ p st' idx h₃
              have h₁ := trStateStoredAt_append_other rfl h₂
              exact .inl (trStateStoredAt_append_other rfl h₁))
            (fun s' pk' n' seed' rIdx' src' h => by
              have h₆ := (eventLogged_append_other_iff (tr := tr₆) rfl).mp h
              rcases (eventLogged_append_same_iff (tr := tr₅) (ev₀ := evHon)).mp h₆ with h₅ | heq
              · rcases (eventLogged_append_same_iff (tr := tr₄) (ev₀ := evDH)).mp h₅ with h₄ | heq
                · have h₃ := (eventLogged_append_other_iff (tr := tr₃) rfl).mp h₄
                  have h₂ := hsk₂₃ s' pk' n' seed' rIdx' src' h₃
                  have h₁ := (eventLogged_append_other_iff (tr := tr₁) rfl).mp h₂
                  exact .inl ((eventLogged_append_other_iff (tr := tr₀) rfl).mp h₁)
                · nomatch heq
              · nomatch heq)
            (fun p st' idx h => by
              have h₆ := pqxdhStoredAt_append_other rfl h
              have h₅ := pqxdhStoredAt_append_other rfl h₆
              have h₄ := pqxdhStoredAt_append_other rfl h₅
              have h₃ := pqxdhStoredAt_append_other rfl h₄
              have h₂ := hpqx₂₃ p st' idx h₃
              have h₁ := pqxdhStoredAt_append_other rfl h₂
              exact .inl (pqxdhStoredAt_append_other rfl h₁))
            (fun b' h => by
              have h₆ := (baseAttackerKnows_append_cEv tr₆ _ b').mp h
              have h₅ := (baseAttackerKnows_append_trEv tr₅ _ b').mp h₆
              have h₄ := (baseAttackerKnows_append_trEv tr₄ _ b').mp h₅
              have h₃ := (baseAttackerKnows_append_pqEv tr₃ _ b').mp h₄
              have h₂ := hbase₂₃ b' h₃
              rcases (baseAttackerKnows_append_net tr₁ key b').mp h₂ with rfl | h₁
              · exact .inr (CompPcsClosed.spqrRecvKey_of hspqr)
              · exact .inl ((baseAttackerKnows_append_rnd tr₀ 32 b').mp h₁))
        have hfresh₀₇ : ∀ dhs s' r', IsCompDhsOf tr₇ dhs s' r' →
            IsCompDhsOf tr₀ dhs s' r' ∨ ∀ t < tr₀.length, ∀ sz, dhs ≠ mkRand t sz := by
          intro dhs s' r' h
          rcases hdhs₀₇ dhs s' r' h with h₀ | ⟨rfl, _, _⟩
          · exact .inl h₀
          · refine .inr fun t hlt sz heq => ?_
            obtain ⟨rfl, _⟩ := mkRand_inj heq
            omega
        have hpq₇ : CompPcsClosed tr₇ msg.pqRatchet := hpq₀.mono_of_fresh hle₀₇ hfresh₀₇
        have hspqr'₇ : CompPcsClosed tr₇ spqr' :=
          CompPcsClosed.spqrRecvState_of hspqr (.spqrInit (.kdf _ _) (.literal _)) hpq₇
        have hdhs₇ : IsCompDhsOf tr₇ st.dhs (st.sessionInfo b) st.rIdx :=
          .inr (.inl ⟨0, eventLogged_mono (Trace.append_le tr₆ _) (eventLogged_here tr₅ evHon), rfl⟩)
        refine run_bind_traceLength ?_
        refine run_bind_logEvent evBob ?_
        simp only [↓reduceIte]
        refine run_bind_logEvent evDH ?_
        refine run_bind_logEvent evHon ?_
        refine run_bind_logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx) ?_
        refine run_bind_traceLength ?_
        exact pcs_decrypt_tail b
          (tr₇.length + (msg.counter.toNat - c.index.toNat) + 2)
          (tr₇.length + (msg.counter.toNat - c.index.toNat) + 2)
          msg st c c' seed pqSalt m spqr' tr₇ hInv₇ hdhs₇
          (Nat.le_add_left 1 1) (.kdf _ _) (.kdf _ _)
          (fun x hx => by dsimp [st] at hx; rw [List.mem_singleton] at hx; subst hx; exact .kdf _ _)
          hcons hspqr'₇
      rcases opkSk with _ | opk_sk
      · exact hCommit tr₂ (Trace.le_refl _) (fun _ _ _ h => h) (fun _ _ _ h => h)
          (fun _ _ _ _ _ _ h => h) (fun _ _ _ h => h) (fun _ h => h)
      · refine run_bind_guardOnTrace (fun tr => !opkUsedB tr b (dhPk opk_sk)) tr₂ hInv₂ ?_
        refine run_bind_logEvent (PQXDHEvent.OPKUsed b (dhPk opk_sk)) ?_
        exact hCommit (tr₂.append (PQEvE (.OPKUsed b (dhPk opk_sk))))
          (Trace.append_le tr₂ _)
          (fun _ _ _ h => isCompDhsOf_append_other rfl rfl h)
          (fun _ _ _ h => trStateStoredAt_append_other rfl h)
          (fun _ _ _ _ _ _ h => (eventLogged_append_other_iff rfl).mp h)
          (fun _ _ _ h => pqxdhStoredAt_append_other rfl h)
          (fun b' h => (baseAttackerKnows_append_pqEv tr₂ _ b').mp h)

private theorem Preserves.pcs_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat)
    (spqrMsgIdx : UInt32) :
    Preserves CompDhsOriginInv (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  have hdhs₀ : IsCompDhsOf tr₀ st₀.dhs (st₀.sessionInfo me) st₀.rIdx :=
    .inl ⟨st₀, stH, hst₀, rfl, rfl, rfl⟩
  have hst₀_closed : TRStateClosed tr₀ st₀ := hInv₀.trSt_ok me st₀ stH hst₀
  refine bind_receiveSignalMsg_pcs msgH tr₀ hInv₀ hInv₀.base_ok fun msg hpq₀ => ?_
  refine bind_ensureReceiverChain_pcs st₀ msg.ratchetKey tr₀ hInv₀
    (fun c _ => ?_) (fun _ _ => ?_)
  · dsimp only
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only; exact run_failure_end hInv₀
    · dsimp only
      rcases hspqr : Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only; exact run_failure_end hInv₀
      · dsimp only
        refine run_bind_sendMessage key tr₀ ?_
        let tr₁ := tr₀.append (NetE key)
        have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_net (CompPcsClosed.spqrRecvKey_of hspqr)
        refine run_bind_receiveMessage pqIdx tr₁ hInv₁ fun pqSalt => ?_
        refine run_bind_verifyMacAndDecrypt st₀ msg pqSalt seed tr₁ hInv₁ fun m => ?_
        have hst₀_₁ : TRStateClosed tr₁ st₀ :=
          hst₀_closed.mono_of_fresh (Trace.append_le tr₀ _) fun _ _ _ h =>
            .inl (isCompDhsOf_append_other rfl rfl h)
        have hpq₁ : CompPcsClosed tr₁ msg.pqRatchet := hpq₀.mono_append_other rfl rfl
        have hspqr'₁ : CompPcsClosed tr₁ spqr' :=
          CompPcsClosed.spqrRecvState_of hspqr hst₀_₁.2.2.2.2 hpq₁
        exact pcs_decrypt_tail me stH stH msg st₀ c c' seed pqSalt m spqr' tr₁ hInv₁
          (hdhs₀.mono (Trace.append_le tr₀ _))
          hst₀_₁.1 hst₀_₁.2.1 hst₀_₁.2.2.1 hst₀_₁.2.2.2.1 hcons hspqr'₁
  · dsimp only
    let dhs' := mkRand tr₀.length 32
    let rk1 := (createChain st₀.rk msg.ratchetKey st₀.dhs).1
    let ckr := (createChain st₀.rk msg.ratchetKey st₀.dhs).2
    let rk2 := (createChain rk1 msg.ratchetKey dhs').1
    let cks := (createChain rk1 msg.ratchetKey dhs').2
    let c : RecvChain :=
      { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := {
      st₀ with rk := rk2, dhs := dhs', cks := cks, ns := 0,
               pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
               recv := (st₀.recv ++ [c]).drop ((st₀.recv.length + 1) - maxReceiverChains) }
    let tr₁ := tr₀.append (RndE 32)
    have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_rnd 32
    rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
    · dsimp only; exact run_failure_end hInv₁
    · dsimp only
      rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
      · dsimp only; exact run_failure_end hInv₁
      · dsimp only
        refine run_bind_sendMessage key tr₁ ?_
        let tr₂ := tr₁.append (NetE key)
        have hInv₂ : CompDhsOriginInv tr₂ := hInv₁.append_net (CompPcsClosed.spqrRecvKey_of hspqr)
        refine run_bind_receiveMessage pqIdx tr₂ hInv₂ fun pqSalt => ?_
        refine run_bind_verifyMacAndDecrypt st msg pqSalt seed tr₂ hInv₂ fun m => ?_
        let evDH := TREvent.DHRatchet me st.peer msg.ratchetKey (dhPk st.dhs)
        let tr₃ := tr₂.append (TREvE evDH)
        let evHon := TREvent.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2)
        let tr₄ := tr₃.append (TREvE evHon)
        have hle₁₄ : tr₁ ≤ tr₄ :=
          Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
            (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _))
        have hle₀₄ : tr₀ ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) hle₁₄
        have hrnd₄ : RandAt tr₄ tr₀.length 32 := randAt_mono hle₁₄ (randAt_here tr₀ 32)
        have hrIdx_eq : (st.rIdx - 2) + 2 = st.rIdx := by dsimp [st]; omega
        have hdhs₀₄ : ∀ dhs s' r', IsCompDhsOf tr₄ dhs s' r' →
            IsCompDhsOf tr₀ dhs s' r' ∨
            (dhs = mkRand tr₀.length 32 ∧ s' = st.sessionInfo me ∧ r' = st.rIdx) := by
          intro dhs s' r' h
          rcases isCompDhsOf_append_honestDH h with h₃ | ⟨rfl, rfl, rfl⟩
          · have h₂ := isCompDhsOf_append_tr_inertB rfl h₃
            have h₁ := isCompDhsOf_append_other rfl rfl h₂
            exact .inl (isCompDhsOf_append_other rfl rfl h₁)
          · exact .inr ⟨rfl, rfl, hrIdx_eq⟩
        have hInv₄ : CompDhsOriginInv tr₄ :=
          hInv₀.preserve_fresh hle₀₄ tr₀.length (st.sessionInfo me) st.rIdx (Nat.le_refl _) hrnd₄ hdhs₀₄
            (fun p st' idx h => by
              have h₃ := trStateStoredAt_append_other rfl h
              have h₂ := trStateStoredAt_append_other rfl h₃
              have h₁ := trStateStoredAt_append_other rfl h₂
              exact .inl (trStateStoredAt_append_other rfl h₁))
            (fun s' pk' n' seed' rIdx' src' h => by
              rcases (eventLogged_append_same_iff (tr := tr₃) (ev₀ := evHon)).mp h with h₃ | heq
              · rcases (eventLogged_append_same_iff (tr := tr₂) (ev₀ := evDH)).mp h₃ with h₂ | heq
                · have h₁ := (eventLogged_append_other_iff (tr := tr₁) rfl).mp h₂
                  exact .inl ((eventLogged_append_other_iff (tr := tr₀) rfl).mp h₁)
                · nomatch heq
              · nomatch heq)
            (fun p st' idx h => by
              have h₃ := pqxdhStoredAt_append_other rfl h
              have h₂ := pqxdhStoredAt_append_other rfl h₃
              have h₁ := pqxdhStoredAt_append_other rfl h₂
              exact .inl (pqxdhStoredAt_append_other rfl h₁))
            (fun b' h => by
              have h₃ := (baseAttackerKnows_append_trEv tr₃ _ b').mp h
              have h₂ := (baseAttackerKnows_append_trEv tr₂ _ b').mp h₃
              rcases (baseAttackerKnows_append_net tr₁ key b').mp h₂ with rfl | h₁
              · exact .inr (CompPcsClosed.spqrRecvKey_of hspqr)
              · exact .inl ((baseAttackerKnows_append_rnd tr₀ 32 b').mp h₁))
        have hfresh₀₄ : ∀ dhs s' r', IsCompDhsOf tr₄ dhs s' r' →
            IsCompDhsOf tr₀ dhs s' r' ∨ ∀ t < tr₀.length, ∀ sz, dhs ≠ mkRand t sz := by
          intro dhs s' r' h
          rcases hdhs₀₄ dhs s' r' h with h₀ | ⟨rfl, _, _⟩
          · exact .inl h₀
          · refine .inr fun t hlt sz heq => ?_
            obtain ⟨rfl, _⟩ := mkRand_inj heq
            omega
        have hst₀_₄ : TRStateClosed tr₄ st₀ := hst₀_closed.mono_of_fresh hle₀₄ hfresh₀₄
        have hpq₄ : CompPcsClosed tr₄ msg.pqRatchet := hpq₀.mono_of_fresh hle₀₄ hfresh₀₄
        have hspqr'₄ : CompPcsClosed tr₄ spqr' :=
          CompPcsClosed.spqrRecvState_of hspqr hst₀_₄.2.2.2.2 hpq₄
        have hdhs₄ : IsCompDhsOf tr₄ st.dhs (st.sessionInfo me) st.rIdx :=
          .inr (.inl ⟨st.rIdx - 2, eventLogged_here tr₃ evHon, hrIdx_eq.symm⟩)
        simp only [↓reduceIte]
        refine run_bind_logEvent evDH ?_
        refine run_bind_logEvent evHon ?_
        exact pcs_decrypt_tail me stH stH msg st c c' seed pqSalt m spqr' tr₄ hInv₄ hdhs₄
          (by dsimp [st]; omega) (.kdf _ _) (.kdf _ _)
          (fun x hx => by
            dsimp [st] at hx
            rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hx' | hx'
            · exact hst₀_₄.2.2.2.1 x hx'
            · rw [List.mem_singleton] at hx'; subst hx'; exact .kdf _ _)
          hcons hspqr'₄

private theorem Preserves.pcs_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompDhsOriginInv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold messageDecryptSkipped
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hdhs₀ : IsCompDhsOf tr₀ st.dhs (st.sessionInfo me) st.rIdx :=
    .inl ⟨st, stH, hst₀, rfl, rfl, rfl⟩
  have hst_closed₀ : TRStateClosed tr₀ st := hInv₀.trSt_ok me st stH hst₀
  refine bind_receiveSignalMsg_pcs msgH tr₀ hInv₀ hInv₀.base_ok fun msg hpq₀ => ?_
  refine bind_getEntry_tr_eq evH tr₀ hInv₀ fun ev _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    refine bind_guardP_at
      (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
        (findRecvChain st.toDRState.recv pk).isSome = true)
      tr₀ hInv₀ fun _ => ?_
    refine run_bind_guardTrace (fun tr => !skippedKeyUsedB tr evH) tr₀ hInv₀ ?_
    rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact run_failure_end hInv₀
    · dsimp only
      refine run_bind_sendMessage key tr₀ ?_
      let tr₁ := tr₀.append (NetE key)
      have hInv₁ : CompDhsOriginInv tr₁ := hInv₀.append_net (CompPcsClosed.spqrRecvKey_of hspqr)
      refine run_bind_receiveMessage pqIdx tr₁ hInv₁ fun pqSalt => ?_
      refine run_bind_verifyMacAndDecrypt st msg pqSalt seed tr₁ hInv₁ fun m => ?_
      let evUsed := TREvent.SkippedKeyUsed s evH
      let tr₂ := tr₁.append (TREvE evUsed)
      have hInv₂ : CompDhsOriginInv tr₂ := hInv₁.append_tr_inert rfl
      let evRec := TREvent.Received me st.peer pk n m
      let tr₃ := tr₂.append (TREvE evRec)
      have hInv₃ : CompDhsOriginInv tr₃ := hInv₂.append_tr_inert rfl
      let evMK := TREvent.MessageKey s .receiver seed pqSalt n rIdx stH
      let tr₄ := tr₃.append (TREvE evMK)
      have hInv₄ : CompDhsOriginInv tr₄ := hInv₃.append_tr_inert rfl
      let st' : TRState := { st with spqr := spqr' }
      let tr₅ := tr₄.append (TRStE me st')
      have hle₀₄ : tr₀ ≤ tr₄ :=
        Trace.le_trans _ _ _ (Trace.append_le tr₀ _)
          (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
            (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
      have hle₀₅ : tr₀ ≤ tr₅ := Trace.le_trans _ _ _ hle₀₄ (Trace.append_le tr₄ _)
      have hfresh₀₅ : ∀ dhs s' r', IsCompDhsOf tr₅ dhs s' r' →
          IsCompDhsOf tr₀ dhs s' r' ∨ ∀ t < tr₀.length, ∀ sz, dhs ≠ mkRand t sz := by
        intro dhs s' r' h
        rcases isCompDhsOf_append_trSt h with h₄ | ⟨rfl, rfl, rfl⟩
        · have h₃ := isCompDhsOf_append_tr_inertB rfl h₄
          have h₂ := isCompDhsOf_append_tr_inertB rfl h₃
          have h₁ := isCompDhsOf_append_tr_inertB rfl h₂
          exact .inl (isCompDhsOf_append_other rfl rfl h₁)
        · exact .inl hdhs₀
      have hst₀_₅ : TRStateClosed tr₅ st := hst_closed₀.mono_of_fresh hle₀₅ hfresh₀₅
      have hpq₅ : CompPcsClosed tr₅ msg.pqRatchet := hpq₀.mono_of_fresh hle₀₅ hfresh₀₅
      have hspqr'₅ : CompPcsClosed tr₅ spqr' :=
        CompPcsClosed.spqrRecvState_of hspqr hst₀_₅.2.2.2.2 hpq₅
      have hst'₅ : TRStateClosed tr₅ st' :=
        ⟨hst₀_₅.1, hst₀_₅.2.1, hst₀_₅.2.2.1, hst₀_₅.2.2.2.1, hspqr'₅⟩
      refine run_bind_logEvent evUsed ?_
      refine run_bind_logEvent evRec ?_
      exact run_logMessageKeyAndStore _ _ _ _ _ _ _ _ _
        (hInv₄.append_trSt_existing (hdhs₀.mono hle₀₄) hst'₅)
  | _ => dsimp only; exact run_failure_end hInv₀

/-- Every trace reachable under `Composed.reachability` satisfies `CompDhsOriginInv`. -/
theorem compDhsOriginInv_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) :
    CompDhsOriginInv tr :=
  composed_reachable_induction
    CompDhsOriginInv.nil
    (fun _ _ hk hInv => hInv.append_net_of (CompPcsClosed.of_attackerKnows hInv.base_ok hk))
    Preserves.pcs_registerIdentity
    Preserves.pcs_registerCorruptIdentity
    Preserves.pcs_genSignedPrekey
    Preserves.pcs_genPQPrekey
    Preserves.pcs_genOneTimePrekey
    Preserves.pcs_aliceStart
    Preserves.pcs_bobStart
    Preserves.pcs_messageEncrypt
    Preserves.pcs_messageEncryptAbort
    Preserves.pcs_messageDecrypt
    Preserves.pcs_messageDecryptSkipped
    Preserves.pcs_exposeKey
    Preserves.pcs_exposeSpqr
    Preserves.pcs_exposeSkipped
    Preserves.pcs_compromiseIK
    Preserves.pcs_compromiseSPK
    Preserves.pcs_compromisePQSPK
    Preserves.pcs_compromiseOPK
    Preserves.pcs_breakDH
    Preserves.pcs_breakKEM
    Preserves.pcs_invertDH
    Preserves.pcs_invertKEM
    hreach

end Symbolic.Swarm.COMPOSED.CompRatchet
