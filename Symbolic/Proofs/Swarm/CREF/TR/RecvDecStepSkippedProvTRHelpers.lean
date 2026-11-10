/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.COMPOSED.CompTrDHS
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TROpen
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Skipped-Key Provenance Helper Invariants

Defines `ProvEvTR`, `InstallWitnessTR`, and `IkShapeTR` and proves their preservation across
reachable composed protocol traces.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace Symbolic.Swarm.CREF.TR.RecvDecStep

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo DRState KeyDir RecvChain findRecvChain setRecvChain
  recvChainFor consumeMessageKey kdfCk x25519LowOrder createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.TR.FreshSigma
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry

def HasRegisteredIk (tr : ExecTrace) (p : Participant) (ikPk : DY.Bytes) : Prop :=
  ∃ vk honest j, tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p ikPk vk honest) j

theorem HasRegisteredIk.mono {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) {p : Participant} {ikPk : DY.Bytes}
    (h : HasRegisteredIk tr₁ p ikPk) : HasRegisteredIk tr₂ p ikPk := by
  obtain ⟨vk, honest, j, hev⟩ := h
  exact ⟨vk, honest, j, Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_mono hle hev⟩

def IkShapeTR (_r₀ : ProtocolSetup) (tr : ExecTrace) (p : Participant) (st : TRState) : Prop :=
  st.peerIk.AttackerKnows tr ∧ st.myIk.AttackerKnows tr ∧
  (∀ p' ik₁ ik₂, HasRegisteredIk tr p' ik₁ → HasRegisteredIk tr p' ik₂ → ik₁ = ik₂) ∧
  (∃ ikMe, HasRegisteredIk tr p ikMe ∧ st.myIk = serializedIk ikMe) ∧
  (∃ ikPeer, HasRegisteredIk tr st.peer ikPeer ∧ st.peerIk = serializedIk ikPeer)

theorem ik_eq_and_known_of_ikShapeTR (r₀ : ProtocolSetup) (tr : ExecTrace) (_hwf : ProtocolSetupWF r₀)
    {p₁ p₂ : Participant} {st₁ st₂ : TRState}
    (h₁ : IkShapeTR r₀ tr p₁ st₁) (h₂ : IkShapeTR r₀ tr p₂ st₂) (hsinfo : st₁.sessionInfo p₁ = st₂.sessionInfo p₂) :
    (st₁.peerIk = st₂.peerIk ∧ st₁.myIk = st₂.myIk ∧ st₂.initiator = st₁.initiator) ∧
    st₁.peerIk.AttackerKnows tr ∧ st₁.myIk.AttackerKnows tr := by
  have hp : p₁ = p₂ := congrArg SessionInfo.me hsinfo
  have hpeer : st₁.peer = st₂.peer := congrArg SessionInfo.peer hsinfo
  have hinit : st₁.initiator = st₂.initiator := congrArg SessionInfo.initiator hsinfo
  obtain ⟨hPeerK, hMyK, hUniq, ⟨ikMe₁, hMe₁, hmy₁⟩, ⟨ikPeer₁, hPeer₁, hpeer₁⟩⟩ := h₁
  obtain ⟨_, _, _, ⟨ikMe₂, hMe₂, hmy₂⟩, ⟨ikPeer₂, hPeer₂, hpeer₂⟩⟩ := h₂
  have hikMe : ikMe₁ = ikMe₂ := hUniq p₁ ikMe₁ ikMe₂ hMe₁ (hp ▸ hMe₂)
  have hikPeer : ikPeer₁ = ikPeer₂ := hUniq st₁.peer ikPeer₁ ikPeer₂ hPeer₁ (hpeer ▸ hPeer₂)
  exact ⟨⟨hpeer₁.trans (hikPeer ▸ hpeer₂.symm), hmy₁.trans (hikMe ▸ hmy₂.symm), hinit.symm⟩, hPeerK, hMyK⟩

theorem mem_recv_of_recvChainFor_false {st : DRState} {pk : DY.Bytes} {c : RecvChain}
    (h : recvChainFor st pk = some (c, false)) : c ∈ st.recv := by
  unfold recvChainFor at h; rcases hfind : findRecvChain st.recv pk with _ | c₀ <;> simp [hfind] at h
  subst h; unfold findRecvChain at hfind; exact List.mem_of_find?_eq_some hfind

theorem prov_consumeMessageKey_ratchetKey {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c n = some (seed, c')) : c'.ratchetKey = c.ratchetKey := by
  unfold consumeMessageKey at h; repeat (split at h; · cases h)
  cases h; rfl

theorem prov_consumeMessageKey_rIdx {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c n = some (seed, c')) : c'.rIdx = c.rIdx := by
  unfold consumeMessageKey at h; repeat (split at h; · cases h)
  cases h; rfl

def ProvEvTR (tr : ExecTrace) : Prop :=
  ∀ s pk n seed rIdx src i,
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    pk.AttackerKnows tr ∧
    (∃ (p₁ : Participant) (st₁ : TRState) (j₁ : Nat) (c₁ : RecvChain),
      Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₁ st₁ j₁ tr ∧
      c₁ ∈ st₁.recv ∧ c₁.ratchetKey = pk ∧ c₁.rIdx = rIdx ∧ st₁.sessionInfo p₁ = s) ∧
    ((∃ (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain) (fresh : Bool) (c₀' : RecvChain),
        Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₀ st₀ src tr ∧ st₀.sessionInfo p₀ = s ∧
        recvChainFor st₀.toDRState pk = some (c₀, fresh) ∧ consumeMessageKey c₀ n = some (seed, c₀')) ∨
     (∃ (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain),
        Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₀ st₀ src tr ∧ st₀.sessionInfo p₀ = s ∧ st₀.initiator = false ∧
        c₀ ∈ st₀.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ n < c₀.index))

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves) in
theorem prov_bind_getLocalState_tr {Inv : ExecTrace → Prop} {α : Type} (me : Participant) (stH : Nat)
    {f : TRState → Traceful α}
    (hf : ∀ st tr, Inv tr → Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt me st stH tr → Inv ((f st).run tr).2.val) :
    Preserves Inv (PersistentLocalState.getLocalState me stH >>= f) := fun tr hInv => by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  have htr : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).2.val = tr :=
    Preserves.getLocalState_tr (Inv := fun t => t = tr) me stH tr rfl
  rcases hget : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 with _ | st <;> rw [htr]
  · exact hInv
  · exact hf st tr hInv (at?_eq_some_of_getLocalState_some hget)

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves) in
private theorem preserves_sendMessage {Inv : ExecTrace → Prop} (msg : DY.Bytes)
    (h : ∀ tr, Inv tr → Inv (tr.append (Network.ExecEntryT.mk msg))) :
    Preserves Inv (Network.sendMessage msg) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact h tr hInv

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves) in
private theorem preserves_genRand {Inv : ExecTrace → Prop} (len : Nat)
    (h : ∀ tr, Inv tr → Inv (tr.append (Random.ExecEntryT.mk len))) :
    Preserves Inv (Random.genRand len) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact h tr hInv

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves) in
private theorem preserves_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev)
    (h : ∀ tr, Inv tr → Inv (tr.append (ProtocolEvent.ExecEntryT.mk ev))) :
    Preserves Inv (ProtocolEvent.logEvent ev) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h tr hInv

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves) in
private theorem preserves_storeLocalState_tr {Inv : ExecTrace → Prop}
    (p : Participant) (st : TRState)
    (h : ∀ tr, Inv tr → Inv (tr.append (⟨⟨p, st⟩⟩ : StEntry))) :
    Preserves Inv (PersistentLocalState.storeLocalState p st) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact h tr hInv

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves PQStE) in
private theorem preserves_storeLocalState_pq {Inv : ExecTrace → Prop}
    (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState)
    (h : ∀ tr, Inv tr → Inv (tr.append (PQStE p st))) :
    Preserves Inv (PersistentLocalState.storeLocalState p st) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact h tr hInv

theorem prov_bind_ensureReceiverChain_tr {Inv : ExecTrace → Prop} {α : Type}
    (st₀ : TRState) (pk : DY.Bytes) {f : TRState × RecvChain × Bool → Traceful α}
    (tr₀ : ExecTrace) (hInv₀ : Inv tr₀)
    (hNoRatchet : ∀ c, recvChainFor st₀.toDRState pk = some (c, false) → Inv ((f (st₀, c, false)).run tr₀).2.val)
    (hRatchet : findRecvChain st₀.recv pk = none → x25519LowOrder pk = false →
      let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₀.length 32
      let (rk1, ckr) := createChain st₀.rk pk st₀.dhs
      let (rk2, cks) := createChain rk1 pk dhs
      let c : RecvChain := { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := st₀.rIdx + 2 }
      let st : TRState := { st₀ with
        rk := rk2, dhs := dhs, cks := cks, ns := 0, pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
        recv := (st₀.recv ++ [c]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
      Inv ((f (st, c, true)).run (tr₀.append (Random.ExecEntryT.mk 32))).2.val) :
    Inv (((DY.Libsignal.TripleRatchet.ensureReceiverChain st₀ pk >>= f).run tr₀).2.val) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  cases hfind : findRecvChain st₀.recv pk with
  | some c =>
    dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd]
    exact hNoRatchet c (by unfold recvChainFor; rw [hfind])
  | none =>
    dsimp only; by_cases hlo : x25519LowOrder pk = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]; dsimp only
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_failure]; exact hInv₀
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
      have hlo_f : x25519LowOrder pk = false := Bool.eq_false_iff.mpr hlo
      rw [ite_eq_left_iff.mpr fun h => absurd (show (!x25519LowOrder pk) = true by rw [hlo_f]; rfl) h]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_genRand_bind_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd,
        Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd]
      exact hRatchet hfind hlo_f

section InstallWitnessTRProof
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves trStateStoredAt_mono trStateStoredAt_here
  trStateStoredAt_append_other trStateStoredAt_append_same)

private def HasInstallOnTR (tr : ExecTrace) (rk : DY.Bytes) : Prop :=
  ∃ p H j, Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p H j tr ∧
    ∃ rk1, H.rk = (createChain rk1 rk H.dhs).1 ∧ ∃ c₁ ∈ H.recv, c₁.ratchetKey = rk

private theorem HasInstallOnTR.mono {tr₁ tr₂ : ExecTrace} (hle : tr₁ ≤ tr₂) {rk : DY.Bytes}
    (h : HasInstallOnTR tr₁ rk) : HasInstallOnTR tr₂ rk := by
  obtain ⟨p, H, j, hst, rk1, hrk, c₁, hc₁, hcrk⟩ := h
  exact ⟨p, H, j, trStateStoredAt_mono hle hst, rk1, hrk, c₁, hc₁, hcrk⟩

private def TraceInstallInvTR (tr : ExecTrace) : Prop :=
  ∀ p st i, Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p st i tr → ∀ c ∈ st.recv, HasInstallOnTR tr c.ratchetKey

private theorem traceInstallInvTR_nil : TraceInstallInvTR Trace.nil := fun _ _ _ hst => by
  simp only [Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt, DY.Trace.at?,
    Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at hst

private theorem traceInstallInvTR_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (h : TraceInstallInvTR tr) : TraceInstallInvTR (tr.append e) :=
  fun p st i hst c hc => (h p st i (trStateStoredAt_append_other hnone_st hst) c hc).mono (Trace.append_le tr e)

private theorem traceInstallInvTR_inertOnNonTR :
    Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS.InertOnNonTR TraceInstallInvTR :=
  ⟨fun _ _ => traceInstallInvTR_append_other rfl, fun _ _ => traceInstallInvTR_append_other rfl,
   fun _ _ => traceInstallInvTR_append_other rfl, fun _ _ => traceInstallInvTR_append_other rfl,
   fun _ _ _ => traceInstallInvTR_append_other rfl⟩

private theorem traceInstallInvTR_append_st {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : ∀ c ∈ st₀.recv, HasInstallOnTR tr c.ratchetKey ∨ ∃ rk1, st₀.rk = (createChain rk1 c.ratchetKey st₀.dhs).1)
    (h : TraceInstallInvTR tr) : TraceInstallInvTR (tr.append (⟨⟨p₀, st₀⟩⟩ : StEntry)) := by
  have hle : tr ≤ tr.append (⟨⟨p₀, st₀⟩⟩ : StEntry) := Trace.append_le tr _
  intro p st i hst c hc
  rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
  · exact (h p st i hst c hc).mono hle
  · exact (hst₀ c hc).elim (fun hold => hold.mono hle)
      (fun ⟨rk1, hrk⟩ => ⟨p₀, st₀, tr.length, trStateStoredAt_here tr p₀ st₀, rk1, hrk, c, hc, rfl⟩)

private def PreservesInstallFromTR (tr₀ : ExecTrace) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, tr₀ ≤ tr → TraceInstallInvTR tr → TraceInstallInvTR (m.run tr).2.val
private theorem PreservesInstallFromTR.of_preserves {tr₀ : ExecTrace} {α : Type} {m : Traceful α}
    (hm : Preserves TraceInstallInvTR m) : PreservesInstallFromTR tr₀ m := fun tr _ h => hm tr h
private theorem PreservesInstallFromTR.bind {tr₀ : ExecTrace} {α β : Type} {m : Traceful α} {f : α → Traceful β}
    (hm : PreservesInstallFromTR tr₀ m) (hf : ∀ a, PreservesInstallFromTR tr₀ (f a)) :
    PreservesInstallFromTR tr₀ (m >>= f) := fun tr hle hInv => by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  have h1 := hm tr hle hInv; have hle1 : tr₀ ≤ (m.run tr).2.val := Trace.le_trans _ _ _ hle (m.run tr).2.property
  cases (m.run tr).1 with | none => exact h1 | some a => exact hf a _ hle1 h1
private theorem PreservesInstallFromTR.storeLocalState {tr₀ : ExecTrace} (me : Participant) (st : TRState)
    (hst : ∀ c ∈ st.recv, HasInstallOnTR tr₀ c.ratchetKey ∨ ∃ rk1, st.rk = (createChain rk1 c.ratchetKey st.dhs).1) :
    PreservesInstallFromTR tr₀ (PersistentLocalState.storeLocalState me st) :=
  fun tr hle hInv => by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact traceInstallInvTR_append_st (fun c hc => (hst c hc).elim (fun h => Or.inl (h.mono hle)) Or.inr) hInv
private theorem PreservesInstallFromTR.logMessageKeyAndStore {tr₀ : ExecTrace}
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (mk pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hst : ∀ c ∈ st.recv, HasInstallOnTR tr₀ c.ratchetKey ∨ ∃ rk1, st.rk = (createChain rk1 c.ratchetKey st.dhs).1) :
    PreservesInstallFromTR tr₀ (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir mk pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
    PreservesInstallFromTR.storeLocalState me st hst
private theorem installTR_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), Preserves TraceInstallInvTR (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | ck, n, k + 1 => by
      unfold DY.Libsignal.TripleRatchet.logSkippedKeys
      exact Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
        installTR_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k
private theorem setRecvChain_ratchetKey_mem {recv : List RecvChain} {c' d : RecvChain}
    (hc' : c'.ratchetKey ∈ recv.map RecvChain.ratchetKey) (hd : d ∈ setRecvChain recv c') :
    d.ratchetKey ∈ recv.map RecvChain.ratchetKey := by
  unfold setRecvChain at hd; obtain ⟨c₀, hc₀, heq⟩ := List.mem_map.mp hd
  split at heq <;> subst heq <;> [exact hc'; exact List.mem_map_of_mem hc₀]
private theorem installTR_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves TraceInstallInvTR (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine traceInstallInvTR_inertOnNonTR.bind_aliceHandshake a b idStateIdx regIdxB bh tr₀ hInv₀ fun o => ?_
  refine (?_ : Preserves TraceInstallInvTR _) _ (traceInstallInvTR_append_other rfl (traceInstallInvTR_append_other rfl hInv₀))
  exact Preserves.bind (preserves_genRand _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    Preserves.bind (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    Preserves.bind (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    Preserves.bind Preserves.traceLength fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
    preserves_storeLocalState_tr _ _ fun _ h =>
      traceInstallInvTR_append_st (fun c hc => by change c ∈ [_] at hc; rw [List.mem_singleton] at hc; subst hc; exact Or.inr ⟨o.keys.rk, rfl⟩) h
private theorem installTR_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceInstallInvTR (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS.InertOnNonTR.bind_bobHandshake b a kh regIdxA mh.ek mh.ct tr₀ hInv₀ fun o => ?_
  refine (PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveSignalMsg _))
    fun msg tr₁ hle₁ hInv₁ => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  let st0 : TRState := {
    peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
    dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit o.keys.pqr spqrB2A }
  refine prov_bind_ensureReceiverChain_tr (Inv := TraceInstallInvTR) st0 msg.ratchetKey tr₁ hInv₁
    (fun c hc_find => nomatch mem_recv_of_recvChainFor_false hc_find) (fun _ _ => ?_)
  dsimp only; let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₁.length 32
  let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st0.rk msg.ratchetKey st0.dhs).2, index := 0, rIdx := st0.rIdx + 2 }
  let st : TRState := { st0 with
    rk := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
    cks := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).2, ns := 0,
    pn := if st0.ns = 0 then 0 else st0.ns - 1, rIdx := st0.rIdx + 2,
    recv := (st0.recv ++ [c1]).drop ((st0.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
  let tr₂ := tr₁.append (Random.ExecEntryT.mk 32)
  have hInv₂ : TraceInstallInvTR tr₂ := traceInstallInvTR_append_other rfl hInv₁
  have hle₂ : tr₀ ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
  rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
  have hc1_mem : c1 ∈ st.recv := List.mem_singleton_self c1
  have hset : ∀ d ∈ setRecvChain st.recv c',
      HasInstallOnTR tr₀ d.ratchetKey ∨ ∃ rk1, st.rk = (createChain rk1 d.ratchetKey st.dhs).1 := fun d hd => by
    obtain ⟨c₀, hc₀, hrk_eq⟩ := List.mem_map.mp (setRecvChain_ratchetKey_mem ((prov_consumeMessageKey_ratchetKey hcons) ▸ List.mem_map_of_mem hc1_mem) hd)
    change c₀ ∈ [c1] at hc₀; rw [List.mem_singleton] at hc₀; subst hc₀
    exact Or.inr ⟨(createChain st0.rk msg.ratchetKey st0.dhs).1, by rw [← hrk_eq]⟩
  refine (?_ : PreservesInstallFromTR tr₀ _) tr₂ hle₂ hInv₂
  refine PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun pqSalt =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun m => ?_
  have hTail : ∀ opkOpt : Option DY.Bytes, PreservesInstallFromTR tr₀ (do
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
        msg.counter c1.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun opkOpt =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves Preserves.traceLength) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves Preserves.traceLength) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (installTR_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hset
  cases o.opk with
  | none =>
    dsimp only [Option.map]
    exact hTail none
  | some opkPk =>
    dsimp only [Option.map]
    exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.requireTracePredicate _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ => hTail (some opkPk)
private theorem installTR_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves TraceInstallInvTR (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀ me st stH hst₀
  refine (?_ : PreservesInstallFromTR tr₀ _) tr₀ (Trace.le_refl tr₀) hInv₀
  refine PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.guardP _)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_genRand _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_genRand _ fun _ => traceInstallInvTR_append_other rfl)) fun coins => ?_
  dsimp only; rcases Spqr.spqrSend st.spqr coins with ⟨spqr', pqPayload, pqSalt⟩
  exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.logMessageKeyAndStore me _ .sender _ _ _ _ _ _ (fun c hc => Or.inl (hst c hc)))
      fun _ => PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)
private theorem installTR_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceInstallInvTR (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine prov_bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀ me st₀ stH hst₀
  refine (PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveSignalMsg _))
    fun msg tr₁ hle₁ hInv₁ => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  refine prov_bind_ensureReceiverChain_tr (Inv := TraceInstallInvTR) st₀ msg.ratchetKey tr₁ hInv₁ (fun c hc_find => ?_) (fun _ _ => ?_)
  · dsimp only; rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    dsimp only; rcases Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    have hset : ∀ d ∈ setRecvChain st₀.recv c',
        HasInstallOnTR tr₀ d.ratchetKey ∨ ∃ rk1, st₀.rk = (createChain rk1 d.ratchetKey st₀.dhs).1 := fun d hd => by
      obtain ⟨c₀, hc₀, hrk_eq⟩ := List.mem_map.mp (setRecvChain_ratchetKey_mem
        ((prov_consumeMessageKey_ratchetKey hcons) ▸ List.mem_map_of_mem (mem_recv_of_recvChainFor_false hc_find)) hd)
      exact Or.inl (hrk_eq ▸ hst c₀ hc₀)
    refine (?_ : PreservesInstallFromTR tr₀ _) tr₁ hle₁ hInv₁
    exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (installTR_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hset
  · dsimp only; let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₁.length 32
    let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2, index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := { st₀ with
      rk := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
      cks := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).2, ns := 0,
      pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
      recv := (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
    let tr₂ := tr₁.append (Random.ExecEntryT.mk 32)
    have hInv₂ : TraceInstallInvTR tr₂ := traceInstallInvTR_append_other rfl hInv₁
    have hle₂ : tr₀ ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
    rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
    dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
    have hc1_mem : c1 ∈ st.recv := by
      show c1 ∈ (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains)
      rw [List.drop_append_of_le_length (by change (st₀.recv.length + 1) - 5 ≤ st₀.recv.length; omega)]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hset : ∀ d ∈ setRecvChain st.recv c',
        HasInstallOnTR tr₀ d.ratchetKey ∨ ∃ rk1, st.rk = (createChain rk1 d.ratchetKey st.dhs).1 := fun d hd => by
      obtain ⟨c₀, hc₀, hrk_eq⟩ := List.mem_map.mp (setRecvChain_ratchetKey_mem ((prov_consumeMessageKey_ratchetKey hcons) ▸ List.mem_map_of_mem hc1_mem) hd)
      rcases List.mem_append.mp (List.mem_of_mem_drop hc₀) with hold | hnew
      · exact Or.inl (hrk_eq ▸ hst c₀ hold)
      · rw [List.mem_singleton] at hnew; subst hnew; exact Or.inr ⟨(createChain st₀.rk msg.ratchetKey st₀.dhs).1, by rw [← hrk_eq]⟩
    refine (?_ : PreservesInstallFromTR tr₀ _) tr₂ hle₂ hInv₂
    exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (installTR_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
      PreservesInstallFromTR.logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hset
private theorem installTR_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceInstallInvTR (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀ me st stH hst₀
  refine (PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveSignalMsg _)) fun msg =>
    PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.getEntry (E := TREntry) evH)) fun e => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only; refine PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.guardP _)) fun _ =>
      PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.guardTrace _)) fun _ => ?_
    split
    · next spqr' key _ =>
      exact PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
        PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
        PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
        PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
        PreservesInstallFromTR.bind (PreservesInstallFromTR.of_preserves (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl)) fun _ =>
        PreservesInstallFromTR.logMessageKeyAndStore me s .receiver seed _ n rIdx stH
          { st with spqr := spqr' } (fun c hc => Or.inl (hst c hc))
    · exact PreservesInstallFromTR.of_preserves Preserves.failure
  | _ => exact PreservesInstallFromTR.of_preserves Preserves.failure
private theorem traceInstallInvTR_reachable {tr : ExecTrace} (hreach : tr.Reachable reachability) : TraceInstallInvTR tr :=
  traceInstallInvTR_inertOnNonTR.reachable_induction traceInstallInvTR_nil
    installTR_aliceStart installTR_bobStart installTR_messageEncrypt
    installTR_messageDecrypt installTR_messageDecryptSkipped
    (fun me stH k => by
      unfold DY.Libsignal.TripleRatchet.exposeKey; refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ _ => ?_
      cases k with
      | rk | dhs | cks =>
        exact (Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
          preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl) tr₀ hInv₀
      | ckr pk =>
        dsimp only
        cases findRecvChain st.recv pk with
        | none => dsimp only; rw [Traceful.run_failure]; exact hInv₀
        | some c =>
          dsimp only
          exact (Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
            preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl) tr₀ hInv₀)
    (fun me stH => by
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      exact prov_bind_getLocalState_tr me stH fun _ tr₀ hInv₀ _ =>
        (Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
          preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl) tr₀ hInv₀)
    (fun evH => by
      unfold DY.Libsignal.TripleRatchet.exposeSkipped
      exact Preserves.bind (Preserves.getEntry (E := ProtocolEvent.ExecEntryT TREvent) evH) fun ⟨ev⟩ tr₀ hInv₀ => by
        cases ev with
        | SkippedKeyStored _ _ _ _ _ _ =>
          dsimp only; refine (Preserves.bind (Preserves.guardTrace _) fun _ => ?_) tr₀ hInv₀
          exact Preserves.bind (preserves_logEvent _ fun _ => traceInstallInvTR_append_other rfl) fun _ =>
            preserves_sendMessage _ fun _ => traceInstallInvTR_append_other rfl
        | _ => dsimp only; rw [Traceful.run_failure]; exact hInv₀)
    hreach
theorem stateStoredAt_of_mem_availableStates_tr (r₀ : ProtocolSetup) (ms : List Move)
    {st : TRState} (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) :
    ∃ p j, Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p st j (runTraceMoves r₀ ms) := by
  unfold availableStates at hst; obtain ⟨⟨p, _⟩, hls, rfl⟩ := List.mem_map.mp hst
  unfold storedStates DY.ExecTrace.getLocalStateAt at hls; obtain ⟨j, _, hj_map⟩ := List.mem_filterMap.mp hls
  rw [Option.map_eq_some_iff] at hj_map; obtain ⟨⟨⟨p', _⟩⟩, hat, hls_eq⟩ := hj_map
  injection hls_eq with hp hst_eq; subst hp hst_eq; exact ⟨p', j, hat⟩
theorem installWitnessTR_of_reachable (r₀ : ProtocolSetup) (ms : List Move)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability) :
    ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), ∀ c ∈ st.recv,
    ∃ H ∈ availableStates r₀ (runTraceMoves r₀ ms), ∃ rk1,
      H.rk = (createChain rk1 c.ratchetKey H.dhs).1 ∧ ∃ c₁ ∈ H.recv, c₁.ratchetKey = c.ratchetKey := fun st hst c hc => by
  obtain ⟨p, i, hst_at⟩ := stateStoredAt_of_mem_availableStates_tr r₀ ms hst
  obtain ⟨_, H, _, hH_at, rk1, hrk, c₁, hc₁, hcrk⟩ := traceInstallInvTR_reachable hreach p st i hst_at c hc
  exact ⟨H, Symbolic.Swarm.CREF.TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms hH_at, rk1, hrk, c₁, hc₁, hcrk⟩
end InstallWitnessTRProof

section IkShapeTRProof
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves PQXDHStoredAt PQXDHEntry PQXDHStEntry PQStE PQEvE
  NetE RndE TRStE eventLoggedAt_mono eventLoggedAt_append_other eventLoggedAt_append_same
  eventLoggedAt_here pqxdhStoredAt_append_other pqxdhStoredAt_append_same trStateStoredAt_mono
  trStateStoredAt_append_other trStateStoredAt_append_same trStateStoredAt_here
  bind_aliceHandshake_at bind_bobHandshake_at bind_receiveMessage_at run_genRand_bind_snd
  composed_reachable_induction)

private theorem not_hasRegisteredIk_of_not_isRegisteredB {tr : ExecTrace} {p : Participant}
    (h : (!DY.Libsignal.PQXDH.isRegisteredB tr p) = true) {ikPk : DY.Bytes}
    (hreg : HasRegisteredIk tr p ikPk) : False := by
  obtain ⟨vk, honest, j, hev⟩ := hreg
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  have hj_lt : j < tr.length := by
    have h1 := Trace.at?_eq_some_implies_length_le (EntryT := PQXDHEntry) tr j
    change (tr.at? j : Option PQXDHEntry) = _ at hev; rw [hev] at h1; exact h1
  have hfalse : DY.Libsignal.PQXDH.isRegisteredB tr p = false := Bool.eq_false_iff.mpr (by simpa using h)
  unfold DY.Libsignal.PQXDH.isRegisteredB at hfalse; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at hfalse
  rw [List.any_eq_false] at hfalse
  have hj_all := hfalse j (List.mem_range.mpr hj_lt)
  change (tr.at? j : Option PQXDHEntry) = _ at hev; rw [hev] at hj_all
  simp [beq_self_eq_true] at hj_all

private theorem serializedIk_attackerKnows {tr : ExecTrace} {ikPk : DY.Bytes}
    (h : ikPk.AttackerKnows tr) : (serializedIk ikPk).AttackerKnows tr :=
  Concat.attacker_knows_concat _ _ tr (Literal.attacker_knows_literalToBytes _ tr) h

private structure TraceIkInv (tr : ExecTrace) : Prop where
  regUniq : ∀ p ik₁ ik₂, HasRegisteredIk tr p ik₁ → HasRegisteredIk tr p ik₂ → ik₁ = ik₂
  regKnows : ∀ p ikPk, HasRegisteredIk tr p ikPk → ikPk.AttackerKnows tr
  pqxIdReg : ∀ p st j, PQXDHStoredAt tr p st j → st.kind = .identity → HasRegisteredIk tr p (dhPk st.sk)
  trStOK : ∀ p st j, Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p st j tr →
    (∃ ikMe, HasRegisteredIk tr p ikMe ∧ st.myIk = serializedIk ikMe) ∧
    (∃ ikPeer, HasRegisteredIk tr st.peer ikPeer ∧ st.peerIk = serializedIk ikPeer)

private theorem traceIkInv_nil : TraceIkInv Trace.nil where
  regUniq := fun _ _ _ ⟨_, _, _, h⟩ _ => by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  regKnows := fun _ _ ⟨_, _, _, h⟩ => by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  pqxIdReg := fun _ _ _ h _ => by
    simp only [PQXDHStoredAt, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  trStOK := fun _ _ _ h => by
    simp only [Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h

private theorem hasRegisteredIk_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    {p : Participant} {ikPk : DY.Bytes} : HasRegisteredIk (tr.append e) p ikPk → HasRegisteredIk tr p ikPk
  | ⟨vk, honest, j, hev⟩ => ⟨vk, honest, j, eventLoggedAt_append_other hnone hev⟩

private theorem hasRegisteredIk_append_nonReg {tr : ExecTrace} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hne : ∀ p ikPk vk honest, ev ≠ .IdentityRegistered p ikPk vk honest)
    {p : Participant} {ikPk : DY.Bytes} (h : HasRegisteredIk (tr.append (PQEvE ev)) p ikPk) :
    HasRegisteredIk tr p ikPk := by
  obtain ⟨vk, honest, j, hev⟩ := h
  rcases eventLoggedAt_append_same hev with ⟨_, hev⟩ | ⟨_, heq⟩
  · exact ⟨vk, honest, j, hev⟩
  · exact False.elim (hne p ikPk vk honest heq)

private theorem traceIkInv_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone_pqEv : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    (hnone_pqSt : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none)
    (hnone_trSt : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (h : TraceIkInv tr) : TraceIkInv (tr.append e) := by
  have hle := Trace.append_le tr e
  refine ⟨fun p ik₁ ik₂ h₁ h₂ => h.regUniq p ik₁ ik₂
      (hasRegisteredIk_append_other hnone_pqEv h₁) (hasRegisteredIk_append_other hnone_pqEv h₂),
    fun p ikPk hreg => DY.Bytes.AttackerKnows_le _ _ _ hle (h.regKnows p ikPk (hasRegisteredIk_append_other hnone_pqEv hreg)),
    fun p st j hst hkind => (h.pqxIdReg p st j (pqxdhStoredAt_append_other hnone_pqSt hst) hkind).mono hle,
    fun p st j hst => ?_⟩
  obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := h.trStOK p st j (trStateStoredAt_append_other hnone_trSt hst)
  exact ⟨⟨ikMe, hMe.mono hle, hmy⟩, ⟨ikPeer, hPeer.mono hle, hpeer⟩⟩

private theorem traceIkInv_append_pqEv_nonReg {tr : ExecTrace} {ev : DY.Libsignal.PQXDH.PQXDHEvent}
    (hne : ∀ p ikPk vk honest, ev ≠ .IdentityRegistered p ikPk vk honest)
    (h : TraceIkInv tr) : TraceIkInv (tr.append (PQEvE ev)) := by
  have hle := Trace.append_le tr (PQEvE ev)
  refine ⟨fun p ik₁ ik₂ h₁ h₂ => h.regUniq p ik₁ ik₂
      (hasRegisteredIk_append_nonReg hne h₁) (hasRegisteredIk_append_nonReg hne h₂),
    fun p ikPk hreg => DY.Bytes.AttackerKnows_le _ _ _ hle (h.regKnows p ikPk (hasRegisteredIk_append_nonReg hne hreg)),
    fun p st j hst hkind => (h.pqxIdReg p st j (pqxdhStoredAt_append_other rfl hst) hkind).mono hle,
    fun p st j hst => ?_⟩
  obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := h.trStOK p st j (trStateStoredAt_append_other rfl hst)
  exact ⟨⟨ikMe, hMe.mono hle, hmy⟩, ⟨ikPeer, hPeer.mono hle, hpeer⟩⟩

private theorem traceIkInv_append_pqSt_nonId {tr : ExecTrace} {p₀ : Participant} {st₀ : DY.Libsignal.PQXDH.PQXDHState}
    (hne : st₀.kind ≠ .identity) (h : TraceIkInv tr) : TraceIkInv (tr.append (PQStE p₀ st₀)) := by
  have hle := Trace.append_le tr (PQStE p₀ st₀)
  refine ⟨fun p ik₁ ik₂ h₁ h₂ => h.regUniq p ik₁ ik₂
      (hasRegisteredIk_append_other rfl h₁) (hasRegisteredIk_append_other rfl h₂),
    fun p ikPk hreg => DY.Bytes.AttackerKnows_le _ _ _ hle (h.regKnows p ikPk (hasRegisteredIk_append_other rfl hreg)),
    fun p st j hst hkind => ?_, fun p st j hst => ?_⟩
  · rcases pqxdhStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
    · exact (h.pqxIdReg p st j hst hkind).mono hle
    · exact False.elim (hne hkind)
  · obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := h.trStOK p st j (trStateStoredAt_append_other rfl hst)
    exact ⟨⟨ikMe, hMe.mono hle, hmy⟩, ⟨ikPeer, hPeer.mono hle, hpeer⟩⟩

private theorem traceIkInv_append_trSt {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : (∃ ikMe, HasRegisteredIk tr p₀ ikMe ∧ st₀.myIk = serializedIk ikMe) ∧
            (∃ ikPeer, HasRegisteredIk tr st₀.peer ikPeer ∧ st₀.peerIk = serializedIk ikPeer))
    (h : TraceIkInv tr) : TraceIkInv (tr.append (TRStE p₀ st₀)) := by
  have hle := Trace.append_le tr (TRStE p₀ st₀)
  refine ⟨fun p ik₁ ik₂ h₁ h₂ => h.regUniq p ik₁ ik₂
      (hasRegisteredIk_append_other rfl h₁) (hasRegisteredIk_append_other rfl h₂),
    fun p ikPk hreg => DY.Bytes.AttackerKnows_le _ _ _ hle (h.regKnows p ikPk (hasRegisteredIk_append_other rfl hreg)),
    fun p st j hst hkind => (h.pqxIdReg p st j (pqxdhStoredAt_append_other rfl hst) hkind).mono hle,
    fun p st j hst => ?_⟩
  rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
  · obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := h.trStOK p st j hst
    exact ⟨⟨ikMe, hMe.mono hle, hmy⟩, ⟨ikPeer, hPeer.mono hle, hpeer⟩⟩
  · obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := hst₀
    exact ⟨⟨ikMe, hMe.mono hle, hmy⟩, ⟨ikPeer, hPeer.mono hle, hpeer⟩⟩

private theorem bind_guardOnTrace_ik {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv (((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.guardTrace; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; exact hInv

private theorem ikO {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (h1 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none := by rfl)
    (h2 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none := by rfl)
    (h3 : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none := by rfl)
    (h : TraceIkInv tr) : TraceIkInv (tr.append e) := traceIkInv_append_other h1 h2 h3 h

private theorem ikInv_registerIdentity (p : Participant) :
    Preserves TraceIkInv (DY.Libsignal.PQXDH.registerIdentity p) := by
  intro tr₀ hInv₀; unfold DY.Libsignal.PQXDH.registerIdentity
  refine bind_guardOnTrace_ik _ tr₀ hInv₀ fun hguard => ?_
  rw [run_genRand_bind_snd]
  let ik := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₀.length 32
  let tr₁ := tr₀.append (RndE 32)
  let ev := DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p (dhPk ik) (DY.Signature.vk ik) true
  let tr₂ := tr₁.append (PQEvE ev); let tr₃ := tr₂.append (NetE (dhPk ik))
  let tr₄ := tr₃.append (NetE (DY.Signature.vk ik))
  let tr₅ := tr₄.append (PQStE p { kind := .identity, sk := ik })
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  change TraceIkInv tr₅
  have hle₃₅ : tr₃ ≤ tr₅ := Trace.le_trans _ _ _ (Trace.append_le tr₃ _) (Trace.append_le tr₄ _)
  have hle₂₅ : tr₂ ≤ tr₅ := Trace.le_trans _ _ _ (Trace.append_le tr₂ _) hle₃₅
  have hle₀₅ : tr₀ ≤ tr₅ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) hle₂₅)
  have hreg_new : HasRegisteredIk tr₅ p (dhPk ik) :=
    ⟨DY.Signature.vk ik, true, tr₁.length, eventLoggedAt_mono hle₂₅ (eventLoggedAt_here tr₁ ev)⟩
  have hnet : Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt (dhPk ik) tr₂.length tr₃ := Trace.at?_append tr₂ (NetE (dhPk ik))
  have hknows_new : (dhPk ik).AttackerKnows tr₅ := DY.Bytes.AttackerKnows_le _ _ _ hle₃₅ hnet.attackerKnows
  have hreg_iff : ∀ p' ik', HasRegisteredIk tr₅ p' ik' → HasRegisteredIk tr₀ p' ik' ∨ (p' = p ∧ ik' = dhPk ik) := by
    intro p' ik' h5
    obtain ⟨vk', honest', j, hev2⟩ := hasRegisteredIk_append_other rfl (hasRegisteredIk_append_other rfl (hasRegisteredIk_append_other rfl h5))
    rcases eventLoggedAt_append_same hev2 with ⟨_, hev1⟩ | ⟨_, heq⟩
    · exact Or.inl (hasRegisteredIk_append_other rfl ⟨vk', honest', j, hev1⟩)
    · injection heq with hp hik _ _; exact Or.inr ⟨hp.symm, hik.symm⟩
  refine ⟨fun p' ik₁ ik₂ h₁ h₂ => ?_, fun p' ikPk hreg => ?_, fun p' st j hst hkind => ?_, fun p' st j hst => ?_⟩
  · rcases hreg_iff p' ik₁ h₁ with h10 | ⟨hp1, hik1⟩ <;> rcases hreg_iff p' ik₂ h₂ with h20 | ⟨hp2, hik2⟩
    · exact hInv₀.regUniq p' ik₁ ik₂ h10 h20
    · subst hp2; exact False.elim (not_hasRegisteredIk_of_not_isRegisteredB hguard h10)
    · subst hp1; exact False.elim (not_hasRegisteredIk_of_not_isRegisteredB hguard h20)
    · exact hik1.trans hik2.symm
  · rcases hreg_iff p' ikPk hreg with h0 | ⟨_, rfl⟩
    · exact DY.Bytes.AttackerKnows_le _ _ _ hle₀₅ (hInv₀.regKnows p' ikPk h0)
    · exact hknows_new
  · rcases pqxdhStoredAt_append_same hst with ⟨_, hst4⟩ | ⟨_, rfl, rfl⟩
    · exact (hInv₀.pqxIdReg p' st j (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl
        (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl hst4)))) hkind).mono hle₀₅
    · exact hreg_new
  · obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := hInv₀.trStOK p' st j
      (trStateStoredAt_append_other rfl (trStateStoredAt_append_other rfl (trStateStoredAt_append_other rfl
        (trStateStoredAt_append_other rfl (trStateStoredAt_append_other rfl hst)))))
    exact ⟨⟨ikMe, hMe.mono hle₀₅, hmy⟩, ⟨ikPeer, hPeer.mono hle₀₅, hpeer⟩⟩

private theorem ikInv_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves TraceIkInv (DY.Libsignal.PQXDH.registerCorruptIdentity p skIdx) := by
  intro tr₀ hInv₀; unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine bind_guardOnTrace_ik _ tr₀ hInv₀ fun hguard => ?_
  refine bind_receiveMessage_at skIdx tr₀ hInv₀ fun sk _ hsk_knows => ?_
  let ev1 := DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered p (dhPk sk) (DY.Signature.vk sk) false
  let tr₁ := tr₀.append (PQEvE ev1)
  have hInv₁ : TraceIkInv tr₁ := by
    have hle₀₁ := Trace.append_le tr₀ (PQEvE ev1)
    have hreg_iff : ∀ p' ik', HasRegisteredIk tr₁ p' ik' → HasRegisteredIk tr₀ p' ik' ∨ (p' = p ∧ ik' = dhPk sk) := by
      intro p' ik' ⟨vk', honest', j, hev1⟩
      rcases eventLoggedAt_append_same hev1 with ⟨_, hev0⟩ | ⟨_, heq⟩
      · exact Or.inl ⟨vk', honest', j, hev0⟩
      · injection heq with hp hik _ _; exact Or.inr ⟨hp.symm, hik.symm⟩
    refine ⟨fun p' ik₁ ik₂ h₁ h₂ => ?_, fun p' ikPk hreg => ?_,
      fun p' st j hst hkind => (hInv₀.pqxIdReg p' st j (pqxdhStoredAt_append_other rfl hst) hkind).mono hle₀₁,
      fun p' st j hst => ?_⟩
    · rcases hreg_iff p' ik₁ h₁ with h10 | ⟨hp1, hik1⟩ <;> rcases hreg_iff p' ik₂ h₂ with h20 | ⟨hp2, hik2⟩
      · exact hInv₀.regUniq p' ik₁ ik₂ h10 h20
      · subst hp2; exact False.elim (not_hasRegisteredIk_of_not_isRegisteredB hguard h10)
      · subst hp1; exact False.elim (not_hasRegisteredIk_of_not_isRegisteredB hguard h20)
      · exact hik1.trans hik2.symm
    · rcases hreg_iff p' ikPk hreg with h0 | ⟨_, rfl⟩
      · exact DY.Bytes.AttackerKnows_le _ _ _ hle₀₁ (hInv₀.regKnows p' ikPk h0)
      · exact DY.Bytes.AttackerKnows_le _ _ _ hle₀₁ (DiffieHellman.attacker_knows_dhPk sk tr₀ hsk_knows)
    · obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := hInv₀.trStOK p' st j (trStateStoredAt_append_other rfl hst)
      exact ⟨⟨ikMe, hMe.mono hle₀₁, hmy⟩, ⟨ikPeer, hPeer.mono hle₀₁, hpeer⟩⟩
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) hInv₁

private theorem ikInv_getKey (p : Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves TraceIkInv (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ => Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private def PreservesIkFromTR (tr₀ : ExecTrace) {α : Type} (m : Traceful α) : Prop :=
  ∀ tr, tr₀ ≤ tr → TraceIkInv tr → TraceIkInv (m.run tr).2.val
private theorem PreservesIkFromTR.of_preserves {tr₀ : ExecTrace} {α : Type} {m : Traceful α}
    (hm : Preserves TraceIkInv m) : PreservesIkFromTR tr₀ m := fun tr _ h => hm tr h
private theorem PreservesIkFromTR.bind {tr₀ : ExecTrace} {α β : Type} {m : Traceful α} {f : α → Traceful β}
    (hm : PreservesIkFromTR tr₀ m) (hf : ∀ a, PreservesIkFromTR tr₀ (f a)) :
    PreservesIkFromTR tr₀ (m >>= f) := fun tr hle hInv => by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  have h1 := hm tr hle hInv; have hle1 : tr₀ ≤ (m.run tr).2.val := Trace.le_trans _ _ _ hle (m.run tr).2.property
  cases (m.run tr).1 with | none => exact h1 | some a => exact hf a _ hle1 h1
private theorem PreservesIkFromTR.logMessageKeyAndStore {tr₀ : ExecTrace}
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (mk pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState)
    (hst : (∃ ikMe, HasRegisteredIk tr₀ me ikMe ∧ st.myIk = serializedIk ikMe) ∧
           (∃ ikPeer, HasRegisteredIk tr₀ st.peer ikPeer ∧ st.peerIk = serializedIk ikPeer)) :
    PreservesIkFromTR tr₀ (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir mk pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ tr hle hInv => by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    exact traceIkInv_append_trSt ⟨let ⟨ik, hr, hm⟩ := hst.1; ⟨ik, hr.mono hle, hm⟩, let ⟨ik, hr, hp⟩ := hst.2; ⟨ik, hr.mono hle, hp⟩⟩ hInv
private theorem ikInv_logSkippedKeys (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (ck : DY.Bytes) (n : UInt32) (k : Nat), Preserves TraceIkInv (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k)
  | _, _, 0 => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | ck, n, k + 1 => by
      unfold DY.Libsignal.TripleRatchet.logSkippedKeys
      exact Preserves.bind (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        ikInv_logSkippedKeys s pk rIdx src (kdfCk ck).1 (n + 1) k

private theorem bind_aliceHandshake_ik {α : Type}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles)
    {f : DY.Libsignal.PQXDH.AliceHandshakeOut → Traceful α}
    (tr : ExecTrace) (hInv : TraceIkInv tr)
    (hf : ∀ o : DY.Libsignal.PQXDH.AliceHandshakeOut,
      HasRegisteredIk tr a o.ikA → HasRegisteredIk tr b o.ikB →
      TraceIkInv ((f o).run ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    TraceIkInv (((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) :=
  Symbolic.Swarm.COMPOSED.CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv (ikO rfl rfl rfl hInv)
    fun ikA ikB vkB spk _ pqpk _ opk honest hstA hregB _ _ _ _ _ _ _ _ _ =>
      hf (Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr ikA ikB spk pqpk opk)
        (hInv.pqxIdReg a { kind := .identity, sk := ikA } idStateIdx hstA rfl)
        ⟨vkB, honest, regIdxB, hregB⟩

private theorem bind_bobHandshake_ik {α : Type}
    (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat)
    {f : DY.Libsignal.PQXDH.BobHandshakeOut → Traceful α}
    (tr : ExecTrace) (hInv : TraceIkInv tr)
    (hf : ∀ o : DY.Libsignal.PQXDH.BobHandshakeOut,
      HasRegisteredIk tr b o.ikB → HasRegisteredIk tr a o.ikA →
      TraceIkInv ((f o).run tr).2.val) :
    TraceIkInv (((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx >>= f).run tr).2.val) :=
  Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at b a kh regIdxA ekIdx ctIdx tr hInv
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys hikB _ _ _ hregA _ _ _ _ =>
      hf { ikB := dhPk ikB, ikA, spk := dhPk spkSk,
           pqpk := DY.PQKem.kemPk pqsk, opk := opkSk.map dhPk,
           ek, ct, spkSk, keys }
        (hInv.pqxIdReg b { kind := .identity, sk := ikB } kh.ik hikB rfl)
        ⟨vkA, honest, regIdxA, hregA⟩

private theorem ikInv_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves TraceIkInv (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_ik a b idStateIdx regIdxB bh tr₀ hInv₀ fun o hMe₀ hPeer₀ => ?_
  let tr₁ := (tr₀.append (RndE 32)).append (RndE 32)
  have hInv₁ : TraceIkInv tr₁ := ikO rfl rfl rfl (ikO rfl rfl rfl hInv₀)
  have hle₀₁ : tr₀ ≤ tr₁ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) (Trace.append_le _ _)
  refine (?_ : PreservesIkFromTR tr₀ _) tr₁ hle₀₁ hInv₁
  exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_genRand _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves Preserves.traceLength) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ tr hle hInv => by
      simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
      exact traceIkInv_append_trSt ⟨⟨o.ikA, hMe₀.mono hle, rfl⟩, ⟨o.ikB, hPeer₀.mono hle, rfl⟩⟩ hInv

private theorem ikInv_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceIkInv (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_ik b a kh regIdxA mh.ek mh.ct tr₀ hInv₀ fun o hMe₀ hPeer₀ => ?_
  refine (PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveSignalMsg _))
    fun msg tr₁ hle₁ hInv₁ => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  let st0 : TRState := {
    peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
    dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit o.keys.pqr spqrB2A }
  refine prov_bind_ensureReceiverChain_tr (Inv := TraceIkInv) st0 msg.ratchetKey tr₁ hInv₁
    (fun c hc_find => nomatch mem_recv_of_recvChainFor_false hc_find) (fun _ _ => ?_)
  dsimp only
  let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₁.length 32
  let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st0.rk msg.ratchetKey st0.dhs).2, index := 0, rIdx := st0.rIdx + 2 }
  let st : TRState := { st0 with
    rk := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
    cks := (createChain (createChain st0.rk msg.ratchetKey st0.dhs).1 msg.ratchetKey dhs).2, ns := 0,
    pn := if st0.ns = 0 then 0 else st0.ns - 1, rIdx := st0.rIdx + 2,
    recv := (st0.recv ++ [c1]).drop ((st0.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
  let tr₂ := tr₁.append (Random.ExecEntryT.mk 32)
  have hInv₂ : TraceIkInv tr₂ := ikO rfl rfl rfl hInv₁
  have hle₂ : tr₀ ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
  rcases consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
  have hst_post : (∃ ikMe, HasRegisteredIk tr₀ b ikMe ∧
        ({ st with recv := setRecvChain st.recv c', spqr := spqr' } : TRState).myIk = serializedIk ikMe) ∧
      (∃ ikPeer, HasRegisteredIk tr₀ ({ st with recv := setRecvChain st.recv c', spqr := spqr' } : TRState).peer ikPeer ∧
        ({ st with recv := setRecvChain st.recv c', spqr := spqr' } : TRState).peerIk = serializedIk ikPeer) :=
    ⟨⟨o.ikB, hMe₀, rfl⟩, ⟨o.ikA, hPeer₀, rfl⟩⟩
  refine (?_ : PreservesIkFromTR tr₀ _) tr₂ hle₂ hInv₂
  refine PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun pqSalt =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun m => ?_
  have hTail : ∀ opkOpt : Option DY.Bytes, PreservesIkFromTR tr₀ (do
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
        msg.counter c1.rIdx childIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun opkOpt =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves Preserves.traceLength) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves Preserves.traceLength) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (ikInv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.logMessageKeyAndStore b _ .receiver _ _ _ _ _ _ hst_post
  cases o.opk with
  | none =>
    dsimp only [Option.map]
    exact hTail none
  | some opkPk =>
    dsimp only [Option.map]
    exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.requireTracePredicate _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)) fun _ =>
      hTail (some opkPk)

private theorem ikInv_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves TraceIkInv (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀.trStOK me st stH hst₀
  refine (?_ : PreservesIkFromTR tr₀ _) tr₀ (Trace.le_refl tr₀) hInv₀
  refine PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.guardP _)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_genRand _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_genRand _ fun _ h => ikO rfl rfl rfl h)) fun coins => ?_
  dsimp only; rcases Spqr.spqrSend st.spqr coins with ⟨spqr', pqPayload, pqSalt⟩
  exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
    PreservesIkFromTR.bind (PreservesIkFromTR.logMessageKeyAndStore me _ .sender _ _ _ _ _ _ hst)
      fun _ => PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)

private theorem ikInv_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceIkInv (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine prov_bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀.trStOK me st₀ stH hst₀
  refine (PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveSignalMsg _))
    fun msg tr₁ hle₁ hInv₁ => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  refine prov_bind_ensureReceiverChain_tr (Inv := TraceIkInv) st₀ msg.ratchetKey tr₁ hInv₁ (fun c _ => ?_) (fun _ _ => ?_)
  · dsimp only; rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    dsimp only; rcases Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    refine (?_ : PreservesIkFromTR tr₀ _) tr₁ hle₁ hInv₁
    exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (ikInv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hst
  · dsimp only
    let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₁.length 32
    let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2, index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := { st₀ with
      rk := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
      cks := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).2, ns := 0,
      pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
      recv := (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
    let tr₂ := tr₁.append (Random.ExecEntryT.mk 32)
    have hInv₂ : TraceIkInv tr₂ := ikO rfl rfl rfl hInv₁
    have hle₂ : tr₀ ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
    rcases consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
    dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₂
    refine (?_ : PreservesIkFromTR tr₀ _) tr₂ hle₂ hInv₂
    exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (ikInv_logSkippedKeys _ _ _ _ _ _ _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
      PreservesIkFromTR.logMessageKeyAndStore me _ .receiver _ _ _ _ _ _ hst

private theorem ikInv_messageDecryptSkipped (me : Participant)
    (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves TraceIkInv (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  have hst := hInv₀.trStOK me st stH hst₀
  refine (PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveSignalMsg _)) fun msg =>
    PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.getEntry (E := TREntry) evH)) fun e => ?_) tr₀ (Trace.le_refl tr₀) hInv₀
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only; refine PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.guardP _)) fun _ =>
      PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.guardTrace _)) fun _ => ?_
    split
    · next spqr' key _ =>
      exact PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
        PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.receiveMessage pqIdx)) fun _ =>
        PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (Preserves.verifyMacAndDecrypt _ _ _ _)) fun _ =>
        PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
        PreservesIkFromTR.bind (PreservesIkFromTR.of_preserves (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h)) fun _ =>
        PreservesIkFromTR.logMessageKeyAndStore me s .receiver seed _ n rIdx stH
          { st with spqr := spqr' } hst
    · exact PreservesIkFromTR.of_preserves Preserves.failure
  | _ => exact PreservesIkFromTR.of_preserves Preserves.failure

private theorem traceIkInv_reachable {tr : ExecTrace} (hreach : tr.Reachable reachability) : TraceIkInv tr :=
  composed_reachable_induction traceIkInv_nil (fun _ _ _ h => ikO rfl rfl rfl h)
    ikInv_registerIdentity ikInv_registerCorruptIdentity
    (fun b idIdx => by
      unfold DY.Libsignal.PQXDH.genSignedPrekey
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h) fun _ =>
        Preserves.bind (preserves_storeLocalState_pq _ _ fun _ h => traceIkInv_append_pqSt_nonId (by nofun) h) fun _ =>
        Preserves.bind (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) fun _ => Preserves.pure _)
    (fun b idIdx => by
      unfold DY.Libsignal.PQXDH.genPQPrekey
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h) fun _ =>
        Preserves.bind (preserves_storeLocalState_pq _ _ fun _ h => traceIkInv_append_pqSt_nonId (by nofun) h) fun _ =>
        Preserves.bind (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) fun _ => Preserves.pure _)
    (fun b => by
      unfold DY.Libsignal.PQXDH.genOneTimePrekey
      exact Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h) fun _ =>
        Preserves.bind (preserves_storeLocalState_pq _ _ fun _ h => traceIkInv_append_pqSt_nonId (by nofun) h) fun _ =>
        Preserves.bind (preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) fun _ => Preserves.pure _)
    ikInv_aliceStart ikInv_bobStart ikInv_messageEncrypt
    (fun me stH => by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
      exact Preserves.bind (Preserves.getLocalState_tr me stH) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => ikO rfl rfl rfl h) fun _ => Preserves.failure)
    ikInv_messageDecrypt ikInv_messageDecryptSkipped
    (fun me stH k => by
      unfold DY.Libsignal.TripleRatchet.exposeKey; refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ _ => ?_
      cases k with
      | rk | dhs | cks =>
        exact (Preserves.bind (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h) fun _ =>
          preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) tr₀ hInv₀
      | ckr pk =>
        dsimp only
        cases findRecvChain st.recv pk with
        | none => dsimp only; rw [Traceful.run_failure]; exact hInv₀
        | some c =>
          dsimp only
          exact (Preserves.bind (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h) fun _ =>
            preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) tr₀ hInv₀)
    (fun me stH => by
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      exact prov_bind_getLocalState_tr me stH fun _ tr₀ hInv₀ _ =>
        (Preserves.bind (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h) fun _ =>
          preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h) tr₀ hInv₀)
    (fun evH => by
      unfold DY.Libsignal.TripleRatchet.exposeSkipped
      exact Preserves.bind (Preserves.getEntry (E := ProtocolEvent.ExecEntryT TREvent) evH) fun ⟨ev⟩ tr₀ hInv₀ => by
        cases ev with
        | SkippedKeyStored _ _ _ _ _ _ =>
          dsimp only; refine (Preserves.bind (Preserves.guardTrace _) fun _ => ?_) tr₀ hInv₀
          exact Preserves.bind (preserves_logEvent _ fun _ h => ikO rfl rfl rfl h) fun _ =>
            preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h
        | _ => dsimp only; rw [Traceful.run_failure]; exact hInv₀)
    (fun _ _ => by
      unfold DY.Libsignal.PQXDH.compromiseIK
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
          fun _ => preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)
    (fun _ _ => by
      unfold DY.Libsignal.PQXDH.compromiseSPK
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
          fun _ => preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)
    (fun _ _ => by
      unfold DY.Libsignal.PQXDH.compromisePQSPK
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
          fun _ => preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)
    (fun _ _ => by
      unfold DY.Libsignal.PQXDH.compromiseOPK
      exact Preserves.bind (ikInv_getKey _ _ _) fun _ =>
        Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
          fun _ => preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)
    (by unfold DY.Libsignal.PQXDH.breakDH; exact preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
    (by unfold DY.Libsignal.PQXDH.breakKEM; exact preserves_logEvent _ fun _ h => traceIkInv_append_pqEv_nonReg (by rintro _ _ _ _ h; nomatch h) h)
    (fun _ => by
      unfold DY.Libsignal.PQXDH.invertDH
      refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
      split <;> [exact preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h; exact Preserves.failure])
    (fun _ => by
      unfold DY.Libsignal.PQXDH.invertKEM
      exact Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
        Preserves.bind (Preserves.receiveMessage _) fun _ =>
        Preserves.bind (Preserves.monadLiftErr _) fun _ =>
        preserves_sendMessage _ fun _ h => ikO rfl rfl rfl h)
    hreach

theorem ikShapeTR_of_trStateStoredAt {r₀ : ProtocolSetup} {ms : List Move} {p : Participant} {st : TRState} {i : Nat}
    (hRun : ModelRun r₀ ms) (hst : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p st i (runTraceMoves r₀ ms)) :
    IkShapeTR r₀ (runTraceMoves r₀ ms) p st := by
  have hInv := traceIkInv_reachable hRun.2.2.1.1
  obtain ⟨⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩ := hInv.trStOK p st i hst
  exact ⟨hpeer ▸ serializedIk_attackerKnows (hInv.regKnows st.peer ikPeer hPeer),
    hmy ▸ serializedIk_attackerKnows (hInv.regKnows p ikMe hMe),
    hInv.regUniq, ⟨ikMe, hMe, hmy⟩, ⟨ikPeer, hPeer, hpeer⟩⟩
end IkShapeTRProof

end Symbolic.Swarm.CREF.TR.RecvDecStep
