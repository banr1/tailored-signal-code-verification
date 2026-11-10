/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTRHelpers
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompTrDHS
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
import Symbolic.Proofs.Swarm.CREF.TROpen
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
# Skipped-Key Provenance Invariant

Proves reachability of the skipped-key provenance invariant `ProvEvTR` and extracts either a
stored provenance state `st_prov` or an initial responder chain witness for every logged
`SkippedKeyStored` event.
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
  recvChainFor consumeMessageKey kdfCk chainKeyAt messageVersion x25519LowOrder createChain
  maxForwardJumps u32Max)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry run_bind_snd run_bind_fst
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry run_bind_snd run_bind_fst

section ProvEvTRReachableProof
open Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompRatchet.TrDHS (InertOnNonTR)

private theorem preserves_sendMessage {Inv : ExecTrace → Prop} (msg : DY.Bytes)
    (h : ∀ tr, Inv tr → Inv (tr.append (Network.ExecEntryT.mk msg))) :
    Preserves Inv (Network.sendMessage msg) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact h tr hInv

private theorem preserves_genRand {Inv : ExecTrace → Prop} (len : Nat)
    (h : ∀ tr, Inv tr → Inv (tr.append (Random.ExecEntryT.mk len))) :
    Preserves Inv (Random.genRand len) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
  exact h tr hInv

private theorem preserves_logEvent {Inv : ExecTrace → Prop} {Ev : Type}
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] (ev : Ev)
    (h : ∀ tr, Inv tr → Inv (tr.append (ProtocolEvent.ExecEntryT.mk ev))) :
    Preserves Inv (ProtocolEvent.logEvent ev) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact h tr hInv

private theorem preserves_storeLocalState_tr {Inv : ExecTrace → Prop}
    (p : Participant) (st : TRState)
    (h : ∀ tr, Inv tr → Inv (tr.append (TRStE p st))) :
    Preserves Inv (PersistentLocalState.storeLocalState p st) := fun tr hInv => by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact h tr hInv

private theorem run_logEvent_bind_snd {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)]
    {α : Type} (ev : Ev) (f : Unit → Traceful α) (tr : ExecTrace) :
    ((ProtocolEvent.logEvent ev >>= f).run tr).2.val =
      ((f ()).run (tr.append (ProtocolEvent.ExecEntryT.mk ev))).2.val := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [run_bind_assoc_snd, run_bind_snd, Traceful.run_mk]
  dsimp only
  rw [run_pure_bind_snd]

private theorem run_traceLength_bind_snd {α : Type} (f : Nat → Traceful α) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.traceLength >>= f).run tr).2.val = ((f tr.length).run tr).2.val := by
  unfold DY.Libsignal.TripleRatchet.traceLength
  rw [run_bind_snd, Traceful.run_mk]

private theorem provEvTR_at_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') (h : ProvEvTR tr)
    {s : SessionInfo} {pk : DY.Bytes} {n : UInt32} {seed : DY.Bytes} {rIdx src i : Nat}
    (hlog : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i) :
    pk.AttackerKnows tr' ∧
    (∃ (p₁ : Participant) (st₁ : TRState) (j₁ : Nat) (c₁ : RecvChain),
      Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₁ st₁ j₁ tr' ∧
      c₁ ∈ st₁.recv ∧ c₁.ratchetKey = pk ∧ c₁.rIdx = rIdx ∧ st₁.sessionInfo p₁ = s) ∧
    ((∃ (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain) (fresh : Bool) (c₀' : RecvChain),
        Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₀ st₀ src tr' ∧ st₀.sessionInfo p₀ = s ∧
        recvChainFor st₀.toDRState pk = some (c₀, fresh) ∧ consumeMessageKey c₀ n = some (seed, c₀')) ∨
     (∃ (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain),
        Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₀ st₀ src tr' ∧ st₀.sessionInfo p₀ = s ∧ st₀.initiator = false ∧
        c₀ ∈ st₀.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ n < c₀.index)) := by
  obtain ⟨hpk, ⟨p₁, st₁, j₁, c₁, h1, hc1, hrk1, hrIdx1, hs1⟩, hmb⟩ := h s pk n seed rIdx src i hlog
  refine ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hpk,
    ⟨p₁, st₁, j₁, c₁, trStateStoredAt_mono hle h1, hc1, hrk1, hrIdx1, hs1⟩, ?_⟩
  rcases hmb with ⟨p₀, st₀, c₀, fresh, c₀', h0, hs0, hrc, hcons⟩ |
      ⟨p₀, st₀, c₀, h0, hs0, hinit, hc0, hrk0, hrIdx0, hlt⟩
  · exact .inl ⟨p₀, st₀, c₀, fresh, c₀', trStateStoredAt_mono hle h0, hs0, hrc, hcons⟩
  · exact .inr ⟨p₀, st₀, c₀, trStateStoredAt_mono hle h0, hs0, hinit, hc0, hrk0, hrIdx0, hlt⟩

private theorem provEvTR_mono_events {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hev : ∀ s pk n seed rIdx src i,
      tr'.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
      tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i)
    (h : ProvEvTR tr) : ProvEvTR tr' :=
  fun s pk n seed rIdx src i hlog => provEvTR_at_mono hle h (hev s pk n seed rIdx src i hlog)

private theorem provEvTR_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {x : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option TREntry) = none)
    (h : ProvEvTR tr) : ProvEvTR (tr.append x) :=
  provEvTR_mono_events (Trace.append_le tr x) (fun _ _ _ _ _ _ _ hl => eventLoggedAt_append_other hnone hl) h

private theorem provEvTR_append_tr {tr : ExecTrace} {ev : TREvent}
    (hev : ∀ s pk n seed rIdx src, ev ≠ TREvent.SkippedKeyStored s pk n seed rIdx src)
    (h : ProvEvTR tr) : ProvEvTR (tr.append (TREvE ev)) :=
  provEvTR_mono_events (Trace.append_le tr _) (fun s pk n seed rIdx src _ hl =>
    (eventLoggedAt_append_same hl).elim And.right fun ⟨_, heq⟩ => absurd heq (hev s pk n seed rIdx src)) h

private theorem provEvTR_inertOnNonTR : InertOnNonTR ProvEvTR where
  append_net _ _ h := provEvTR_append_other rfl h
  append_rnd _ _ h := provEvTR_append_other rfl h
  append_pqxEv _ _ h := provEvTR_append_other rfl h
  append_cEv _ _ h := provEvTR_append_other rfl h
  append_pqxSt _ _ _ h := provEvTR_append_other rfl h

private theorem consumeMessageKey_skipped_tr {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) {j : Nat}
    (hj : j < counter.toNat - c.index.toNat) :
    ∃ c₀', consumeMessageKey c (c.index + UInt32.ofNat j) =
      some ((kdfCk (chainKeyAt c.chainKey j)).2, c₀') := by
  unfold consumeMessageKey at h
  split at h; · cases h
  rename_i hlt; split at h; · cases h
  rename_i hjump; split at h; · cases h
  rename_i hne
  have hlt' : c.index.toNat ≤ counter.toNat := by rw [UInt32.lt_iff_toNat_lt] at hlt; omega
  have hcn : counter.toNat < 2 ^ 32 := counter.toNat_lt
  have hcne : counter.toNat ≠ 4294967295 := fun heq => hne (UInt32.toNat_inj.mp (by rw [heq]; rfl))
  have hjNat : (UInt32.ofNat j).toNat = j := UInt32.toNat_ofNat_of_lt' (by change j < 4294967296; omega)
  have hsum : (c.index + UInt32.ofNat j).toNat = c.index.toNat + j := by
    rw [UInt32.toNat_add, hjNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold consumeMessageKey
  have h1 : ¬ (c.index + UInt32.ofNat j < c.index) := by rw [UInt32.lt_iff_toNat_lt, hsum]; omega
  have h2 : ¬ ((c.index + UInt32.ofNat j).toNat - c.index.toNat > DY.Libsignal.TripleRatchet.maxForwardJumps) := by
    rw [hsum]; have := Nat.le_of_not_gt hjump; omega
  have h3 : ¬ (c.index + UInt32.ofNat j = u32Max) := by
    intro heq; have := congrArg UInt32.toNat heq; rw [hsum] at this; change c.index.toNat + j = 4294967295 at this; omega
  have hidx : (c.index + UInt32.ofNat j).toNat - c.index.toNat = j := by rw [hsum]; omega
  have h2' : ¬ (j > DY.Libsignal.TripleRatchet.maxForwardJumps) := hidx ▸ h2
  simp only [h1, h3, ↓reduceIte, hidx, h2']; exact ⟨_, rfl⟩

private theorem logSkippedKeys_run_step (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).1 = some () ∧
      ((logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val =
        logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero =>
    unfold logSkippedKeys logSkippedKeysTr
    rw [Traceful.run_pure]
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    unfold logSkippedKeys logSkippedKeysTr
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1]
    rw [Traceful.run_bind, Traceful.run_bind, Traceful.run_mk]
    dsimp only
    rw [Traceful.run_pure]
    exact ih (kdfCk ck).1 (n + 1) _

private theorem decTailTr_run (me : Participant) (stH : Nat) (st1 : TRState) (c c' : RecvChain)
    (pk seed pqSalt m spqr' : DY.Bytes) (n : UInt32) (tr : ExecTrace) :
    ((do
      let _ ← logSkippedKeys (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat)
      let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer pk n m)
      logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt n
        c.rIdx stH { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } : Traceful Nat).run tr).2.val =
      decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n := by
  obtain ⟨hsk1, hsk2⟩ := logSkippedKeys_run_step (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr
  rw [run_bind_snd, hsk1, hsk2]
  dsimp only
  unfold logMessageKeyAndStore decTailTr
  rw [run_logEvent_bind_snd, run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]

private theorem decTailTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st1 : TRState)
    (c c' : RecvChain) (pk seed pqSalt m spqr' : DY.Bytes) (n : UInt32) :
    tr ≤ decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n := by
  rw [← decTailTr_run]
  exact ((do
    let _ ← logSkippedKeys (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat)
    let _ ← DY.ProtocolEvent.logEvent (TREvent.Received me st1.peer pk n m)
    logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt n
      c.rIdx stH { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } : Traceful Nat).run tr).2.property

private theorem provEvTR_decTailTr {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st₀ st1 : TRState} {c c' : RecvChain} {fresh : Bool} {pk seed pqSalt m spqr' : DY.Bytes} {n : UInt32}
    (hEv : ProvEvTR tr) (hst₀ : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt me st₀ stH tr) (hpkK : pk.AttackerKnows tr)
    (hrc : recvChainFor st₀.toDRState pk = some (c, fresh))
    (hmem : c ∈ st1.recv) (hrk : c.ratchetKey = pk) (hini : st1.sessionInfo me = st₀.sessionInfo me)
    (hcons : consumeMessageKey c n = some (seed, c')) :
    ProvEvTR (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := by
  have hrk' : c'.ratchetKey = pk := (prov_consumeMessageKey_ratchetKey hcons).trans hrk
  have hrIdx' : c'.rIdx = c.rIdx := prov_consumeMessageKey_rIdx hcons
  have hle := decTailTr_le tr me stH st1 c c' pk seed pqSalt m spqr' n
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr
  let tr_rcv := tr_sk.append (TREvE (TREvent.Received me st1.peer pk n m))
  let tr_mk := tr_rcv.append (TREvE (TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stH))
  let st₁_post : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
  have hst₁ : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt me st₁_post tr_mk.length
      (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := by
    unfold decTailTr; exact trStateStoredAt_here _ _ _
  have hc'_mem : c' ∈ st₁_post.recv := List.mem_map.mpr ⟨c, hmem, by simp [hrk, hrk']⟩
  intro s' pk' n' seed' r' src' i hlog
  have hlog' : (tr_mk.append (TRStE me st₁_post)).EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := by
    simpa [decTailTr] using hlog
  rcases eventLoggedAt_append_same (eventLoggedAt_append_other rfl hlog') with ⟨_, hlog_rcv⟩ | ⟨_, heq⟩
  · rcases eventLoggedAt_append_same hlog_rcv with ⟨_, hlog_sk⟩ | ⟨_, heq⟩
    · by_cases hi : i < tr.length
      · have hlog0 : tr.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := by
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
          rw [← at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_sk
          exact hlog_sk
        exact provEvTR_at_mono hle hEv hlog0
      · have hi_lt : i < tr_sk.length := by
          by_contra hge
          have hnone : (tr_sk.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) = none := at?_eq_none_of_le tr_sk (Nat.le_of_not_lt hge)
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, hnone] at hlog_sk; cases hlog_sk
        have hlen_sk : tr_sk.length = tr.length + (n.toNat - c.index.toNat) := logSkippedKeysTr_length _ _ _ _ _ _ _ _
        have hj : i - tr.length < n.toNat - c.index.toNat := by omega
        have hi_eq : i = tr.length + (i - tr.length) := by omega
        have hat := at?_trEntry_logSkippedKeysTr_add (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr hj
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, hi_eq, hat] at hlog_sk; cases hlog_sk
        obtain ⟨c₀', hc0⟩ := consumeMessageKey_skipped_tr hcons hj
        exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hpkK,
          ⟨me, st₁_post, tr_mk.length, c', hst₁, hc'_mem, hrk', hrIdx', rfl⟩,
          .inl ⟨me, st₀, c, fresh, c₀', trStateStoredAt_mono hle hst₀, hini.symm, hrc, hc0⟩⟩
    · nomatch heq
  · nomatch heq

private theorem consumeMessageKey_index_gt {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) {j : Nat}
    (hj : j < counter.toNat - c.index.toNat) :
    (c.index + UInt32.ofNat j).toNat < c'.index.toNat := by
  unfold consumeMessageKey at h
  split at h; · cases h
  rename_i hlt; split at h; · cases h
  rename_i hjump; split at h; · cases h
  rename_i hne; cases h
  have hlt' : c.index.toNat ≤ counter.toNat := by rw [UInt32.lt_iff_toNat_lt] at hlt; omega
  have hcn : counter.toNat < 2 ^ 32 := counter.toNat_lt
  have hcne : counter.toNat ≠ 4294967295 := fun heq => hne (UInt32.toNat_inj.mp (by rw [heq]; rfl))
  have hjNat : (UInt32.ofNat j).toNat = j := UInt32.toNat_ofNat_of_lt' (by change j < 4294967296; omega)
  have hsum : (c.index + UInt32.ofNat j).toNat = c.index.toNat + j := by
    rw [UInt32.toNat_add, hjNat]; exact Nat.mod_eq_of_lt (by omega)
  have h1 : (counter + 1).toNat = counter.toNat + 1 := by
    rw [UInt32.toNat_add]; change (counter.toNat + 1) % 4294967296 = counter.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  dsimp only; rw [hsum, h1]; omega

private theorem provEvTR_decTailTr_bob {tr : ExecTrace} {me : Participant} {stH : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk seed pqSalt m spqr' : DY.Bytes} {n : UInt32}
    (hEv : ProvEvTR tr) (hpkK : pk.AttackerKnows tr)
    (hstH : stH = tr.length + (n.toNat - c.index.toNat) + 2)
    (hinit : st1.initiator = false)
    (hmem : c ∈ st1.recv) (hrk : c.ratchetKey = pk)
    (hcons : consumeMessageKey c n = some (seed, c')) :
    ProvEvTR (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := by
  have hrk' : c'.ratchetKey = pk := (prov_consumeMessageKey_ratchetKey hcons).trans hrk
  have hrIdx' : c'.rIdx = c.rIdx := prov_consumeMessageKey_rIdx hcons
  have hle := decTailTr_le tr me stH st1 c c' pk seed pqSalt m spqr' n
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr
  let tr_rcv := tr_sk.append (TREvE (TREvent.Received me st1.peer pk n m))
  let tr_mk := tr_rcv.append (TREvE (TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stH))
  let st₁_post : TRState := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
  have hlen_sk : tr_sk.length = tr.length + (n.toNat - c.index.toNat) := logSkippedKeysTr_length _ _ _ _ _ _ _ _
  have hlen_mk : tr_mk.length = stH := by simp [tr_mk, tr_rcv, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, hlen_sk, hstH]
  have hst₁_mk : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt me st₁_post tr_mk.length
      (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := by
    unfold decTailTr; exact trStateStoredAt_here _ _ _
  have hst₁ : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt me st₁_post stH
      (decTailTr tr me stH st1 c c' pk seed pqSalt m spqr' n) := hlen_mk ▸ hst₁_mk
  have hc'_mem : c' ∈ st₁_post.recv := List.mem_map.mpr ⟨c, hmem, by simp [hrk, hrk']⟩
  intro s' pk' n' seed' r' src' i hlog
  have hlog' : (tr_mk.append (TRStE me st₁_post)).EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := by
    simpa [decTailTr] using hlog
  rcases eventLoggedAt_append_same (eventLoggedAt_append_other rfl hlog') with ⟨_, hlog_rcv⟩ | ⟨_, heq⟩
  · rcases eventLoggedAt_append_same hlog_rcv with ⟨_, hlog_sk⟩ | ⟨_, heq⟩
    · by_cases hi : i < tr.length
      · have hlog0 : tr.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' r' src') i := by
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
          rw [← at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog_sk
          exact hlog_sk
        exact provEvTR_at_mono hle hEv hlog0
      · have hi_lt : i < tr_sk.length := by
          by_contra hge
          have hnone : (tr_sk.at? i : Option (ProtocolEvent.ExecEntryT TREvent)) = none := at?_eq_none_of_le tr_sk (Nat.le_of_not_lt hge)
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, hnone] at hlog_sk; cases hlog_sk
        have hj : i - tr.length < n.toNat - c.index.toNat := by omega
        have hi_eq : i = tr.length + (i - tr.length) := by omega
        have hat := at?_trEntry_logSkippedKeysTr_add (st1.sessionInfo me) pk c.rIdx stH c.chainKey c.index (n.toNat - c.index.toNat) tr hj
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, hi_eq, hat] at hlog_sk; cases hlog_sk
        exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hpkK,
          ⟨me, st₁_post, stH, c', hst₁, hc'_mem, hrk', hrIdx', rfl⟩,
          .inr ⟨me, st₁_post, c', hst₁, rfl, hinit, hc'_mem, hrk', hrIdx', consumeMessageKey_index_gt hcons hj⟩⟩
    · nomatch heq
  · nomatch heq

private theorem provEvTR_logMessageKeyAndStore (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (mk pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves ProvEvTR (logMessageKeyAndStore me s dir mk pqSalt n rIdx par st) := by
  unfold logMessageKeyAndStore
  exact Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
    preserves_storeLocalState_tr me st (fun _ h => provEvTR_append_other rfl h)

private theorem provEvTR_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat)
    (bh : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves ProvEvTR (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine provEvTR_inertOnNonTR.bind_aliceHandshake a b idStateIdx regIdxB bh tr₀ hInv₀ fun _ => ?_
  refine (?_ : Preserves ProvEvTR _) _ (provEvTR_append_other rfl (provEvTR_append_other rfl hInv₀))
  exact Preserves.bind (preserves_genRand _ fun _ h => provEvTR_append_other rfl h) fun _ =>
    Preserves.bind (preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) fun _ =>
    Preserves.bind (preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) fun _ =>
    Preserves.bind Preserves.traceLength fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_other rfl h) fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
    Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_other rfl h) fun _ =>
    preserves_storeLocalState_tr _ _ fun _ h => provEvTR_append_other rfl h

private theorem run_sendMessage_bind_snd {α : Type} (msg : DY.Bytes) (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val = ((f tr.length).run (tr.append (NetE msg))).2.val := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [run_bind_snd, Traceful.run_mk]

private theorem receiveMessage_trace (idx : Nat) (tr : ExecTrace) :
    ((Network.receiveMessage idx).run tr).2.val = tr :=
  Preserves.receiveMessage (Inv := fun t => t = tr) idx tr rfl

private theorem receiveSignalMsg_trace (msgH : Nat) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH).run tr).2.val = tr :=
  Preserves.receiveSignalMsg (Inv := fun t => t = tr) msgH tr rfl

private theorem ratchetKey_of_recvChainFor_false {st : DRState}
    {pk : DY.Bytes} {c : RecvChain} (h : recvChainFor st pk = some (c, false)) : c.ratchetKey = pk := by
  unfold recvChainFor findRecvChain at h; cases hfind : st.recv.find? (fun d => d.ratchetKey == pk) with
  | some c₀ =>
    rw [hfind] at h; injection h with h; injection h with hc _; subst hc
    exact beq_iff_eq.mp (List.find?_some (p := fun (d : RecvChain) => d.ratchetKey == pk) hfind)
  | none =>
    rw [hfind] at h; cases hlow : x25519LowOrder pk <;> simp only [hlow, ↓reduceIte, Bool.false_eq_true] at h
    · injection h with h; injection h with _ hb; cases hb
    · cases h

private theorem attackerKnows_ratchetKey_of_receiveSignalMsg {tr₀ : ExecTrace} {msgH : Nat} {msg : TRSignalMsg}
    (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH).run tr₀).1 = some msg) :
    msg.ratchetKey.AttackerKnows tr₀ := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h
  rw [run_bind_fst, receiveMessage_fst, receiveMessage_snd] at h
  rcases hat : (tr₀.at? msgH : Option NetEntry) with _ | e; · rw [hat] at h; cases h
  rw [hat] at h; dsimp only at h
  rcases hparse : parseTrSignalMsg e.msg with _ | m₀
  · rw [hparse] at h; dsimp only at h; rw [Traceful.run_failure] at h; cases h
  · rw [hparse] at h; dsimp only at h; unfold _root_.guard at h; split at h
    · rw [run_bind_fst, Traceful.run_pure] at h; dsimp only at h; rw [Traceful.run_pure] at h
      injection h with h; subst h; exact attackerKnows_ratchetKey_of_at?_network hat hparse
    · rw [run_bind_fst, Traceful.run_failure] at h; cases h

private theorem provEvTR_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regIdxA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves ProvEvTR (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr₀ hInv₀; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine InertOnNonTR.bind_bobHandshake b a kh regIdxA mh.ek mh.ct tr₀ hInv₀ fun o => ?_
  rw [run_bind_snd, receiveSignalMsg_trace]
  rcases hrcv : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr₀).1 with _ | msg; · exact hInv₀
  dsimp only
  have hrkK₀ : msg.ratchetKey.AttackerKnows tr₀ := attackerKnows_ratchetKey_of_receiveSignalMsg hrcv
  let st0 : TRState := {
    peer := a, myIk := serializedIk o.ikB, peerIk := serializedIk o.ikA, rk := o.keys.rk,
    dhs := o.spkSk, cks := o.keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (X25519.normalizeX25519Key msg.ratchetKey) o.keys.rk,
    initiator := false, rIdx := 0, recv := [], spqr := Spqr.spqrInit o.keys.pqr spqrB2A }
  refine prov_bind_ensureReceiverChain_tr (Inv := ProvEvTR) st0 msg.ratchetKey tr₀ hInv₀
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
  have hInv₁ : ProvEvTR tr₁ := provEvTR_append_other rfl hInv₀
  rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
  dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
  dsimp only; let tr₂ := tr₁.append (Network.ExecEntryT.mk key)
  have hInv₂ : ProvEvTR tr₂ := provEvTR_append_other rfl hInv₁
  rw [run_sendMessage_bind_snd, run_bind_snd, receiveMessage_trace]
  rcases ((Network.receiveMessage pqIdx).run tr₂).1 with _ | pqSalt; · exact hInv₂
  dsimp only; rw [run_bind_snd, verifyMacAndDecrypt_trace]
  rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₂
  have hc1_mem : c1 ∈ st.recv := List.mem_singleton_self c1
  have hTail : ∀ (t : ExecTrace) (opkOpt : Option DY.Bytes), tr₀ ≤ t → ProvEvTR t →
      ProvEvTR ((do
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
    intro t4 opkOpt hle04 hInv4
    let t5 := t4.append (PQEvE (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk opkOpt o.ek o.ct o.keys))
    let t6 := t5.append (TREvE (TREvent.DHRatchet b st.peer msg.ratchetKey (dhPk st.dhs)))
    let t7 := t6.append (TREvE (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
    let t8 := t7.append (CEvE (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (st.sessionInfo b) t4.length))
    have hInv8 : ProvEvTR t8 :=
      provEvTR_append_other rfl (provEvTR_append_tr (by intro _ _ _ _ _ _; nofun)
        (provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) (provEvTR_append_other rfl hInv4)))
    have hle08 : tr₀ ≤ t8 :=
      Trace.le_trans _ _ _ hle04 (Trace.le_trans _ _ _ (Trace.append_le t4 _)
        (Trace.le_trans _ _ _ (Trace.append_le t5 _) (Trace.le_trans _ _ _ (Trace.append_le t6 _) (Trace.append_le t7 _))))
    rw [run_traceLength_bind_snd, run_logEvent_bind_snd]
    simp only [↓reduceIte]
    rw [run_logEvent_bind_snd, run_logEvent_bind_snd, run_logEvent_bind_snd,
      run_traceLength_bind_snd, decTailTr_run]
    exact provEvTR_decTailTr_bob hInv8 (DY.Bytes.AttackerKnows_le _ _ _ hle08 hrkK₀) rfl rfl hc1_mem rfl hcons
  have hle02 : tr₀ ≤ tr₂ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) (Trace.append_le tr₁ _)
  cases o.opk with
  | none =>
    dsimp only [Option.map]
    exact hTail tr₂ none hle02 hInv₂
  | some opkPk =>
    dsimp only [Option.map]
    have hguard : ((DY.Libsignal.PQXDH.guardTrace fun tr => !DY.Libsignal.PQXDH.opkUsedB tr b opkPk).run tr₂).2.val = tr₂ :=
      Preserves.requireTracePredicate (Inv := fun t => t = tr₂) _ tr₂ rfl
    rw [run_bind_snd]
    rcases ((DY.Libsignal.PQXDH.guardTrace fun tr => !DY.Libsignal.PQXDH.opkUsedB tr b opkPk).run tr₂).1 with _ | _
    · rw [hguard]; exact hInv₂
    · dsimp only; rw [hguard, run_logEvent_bind_snd]
      exact hTail (tr₂.append (PQEvE (.OPKUsed b opkPk))) (some opkPk)
        (Trace.le_trans _ _ _ hle02 (Trace.append_le tr₂ _)) (provEvTR_append_other rfl hInv₂)

private theorem provEvTR_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves ProvEvTR (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine prov_bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  rw [run_bind_snd, receiveSignalMsg_trace]
  rcases hrcv : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgH).run tr₀).1 with _ | msg; · exact hInv₀
  dsimp only; have hrkK₀ : msg.ratchetKey.AttackerKnows tr₀ := attackerKnows_ratchetKey_of_receiveSignalMsg hrcv
  refine prov_bind_ensureReceiverChain_tr (Inv := ProvEvTR) st₀ msg.ratchetKey tr₀ hInv₀
    (fun c hc_find => ?_) (fun hfind hlow => ?_)
  · dsimp only; rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₀
    dsimp only; rcases Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₀
    dsimp only; let tr₁ := tr₀.append (Network.ExecEntryT.mk key)
    have hInv₁ : ProvEvTR tr₁ := provEvTR_append_other rfl hInv₀
    rw [run_sendMessage_bind_snd, run_bind_snd, receiveMessage_trace]
    rcases ((Network.receiveMessage pqIdx).run tr₁).1 with _ | pqSalt; · exact hInv₁
    dsimp only; rw [run_bind_snd, verifyMacAndDecrypt_trace]
    rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₁
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [decTailTr_run]
    exact provEvTR_decTailTr hInv₁ (trStateStoredAt_mono (Trace.append_le tr₀ _) hst₀)
      (DY.Bytes.AttackerKnows_le _ _ _ (Trace.append_le tr₀ _) hrkK₀) hc_find
      (mem_recv_of_recvChainFor_false hc_find) (ratchetKey_of_recvChainFor_false hc_find) rfl hcons
  · dsimp only; let dhs := Symbolic.Swarm.COMPOSED.CompTrace.mkRand tr₀.length 32
    let c1 : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2, index := 0, rIdx := st₀.rIdx + 2 }
    let st : TRState := { st₀ with
      rk := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).1, dhs := dhs,
      cks := (createChain (createChain st₀.rk msg.ratchetKey st₀.dhs).1 msg.ratchetKey dhs).2, ns := 0,
      pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
      recv := (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains) }
    let tr₁ := tr₀.append (Random.ExecEntryT.mk 32)
    have hInv₁ : ProvEvTR tr₁ := provEvTR_append_other rfl hInv₀
    rcases hcons : consumeMessageKey c1 msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    dsimp only; rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hInv₁
    dsimp only; let tr₂ := tr₁.append (Network.ExecEntryT.mk key)
    have hInv₂ : ProvEvTR tr₂ := provEvTR_append_other rfl hInv₁
    rw [run_sendMessage_bind_snd, run_bind_snd, receiveMessage_trace]
    rcases ((Network.receiveMessage pqIdx).run tr₂).1 with _ | pqSalt; · exact hInv₂
    dsimp only; rw [run_bind_snd, verifyMacAndDecrypt_trace]
    rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _ msg pqSalt seed).run _).1 with _ | m; · exact hInv₂
    let tr₃ := tr₂.append (TREvE (TREvent.DHRatchet me st.peer msg.ratchetKey (dhPk st.dhs)))
    let tr₄ := tr₃.append (TREvE (TREvent.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2)))
    have hInv₄ : ProvEvTR tr₄ := provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) (provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) hInv₂)
    have hle04 : tr₀ ≤ tr₄ :=
      Trace.le_trans _ _ _ (Trace.append_le tr₀ _) (Trace.le_trans _ _ _ (Trace.append_le tr₁ _)
        (Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)))
    have hc1_mem : c1 ∈ st.recv := by
      show c1 ∈ (st₀.recv ++ [c1]).drop ((st₀.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains)
      rw [List.drop_append_of_le_length (by change (st₀.recv.length + 1) - 5 ≤ st₀.recv.length; omega)]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    simp only [↓reduceIte]
    rw [run_logEvent_bind_snd, run_logEvent_bind_snd,
      decTailTr_run me stH st c1 c' msg.ratchetKey seed pqSalt m spqr' msg.counter tr₄]
    have hrc_c1 : recvChainFor st₀.toDRState msg.ratchetKey = some (c1, true) := by
      unfold recvChainFor; rw [hfind]; simp [hlow, c1]
    exact provEvTR_decTailTr hInv₄ (trStateStoredAt_mono hle04 hst₀) (DY.Bytes.AttackerKnows_le _ _ _ hle04 hrkK₀)
      hrc_c1 hc1_mem rfl rfl hcons

theorem provEvTR_reachable {tr : ExecTrace} (hreach : tr.Reachable reachability) : ProvEvTR tr :=
  provEvTR_inertOnNonTR.reachable_induction
    (fun _ _ _ _ _ _ _ h => by
      simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
        Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h)
    provEvTR_aliceStart provEvTR_bobStart
    (fun me stH coinsLen pqIdx => by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt
      refine Preserves.bind (Preserves.getLocalState_tr me stH) fun st => Preserves.bind (Preserves.guardP _) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => provEvTR_append_other rfl h) fun _ =>
        Preserves.bind (preserves_genRand _ fun _ h => provEvTR_append_other rfl h) fun coins => ?_
      dsimp only; rcases Spqr.spqrSend st.spqr coins with ⟨spqr', pqPayload, pqSalt⟩
      exact Preserves.bind (preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) fun _ =>
        Preserves.bind (Preserves.receiveMessage pqIdx) fun _ =>
        Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
        Preserves.bind (provEvTR_logMessageKeyAndStore _ _ .sender _ _ _ _ _ _) fun _ =>
        preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h)
    provEvTR_messageDecrypt
    (fun me stH msgH evH pqIdx spqrMsgIdx => by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
      refine Preserves.bind (Preserves.getLocalState_tr me stH) fun st =>
        Preserves.bind (Preserves.receiveSignalMsg msgH) fun msg =>
        Preserves.bind (Preserves.getEntry (E := ProtocolEvent.ExecEntryT TREvent) evH) fun e => ?_
      rcases e with ⟨ev⟩; cases ev with
      | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
        dsimp only; refine Preserves.bind (Preserves.guardP _) fun _ => Preserves.bind (Preserves.guardTrace _) fun _ => ?_
        split
        · next spqr' key _ =>
          exact Preserves.bind (preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) fun _ =>
            Preserves.bind (Preserves.receiveMessage pqIdx) fun _ => Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
            Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
            Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
            provEvTR_logMessageKeyAndStore me s .receiver seed _ n rIdx stH { st with spqr := spqr' }
        · exact Preserves.failure
      | _ => exact Preserves.failure)
    (fun me stH k => by
      unfold DY.Libsignal.TripleRatchet.exposeKey
      refine prov_bind_getLocalState_tr me stH fun st tr₀ hInv₀ _ => ?_
      cases k with
      | rk | dhs | cks =>
        exact (Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
          preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) tr₀ hInv₀
      | ckr pk =>
        dsimp only
        cases findRecvChain st.recv pk with
        | none => dsimp only; rw [Traceful.run_failure]; exact hInv₀
        | some _ =>
          dsimp only
          exact (Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
            preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) tr₀ hInv₀)
    (fun me stH => by
      unfold DY.Libsignal.TripleRatchet.exposeSpqr
      exact prov_bind_getLocalState_tr me stH fun _ tr₀ hInv₀ _ =>
        (Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
          preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h) tr₀ hInv₀)
    (fun evH => by
      unfold DY.Libsignal.TripleRatchet.exposeSkipped
      exact Preserves.bind (Preserves.getEntry (E := ProtocolEvent.ExecEntryT TREvent) evH) fun ⟨ev⟩ tr₀ hInv₀ => by
        cases ev with
        | SkippedKeyStored _ _ _ _ _ _ =>
          dsimp only; refine (Preserves.bind (Preserves.guardTrace _) fun _ => ?_) tr₀ hInv₀
          exact Preserves.bind (preserves_logEvent _ fun _ h => provEvTR_append_tr (by intro _ _ _ _ _ _; nofun) h) fun _ =>
            preserves_sendMessage _ fun _ h => provEvTR_append_other rfl h
        | _ => dsimp only; rw [Traceful.run_failure]; exact hInv₀)
    hreach

end ProvEvTRReachableProof

/-- Every logged `SkippedKeyStored` event arises either from an available provenance state
`st_prov` with `recvSeed st_prov msg₀ = some seed` or from an initial `bobStart` receiver
chain at counter `msg₀.counter < c₀.index`. -/
theorem provEvTR_st_prov_or_bobStart
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (ms₁ : List Move)
    (p : Participant) (st₀ : TRState) (stateIdx₀ : Nat)
    (m : SignalMessage) (msg₀ : TRSignalMsg)
    (pk seed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hRun : ModelRun r₀ ms₁)
    (hst₀ : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter) :
    (∃ (st_prov : TRState) (k_own : DY.Bytes),
      st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
      (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) ∧
      (∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter →
        recvSeed st_prov msg = some seed) ∧
      k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st_prov msg₀ ∧
      st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧ st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁)) ∨
    (∃ (p₀ : Participant) (st₀_src : TRState) (c₀ : RecvChain) (k_own : DY.Bytes),
      Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p₀ st₀_src srcIdx (runTraceMoves r₀ ms₁) ∧
      st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
      (st₀_src.peerIk = st₀.peerIk ∧ st₀_src.myIk = st₀.myIk) ∧
      st₀_src.sessionInfo p₀ = st₀.sessionInfo p ∧ st₀_src.initiator = false ∧
      c₀ ∈ st₀_src.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ msg₀.counter < c₀.index ∧
      k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀ ∧
      st₀_src.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧ st₀_src.myIk.AttackerKnows (runTraceMoves r₀ ms₁)) := by
  obtain ⟨_hrkK, _hpost, hProvMB⟩ :=
    provEvTR_reachable hRun.2.2.1.1 (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx skIdx hlog
  have hst₀_at : Symbolic.Swarm.CREF.TR.G1.TRStateStoredAt p st₀ stateIdx₀ (runTraceMoves r₀ ms₁) :=
    at?_eq_some_of_getLocalState_some hst₀
  have hst₀_avail : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
    Symbolic.Swarm.CREF.TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms₁ hst₀_at
  have hik₀ : IkShapeTR r₀ (runTraceMoves r₀ ms₁) p st₀ := ikShapeTR_of_trStateStoredAt hRun hst₀_at
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  rcases hProvMB with
    ⟨p₀, st₀_src, c₀, fresh, c₀', hst₀_src_at, hsinfo_src, hrc₀, hcons₀⟩ |
    ⟨p₀, st₀_src, c₀, hst₀_src_at, hsinfo_src, hinit_false, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩
  · have hst₀_src_avail : st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
      Symbolic.Swarm.CREF.TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms₁ hst₀_src_at
    have hik_src : IkShapeTR r₀ (runTraceMoves r₀ ms₁) p₀ st₀_src := ikShapeTR_of_trStateStoredAt hRun hst₀_src_at
    obtain ⟨hIkEq, hPeerK, hMyK⟩ := ik_eq_and_known_of_ikShapeTR r₀ (runTraceMoves r₀ ms₁) hwf hik_src hik₀ hsinfo_src
    have hseed_pk : ∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter →
        recvSeed st₀_src msg = some seed := by
      intro msg hver hrk_eq hctr_eq
      unfold recvSeed; simp only [hver, ↓reduceIte, hrk_eq, hrc₀, hctr_eq.trans hctr₀, hcons₀, Option.map]
    have hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀ := by
      unfold ownKeys
      refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, ?_⟩)
      rw [hIkEq.2.2]; exact beq_self_eq_true _
    exact Or.inl ⟨st₀_src, k_own, hst₀_src_avail, ⟨hIkEq.1, hIkEq.2.1⟩, hseed_pk, rfl, hk_own, hPeerK, hMyK⟩
  · have hst₀_src_avail : st₀_src ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
      Symbolic.Swarm.CREF.TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms₁ hst₀_src_at
    have hik_src : IkShapeTR r₀ (runTraceMoves r₀ ms₁) p₀ st₀_src := ikShapeTR_of_trStateStoredAt hRun hst₀_src_at
    obtain ⟨hIkEq, hPeerK, hMyK⟩ := ik_eq_and_known_of_ikShapeTR r₀ (runTraceMoves r₀ ms₁) hwf hik_src hik₀ hsinfo_src
    have hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀_src msg₀ := by
      unfold ownKeys
      refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, ?_⟩)
      rw [hIkEq.2.2]; exact beq_self_eq_true _
    exact Or.inr ⟨p₀, st₀_src, c₀, k_own, hst₀_src_at, hst₀_src_avail, ⟨hIkEq.1, hIkEq.2.1⟩,
      hsinfo_src, hinit_false, hc₀, hc₀_rk, hc₀_rIdx, hctr₀.symm ▸ hlt, rfl, hk_own, hPeerK, hMyK⟩

end Symbolic.Swarm.CREF.TR.RecvDecStep
