/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecordsBridgePure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
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
public meta import Mathlib.Tactic.ToAdditive
public import Symbolic.Proofs.Swarm.CREF.RelPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TRView
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.MacInv -- shake: keep
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
# Pre-Key Representations and `bobStart` Visible Trace Lemmas

Proves non-emptiness and trace monotonicity of `preKeyRepresentations` on an accepting pre-key
wire, and computes the random draws, completion event index, received plaintext, and visible trace
entries of `Move.bobStart`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoGames.LibsignalSession (SignalMessage)
open DY.Libsignal.HwEvents (StateAndMessage)

private theorem rpk_parsePreKey_inv {v : HwBytes} {p : PreKeyFields}
    (h : parsePreKey v = some p) :
    ecKeyParses p.baseKey = true ∧ ecKeyParses p.identityKey = true ∧
    SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKey at h
  rcases v with _ | ⟨vb, body⟩; · cases h
  dsimp only at h; split at h; · cases h
  rcases hd : decodePreKey body with _ | m; · rw [hd] at h; cases h
  rw [hd] at h; dsimp only at h
  rcases hbk : m.baseKey with _ | bk; · rw [hbk] at h; cases h
  rcases hik : m.identityKey with _ | ik; · rw [hbk, hik] at h; cases h
  rcases hmsg : m.message with _ | msg; · rw [hbk, hik, hmsg] at h; cases h
  rcases hsid : m.signedPreKeyId with _ | sid; · rw [hbk, hik, hmsg, hsid] at h; cases h
  rw [hbk, hik, hmsg, hsid] at h; dsimp only at h; split at h
  · next hcond =>
    rcases htry : SignalMessage.tryFrom protoSignalCodec msg with _ | inner
    · rw [htry] at h; cases h
    · rw [htry] at h; injection h with hp; subst hp
      simp only [Bool.and_eq_true] at hcond; exact ⟨hcond.1.2, hcond.2, htry⟩
  · cases h

private theorem rpk_parsePreKeyWire_inv {b : HwBytes} {p : PreKeyFields}
    (h : parsePreKeyWire b = some p) :
    ecKeyParses p.baseKey = true ∧ ecKeyParses p.identityKey = true ∧
    SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at h
  rcases b with _ | ⟨t, body⟩; · cases h
  dsimp only at h; split at h; (exact rpk_parsePreKey_inv h); cases h

private theorem rpk_ecKey_take33_of_ecKeyParses {bk : HwBytes} (h : ecKeyParses bk = true) :
    bk.take 33 = ecKey ((bk.drop 1).take 32) ∧ ((bk.drop 1).take 32).length = 32 := by
  unfold ecKeyParses at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases bk with _ | ⟨b0, rest⟩; · simp at h
  simp only [List.head?_cons, Option.some.injEq] at h; rcases h with ⟨rfl, hlen⟩
  simp only [List.length_cons] at hlen
  simp only [List.take_succ_cons, List.drop_succ_cons, List.drop_zero, ecKey,
    true_and, List.length_take]; omega

/-- `preKeyRepresentations` is non-empty for any well-formed v4 pre-key wire carrying an honest
peer identity and matching pre-key identifiers. -/
theorem rpk_reps_nonempty (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (b : HwBytes) (p : PreKeyFields) (ct_bytes : HwBytes)
    (hp : parsePreKeyWire b = some p) (hv4 : p.version = 4)
    (hspk : p.signedPreKeyId = r.spkId) (hkpk : p.kyberPreKeyId = some r.kpkId)
    (hct : p.kyberCiphertext = some (kyberKey ct_bytes))
    (hhon : HonestIdentity interpretation r b)
    (hopk : p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId)) :
    ∃ x, x ∈ preKeyRepresentations interpretation r S g ms b := by
  obtain ⟨hbk, _, htry⟩ := rpk_parsePreKeyWire_inv hp
  obtain ⟨hbk_eq, _⟩ := rpk_ecKey_take33_of_ecKeyParses hbk
  obtain ⟨t, msg, ⟨ht_ak, ht_gamma, _, ht_fields⟩, hparse, _, _, _⟩ :=
    TR.RecvRep.decrypt_recvRepresentations_nonempty_of_tryFrom
      interpretation r S g ms p.message p.inner htry
  obtain ⟨hw, hmac, hspqr, hinner⟩ := ht_fields msg hparse
  obtain ⟨hcipher, hrk, hpq, hctr, hver⟩ := hinner p.inner htry
  let ek_bytes := (p.baseKey.drop 1).take 32
  have hopk_named : ∃ used, OpkNamed r b used := by
    rcases hopk with hnone | ⟨hw_opk, hsome⟩
    · exact ⟨false, p, hp, hnone⟩
    · exact ⟨true, p, hp, hsome, hw_opk⟩
  refine ⟨{ ek := litOf ek_bytes, ct := litOf ct_bytes, msg := t },
    TR.RecvRep.knows_litOf ek_bytes _, TR.RecvRep.knows_litOf ct_bytes _, ht_ak,
    ⟨p, hp, ?_, ?_, ht_gamma.symm, hv4, hspk, hkpk, hhon p hp, hopk_named⟩,
    p, hp, msg, hparse, hw, hmac, hspqr, hcipher, hrk, hpq, hctr, hver⟩
  · rw [TR.RecvRep.gamma_litOf]; exact hbk_eq
  · rw [TR.RecvRep.gamma_litOf]; exact hct

theorem rpk_reps_nonempty_of_contract {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} (g : Ghost) (ms : List Move) {used : Bool} {b : HwBytes}
    {sm : StateAndMessage} {p : PreKeyFields} {d ct_bytes pt : HwBytes}
    (hhon : HonestIdentity interpretation r b)
    (hC : RecvAcceptContractPure interpretation r used b sm p d ct_bytes pt) :
    ∃ x, x ∈ preKeyRepresentations interpretation r S g ms b :=
  rpk_reps_nonempty interpretation r S g ms b p ct_bytes hC.parse hC.outer_ver
    hC.spkId_eq hC.kpkId_eq hC.kyber_ct hhon
    (hC.opk_ok.imp id fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩)

theorem preKeyRepresentations_mono_append {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms ms' : List Move} {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) :
    x ∈ preKeyRepresentations interpretation r S g (ms ++ ms') b := by
  have hle := runTrace_le_append r ms ms'
  exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hx.1, DY.Bytes.AttackerKnows_le _ _ _ hle hx.2.1,
    DY.Bytes.AttackerKnows_le _ _ _ hle hx.2.2.1, hx.2.2.2⟩

open Symbolic.Swarm.CREF.TR (EvE NetE RndE)
open Symbolic.Swarm.COMPOSED
open DY.Libsignal.TripleRatchet (TRSignalMsg)

private theorem newIndices_trans {tr₀ tr₁ tr₂ : ExecTrace} (h01 : tr₀ ≤ tr₁) (h12 : tr₁ ≤ tr₂) :
    newIndices tr₀ tr₂ = newIndices tr₀ tr₁ ++ newIndices tr₁ tr₂ := by
  unfold newIndices; have hlen01 := Trace.length_le tr₀ tr₁ h01; have hlen12 := Trace.length_le tr₁ tr₂ h12
  have hadd : tr₂.length - tr₀.length = (tr₁.length - tr₀.length) + (tr₂.length - tr₁.length) := by omega
  have hmid : tr₀.length + (tr₁.length - tr₀.length) = tr₁.length := by omega
  rw [hadd, ← List.range'_append_1, hmid]

private theorem mem_newIndices_lt {tr₀ tr₁ : ExecTrace} {i : Nat} (hi : i ∈ newIndices tr₀ tr₁) :
    i < tr₁.length := by
  unfold newIndices at hi; rw [List.mem_range'] at hi; rcases hi with ⟨k, hk, rfl⟩; omega

private theorem newIndices_append_singleton {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    newIndices tr (tr.append e) = [tr.length] := by
  unfold newIndices; have hlen : (tr.append e).length - tr.length = 1 := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen]; rfl

theorem at?_append_self_proj {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by simp [Symbolic.DYBridge.DY.Trace.length_eq_2]
  simp only [Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

private theorem newRandoms_trans {tr₀ tr₁ tr₂ : ExecTrace} (h01 : tr₀ ≤ tr₁) (h12 : tr₁ ≤ tr₂) :
    newRandoms tr₀ tr₂ = newRandoms tr₀ tr₁ ++ newRandoms tr₁ tr₂ := by
  unfold newRandoms; rw [newIndices_trans h01 h12, List.filterMap_append]; congr 1
  exact List.filterMap_congr fun i hi => by rw [at?_of_le h12 (mem_newIndices_lt hi)]

private theorem newRandoms_append_rnd_self (tr : ExecTrace) (n : Nat) :
    newRandoms tr (tr.append (RndE n)) = [(randTerm tr.length n, n)] := by
  unfold newRandoms; rw [newIndices_append_singleton, List.filterMap_cons, List.filterMap_nil,
    at?_append_self_proj, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq]; rfl

private theorem newRandoms_append_other {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none := by rfl) :
    newRandoms tr (tr.append e) = [] := by
  unfold newRandoms; rw [newIndices_append_singleton, List.filterMap_cons, List.filterMap_nil,
    at?_append_self_proj, hnone]; rfl

private theorem append_le_of_le {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    {e : E} (hle : tr₀ ≤ tr) : tr₀ ≤ tr.append e :=
  Trace.le_trans tr₀ tr (tr.append e) hle (Trace.append_le tr e)

macro "rpk_le_tac" : tactic => `(tactic|
  repeat (first | exact Trace.le_refl _ | assumption | apply append_le_of_le))

private theorem newRandoms_snoc_other {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    {e : E} (hle : tr₀ ≤ tr := by rpk_le_tac)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none := by rfl) :
    newRandoms tr₀ (tr.append e) = newRandoms tr₀ tr := by
  rw [newRandoms_trans hle (Trace.append_le tr e), newRandoms_append_other tr e hnone, List.append_nil]

private theorem newRandoms_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      newRandoms tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val = []
  | 0, _, _, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; simp only [DY.Traceful.run_pure]
    unfold newRandoms; rw [newIndices_self]; rfl
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    let tr₁ := tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    have hlog_run :
        (DY.ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
          s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx)).run tr =
        (some (), ⟨tr₁, Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1]
      rfl
    rw [DY.Traceful.run_bind, hlog_run]
    dsimp only
    rw [newRandoms_trans (Trace.append_le tr _)
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
        (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.property,
      newRandoms_append_other tr _, newRandoms_logSkippedKeys s pk rIdx srcIdx k _ _ tr₁]; rfl

private theorem getEventAt_of_le (Ev : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT Ev)]
    {tr₁ tr₂ : ExecTrace} (h12 : tr₁ ≤ tr₂) {i : Nat} (hi : i < tr₁.length) :
    tr₂.getEventAt Ev i = tr₁.getEventAt Ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [at?_of_le h12 hi]

private theorem getEventAt_append_self (Ev : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT Ev)]
    (tr : ExecTrace) (ev : Ev) :
    (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT Ev)).getEventAt Ev tr.length = some ev := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [at?_append_self_proj, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq]

private theorem getEventAt_append_other (Ev : Type) [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT Ev)]
    {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT Ev)) = none := by rfl) :
    (tr.append e).getEventAt Ev tr.length = none := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [at?_append_self_proj, hnone]

private theorem eventIdx_trans {p : PQXDH.PQXDHEvent → Bool} {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : tr₀ ≤ tr₁) (h12 : tr₁ ≤ tr₂) :
    eventIdx p tr₀ tr₂ = (eventIdx p tr₀ tr₁).or (eventIdx p tr₁ tr₂) := by
  unfold eventIdx; rw [newIndices_trans h01 h12, List.find?_append]; congr 1
  have hcongr : ∀ l : List Nat, (∀ i ∈ l, i < tr₁.length) →
      (l.find? fun i => ((tr₂.getEventAt PQXDH.PQXDHEvent i).map p).getD false) =
      (l.find? fun i => ((tr₁.getEventAt PQXDH.PQXDHEvent i).map p).getD false) := by
    intro l hl; induction l with
    | nil => rfl
    | cons i is ih =>
      simp only [List.find?_cons]
      rw [getEventAt_of_le PQXDH.PQXDHEvent h12 (hl i List.mem_cons_self),
        ih (fun j hj => hl j (List.mem_cons_of_mem i hj))]
  exact hcongr (newIndices tr₀ tr₁) fun i hi => mem_newIndices_lt hi

private theorem eventIdx_append_pq (p : PQXDH.PQXDHEvent → Bool) (tr : ExecTrace)
    (ev : PQXDH.PQXDHEvent) :
    eventIdx p tr (tr.append (EvE ev)) = if p ev then some tr.length else none := by
  unfold eventIdx; rw [newIndices_append_singleton, List.find?_cons, List.find?_nil, getEventAt_append_self]
  cases h : p ev <;> simp [h]

private theorem eventIdx_append_other (p : PQXDH.PQXDHEvent → Bool)
    {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by rfl) :
    eventIdx p tr (tr.append e) = none := by
  unfold eventIdx; rw [newIndices_append_singleton, List.find?_cons, List.find?_nil,
    getEventAt_append_other _ tr e hnone]; rfl

private theorem eventIdx_snoc_other {p : PQXDH.PQXDHEvent → Bool}
    {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace} {e : E}
    (hle : tr₀ ≤ tr := by rpk_le_tac)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by rfl) :
    eventIdx p tr₀ (tr.append e) = eventIdx p tr₀ tr := by
  rw [eventIdx_trans hle (Trace.append_le tr e), eventIdx_append_other p tr e hnone, Option.or_none]

private theorem eventIdx_logSkippedKeys (p : PQXDH.PQXDHEvent → Bool)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      eventIdx p tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val = none
  | 0, _, _, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; simp only [DY.Traceful.run_pure]
    unfold eventIdx; rw [newIndices_self]; rfl
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    let tr₁ := tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    have hlog_run :
        (DY.ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
          s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx)).run tr =
        (some (), ⟨tr₁, Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1]
      rfl
    rw [DY.Traceful.run_bind, hlog_run]
    dsimp only
    rw [eventIdx_trans (Trace.append_le tr _)
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
        (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.property,
      eventIdx_append_other p tr _, eventIdx_logSkippedKeys p s pk rIdx srcIdx k _ _ tr₁]; rfl

private theorem receivedPlaintext_trans {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : tr₀ ≤ tr₁) (h12 : tr₁ ≤ tr₂) :
    receivedPlaintext tr₀ tr₂ = (receivedPlaintext tr₀ tr₁).or (receivedPlaintext tr₁ tr₂) := by
  unfold receivedPlaintext; rw [newIndices_trans h01 h12, List.findSome?_append]; congr 1
  have hcongr : ∀ l : List Nat, (∀ i ∈ l, i < tr₁.length) →
      (l.findSome? fun i => match tr₂.getEventAt DY.Libsignal.TripleRatchet.TREvent i with
        | some (.Received _ _ _ _ m) => some m | _ => none) =
      (l.findSome? fun i => match tr₁.getEventAt DY.Libsignal.TripleRatchet.TREvent i with
        | some (.Received _ _ _ _ m) => some m | _ => none) := by
    intro l hl; induction l with
    | nil => rfl
    | cons i is ih =>
      simp only [List.findSome?_cons]
      rw [getEventAt_of_le _ h12 (hl i List.mem_cons_self),
        ih (fun j hj => hl j (List.mem_cons_of_mem i hj))]
  exact hcongr (newIndices tr₀ tr₁) fun i hi => mem_newIndices_lt hi

private theorem receivedPlaintext_append_tr (tr : ExecTrace)
    (ev : DY.Libsignal.TripleRatchet.TREvent) :
    receivedPlaintext tr (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE ev)) =
      match ev with | .Received _ _ _ _ m => some m | _ => none := by
  unfold receivedPlaintext; rw [newIndices_append_singleton, List.findSome?_cons, List.findSome?_nil, getEventAt_append_self]
  cases ev <;> rfl

private theorem receivedPlaintext_append_other {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) = none := by rfl) :
    receivedPlaintext tr (tr.append e) = none := by
  unfold receivedPlaintext; rw [newIndices_append_singleton, List.findSome?_cons, List.findSome?_nil,
    getEventAt_append_other _ tr e hnone]

private theorem receivedPlaintext_snoc_other {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    {e : E} (hle : tr₀ ≤ tr := by rpk_le_tac)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) = none := by rfl) :
    receivedPlaintext tr₀ (tr.append e) = receivedPlaintext tr₀ tr := by
  rw [receivedPlaintext_trans hle (Trace.append_le tr e),
    receivedPlaintext_append_other tr e hnone, Option.or_none]

private theorem receivedPlaintext_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      receivedPlaintext tr
        ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val = none
  | 0, _, _, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; simp only [DY.Traceful.run_pure]
    unfold receivedPlaintext; rw [newIndices_self]; rfl
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    let tr₁ := tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    have hlog_run :
        (DY.ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
          s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx)).run tr =
        (some (), ⟨tr₁, Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1]
      rfl
    rw [DY.Traceful.run_bind, hlog_run]
    dsimp only
    rw [receivedPlaintext_trans (Trace.append_le tr _)
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
        (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.property,
      receivedPlaintext_append_tr tr _, receivedPlaintext_logSkippedKeys s pk rIdx srcIdx k _ _ tr₁]; rfl

private theorem bobStartPreSkipTr_le (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) :
    tr ≤ bobStartPreSkipTr tr b a o msg key := by
  unfold bobStartPreSkipTr; dsimp only; cases o.opk <;> rpk_le_tac

private abbrev bobSkipTr (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) : ExecTrace :=
  let tr_pre := bobStartPreSkipTr tr b a o msg key
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
  let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
  let skipped := msg.counter.toNat - c.index.toNat
  ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx
    (tr_pre.length + skipped + 2) c.chainKey c.index skipped).run tr_pre).2.val

private theorem bobStartPreSkipTr_le_bobSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) : bobStartPreSkipTr tr b a o msg key ≤ bobSkipTr tr b a o msg key :=
  ((DY.Libsignal.TripleRatchet.logSkippedKeys _ _ _ _ _ _ _).run _).2.property

private theorem newRandoms_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    newRandoms tr (bobStartPreSkipTr tr b a o msg key) = [(randTerm tr.length 32, 32)] := by
  unfold bobStartPreSkipTr; dsimp only; cases o.opk with
  | none =>
    rw [newRandoms_snoc_other, newRandoms_snoc_other, newRandoms_snoc_other,
      newRandoms_snoc_other, newRandoms_snoc_other, newRandoms_append_rnd_self]
  | some _ =>
    rw [newRandoms_snoc_other, newRandoms_snoc_other, newRandoms_snoc_other,
      newRandoms_snoc_other, newRandoms_snoc_other, newRandoms_snoc_other,
      newRandoms_append_rnd_self]

theorem newRandoms_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    newRandoms tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) = [(randTerm tr.length 32, 32)] := by
  unfold bobStartTr; dsimp only
  have hpre := bobStartPreSkipTr_le tr b a o msg key; have hskip := bobStartPreSkipTr_le_bobSkipTr tr b a o msg key
  have hle1 := Trace.le_trans _ _ _ hpre hskip
  rw [newRandoms_snoc_other, newRandoms_snoc_other, newRandoms_snoc_other,
    newRandoms_trans hpre hskip, newRandoms_logSkippedKeys, newRandoms_bobStartPreSkipTr, List.append_nil]

private theorem eventIdx_bobDone_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (key : DY.Bytes) :
    eventIdx isBobDone tr (bobStartPreSkipTr tr b a o msg key) =
      some (match o.opk with
        | some opkPk => ((tr.append (RndE 32)).append (NetE key)).append (EvE (.OPKUsed b opkPk))
        | none => (tr.append (RndE 32)).append (NetE key)).length := by
  unfold bobStartPreSkipTr; dsimp only; cases o.opk with
  | none =>
    rw [eventIdx_snoc_other, eventIdx_snoc_other, eventIdx_snoc_other,
      eventIdx_trans (by rpk_le_tac) (Trace.append_le _ _), eventIdx_append_pq,
      eventIdx_snoc_other, eventIdx_append_other isBobDone tr (RndE 32)]; rfl
  | some _ =>
    rw [eventIdx_snoc_other, eventIdx_snoc_other, eventIdx_snoc_other,
      eventIdx_trans (by rpk_le_tac) (Trace.append_le _ _), eventIdx_append_pq,
      eventIdx_trans (by rpk_le_tac) (Trace.append_le _ _), eventIdx_append_pq,
      eventIdx_snoc_other, eventIdx_append_other isBobDone tr (RndE 32)]; rfl

theorem eventIdx_bobDone_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    eventIdx isBobDone tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) =
      some (match o.opk with
        | some opkPk => ((tr.append (RndE 32)).append (NetE key)).append (EvE (.OPKUsed b opkPk))
        | none => (tr.append (RndE 32)).append (NetE key)).length := by
  unfold bobStartTr; dsimp only
  have hpre := bobStartPreSkipTr_le tr b a o msg key; have hskip := bobStartPreSkipTr_le_bobSkipTr tr b a o msg key
  have hle1 := Trace.le_trans _ _ _ hpre hskip
  rw [eventIdx_snoc_other, eventIdx_snoc_other, eventIdx_snoc_other,
    eventIdx_trans hpre hskip, eventIdx_logSkippedKeys, eventIdx_bobDone_bobStartPreSkipTr, Option.or_none]; rfl

private theorem receivedPlaintext_bobStartPreSkipTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) :
    receivedPlaintext tr (bobStartPreSkipTr tr b a o msg key) = none := by
  unfold bobStartPreSkipTr; dsimp only; cases o.opk with
  | none =>
    rw [receivedPlaintext_snoc_other, receivedPlaintext_trans (by rpk_le_tac) (Trace.append_le _ _),
      receivedPlaintext_append_tr, Option.or_none, receivedPlaintext_trans (by rpk_le_tac) (Trace.append_le _ _),
      receivedPlaintext_append_tr, Option.or_none, receivedPlaintext_snoc_other,
      receivedPlaintext_snoc_other, receivedPlaintext_append_other tr (RndE 32)]
  | some _ =>
    rw [receivedPlaintext_snoc_other, receivedPlaintext_trans (by rpk_le_tac) (Trace.append_le _ _),
      receivedPlaintext_append_tr, Option.or_none, receivedPlaintext_trans (by rpk_le_tac) (Trace.append_le _ _),
      receivedPlaintext_append_tr, Option.or_none, receivedPlaintext_snoc_other,
      receivedPlaintext_snoc_other, receivedPlaintext_snoc_other, receivedPlaintext_append_other tr (RndE 32)]

theorem receivedPlaintext_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    receivedPlaintext tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) = some m := by
  unfold bobStartTr; dsimp only
  have hpre := bobStartPreSkipTr_le tr b a o msg key; have hskip := bobStartPreSkipTr_le_bobSkipTr tr b a o msg key
  have hle1 := Trace.le_trans _ _ _ hpre hskip
  rw [receivedPlaintext_snoc_other, receivedPlaintext_trans (by rpk_le_tac) (Trace.append_le _ _),
    receivedPlaintext_append_tr, Option.or_none, receivedPlaintext_trans hle1 (Trace.append_le _ _),
    receivedPlaintext_append_tr, receivedPlaintext_trans hpre hskip, receivedPlaintext_logSkippedKeys,
    receivedPlaintext_bobStartPreSkipTr]; rfl

private def isPqCompromise : PQXDH.PQXDHEvent → Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => true
  | _ => false

private def IsTRExposure : DY.Libsignal.TripleRatchet.TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr .. | .ExposedMK .. | .ExposedSpqr .. => true
  | _ => false

private def NonLeakEventsIn (tr₀ tr₁ : ExecTrace) : Prop :=
  ∀ j ∈ newIndices tr₀ tr₁,
    ((tr₁.getEventAt PQXDH.PQXDHEvent j).map isPqCompromise).getD false = false ∧
    ((tr₁.getEventAt DY.Libsignal.TripleRatchet.TREvent j).map IsTRExposure).getD false = false

private theorem nonLeakEventsIn_refl (tr : ExecTrace) : NonLeakEventsIn tr tr := by
  intro j hj; rw [newIndices_self] at hj; cases hj

private theorem nonLeakEventsIn_trans {tr₀ tr₁ tr₂ : ExecTrace} (h01 : tr₀ ≤ tr₁) (h12 : tr₁ ≤ tr₂)
    (h1 : NonLeakEventsIn tr₀ tr₁) (h2 : NonLeakEventsIn tr₁ tr₂) : NonLeakEventsIn tr₀ tr₂ := by
  intro j hj; rw [newIndices_trans h01 h12, List.mem_append] at hj; rcases hj with hj | hj
  · rw [getEventAt_of_le PQXDH.PQXDHEvent h12 (mem_newIndices_lt hj),
      getEventAt_of_le DY.Libsignal.TripleRatchet.TREvent h12 (mem_newIndices_lt hj)]
    exact h1 j hj
  · exact h2 j hj

private theorem nonLeakEventsIn_snoc {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    {e : E} (hle : tr₀ ≤ tr := by rpk_le_tac) (h0 : NonLeakEventsIn tr₀ tr)
    (hpq : ((match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) with
      | none => none | some x => some x.ev).map isPqCompromise).getD false = false := by rfl)
    (htr : ((match (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) with
      | none => none | some x => some x.ev).map IsTRExposure).getD false = false := by rfl) :
    NonLeakEventsIn tr₀ (tr.append e) := by
  refine nonLeakEventsIn_trans hle (Trace.append_le tr e) h0 fun j hj => ?_
  rw [newIndices_append_singleton, List.mem_singleton] at hj; subst hj
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]; rw [at?_append_self_proj, at?_append_self_proj]; refine ⟨?_, ?_⟩
  · rcases h : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) with _ | x <;> [rfl; (rw [h] at hpq; exact hpq)]
  · rcases h : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) with _ | x <;> [rfl; (rw [h] at htr; exact htr)]

private theorem nonLeakEventsIn_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx srcIdx : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32) (tr : ExecTrace),
      NonLeakEventsIn tr ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val
  | 0, _, _, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; simp only [DY.Traceful.run_pure]
    exact nonLeakEventsIn_refl tr
  | k + 1, ck, idx, tr => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    let tr₁ := tr.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE
      (.SkippedKeyStored s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx))
    have hlog_run :
        (DY.ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored
          s pk idx (DY.Libsignal.TripleRatchet.kdfCk ck).2 rIdx srcIdx)).run tr =
        (some (), ⟨tr₁, Trace.append_le tr _⟩) := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
        Symbolic.DYBridge.DY.Traceful.mk_eq_1]
      rfl
    rw [DY.Traceful.run_bind, hlog_run]
    dsimp only
    exact nonLeakEventsIn_trans (Trace.append_le tr _)
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx
        (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) k).run tr₁).2.property
      (nonLeakEventsIn_snoc (Trace.le_refl tr) (nonLeakEventsIn_refl tr))
      (nonLeakEventsIn_logSkippedKeys s pk rIdx srcIdx k _ _ tr₁)

private theorem exposures_bobStartTr (tr : ExecTrace) (b a : Participant)
    (o : PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    exposures tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) = [] := by
  have hpre_nl : NonLeakEventsIn tr (bobStartPreSkipTr tr b a o msg key) := by
    unfold bobStartPreSkipTr; dsimp only; cases o.opk with
    | none =>
      exact nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc
        (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_refl tr))))))
    | some _ =>
      exact nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc
        (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_refl tr)))))))
  have hpre := bobStartPreSkipTr_le tr b a o msg key; have hskip := bobStartPreSkipTr_le_bobSkipTr tr b a o msg key
  have hle1 := Trace.le_trans _ _ _ hpre hskip
  have hnl : NonLeakEventsIn tr (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) := by
    unfold bobStartTr; dsimp only
    exact nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc (h0 := nonLeakEventsIn_snoc
      (h0 := nonLeakEventsIn_trans hpre hskip hpre_nl (nonLeakEventsIn_logSkippedKeys _ _ _ _ _ _ _ _))))
  apply exposures_eq_nil; intro j hj; obtain ⟨hpq, htr⟩ := hnl j hj; refine ⟨?_, ?_⟩
  · unfold pqExposureAt
    rcases hev : (bobStartTr tr b a o msg c' spqr' key seed pqSalt m).getEventAt PQXDH.PQXDHEvent j with _ | ev; · rfl
    rw [hev] at hpq; cases ev <;> simp [isPqCompromise] at hpq <;> rfl
  · unfold trExposureAt
    rcases hev : (bobStartTr tr b a o msg c' spqr' key seed pqSalt m).getEventAt DY.Libsignal.TripleRatchet.TREvent j with _ | ev; · rfl
    rw [hev] at htr; cases ev <;> simp [IsTRExposure] at htr <;> rfl

theorem vis_bobStart {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regIdxA pqIdx : Nat} {mh : PQXDH.PreKeyMsgHandles} {spqrMsgIdx : UInt32}
    {o : PQXDH.BobHandshakeOut} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c' : DY.Libsignal.TripleRatchet.RecvChain}
    {spqr' key seed pqSalt m raw : DY.Bytes} {opk : Option DY.Bytes}
    (hnext : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).next tr =
      bobStartTr tr b a o msg c' spqr' key seed pqSalt m)
    (hopk : bobOpkPk b kh tr = opk) (hek : tr.getMessageSentAt mh.ek = some o.ek)
    (hct : tr.getMessageSentAt mh.ct = some o.ct) (hmsg : tr.getMessageSentAt mh.msg = some raw) :
    (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).vis tr =
      [⟨.recv, [o.ek, o.ct, raw] ++ opk.toList, .preKeyRecv, none⟩,
       ⟨.rng, [randTerm tr.length 32], .single, none⟩,
       ⟨.accept, [m], .single,
         some (match o.opk with
           | some opkPk => ((tr.append (RndE 32)).append (NetE key)).append (EvE (.OPKUsed b opkPk))
           | none => (tr.append (RndE 32)).append (NetE key)).length⟩] := by
  have hrecv : received tr [mh.ek, mh.ct, mh.msg] = [o.ek, o.ct, raw] := by simp [received, hek, hct, hmsg]
  unfold Move.vis; dsimp only; rw [hnext, exposures_bobStartTr, List.append_nil, hopk]
  unfold bobVis rngEntry
  rw [hrecv, newRandoms_bobStartTr, eventIdx_bobDone_bobStartTr, receivedPlaintext_bobStartTr]; rfl

theorem rpk_getMessageSentAt_of_at? {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : tr.at? i = some (NetE b)) : tr.getMessageSentAt i = some b := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]; rw [h]

theorem anchored_bobStart {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regIdxA pqIdx : Nat} {mh : PQXDH.PreKeyMsgHandles} {spqrMsgIdx : UInt32}
    {o : PQXDH.BobHandshakeOut} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c' : DY.Libsignal.TripleRatchet.RecvChain}
    {spqr' key seed pqSalt m raw : DY.Bytes} {opk : Option DY.Bytes}
    (hnext : (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).next tr =
      bobStartTr tr b a o msg c' spqr' key seed pqSalt m)
    (hopk : bobOpkPk b kh tr = opk) (hek : tr.getMessageSentAt mh.ek = some o.ek)
    (hct : tr.getMessageSentAt mh.ct = some o.ct) (hmsg : tr.getMessageSentAt mh.msg = some raw) :
    (Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx 3).LogsSessionCompletion tr := by
  refine ⟨by decide, fun i hi => ?_⟩
  rw [vis_bobStart hnext hopk hek hct hmsg]
  rw [hnext, eventIdx_bobDone_bobStartTr, Option.some.injEq] at hi; subst hi
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), rfl⟩

end Symbolic.Swarm.CREF.CliPure
