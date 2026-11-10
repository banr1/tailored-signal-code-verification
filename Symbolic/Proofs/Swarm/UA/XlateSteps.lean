/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
public import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitModelPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure
import Symbolic.Proofs.Swarm.UA.Base

/-!
# Step-to-Move Translation Helpers and Accumulator Invariant

Shared helpers translating between `Step`-level and `Move`-level explanations: visible-entry
`.send`/`.pt` agreement (`VisSendPtEq`) and collision equivalences, `EventMatchesEntry` vs
`BytesMatchEntry` bridges, 32-byte fresh-randomness preservation (`Rand32From`), and the prefix
accumulator invariant `AccInv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.XlateSteps

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent RunEvent EnvEvent CliEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF (SemReady)
open _root_.DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.Proofs.Swarm.UA.Defs (runOk flatEntry flatExit failedSend flatEvent flatEvents
  callsOf SchedFits)

/-! ## `VisSendPtEq` and Collision Equivalences -/

/-- Two visible-entry lists agree on their `.send` and `.pt` entries (`Move.reject []` adds only an
unconstrained `.recv` entry). -/
def VisSendPtEq (v₁ v₂ : List VisEntry) : Prop :=
  v₁.filter (·.kind == .send) = v₂.filter (·.kind == .send) ∧
    v₁.filter (·.kind == .pt) = v₂.filter (·.kind == .pt)

theorem visSendPtEq_refl (v : List VisEntry) : VisSendPtEq v v := ⟨rfl, rfl⟩

theorem visSendPtEq_append {a₁ b₁ a₂ b₂ : List VisEntry}
    (ha : VisSendPtEq a₁ a₂) (hb : VisSendPtEq b₁ b₂) :
    VisSendPtEq (a₁ ++ b₁) (a₂ ++ b₂) := by
  refine ⟨?_, ?_⟩
  · simp only [List.filter_append, ha.1, hb.1]
  · simp only [List.filter_append, ha.2, hb.2]

theorem visSendPtEq_reject_nil :
    VisSendPtEq [⟨.recv, [], .unconstrained, none⟩] [] := ⟨rfl, rfl⟩

theorem ptAtoms_eq_of_visSendPtEq {v₁ v₂ : List VisEntry} (h : VisSendPtEq v₁ v₂) :
    plaintextTerms v₁ = plaintextTerms v₂ := by
  simp only [plaintextTerms, h.2]

theorem principalTerms_eq_of_visSendPtEq (r : ProtocolSetup) (tr : ExecTrace) {v₁ v₂ : List VisEntry}
    (h : VisSendPtEq v₁ v₂) :
    principalTerms r tr v₁ = principalTerms r tr v₂ := by
  simp only [principalTerms, h.1]

theorem prefixTerms_eq_of_visSendPtEq (r : ProtocolSetup) (tr : ExecTrace) {v₁ v₂ : List VisEntry}
    (h : VisSendPtEq v₁ v₂) :
    prefixTerms r tr v₁ = prefixTerms r tr v₂ := by
  simp only [prefixTerms, principalTerms_eq_of_visSendPtEq r tr h, ptAtoms_eq_of_visSendPtEq h]

theorem memoCollisionOn_iff_of_terms {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {known : _root_.DY.Bytes → Prop} {tr : ExecTrace} {v₁ v₂ : List VisEntry}
    {newTerms newPts : List _root_.DY.Bytes}
    (hpre : prefixTerms r tr v₁ = prefixTerms r tr v₂)
    (hpt : plaintextTerms v₁ = plaintextTerms v₂) :
    MemoCollisionOn interp r S g known tr v₁ newTerms newPts ↔
      MemoCollisionOn interp r S g known tr v₂ newTerms newPts := by
  simp only [MemoCollisionOn, hpre, hpt]

theorem recvRepresentations_eq {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} (htr : runTraceMoves r ms = tr) (b : HwBytes) :
    recvRepresentations interp r S g ms b = recvRepresentationsOn interp S g tr b := by
  subst htr; rfl

theorem preKeyRepresentations_eq {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} (htr : runTraceMoves r ms = tr) (b : HwBytes) :
    preKeyRepresentations interp r S g ms b = preKeyRepresentationsOn interp r S g tr b := by
  subst htr; rfl

theorem recvBody_iff (input b : HwBytes) :
    RecvBody input b ↔ RecvMsgBody (.recv input) b := by
  cases input <;> rfl

theorem recvCollision_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List _root_.DY.Bytes} {t : _root_.DY.Bytes}
    (htr : runTraceMoves r ms = tr) (hsalts : honestSalts r ms = salts)
    (hpre : prefixTerms r tr (runVis r ms) = prefixTerms r tr vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    RecvCollision interp r S g ms t ↔ RecvCollisionOn interp r S g tr vis salts t := by
  subst htr; subst hsalts
  unfold RecvCollision RecvCollisionOn
  dsimp only
  cases parseTrSignalMsg t with
  | none => exact memoCollisionOn_iff_of_terms hpre hpt
  | some msg => exact or_congr_left (memoCollisionOn_iff_of_terms hpre hpt)

theorem reselectCollision_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List _root_.DY.Bytes} {t : _root_.DY.Bytes}
    (htr : runTraceMoves r ms = tr) (hsalts : honestSalts r ms = salts)
    (hpre : prefixTerms r tr (runVis r ms) = prefixTerms r tr vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    ReselectCollision interp r S g ms t ↔ ReselectCollisionOn interp r S g tr vis salts t := by
  subst htr
  constructor
  · rintro ⟨msg, hmsg, rk, hrk, hγ, hne, hex, hall⟩
    exact ⟨msg, hmsg, rk, hrk, hγ, hne, hex, fun t' ht' msg' hmsg' hres =>
      (recvCollision_iff rfl hsalts hpre hpt).mp (hall t' ht' msg' hmsg' hres)⟩
  · rintro ⟨msg, hmsg, rk, hrk, hγ, hne, hex, hall⟩
    exact ⟨msg, hmsg, rk, hrk, hγ, hne, hex, fun t' ht' msg' hmsg' hres =>
      (recvCollision_iff rfl hsalts hpre hpt).mpr (hall t' ht' msg' hmsg' hres)⟩

theorem bobStartCollision_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List _root_.DY.Bytes} {p : PreKeyFields} {x : PreKeyRep}
    (htr : runTraceMoves r ms = tr) (hsalts : honestSalts r ms = salts)
    (hpre : prefixTerms r tr (runVis r ms) = prefixTerms r tr vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    BobSessionStartCollidesOrImplicitRejects interp r S g ms p x ↔ BobSessionStartCollidesOrImplicitRejectsOn interp r S g tr vis salts p x := by
  subst htr; subst hsalts
  unfold BobSessionStartCollidesOrImplicitRejects BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only
  cases parseTrSignalMsg x.msg with
  | none => exact memoCollisionOn_iff_of_terms hpre hpt
  | some msg => exact or_congr_left (memoCollisionOn_iff_of_terms hpre hpt)

/-! ## Step Reachability, `EventMatchesEntry` Bridges, and `pendingPreKey` Handles -/

theorem stepIn_next (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

theorem stepIn_ok (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (i.pf_step x).symm

theorem stepIn_pre (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    reachability.PreCond (stepIn c x) tr = c.PreCond x tr :=
  (i.pf_pre x tr).symm

theorem step_reachable {tr : ExecTrace} {s : Step}
    (hr : tr.Reachable reachability) (hp : s.PreCond tr) :
    (s.next tr).Reachable reachability :=
  _root_.DY.Trace.Reachable.Step s.toInput hp hr

theorem runSteps_reachable :
    ∀ (ss : List Step) {tr : ExecTrace},
      tr.Reachable reachability → StepsWF ss tr → (runSteps ss tr).Reachable reachability
  | [], _, hr, _ => hr
  | _ :: ss, _, hr, ⟨hp, _, hwf⟩ => runSteps_reachable ss (step_reachable hr hp) hwf

theorem invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

theorem network_preCond (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).PreCond tr = msg.AttackerKnows tr :=
  stepIn_pre _root_.DY.Network.reachability msg tr

theorem attackerSend_next_eq_network (msg : _root_.DY.Bytes) (tr : ExecTrace) :
    (Move.attackerSend msg).next tr = (Step.network msg).next tr := by
  dsimp only [Move.next, Move.act, Step.next, Step.toInput]
  rw [Symbolic.Swarm.CREF.b5_run_bind_pure_val, stepIn_next]

theorem eventMatchesEntry_of_bytesMatchEntry {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {e : MachineEvent} {v : VisEntry}
    {initIds : Option BundlePreKeyIds}
    (h : BytesMatchEntry interp r S g (eventKind e) (eventBytes e) v initIds) :
    EventMatchesEntry interp r S g e v := by
  unfold BytesMatchEntry at h
  unfold EventMatchesEntry
  refine ⟨h.1, ?_⟩
  have hm := h.2
  cases hl : v.layout <;> simp only [hl] at hm ⊢
  case preKeySend =>
    rcases hterms : v.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | _⟩⟩⟩ <;>
      simp only [SendMatches, hterms] at hm ⊢
    obtain ⟨preKeyId, spkId, kpkId, _, hwire⟩ := hm
    exact ⟨(preKeyId, spkId, kpkId), preKeyId, spkId, kpkId, rfl, hwire⟩
  case preKeyInner eks =>
    obtain ⟨t, p, hterms, hpw, _, _, hex_ek, hmsg⟩ := hm
    exact ⟨t, p, hterms, hpw, hex_ek, hmsg⟩
  all_goals exact hm

theorem bytesMatchEntry_of_eventMatchesEntry {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {e : MachineEvent} {v : VisEntry}
    {initIds : Option BundlePreKeyIds} (hv : v.layout ≠ .preKeySend)
    (hpk : ∀ eks, v.layout = .preKeyInner eks → ∀ p, parsePreKeyWire (eventBytes e) = some p →
      p.version = 4 ∧ p.identityKey.take 33 = ecKey (pubBytes interp (secretBytes r 0)))
    (h : EventMatchesEntry interp r S g e v) :
    BytesMatchEntry interp r S g (eventKind e) (eventBytes e) v initIds := by
  unfold EventMatchesEntry at h
  unfold BytesMatchEntry
  refine ⟨h.1, ?_⟩
  have hm := h.2
  cases hl : v.layout <;> simp only [hl] at hm ⊢
  case preKeySend => exact absurd hl hv
  case preKeyInner eks =>
    obtain ⟨t, p, hterms, hpw, hex_ek, hmsg⟩ := hm
    obtain ⟨hver, hik⟩ := hpk eks hl p hpw
    exact ⟨t, p, hterms, hpw, hver, hik, hex_ek, hmsg⟩
  all_goals exact hm

theorem eventMatchesEntry_pt_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : v.layout ≠ .preKeySend) (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks) :
    EventMatchesEntry interp r S g (.pt b) v ↔ BytesMatchEntry interp r S g .pt b v initIds :=
  ⟨bytesMatchEntry_of_eventMatchesEntry hv (fun eks h => absurd h (hv2 eks)),
   eventMatchesEntry_of_bytesMatchEntry (e := .pt b)⟩

theorem eventMatchesEntry_recv_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : v.layout ≠ .preKeySend)
    (hpk : ∀ eks, v.layout = .preKeyInner eks → ∀ p, parsePreKeyWire b = some p →
      p.version = 4 ∧ p.identityKey.take 33 = ecKey (pubBytes interp (secretBytes r 0))) :
    EventMatchesEntry interp r S g (.recv b) v ↔ BytesMatchEntry interp r S g .recv b v initIds :=
  ⟨bytesMatchEntry_of_eventMatchesEntry hv hpk, eventMatchesEntry_of_bytesMatchEntry (e := .recv b)⟩

theorem eventMatchesEntry_rng_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : v.layout ≠ .preKeySend) (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks) :
    EventMatchesEntry interp r S g (.rng b) v ↔ BytesMatchEntry interp r S g .rng b v initIds :=
  ⟨bytesMatchEntry_of_eventMatchesEntry hv (fun eks h => absurd h (hv2 eks)),
   eventMatchesEntry_of_bytesMatchEntry (e := .rng b)⟩

theorem eventMatchesEntry_of_bytesMatchEntry_send {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {b : HwBytes} {v : VisEntry}
    {initIds : Option BundlePreKeyIds}
    (h : BytesMatchEntry interp r S g .send b v initIds) :
    EventMatchesEntry interp r S g (.send b) v :=
  eventMatchesEntry_of_bytesMatchEntry (e := .send b) h

theorem eventMatchesEntry_accept_iff {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : v.layout ≠ .preKeySend) (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks) :
    EventMatchesEntry interp r S g (.accept b) v ↔
      BytesMatchEntry interp r S g .accept b v initIds :=
  ⟨bytesMatchEntry_of_eventMatchesEntry hv (fun eks h => absurd h (hv2 eks)),
   eventMatchesEntry_of_bytesMatchEntry (e := .accept b)⟩

theorem eventMatchesEntry_leak_iff {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {b : HwBytes} {v : VisEntry} {initIds : Option BundlePreKeyIds}
    (hv : v.layout ≠ .preKeySend) (hv2 : ∀ eks, v.layout ≠ .preKeyInner eks) :
    EventMatchesEntry interp r S g (.leak b) v ↔ BytesMatchEntry interp r S g .leak b v initIds :=
  ⟨bytesMatchEntry_of_eventMatchesEntry hv (fun eks h => absurd h (hv2 eks)),
   eventMatchesEntry_of_bytesMatchEntry (e := .leak b)⟩

theorem pendingPreKey_handles_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable reachability) {stateIdx : Nat} {ek ct : _root_.DY.Bytes}
    (hppk : pendingPreKey tr stateIdx = some (ek, ct)) :
    ∃ ekIdx ctIdx, tr.getMessageSentAt ekIdx = some ek ∧ tr.getMessageSentAt ctIdx = some ct := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hppk
  split at hppk
  · dsimp only at hppk
    split at hppk
    · simp at hppk
    · obtain ⟨pEv₀, hpq_mem, hi⟩ := List.exists_of_findSome?_eq_some hppk
      obtain ⟨i, _, hce_get⟩ := List.mem_filterMap.mp hpq_mem
      rcases hce : tr.getEventAt ComposedEvent i with _ | ⟨s, d⟩
      · simp [hce] at hce_get
      · simp only [hce] at hce_get
        split at hce_get
        · rcases hpq : tr.getEventAt DY.Libsignal.PQXDH.PQXDHEvent d with _ | pEv
          · simp [hpq] at hce_get
          · simp only [hpq, Option.some.injEq] at hce_get
            subst pEv₀
            cases pEv with
            | AliceDone a b ikA ikB spk pqpk opk ek₀ ct₀ keys =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hi
              rcases hi with ⟨rfl, rfl⟩
              have hlog : tr.EventLoggedAt
                  (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone
                    a b ikA ikB spk pqpk opk ek₀ ct₀ keys) d :=
                (DY.Trace.EventLoggedAt_eq_getEventAt _ d tr).mpr hpq
              have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hreach
              obtain ⟨t, _, rfl, hslot, -⟩ :=
                hinv.aliceDone a b ikA ikB spk pqpk opk ek₀ ct₀ keys d hlog
              obtain ⟨_, _, _, a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys',
                hnet_ek, hnet_ct, hlog'⟩ := hslot
              have hpq' : tr.getEventAt _root_.DY.Libsignal.PQXDH.PQXDHEvent (t + 5) =
                  some (.AliceDone a' b' ikA' ikB' spk' pqpk' opk' ek' ct' keys') :=
                (_root_.DY.Trace.EventLoggedAt_eq_getEventAt _ (t + 5) tr).mp hlog'
              rw [hpq] at hpq'
              injection hpq' with had_eq
              cases had_eq
              exact ⟨t + 3, t + 4,
                by simp [_root_.DY.Trace.getMessageSentAt, Symbolic.Swarm.COMPOSED.CompInv.NetAt] at hnet_ek ⊢; simp [hnet_ek],
                by simp [_root_.DY.Trace.getMessageSentAt, Symbolic.Swarm.COMPOSED.CompInv.NetAt] at hnet_ct ⊢; simp [hnet_ct]⟩
            | _ => simp at hi
        · simp at hce_get
  · simp at hppk

theorem encSend_some_eq_encSendEntry (tr tr' : ExecTrace) {stateIdx ekIdx ctIdx : Nat}
    {ek ct : _root_.DY.Bytes} (hppk : pendingPreKey tr stateIdx = some (ek, ct))
    (hek : tr.getMessageSentAt ekIdx = some ek) (hct : tr.getMessageSentAt ctIdx = some ct) :
    encSend tr tr' (some (ekIdx, ctIdx)) = encSendEntry tr tr' stateIdx true := by
  unfold encSend encSendEntry received
  cases lastSent tr tr' with
  | none => rfl
  | some w => simp [hppk, hek, hct]

section UnsealedRand
unseal _root_.DY.Bytes

theorem gamma_randTerm_eq (interp : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (idx n : Nat) (hn : n ≠ 0) :
    gamma interp S g (randTerm idx n) = g.σ idx n := by
  unfold gamma gamma' randTerm
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interp S g)]
  simp [concretizeRandom, node, hn]

end UnsealedRand

theorem exposures_kind {tr tr' : ExecTrace} {v : VisEntry} (hv : v ∈ exposures tr tr') :
    v.kind = .leak := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> rfl
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> rfl

theorem exposures_layout_ne_preKeySend {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.layout ≠ .preKeySend := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> intro hc <;> cases hc
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> intro hc <;> cases hc

theorem decVis_layout_ne_preKeySend {tr tr' : ExecTrace} {stateIdx msgIdx : Nat} {wrapped : Bool}
    {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) : v.layout ≠ .preKeySend := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with h | h
  · rcases List.mem_append.mp h with h | h
    · cases hget : tr.getMessageSentAt msgIdx <;> simp [hget] at h
      subst h
      cases wrapped <;> intro hc <;> cases hc
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      intro hc; cases hc
  · cases hrp : receivedPlaintext tr tr' <;> simp [hrp] at h
    subst h
    intro hc; cases hc

theorem exposures_layout_ne_preKeyInner {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') (eks : List _root_.DY.Bytes) : v.layout ≠ .preKeyInner eks := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> intro hc <;> cases hc
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> subst hj <;> intro hc <;> cases hc

theorem decVis_layout_ne_preKeyInner_of_kind_ne_recv {tr tr' : ExecTrace} {stateIdx msgIdx : Nat}
    {wrapped : Bool} {v : VisEntry} (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped)
    (hk : v.kind ≠ .recv) (eks : List _root_.DY.Bytes) : v.layout ≠ .preKeyInner eks := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with h | h
  · rcases List.mem_append.mp h with h | h
    · cases hget : tr.getMessageSentAt msgIdx <;> simp [hget] at h
      subst h
      exact absurd rfl hk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      intro hc; cases hc
  · cases hrp : receivedPlaintext tr tr' <;> simp [hrp] at h
    subst h
    intro hc; cases hc

theorem bobVis_layout_ne_preKeySend {tr tr' : ExecTrace}
    {mh : _root_.DY.Libsignal.PQXDH.PreKeyMsgHandles} {opk : Option _root_.DY.Bytes}
    {v : VisEntry} (hv : v ∈ bobVis tr tr' mh opk) : v.layout ≠ .preKeySend := by
  unfold bobVis at hv
  rcases List.mem_append.mp hv with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · intro hc; cases hc
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      intro hc; cases hc
  · cases hrp : receivedPlaintext tr tr' <;> simp [hrp] at h
    subst h
    intro hc; cases hc

theorem encDraws_kind {rs : List (_root_.DY.Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws rs) : v.kind = .pt ∨ v.kind = .rng := by
  cases rs with
  | nil => cases hv
  | cons hd tl =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact Or.inr rfl

theorem encSendEntry_kind {tr tr' : ExecTrace} {stateIdx : Nat} {wrapped : Bool}
    {v : VisEntry} (hv : v ∈ encSendEntry tr tr' stateIdx wrapped) : v.kind = .send := by
  unfold encSendEntry at hv
  rcases hls : lastSent tr tr' with _ | w
  · simp [hls] at hv
  · cases wrapped with
    | false =>
      rcases hppk : pendingPreKey tr stateIdx with _ | _
      · simp only [hls, hppk, List.mem_singleton] at hv
        subst hv; rfl
      · simp [hls, hppk] at hv
    | true =>
      rcases hppk : pendingPreKey tr stateIdx with _ | ⟨ek, ct⟩
      · simp [hls, hppk] at hv
      · simp only [hls, hppk, List.mem_singleton] at hv
        subst hv; rfl

theorem encSend_kind {tr tr' : ExecTrace} {wrap : Option (Nat × Nat)} {v : VisEntry}
    (hv : v ∈ encSend tr tr' wrap) : v.kind = .send := by
  unfold encSend at hv
  rcases hls : lastSent tr tr' with _ | w
  · simp [hls] at hv
  · rcases wrap with _ | ⟨e, c⟩ <;>
      (simp only [hls, List.mem_singleton] at hv; subst hv; rfl)

theorem run_bind_pure_isSome {α : Type} (x : _root_.DY.Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).1.isSome = (x.run tr).1.isSome := by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst]
  rcases (x.run tr).1 <;> rfl

theorem run_bind_pure_snd {α : Type} (x : _root_.DY.Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
  rcases (x.run tr).1 <;> rfl

theorem messageEncrypt_fail_not_ok (me : Participant) (stateIdx coinsLen : Nat)
    (tr : ExecTrace) :
    (Step.messageEncrypt me stateIdx coinsLen (tr.length + 3)).ok tr = false := by
  dsimp only [Step.ok, Step.toInput]
  erw [stepIn_ok]
  change ((_root_.DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen
      (tr.length + 3)).run tr).1.isSome = false
  unfold _root_.DY.Libsignal.TripleRatchet.messageEncrypt
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst]
  rcases hst : ((_root_.DY.PersistentLocalState.getLocalState me stateIdx :
      _root_.DY.Traceful _root_.DY.Libsignal.TripleRatchet.TRState).run tr).1 with _ | st
  · rfl
  · rw [Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd me stateIdx tr]; dsimp only
    by_cases hns : st.ns = _root_.DY.Libsignal.TripleRatchet.u32Max
    · have hf : ((failure : _root_.DY.Traceful Unit).run tr).1 = none := rfl
      simp [_root_.guard, hns, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hf]
    · have hguard : ((_root_.guard (st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max) :
          _root_.DY.Traceful Unit).run tr).1 = some () ∧
          ((_root_.guard (st.ns ≠ _root_.DY.Libsignal.TripleRatchet.u32Max) :
          _root_.DY.Traceful Unit).run tr).2.val = tr := by
        simp [_root_.guard, hns]; exact ⟨rfl, rfl⟩
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hguard.1, hguard.2]; dsimp only
      let spqrMsg := (_root_.DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) coinsLen)).2.1
      let tr1 := tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)
      let tr2 := tr1.append (⟨coinsLen⟩ : _root_.DY.Random.ExecEntryT)
      let tr3 := tr2.append (⟨spqrMsg⟩ : _root_.DY.Network.ExecEntryT)
      have hg1 : ((_root_.DY.Random.genRand 32).run tr).1 = some (randTerm tr.length 32) ∧
          ((_root_.DY.Random.genRand 32).run tr).2.val = tr1 := ⟨rfl, rfl⟩
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hg1.1, hg1.2]; dsimp only
      have hg2 : ((_root_.DY.Random.genRand coinsLen).run tr1).1 =
          some (randTerm (tr.length + 1) coinsLen) ∧
          ((_root_.DY.Random.genRand coinsLen).run tr1).2.val = tr2 := ⟨rfl, rfl⟩
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hg2.1, hg2.2]; dsimp only
      have hsnd : ((_root_.DY.Network.sendMessage spqrMsg).run tr2).1 = some tr2.length ∧
          ((_root_.DY.Network.sendMessage spqrMsg).run tr2).2.val = tr3 := ⟨rfl, rfl⟩
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hsnd.1, hsnd.2]; dsimp only
      have hlen3 : tr3.length ≤ tr.length + 3 := by
        change tr.length + 3 ≤ tr.length + 3; exact Nat.le_refl _
      have hrcv : ((_root_.DY.Network.receiveMessage (tr.length + 3)).run tr3).1 = none := by
        unfold _root_.DY.Network.receiveMessage
        rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst]
        have hmk : ((_root_.DY.getEntry (tr.length + 3) :
            _root_.DY.Traceful _root_.DY.Network.ExecEntryT).run tr3).1 =
            (tr3.at? (tr.length + 3) : Option _root_.DY.Network.ExecEntryT) := rfl
        rw [hmk, Symbolic.Swarm.CREF.at?_ge_length tr3 hlen3]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hrcv]
      rfl

theorem aliceStart_ok_trOfOut {a b : Participant} {idStateIdx regIdxB : Nat}
    {bh : _root_.DY.Libsignal.PQXDH.BundleHandles} {tr : ExecTrace}
    (hok : (Step.aliceStart a b idStateIdx regIdxB bh).ok tr = true) :
    ∃ o, (Move.aliceStart a b idStateIdx regIdxB bh 35).next tr =
      Symbolic.Swarm.CREF.aliceStartTrOfOut tr a b o := by
  dsimp only [Step.ok, Step.toInput] at hok
  erw [stepIn_ok] at hok
  change ((_root_.DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).1.isSome =
    true at hok
  have hlen_ge : tr.length + 4 ≤
      ((Move.aliceStart a b idStateIdx regIdxB bh 35).next tr).length := by
    rw [Symbolic.Swarm.CREF.b5_aliceStart_next]
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.aliceStart_eq_inline] at hok ⊢
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd]
    rcases h1 : ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).1
      with _ | o
    · simp [h1] at hok
    · have hle : tr.length ≤
          ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.val.length :=
        _root_.DY.Trace.length_le _ _
          ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.property
      dsimp only
      change tr.length + 4 ≤
        ((_root_.DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh).run tr).2.val.length + 7
      omega
  rcases Symbolic.Swarm.CREF.aliceStart_next_cases a b idStateIdx regIdxB bh 35 tr with
    h0 | h1 | ⟨ikA, ikB, _, spk, _, pqpk, _, opk, _, _, _, _, _, _, _, _, h3⟩
  · rw [h0] at hlen_ge; omega
  · rw [h1] at hlen_ge
    change tr.length + 4 ≤ tr.length + 1 at hlen_ge; omega
  · exact ⟨_, h3⟩

/-! ## Fresh 32-Byte Draw Preservation (`Rand32From`) -/

private def Rand32From (tr₀ tr' : ExecTrace) : Prop :=
  ∀ i, tr₀.length ≤ i → ∀ (e : _root_.DY.Random.ExecEntryT), tr'.at? i = some e → e.length = 32

private theorem rand32From_refl (tr₀ : ExecTrace) : Rand32From tr₀ tr₀ := by
  intro i hi e he
  rw [Symbolic.Swarm.CREF.at?_ge_length tr₀ hi] at he
  cases he

section Rand32Walks

open Symbolic.Swarm.COMPOSED.CompTrace (Preserves NetE TREvE PQEvE TRStE)
open _root_.DY.Libsignal.TripleRatchet (SessionInfo KeyDir TREvent)

private theorem r32_append_other {E : Type} [_root_.DY.ExecTraceTypes.Has E]
    {tr₀ tr : ExecTrace} {e : E}
    (hnone : (_root_.DY.TraceEntryHas.proj (_root_.DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option _root_.DY.Random.ExecEntryT) = none)
    (h : Rand32From tr₀ tr) : Rand32From tr₀ (tr.append e) := by
  intro i hi r hr
  by_cases hlt : i < tr.length
  · rw [Symbolic.Swarm.CREF.TR.at?_append_of_lt tr e hlt] at hr
    exact h i hi r hr
  · by_cases heq : i = tr.length
    · subst heq
      rw [Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj tr e rfl none hnone] at hr
      cases hr
    · have hge : (tr.append e).length ≤ i := by
        change tr.length + 1 ≤ i; omega
      rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) hge] at hr
      cases hr

private theorem r32_pres_genRand32 {tr₀ : ExecTrace} :
    Preserves (Rand32From tr₀) (_root_.DY.Random.genRand 32) := by
  intro tr h i hi r hr
  change ((tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)).at? i = some r) at hr
  by_cases hlt : i < tr.length
  · rw [Symbolic.Swarm.CREF.TR.at?_append_of_lt tr _ hlt] at hr
    exact h i hi r hr
  · by_cases heq : i = tr.length
    · subst heq
      rw [Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj tr
        (⟨32⟩ : _root_.DY.Random.ExecEntryT) rfl (some ⟨32⟩) rfl] at hr
      injection hr with hr'; rw [← hr']
    · have hge : (tr.append (⟨32⟩ : _root_.DY.Random.ExecEntryT)).length ≤ i := by
        change tr.length + 1 ≤ i; omega
      rw [Symbolic.Swarm.CREF.at?_ge_length _ hge] at hr
      cases hr

private theorem r32_pres_sendMessage {tr₀ : ExecTrace} (m : _root_.DY.Bytes) :
    Preserves (Rand32From tr₀) (_root_.DY.Network.sendMessage m) :=
  fun _ h => r32_append_other (e := NetE m) rfl h

private theorem r32_pres_logTR {tr₀ : ExecTrace} (ev : TREvent) :
    Preserves (Rand32From tr₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => r32_append_other (e := TREvE ev) rfl h

private theorem r32_pres_logPQ {tr₀ : ExecTrace} (ev : _root_.DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves (Rand32From tr₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => r32_append_other (e := PQEvE ev) rfl h

private theorem r32_pres_logHS {tr₀ : ExecTrace} (ev : ComposedEvent) :
    Preserves (Rand32From tr₀) (_root_.DY.ProtocolEvent.logEvent ev) :=
  fun _ h => r32_append_other (e := (⟨ev⟩ : _root_.DY.ProtocolEvent.ExecEntryT ComposedEvent)) rfl h

private theorem r32_pres_storeTR {tr₀ : ExecTrace} (p : Participant)
    (st : _root_.DY.Libsignal.TripleRatchet.TRState) :
    Preserves (Rand32From tr₀) (_root_.DY.PersistentLocalState.storeLocalState p st) :=
  fun _ h => r32_append_other (e := TRStE p st) rfl h

private theorem r32_pres_prodCasesOn {tr₀ : ExecTrace} {α β γ : Type} (p : α × β)
    (f : α → β → _root_.DY.Traceful γ) (hf : ∀ a b, Preserves (Rand32From tr₀) (f a b)) :
    Preserves (Rand32From tr₀) (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

private theorem r32_pres_optionCasesOn {tr₀ : ExecTrace} {α β : Type} (o : Option α)
    (noneCase : _root_.DY.Traceful β) (someCase : α → _root_.DY.Traceful β)
    (hn : Preserves (Rand32From tr₀) noneCase)
    (hs : ∀ a, Preserves (Rand32From tr₀) (someCase a)) :
    Preserves (Rand32From tr₀) (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem r32_pres_getKey {tr₀ : ExecTrace} (p : Participant) (h : Nat)
    (kind : _root_.DY.Libsignal.PQXDH.KeyKind) :
    Preserves (Rand32From tr₀) (_root_.DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold _root_.DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem r32_pres_lookupIdentity {tr₀ : ExecTrace} (p : Participant) (h : Nat) :
    Preserves (Rand32From tr₀) (_root_.DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold _root_.DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem r32_pres_dhRatchetStep {tr₀ : ExecTrace}
    (st : _root_.DY.Libsignal.TripleRatchet.TRState) (pk : _root_.DY.Bytes) :
    Preserves (Rand32From tr₀) (_root_.DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind r32_pres_genRand32 fun _ => Preserves.pure _

private theorem r32_pres_ensureReceiverChain {tr₀ : ExecTrace}
    (st : _root_.DY.Libsignal.TripleRatchet.TRState) (pk : _root_.DY.Bytes) :
    Preserves (Rand32From tr₀)
      (_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (r32_pres_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem r32_pres_logSkippedKeys {tr₀ : ExecTrace} (s : SessionInfo) (pk : _root_.DY.Bytes)
    (rIdx src : Nat) (ck : _root_.DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (Rand32From tr₀)
      (_root_.DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold _root_.DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | succ k ih =>
    unfold _root_.DY.Libsignal.TripleRatchet.logSkippedKeys
    exact Preserves.bind (r32_pres_logTR _) fun _ => ih _ _

private theorem r32_pres_logMessageKeyAndStore {tr₀ : ExecTrace} (me : Participant)
    (s : SessionInfo) (dir : KeyDir) (seed pqSalt : _root_.DY.Bytes) (n : UInt32)
    (rIdx par : Nat) (st : _root_.DY.Libsignal.TripleRatchet.TRState) :
    Preserves (Rand32From tr₀)
      (_root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
        me s dir seed pqSalt n rIdx par st) := by
  unfold _root_.DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (r32_pres_logTR _) fun _ => r32_pres_storeTR me st

local macro "r32_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply r32_pres_prodCasesOn
  | with_reducible apply r32_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply r32_pres_genRand32 | with_reducible apply r32_pres_storeTR
  | with_reducible apply r32_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply r32_pres_getKey
  | with_reducible apply r32_pres_lookupIdentity | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply r32_pres_dhRatchetStep
  | with_reducible apply r32_pres_ensureReceiverChain
  | with_reducible apply r32_pres_logSkippedKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply r32_pres_logMessageKeyAndStore
  | with_reducible apply r32_pres_logPQ | with_reducible apply r32_pres_logTR
  | with_reducible apply r32_pres_logHS
  | split | with_reducible intro))

private theorem r32_pres_bobHandshake {tr₀ : ExecTrace} (b a : Participant)
    (kh : _root_.DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (Rand32From tr₀)
      (_root_.DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold _root_.DY.Libsignal.PQXDH.bobHandshake; r32_tac

private theorem newRandoms_all_32_of_rand32From {tr tr' : ExecTrace} (h : Rand32From tr tr') :
    ∀ r ∈ newRandoms tr tr', ∃ ts, r = (randTerm ts 32, 32) := by
  intro r hr
  unfold newRandoms newIndices at hr
  obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hr
  simp only [List.mem_range'_1] at hi
  rcases hat : (tr'.at? i : Option _root_.DY.Random.ExecEntryT) with _ | e
  · simp [hat] at hmap
  · simp only [hat, Option.map_some, Option.some.injEq] at hmap
    have he32 : e.length = 32 := h i hi.1 e hat
    exact ⟨i, by rw [← hmap, he32]⟩

theorem bobStart_newRandoms_32 (b a : Participant)
    (kh : _root_.DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : _root_.DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32)
    (tr : ExecTrace) :
    ∀ r ∈ newRandoms tr ((Step.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).next tr),
      ∃ ts, r = (randTerm ts 32, 32) := by
  apply newRandoms_all_32_of_rand32From
  dsimp only [Step.next, Step.toInput]
  erw [stepIn_next]
  change Rand32From tr ((_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx
    spqrMsgIdx).run tr).2.val
  have hp : Preserves (Rand32From tr)
      (_root_.DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.Composed.bobStart_eq_inline]
    refine Preserves.bind (r32_pres_bobHandshake b a kh regIdxA mh.ek mh.ct) fun _ => ?_
    r32_tac
  exact hp tr (rand32From_refl tr)

theorem messageDecrypt_newRandoms_32 (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    ∀ r ∈ newRandoms tr ((Step.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).next tr),
      ∃ ts, r = (randTerm ts 32, 32) := by
  apply newRandoms_all_32_of_rand32From
  dsimp only [Step.next, Step.toInput]
  erw [stepIn_next]
  change Rand32From tr ((_root_.DY.Libsignal.TripleRatchet.messageDecrypt
    me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val
  have hp : Preserves (Rand32From tr)
      (_root_.DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [_root_.DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; r32_tac
  exact hp tr (rand32From_refl tr)

theorem messageDecryptSkipped_newRandoms_32 (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (tr : ExecTrace) :
    ∀ r ∈ newRandoms tr
        ((Step.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).next tr),
      ∃ ts, r = (randTerm ts 32, 32) := by
  apply newRandoms_all_32_of_rand32From
  dsimp only [Step.next, Step.toInput]
  erw [stepIn_next]
  change Rand32From tr ((_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
    me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).2.val
  have hp : Preserves (Rand32From tr)
      (_root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped
        me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
    unfold _root_.DY.Libsignal.TripleRatchet.messageDecryptSkipped; r32_tac
  exact hp tr (rand32From_refl tr)

end Rand32Walks

theorem list_split_of_getElem? {α : Type} :
    ∀ {l : List α} {i : Nat} {x : α}, l[i]? = some x → l = l.take i ++ x :: l.drop (i + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simp at h; subst h; rfl
  | a :: _, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (a :: ·) (list_split_of_getElem? h)

def NoReadColAt (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (τ : List MachineEvent) : Prop :=
  ∀ (i : Nat) (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent) (m : Move),
    τ = τ₁ ++ e :: τ₂ → ms[i]? = some m →
    List.Forall₂ (EventMatchesEntry interp r S g) τ₁ (runVis r (ms.take i)) →
    ¬ MoveReadsCollidingMsg interp r S g (ms.take i) e m

theorem not_readCollision_of_noReadColAt {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : NoReadColAt interp r S g ms τ) : ¬ ReadCollision interp r S g ms τ :=
  fun ⟨i, τ₁, e, τ₂, m, hsplit, hmi, hF₁, _, hcol⟩ => h i τ₁ e τ₂ m hsplit hmi hF₁ hcol

theorem readColMove_vis_pos {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {pre : List Move} {e : MachineEvent} {m : Move}
    (hcol : MoveReadsCollidingMsg interp r S g pre e m) :
    0 < (m.vis (runTraceMoves r pre)).length := by
  cases m <;> try exact False.elim hcol
  all_goals
    obtain ⟨_, t, _, hmsg, _⟩ := hcol
    simp [Move.vis, decVis, hmsg]

theorem noReadColAt_snoc {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {m : Move}
    {τ blk : List MachineEvent}
    (hmp : MatchedPrefix interp r S who g ms τ)
    (hnr : NoReadColAt interp r S g ms τ)
    (hm : ∀ e τ₂, blk = e :: τ₂ → ¬ MoveReadsCollidingMsg interp r S g ms e m) :
    NoReadColAt interp r S g (ms ++ [m]) (τ ++ blk) := by
  intro i τ₁ e τ₂ m_i hsplit hmi hF₁ hcol
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hF₁ hcol
    have hpos : 0 < (m_i.vis (runTraceMoves r (ms.take i))).length := readColMove_vis_pos hcol
    have hms_split := list_split_of_getElem? hmi
    have hlen_lt : τ₁.length < τ.length := by
      rw [hF₁.length_eq, matchedPrefix_length_eq hmp]
      conv_rhs => rw [hms_split]
      rw [runVis_append]
      simp only [runMoves, List.length_append]
      omega
    have htake1 : (τ ++ blk).take τ₁.length = τ.take τ₁.length :=
      List.take_append_of_le_length (Nat.le_of_lt hlen_lt)
    have htake2 : (τ₁ ++ e :: τ₂).take τ₁.length = τ₁ := by simp
    have hτ₁_eq : τ.take τ₁.length = τ₁ := by rw [← htake1, hsplit, htake2]
    have hget1 : (τ ++ blk)[τ₁.length]? = τ[τ₁.length]? := List.getElem?_append_left hlen_lt
    have hget2 : (τ₁ ++ e :: τ₂)[τ₁.length]? = some e := by simp
    have he_eq : τ[τ₁.length]? = some e := by rw [← hget1, hsplit, hget2]
    have hτ_split : τ = τ₁ ++ e :: τ.drop (τ₁.length + 1) := by
      have hs := list_split_of_getElem? he_eq
      rwa [hτ₁_eq] at hs
    exact hnr i τ₁ e (τ.drop (τ₁.length + 1)) m_i hτ_split hmi hF₁ hcol
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmi
    subst hmi
    have htake : (ms ++ [m]).take ms.length = ms := by simp
    rw [htake] at hF₁ hcol
    have hlen_eq : τ.length = τ₁.length := by
      rw [matchedPrefix_length_eq hmp, hF₁.length_eq]
    obtain ⟨_, hblk⟩ := List.append_inj hsplit hlen_eq
    exact hm e τ₂ hblk hcol

theorem matchesEventsAt_append_invisible {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step} (hinv : ∀ x ∈ pre, x.cls = .invisible) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
      {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsClassicalAt interp r S g initIds tr ss evs vis →
      MatchesEventsClassicalAt interp r S g initIds tr (ss ++ pre) evs vis
  | _, _, ss, _, _, .nil h => .nil fun x hx =>
    (List.mem_append.mp hx).elim (h x) (hinv x)
  | _, _, _, _, _, .run1 hp hrm hrest => by
    simpa [List.append_assoc] using
      MatchesEventsClassicalAt.run1 hp hrm (matchesEventsAt_append_invisible hinv hrest)
  | _, _, _, _, _, .run0 hp hrej hrest => by
    simpa [List.append_assoc] using
      MatchesEventsClassicalAt.run0 hp hrej (matchesEventsAt_append_invisible hinv hrest)
  | _, _, _, _, _, .env hp hem hrest => by
    simpa [List.append_assoc] using
      MatchesEventsClassicalAt.env hp hem (matchesEventsAt_append_invisible hinv hrest)

theorem matchesEvents_append_invisible {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step} (hinv : ∀ x ∈ pre, x.cls = .invisible)
    {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (h : MatchesEventsClassical interp r S g tr ss evs vis) :
    MatchesEventsClassical interp r S g tr (ss ++ pre) evs vis :=
  matchesEventsAt_append_invisible hinv h

/-! ## Accumulator Invariant and Network Steppers -/

private theorem callStarts_rng_map :
    ∀ (ps : List HwBytes) (τ : List MachineEvent),
      callStarts (ps.map .rng ++ τ) = callStarts τ
  | [], _ => rfl
  | _ :: ps, τ => callStarts_rng_map ps τ

theorem callStarts_eq_of_coinSplit {σ τ : List MachineEvent} (hcs : CoinSplit σ τ) :
    callStarts τ = callStarts σ := by
  induction hcs with
  | nil => rfl
  | keep _ _ ih =>
    simp only [callStarts] at ih ⊢
    simp [List.filter_cons, ih]
  | split _ _ _ ih =>
    rw [callStarts_rng_map]
    simp only [callStarts, List.filter_cons]
    exact ih

theorem honestKeysFrom_append :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace),
      honestKeysFrom tr (ms₁ ++ ms₂) =
        honestKeysFrom tr ms₁ ++ honestKeysFrom (runMoves ms₁ tr).1 ms₂
  | [], _, _ => rfl
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, honestKeysFrom, runMoves, List.append_assoc]
    exact congrArg _ (honestKeysFrom_append ms₁ ms₂ (m.next tr))

theorem honestKeysOf_append :
    ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
      honestKeysOf tr (ss₁ ++ ss₂) =
        honestKeysOf tr ss₁ ++ honestKeysOf (runSteps ss₁ tr) ss₂
  | [], _, _ => rfl
  | s :: ss₁, ss₂, tr => by
    simp only [List.cons_append, honestKeysOf, runSteps, List.append_assoc]
    exact congrArg _ (honestKeysOf_append ss₁ ss₂ (s.next tr))

def PrekeyCallsPos (r : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ (i : Nat) (m : Move), ms[i]? = some m → m.prekeyPath?.isSome = true →
    0 < callCount (m.vis (runTraceMoves r (ms.take i)))

theorem prekeyCallsPos_snoc {r : ProtocolSetup} {ms : List Move} {m : Move}
    (h : PrekeyCallsPos r ms)
    (hm : m.prekeyPath?.isSome = true → 0 < callCount (m.vis (runTraceMoves r ms))) :
    PrekeyCallsPos r (ms ++ [m]) := by
  intro i mi hmi hp
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact h i mi hmi hp
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmi
    subst hmi
    simpa using hm hp

theorem pathFaithful_append_of_prekeyCallsPos {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent} (hmp : MatchedPrefix interp r S who g ms τ)
    (hpos : PrekeyCallsPos r ms) (blk : List MachineEvent) :
    PathFaithful interp r S g ms (τ ++ blk) := by
  intro i m promote b p hmi hp hcs hpw
  have hlt_i : i < ms.length := (List.getElem?_eq_some_iff.mp hmi).1
  have hcpos : 0 < callCount (m.vis (runTraceMoves r (ms.take i))) :=
    hpos i m hmi (by simp [hp])
  have hms_split := list_split_of_getElem? hmi
  have hcc_lt : callCount (runVis r (ms.take i)) < (callStarts τ).length := by
    rw [← matchedPrefix_callCount_eq hmp]
    conv_rhs => rw [hms_split]
    rw [runVis_append]
    simp only [runMoves, callCount_append]
    omega
  rw [callStarts_append, List.getElem?_append_left hcc_lt] at hcs
  exact hmp.2.2.2.1 i m promote b p hmi hp hcs hpw

def OutcomeFaithfulCli2 (r : ProtocolSetup) (ok : Nat → Bool) (ms : List Move) : Prop :=
  ∀ (i : Nat) (m : Move), ms[i]? = some m →
    let tr := runTraceMoves r (ms.take i)
    let vs := m.vis tr
    vs.any (fun v => v.kind == .recv || v.kind == .pt) →
    ok (callCount (runVis r (ms.take i))) = true →
    vs.any (fun v => v.kind == .send || v.kind == .accept) ∨
      (eventIdx isAliceDone tr (m.next tr)).isSome

theorem outcomeFaithfulCli2_snoc {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move}
    {m : Move} (h : OutcomeFaithfulCli2 r ok ms)
    (hm : (m.vis (runTraceMoves r ms)).any (fun v => v.kind == .recv || v.kind == .pt) →
      ok (callCount (runVis r ms)) = true →
      (m.vis (runTraceMoves r ms)).any (fun v => v.kind == .send || v.kind == .accept) ∨
        (eventIdx isAliceDone (runTraceMoves r ms) (m.next (runTraceMoves r ms))).isSome) :
    OutcomeFaithfulCli2 r ok (ms ++ [m]) := by
  intro i mi hmi
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using h i mi hmi
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmi
    subst hmi
    simpa using hm

theorem rngLengthsFaithfulCli_snoc {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {m : Move}
    (h : RngLengthsFaithfulCli interp r S g ms)
    (hm : (m.vis (runTraceMoves r ms)).any (fun v => v.kind == .recv) →
      ∀ (v : VisEntry) (t : _root_.DY.Bytes),
        v ∈ m.vis (runTraceMoves r ms) → v.kind = .rng → v.layout = .single → v.terms = [t] →
        (gamma interp S g t).length = 32) :
    RngLengthsFaithfulCli interp r S g (ms ++ [m]) := by
  intro i mi hmi
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hmi
    simpa [List.take_append_of_le_length (Nat.le_of_lt hlt)] using h i mi hmi
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmi
    subst hmi
    simpa using hm

def StateLoadSub (r : ProtocolSetup) (ms : List Move) (ss : List Step) : Prop :=
  ∀ (j : Nat) (mj : Move) (p : Participant) (k : Nat) (b : Bool),
    ms[j]? = some mj → mj.stateLoad? = some (p, k, b) →
    ∃ (i : Nat) (si : Step), ss[i]? = some si ∧ si.stateLoad? = some (p, k, b) ∧
      ((mj.act.run (runTraceMoves r (ms.take j))).1.isSome = si.ok (runTrace r (ss.take i)))

theorem stateLoadSub_append_steps {r : ProtocolSetup} {ms : List Move} {ss : List Step}
    (h : StateLoadSub r ms ss) (ss' : List Step) : StateLoadSub r ms (ss ++ ss') := by
  intro j mj p k b hmj hld
  obtain ⟨i, si, hsi, hsil, hok⟩ := h j mj p k b hmj hld
  have hlt : i < ss.length := (List.getElem?_eq_some_iff.mp hsi).1
  refine ⟨i, si, ?_, hsil, ?_⟩
  · rwa [List.getElem?_append_left hlt]
  · rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)]

theorem stateLoadSub_snoc_none {r : ProtocolSetup} {ms : List Move} {ss : List Step}
    {m : Move} (h : StateLoadSub r ms ss) (hm : m.stateLoad? = none) :
    StateLoadSub r (ms ++ [m]) ss := by
  intro j mj p k b hmj hld
  by_cases hlt : j < ms.length
  · rw [List.getElem?_append_left hlt] at hmj
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact h j mj p k b hmj hld
  · have hj_lt : j < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmj).1
    simp only [List.length_append, List.length_singleton] at hj_lt
    have hj_eq : j = ms.length := by omega
    subst hj_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmj
    subst hmj
    simp [hm] at hld

theorem stateLoadSub_snoc_step {r : ProtocolSetup} {ms : List Move} {ss : List Step}
    {m : Move} {s : Step} (h : StateLoadSub r ms ss)
    (hld_eq : m.stateLoad? = s.stateLoad?)
    (hok_eq : (m.act.run (runTraceMoves r ms)).1.isSome = s.ok (runTrace r ss)) :
    StateLoadSub r (ms ++ [m]) (ss ++ [s]) := by
  intro j mj p k b hmj hld
  by_cases hlt : j < ms.length
  · rw [List.getElem?_append_left hlt] at hmj
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact stateLoadSub_append_steps h [s] j mj p k b hmj hld
  · have hj_lt : j < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hmj).1
    simp only [List.length_append, List.length_singleton] at hj_lt
    have hj_eq : j = ms.length := by omega
    subst hj_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hmj
    subst hmj
    refine ⟨ss.length, s, by simp, ?_, ?_⟩
    · rwa [← hld_eq]
    · have htkm : (ms ++ [m]).take ms.length = ms := by simp
      have htks : (ss ++ [s]).take ss.length = ss := by simp
      rw [htkm, htks]
      exact hok_eq

structure AccInv (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost)
    (evs_acc : List CliEvent) (ss_acc : List Step) (vis_acc : List VisEntry)
    (τ : List MachineEvent) (ms : List Move) : Prop where
  cs : CoinSplit (flatEvents evs_acc) τ
  clean : Clean interp r S who ok g ms τ
  nr : NoReadColAt interp r S g ms τ
  ppos : PrekeyCallsPos r ms
  out2 : OutcomeFaithfulCli2 r ok ms
  rng32 : RngLengthsFaithfulCli interp r S g ms
  tr_eq : runTraceMoves r ms = runTrace r ss_acc
  keys_eq : honestKeysFrom (setupTrace r) ms = honestKeysOf (setupTrace r) ss_acc
  vpt : VisSendPtEq (runVis r ms) vis_acc
  mev : MatchesEventsClassical interp r S g (setupTrace r) ss_acc evs_acc vis_acc
  sload : StateLoadSub r ms ss_acc

theorem accInv_nil {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hwf : ProtocolSetupWF r) (hS : SemReady interp r S) (who : List Participant) (ok : Nat → Bool)
    {g : Ghost} (hcompat : GhostAndSemMatchSetup interp r S g) :
    AccInv interp r S who ok g [] [] [] [] [] := by
  have hm0 := Symbolic.Swarm.CREF.CliPure.init_matchedPrefix_nil hwf hS who
  have hvis0 : runVis r [] = [] :=
    List.eq_nil_of_length_eq_zero hm0.2.2.2.2.2.length_eq.symm
  have hmp : MatchedPrefix interp r S who g [] [] :=
    ⟨hcompat, Symbolic.Swarm.CREF.TR.modelRun_nil r hwf,
      by simp [RoleFaithful], by simp [PathFaithful], by simp [ReadFaithful],
      by rw [hvis0]; exact .nil⟩
  have hnr : NoReadColAt interp r S g [] [] := fun _ _ _ _ _ h => by simp at h
  exact {
    cs := .nil
    clean := ⟨⟨hmp, fun _ _ hi => nomatch hi⟩, not_readCollision_of_noReadColAt hnr⟩
    nr := hnr
    ppos := fun _ _ hi => nomatch hi
    out2 := fun _ _ hi => nomatch hi
    rng32 := fun _ _ hi => nomatch hi
    tr_eq := rfl
    keys_eq := rfl
    vpt := by rw [hvis0]; exact visSendPtEq_refl []
    mev := .nil fun _ hx => nomatch hx
    sload := fun _ _ _ _ _ hi => nomatch hi
  }

theorem accInv_step_network {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} {ss_acc : List Step} {vis_acc : List VisEntry}
    {τ : List MachineEvent} {ms : List Move} (msg : _root_.DY.Bytes)
    (hpre : (Step.network msg).PreCond (runTrace r ss_acc))
    (h : AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms) :
    AccInv interp r S who ok g evs_acc (ss_acc ++ [.network msg]) vis_acc τ
      (ms ++ [.attackerSend msg]) := by
  have htr' : runTraceMoves r (ms ++ [.attackerSend msg]) =
      runTrace r (ss_acc ++ [.network msg]) := by
    rw [runTrace_snoc, Symbolic.Proofs.Swarm.UA.Base.runTrace_append, runSteps, runSteps,
      attackerSend_next_eq_network, h.tr_eq]
  have hreach' : (runTraceMoves r (ms ++ [.attackerSend msg])).Reachable reachability := by
    rw [runTrace_snoc, attackerSend_next_eq_network, h.tr_eq]
    exact step_reachable (by rw [← h.tr_eq]; exact h.clean.1.1.2.1.2.2.1.1) hpre
  have hcl' : Clean interp r S who ok g (ms ++ [.attackerSend msg]) τ :=
    clean_attackerSend h.clean hreach'
  have hvis_nil : (Move.attackerSend msg).vis (runTraceMoves r ms) = [] := by
    have hlen1 := h.clean.1.1.2.2.2.2.2.length_eq
    have hlen2 := hcl'.1.1.2.2.2.2.2.length_eq
    rw [runVis_snoc, List.length_append] at hlen2
    exact List.eq_nil_of_length_eq_zero (by omega)
  exact {
    cs := h.cs
    clean := hcl'
    nr := by
      simpa using noReadColAt_snoc (m := .attackerSend msg) (blk := []) h.clean.1.1 h.nr
        (fun _ _ hb => nomatch hb)
    ppos := prekeyCallsPos_snoc h.ppos (fun hp => nomatch hp)
    out2 := outcomeFaithfulCli2_snoc h.out2 (by simp [hvis_nil])
    rng32 := rngLengthsFaithfulCli_snoc h.rng32 (by simp [hvis_nil])
    tr_eq := htr'
    keys_eq := by
      rw [honestKeysFrom_append, honestKeysOf_append]
      simp [honestKeysFrom, honestKeysOf, Step.publishedSpqrKey?, h.keys_eq]
    vpt := by
      rw [runVis_snoc, hvis_nil, List.append_nil]; exact h.vpt
    mev := matchesEvents_append_invisible (fun x hx => by
      rcases List.mem_singleton.mp hx with rfl; rfl) h.mev
    sload := stateLoadSub_append_steps (stateLoadSub_snoc_none h.sload rfl) [.network msg]
  }

theorem accInv_step_invisible_list {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {evs_acc : List CliEvent} :
    ∀ {pre rest : List Step} (_hinv : ∀ x ∈ pre, x.cls = .invisible)
      {ss_acc : List Step} (_hwf : StepsWF (pre ++ rest) (runTrace r ss_acc))
      {vis_acc : List VisEntry} {τ : List MachineEvent} {ms : List Move},
      AccInv interp r S who ok g evs_acc ss_acc vis_acc τ ms →
      ∃ ms', AccInv interp r S who ok g evs_acc (ss_acc ++ pre) vis_acc τ ms'
  | [], _, _, _, _, _, _, ms, h => ⟨ms, by simpa using h⟩
  | s :: pre, rest, hinv, ss_acc, hwf, vis_acc, τ, ms, h => by
    obtain ⟨msg, rfl⟩ := invisible_eq_network (hinv s (List.mem_cons_self ..))
    have h1 := accInv_step_network msg hwf.1 h
    have hwf' : StepsWF (pre ++ rest) (runTrace r (ss_acc ++ [.network msg])) := by
      simpa [Symbolic.Proofs.Swarm.UA.Base.runTrace_append, runSteps] using hwf.2.2
    obtain ⟨ms', h2⟩ := accInv_step_invisible_list (rest := rest)
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx)) hwf' h1
    exact ⟨ms', by simpa [List.append_assoc] using h2⟩

end Symbolic.Proofs.Swarm.UA.XlateSteps
