/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Swarm.UA.HwKnows -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Plaintext Draw Non-Collision

Proves `not_nextEventCollides_pt`: under the collision-free witness `(myInterp, mkRecords, mySem)`,
any 9-byte `.send` plaintext `ev.input` containing `'m'` (`109#8`) cannot trigger
`NextEventCollides` after an explained CLI prefix `evs₁` whose run coin files exclude `109#8`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent)
open DY.Libsignal.PQXDH (PQXDHEvent BundleHandles)
open DY.Libsignal.Composed (ComposedEvent reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma' gamma
   setupTrace newIndices newRandoms rngEntry eventIdx isAliceDone
   kyberCoinEntries aliceDraws aliceVis bobOpkPk bobVis encDraws encSendEntry decVis
   invertEntry stepView runSteps
   randTerm setupRandomsAt runTrace ptEntryAt
   storedStates storedSecrets principalTerms
   BytesMatchEntry DrawsMatch OutputsMatch inputKind runWrapped
   EnvMatches RunMatches MatchesEventsAt MatchesEvents Explains HwAttackerKnows
   plaintextTerms prefixTerms MemoCollisionOn)
open DY.Libsignal.Composed.Refinement.Cli
  (PrefixExplainingGhosts NextEventCollides)
open DY.Libsignal.Composed.Refinement.Cli.UA
  (hwAttackerKnows_implies_attackerKnows_of_explains')
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp mkRecords mySem not_mem_109_freshBytes)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt TermRandAt termRandAt_rand StEntry TREntry PQStEntry PQEvEntry
   TraceEntriesRand traceEntriesRand_knows traceEntriesRand_at?_st traceEntriesRand_at?_pqst
   termRandAt_serialize_tr termRandAt_serialize_pq traceEntriesRand_of_reachable
   pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero
   nonRandom_assumedInjective_len_ne_9)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (randTerm_inj)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (stepIn_next stepIn_ok runSteps_reachable invisible_eq_network
   exposures_kind encSendEntry_kind
   bobStart_newRandoms_32 messageDecrypt_newRandoms_32 messageDecryptSkipped_newRandoms_32)
open Symbolic.Swarm.CREF.TR
  (at?_append_of_lt at?_append_self at?_append_eq_of_proj
   setupTrace_eq newRandoms_setupTr4 newRandoms_setupTr5)

private theorem randAt_envMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {s : Step}
    {ev : EnvEvent} {vis : List VisEntry} {ts sz : Nat}
    (hem : EnvMatches interp r S g tr s ev vis)
    (hrnd : RandAt (s.next tr) ts sz) : RandAt tr ts sz := by
  by_contra hno
  cases ev with
  | registerCorrupt _ _ => exact hem
  | breakDH =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakDH.next tr = (DY.Libsignal.PQXDH.breakDH.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakDH.reachability () tr] at hrnd
    have hb : (DY.Libsignal.PQXDH.breakDH.run tr).2.val =
        tr.append ({ ev := PQXDHEvent.BrokenDH } : PQEvEntry) := by
      unfold DY.Libsignal.PQXDH.breakDH
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
        Traceful.run_pure]
    rw [hb] at hrnd
    exact noRandAt_append_nonRnd ({ ev := PQXDHEvent.BrokenDH } : PQEvEntry) rfl hno hrnd
  | breakKEM =>
    rcases hem with ⟨rfl, _⟩
    rw [show Step.breakKEM.next tr = (DY.Libsignal.PQXDH.breakKEM.run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.breakKEM.reachability () tr] at hrnd
    have hb : (DY.Libsignal.PQXDH.breakKEM.run tr).2.val =
        tr.append ({ ev := PQXDHEvent.BrokenKEM } : PQEvEntry) := by
      unfold DY.Libsignal.PQXDH.breakKEM
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_bind, Traceful.run_mk,
        Traceful.run_pure]
    rw [hb] at hrnd
    exact noRandAt_append_nonRnd ({ ev := PQXDHEvent.BrokenKEM } : PQEvEntry) rfl hno hrnd
  | invertDH _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertDH h).next tr = ((DY.Libsignal.PQXDH.invertDH h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertDH.reachability h tr] at hrnd
    exact (noRandAt_invertDH h).run tr hno hrnd
  | invertKEM _ _ =>
    rcases hem with ⟨h, rfl, _⟩
    rw [show (Step.invertKEM h).next tr = ((DY.Libsignal.PQXDH.invertKEM h).run tr).2.val from
      stepIn_next DY.Libsignal.PQXDH.invertKEM.reachability h tr] at hrnd
    exact (noRandAt_invertKEM h).run tr hno hrnd
  | leak _ _ =>
    have hleak : s.IsLeak := hem.2.1
    cases s <;> try exact False.elim hleak
    · rename_i me si k
      rw [show (Step.exposeKey me si k).next tr =
          ((DY.Libsignal.TripleRatchet.exposeKey me si k).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability (me, si, k) tr] at hrnd
      exact (noRandAt_exposeKey me si k).run tr hno hrnd
    · rename_i me si
      rw [show (Step.exposeSpqr me si).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSpqr me si).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSpqr.reachability (me, si) tr] at hrnd
      exact (noRandAt_exposeSpqr me si).run tr hno hrnd
    · rename_i sk
      rw [show (Step.exposeSkipped sk).next tr =
          ((DY.Libsignal.TripleRatchet.exposeSkipped sk).run tr).2.val from
        stepIn_next DY.Libsignal.TripleRatchet.exposeSkipped.reachability sk tr] at hrnd
      exact (noRandAt_exposeSkipped sk).run tr hno hrnd
    · rename_i p si
      rw [show (Step.compromiseIK p si).next tr =
          ((DY.Libsignal.PQXDH.compromiseIK p si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseIK.reachability (p, si) tr] at hrnd
      exact (noRandAt_compromise p si .identity
        (PQXDHEvent.CompromisedIK p ∘ DY.DiffieHellman.dhPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromiseSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseSPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromise b si .signedPrekey
        (PQXDHEvent.CompromisedSPK b ∘ DY.DiffieHellman.dhPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromisePQSPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromisePQSPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromisePQSPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromise b si .pqPrekey
        (PQXDHEvent.CompromisedPQSPK b ∘ DY.PQKem.kemPk)).run tr hno hrnd
    · rename_i b si
      rw [show (Step.compromiseOPK b si).next tr =
          ((DY.Libsignal.PQXDH.compromiseOPK b si).run tr).2.val from
        stepIn_next DY.Libsignal.PQXDH.compromiseOPK.reachability (b, si) tr] at hrnd
      exact (noRandAt_compromiseOPK b si).run tr hno hrnd

private theorem genRand_run_fst (n : Nat) (tr : ExecTrace) :
    ((DY.Random.genRand n).run tr).1 = some (randTerm tr.length n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, Traceful.run_pure]
  rfl
private theorem genRand_run_snd (n : Nat) (tr : ExecTrace) :
    ((DY.Random.genRand n).run tr).2.val = tr.append (DY.Random.ExecEntryT.mk n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Traceful.run_bind,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk, Traceful.run_pure]
private theorem pure_run_fst {α : Type} (a : α) (tr : ExecTrace) :
    ((Pure.pure a : Traceful α).run tr).1 = some a := by
  rw [Traceful.run_pure]
private theorem pure_run_snd {α : Type} (a : α) (tr : ExecTrace) :
    ((Pure.pure a : Traceful α).run tr).2.val = tr := by
  rw [Traceful.run_pure]
private theorem failure_run_fst {α : Type} (tr : ExecTrace) :
    ((Alternative.failure : Traceful α).run tr).1 = none := by
  rw [Traceful.run_failure]
private theorem failure_run_snd {α : Type} (tr : ExecTrace) :
    ((Alternative.failure : Traceful α).run tr).2.val = tr := by
  rw [Traceful.run_failure]

private structure HSWp (tr₀ : ExecTrace) {α : Type} (x : Traceful α) : Prop where
  ok :
    ((x.run tr₀).1 = none ∧
      ((x.run tr₀).2.val = tr₀ ∨ (x.run tr₀).2.val = tr₀.append (DY.Random.ExecEntryT.mk 32))) ∨
    ((x.run tr₀).1.isSome = true ∧
      (x.run tr₀).2.val =
        (tr₀.append (DY.Random.ExecEntryT.mk 32)).append (DY.Random.ExecEntryT.mk 32))

private theorem HSWp.bind_ro {tr₀ : ExecTrace} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves (fun t => t = tr₀) x) (hf : ∀ a, HSWp tr₀ (f a)) : HSWp tr₀ (x >>= f) :=
  ⟨by
    rw [run_bind_fst, run_bind_snd]
    have htr : (x.run tr₀).2.val = tr₀ := hx.run tr₀ rfl
    cases (x.run tr₀).1 with
    | none => exact Or.inl ⟨rfl, Or.inl htr⟩
    | some a => rw [htr]; exact (hf a).ok⟩

private theorem HSWp.tail (tr₀ : ExecTrace) (p₁ p₂ : Prop) [Decidable p₁] [Decidable p₂]
    {α : Type} (k : DY.Bytes → DY.Bytes → α) :
    HSWp tr₀ (do
      let ek ← DY.Random.genRand 32
      _root_.guard p₁
      _root_.guard p₂
      let entropy ← DY.Random.genRand 32
      Pure.pure (k ek entropy)) :=
  ⟨by
    unfold _root_.guard
    by_cases hp1 : p₁
    · by_cases hp2 : p₂
      · exact Or.inr (by simp [hp1, hp2, run_bind_fst, run_bind_snd, genRand_run_fst,
          genRand_run_snd, pure_run_fst, pure_run_snd])
      · exact Or.inl ⟨by simp [hp1, hp2, run_bind_fst, genRand_run_fst,
          pure_run_fst, failure_run_fst],
          Or.inr (by simp [hp1, hp2, run_bind_snd, genRand_run_fst,
            genRand_run_snd, pure_run_fst, pure_run_snd, failure_run_fst, failure_run_snd])⟩
    · exact Or.inl ⟨by simp [hp1, run_bind_fst, genRand_run_fst, failure_run_fst],
        Or.inr (by simp [hp1, run_bind_snd, genRand_run_fst, genRand_run_snd,
          failure_run_fst, failure_run_snd])⟩⟩

private theorem aliceHandshake_run_cases
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) (tr₀ : ExecTrace) :
    HSWp tr₀ (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  apply HSWp.bind_ro (Preserves.getKey a idStateIdx .identity); intro _
  apply HSWp.bind_ro (Preserves.lookupIdentity b regIdxB); intro p
  rcases p with ⟨_, _⟩; dsimp only
  apply HSWp.bind_ro (Preserves.receiveMessage h.spk); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.spkSig); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.pqpk); intro _
  apply HSWp.bind_ro (Preserves.receiveMessage h.pqpkSig); intro _
  apply HSWp.bind_ro (Preserves.guardP _); intro _
  apply HSWp.bind_ro (Preserves.guardP _); intro _
  cases h.opk <;> dsimp only
  · apply HSWp.bind_ro Preserves.pure; intro _
    exact HSWp.tail tr₀ _ _ _
  · apply HSWp.bind_ro (Preserves.receiveMessage _); intro _
    apply HSWp.bind_ro Preserves.pure; intro _
    exact HSWp.tail tr₀ _ _ _

private theorem aliceStart_ok_newRandoms
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) (tr₀ : ExecTrace)
    (hok : (Step.aliceStart a b idStateIdx regIdxB h).ok tr₀ = true) :
    newRandoms tr₀ ((Step.aliceStart a b idStateIdx regIdxB h).next tr₀) =
      [(randTerm tr₀.length 32, 32),
       (randTerm (tr₀.length + 1) 32, 32),
       (randTerm (tr₀.length + 2) 32, 32)] := by
  have hnext_eq :
      (Step.aliceStart a b idStateIdx regIdxB h).next tr₀ =
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).2.val :=
    stepIn_next DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, h) tr₀
  have hok_eq :
      ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).1.isSome = true := by
    rwa [show (Step.aliceStart a b idStateIdx regIdxB h).ok tr₀ =
        ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h).run tr₀).1.isSome from
      stepIn_ok DY.Libsignal.Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, h) tr₀] at hok
  rcases (aliceHandshake_run_cases a b idStateIdx regIdxB h tr₀).ok with
    ⟨hnone, _⟩ | ⟨hsome_b, htr_eq⟩
  · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline] at hok_eq
    rw [run_bind_fst, hnone] at hok_eq
    cases hok_eq
  · obtain ⟨_, hsome⟩ := Option.isSome_iff_exists.mp hsome_b
    have htr1 :
        ∃ (e1 e2 : Network.ExecEntryT) (e3 : PQEvEntry) (e4 : TREntry)
          (e5 : DY.ProtocolEvent.ExecEntryT ComposedEvent) (e6 : StEntry),
          (Step.aliceStart a b idStateIdx regIdxB h).next tr₀ =
            ((((((((tr₀.append (DY.Random.ExecEntryT.mk 32)).append
              (DY.Random.ExecEntryT.mk 32)).append
              (DY.Random.ExecEntryT.mk 32)).append e1).append e2).append e3).append e4).append e5).append e6 := by
      rw [hnext_eq]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
      rw [run_bind_snd, hsome, htr_eq]
      dsimp only
      simp only [DY.Libsignal.TripleRatchet.traceLength,
        Symbolic.DYBridge.DY.Random.genRand_eq_1,
        Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
        Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1,
        Traceful.run_bind, Traceful.run_mk, Traceful.run_pure]
      exact ⟨_, _, _, _, _, _, rfl⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, htr1⟩ := htr1
    rw [htr1]
    have hlen_app : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (x : E),
        (t.append x).length = t.length + 1 := fun _ _ => by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e6 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e5 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e4 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e3 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e2 rfl,
      newRandoms_append_nonRnd_ge (by simp only [hlen_app]; omega) e1 rfl,
      newRandoms_append_rnd_ge (by simp only [hlen_app]; omega) 32,
      newRandoms_append_rnd_ge (by simp only [hlen_app]; omega) 32,
      newRandoms_append_rnd_ge (Nat.le_refl _) 32,
      newRandoms_self]
    simp only [hlen_app, List.nil_append, List.cons_append]

private def CoinDrawn (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (evs : List CliEvent) (vis : List VisEntry)
    (ts sz : Nat) : Prop :=
  randTerm ts sz ∈ plaintextTerms vis ∨
  (∃ v ∈ vis, v.kind = .rng ∧ sz = 32 ∧ randTerm ts sz ∈ v.terms) ∨
  (∃ rEv, .run rEv ∈ evs ∧ ∃ p, (∀ x ∈ p, x ∈ rEv.coins) ∧
    ∃ v ∈ vis, v.kind = .rng ∧ v.layout = .single ∧ v.terms = [randTerm ts sz] ∧
      BytesMatchEntry interp r S g .rng p v)

private theorem coinDrawn_mono {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {evs₁ evs₂ : List CliEvent} {v₁ v₂ : List VisEntry}
    {ts sz : Nat}
    (hevs : ∀ x ∈ evs₁, x ∈ evs₂) (hvis : ∀ x ∈ v₁, x ∈ v₂)
    (h : CoinDrawn interp r S g evs₁ v₁ ts sz) :
    CoinDrawn interp r S g evs₂ v₂ ts sz := by
  rcases h with hpt | ⟨v, hv, hk, h32, ht⟩ | ⟨rEv, hrEv, p, hp, v, hv, hk, hl, hts, hbme⟩
  · unfold plaintextTerms at hpt
    obtain ⟨v, hv_filt, ht⟩ := List.mem_flatMap.mp hpt
    obtain ⟨hv, hk⟩ := List.mem_filter.mp hv_filt
    refine Or.inl ?_
    unfold plaintextTerms
    exact List.mem_flatMap.mpr ⟨v, List.mem_filter.mpr ⟨hvis v hv, hk⟩, ht⟩
  · exact Or.inr (Or.inl ⟨v, hvis v hv, hk, h32, ht⟩)
  · exact Or.inr (Or.inr ⟨rEv, hevs _ hrEv, p, hp, v, hvis v hv, hk, hl, hts, hbme⟩)

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (hf : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction hf with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hr'⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hr'⟩

private theorem rng_mem_drs_of_runMatches {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {ev : RunEvent} {inp : VisEntry}
    {drs outs : List VisEntry} {w : VisEntry}
    (hinp : BytesMatchEntry interp r S g (inputKind ev) ev.input inp)
    (houts : OutputsMatch interp r S g ev outs initIds)
    (hw_mem : w ∈ inp :: (drs ++ outs)) (hw_rng : w.kind = .rng) :
    w ∈ drs := by
  rcases List.mem_cons.mp hw_mem with rfl | hdo
  · have hk := hinp.1
    rw [hw_rng] at hk
    unfold inputKind at hk
    split at hk <;> cases hk
  · rcases List.mem_append.mp hdo with hdrs | ho
    · exact hdrs
    · unfold OutputsMatch at houts
      split at houts
      · obtain ⟨_, rfl, hbme⟩ := houts
        rcases List.mem_singleton.mp ho with rfl
        have hk := hbme.1; rw [hw_rng] at hk; cases hk
      · obtain ⟨_, rfl, hbme⟩ := houts
        rcases List.mem_singleton.mp ho with rfl
        have hk := hbme.1; rw [hw_rng] at hk; cases hk
      · rw [houts] at ho; cases ho

private theorem runMatches_coinDrawn {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {s : Step}
    {ev : RunEvent} {v : List VisEntry} {ts sz : Nat}
    (hsz : sz ≠ 0)
    (hrm : RunMatches interp r S g tr s ev v initIds)
    (hlo : tr.length ≤ ts)
    (hrnd : RandAt (s.next tr) ts sz) :
    CoinDrawn interp r S g [.run ev] v ts sz := by
  obtain ⟨hcls, _, _, _, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, hdrs, houts, _, _⟩ := hrm
  have hmem_nr : (randTerm ts sz, sz) ∈ newRandoms tr (s.next tr) :=
    mem_newRandoms_of_randAt hlo hrnd
  have henc : ∀ (hsub : ∀ w ∈ encDraws (newRandoms tr (s.next tr)), w ∈ v),
      CoinDrawn interp r S g [.run ev] v ts sz := by
    intro hsub
    cases hnr : newRandoms tr (s.next tr) with
    | nil => rw [hnr] at hmem_nr; cases hmem_nr
    | cons r0 rest =>
      rcases r0 with ⟨m0, n0⟩
      rw [hnr] at hmem_nr
      rcases List.mem_cons.mp hmem_nr with hhead | htail
      · injection hhead with hm0 _
        subst hm0
        have hv_pt : (⟨.pt, [randTerm ts sz], .single, none⟩ : VisEntry) ∈ v := by
          apply hsub; rw [hnr]; exact List.mem_cons_self
        refine Or.inl ?_
        unfold plaintextTerms
        exact List.mem_flatMap.mpr ⟨_, List.mem_filter.mpr ⟨hv_pt, rfl⟩, List.mem_singleton.mpr rfl⟩
      · have hfilt : (randTerm ts sz, sz) ∈ rest.filter (·.2 != 0) :=
          List.mem_filter.mpr ⟨htail, bne_iff_ne.mpr hsz⟩
        have hv_rng : rngEntry (randTerm ts sz) ∈ v := by
          apply hsub; rw [hnr]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hfilt, rfl⟩)
        have hdrs_mem : rngEntry (randTerm ts sz) ∈ drs :=
          rng_mem_drs_of_runMatches hinp houts (hv_split ▸ hv_rng) rfl
        obtain ⟨pieces, _, hflat_pre, hfa2⟩ := hdrs
        obtain ⟨p, hp_mem, hbme⟩ := forall₂_mem_right hfa2 hdrs_mem
        refine Or.inr (Or.inr ⟨ev, List.mem_singleton.mpr rfl, p, ?_,
          rngEntry (randTerm ts sz), hv_rng, rfl, rfl, rfl, hbme⟩)
        intro x hx
        exact hflat_pre.subset (List.mem_flatten.mpr ⟨p, hp_mem, hx⟩)
  cases s with
  | aliceStart a b idStateIdx regIdxB h =>
    have hnr := aliceStart_ok_newRandoms a b idStateIdx regIdxB h tr hok
    rw [hnr] at hmem_nr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem_nr
    have hv_own : ∀ w ∈ aliceVis tr ((Step.aliceStart a b idStateIdx regIdxB h).next tr) h,
        w ∈ v := by
      intro w hw
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      exact List.mem_append_left _ hw
    rcases hmem_nr with ⟨heq, rfl⟩ | ⟨heq, rfl⟩ | ⟨heq, rfl⟩
    · have hw : rngEntry (randTerm tr.length 32) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [rngEntry, heq]⟩)
    · have hkyb0 : (⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈
          kyberCoinEntries (randTerm (tr.length + 1) 32) := by
        unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by simp, rfl⟩
      have hw : (⟨.rng, [randTerm (tr.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hkyb0))
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [heq]⟩)
    · let done := eventIdx isAliceDone tr ((Step.aliceStart a b idStateIdx regIdxB h).next tr)
      have hw : ({ rngEntry (randTerm (tr.length + 2) 32) with anchor := done } : VisEntry) ∈ v := by
        apply hv_own; unfold aliceVis; rw [hnr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_singleton.mpr rfl)))
      exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, by simp [rngEntry, heq]⟩)
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    obtain ⟨_, h32⟩ := bobStart_newRandoms_32 b a kh regIdxA mh pqIdx spqrMsgIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left
      unfold bobVis
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageDecrypt me sIdx mIdx pqIdx spqrIdx =>
    obtain ⟨_, h32⟩ := messageDecrypt_newRandoms_32 me sIdx mIdx pqIdx spqrIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left; unfold decVis
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageDecryptSkipped me sIdx mIdx skIdx pqIdx spqrIdx =>
    obtain ⟨_, h32⟩ :=
      messageDecryptSkipped_newRandoms_32 me sIdx mIdx skIdx pqIdx spqrIdx tr _ hmem_nr
    injection h32 with _ hsz32
    subst hsz32
    have hw : rngEntry (randTerm ts 32) ∈ v := by
      rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left; unfold decVis
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem_nr, rfl⟩))
    exact Or.inr (Or.inl ⟨_, hw, rfl, rfl, List.mem_singleton.mpr rfl⟩)
  | messageEncrypt _ _ _ _ =>
    refine henc fun w hw => ?_
    rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_append_left _ hw)
  | messageEncryptAbort _ _ =>
    refine henc fun w hw => ?_
    rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
    exact List.mem_append_left _ hw
  | _ => cases hcls

private theorem matchesEvents_coinDrawn {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr₀ : ExecTrace} {ss : List Step}
    {evs : List CliEvent} {vis : List VisEntry} {ts sz : Nat}
    (hsz : sz ≠ 0)
    (hMe : MatchesEventsAt interp r S g initIds tr₀ ss evs vis)
    (hlo : tr₀.length ≤ ts)
    (hrnd : RandAt (runSteps ss tr₀) ts sz) :
    CoinDrawn interp r S g evs vis ts sz := by
  induction hMe with
  | nil hinv =>
    have hrnd₀ := randAt_invisible hinv hrnd
    exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
  | @run0 _ tr pre ss' ev evs' vs hinv _ _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt : ts < (runSteps pre tr).length
    · have hrnd₀ := randAt_invisible hinv (randAt_of_le_of_lt (runSteps_le ss' _) hlt hrnd)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx) (fun _ h => h)
        (ih (Nat.not_lt.mp hlt) hrnd)
  | @env _ tr pre s ss' ev evs' v_step vs hinv hem _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt : ts < (s.next (runSteps pre tr)).length
    · have hrnd_s := randAt_of_le_of_lt (runSteps_le ss' _) hlt hrnd
      have hrnd₀ := randAt_invisible hinv (randAt_envMatches hem hrnd_s)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx)
        (fun x hx => List.mem_append_right _ hx) (ih (Nat.not_lt.mp hlt) hrnd)
  | @run1 _ tr pre s ss' ev evs' v_step vs hinv hrm _ ih =>
    rw [runSteps_append] at hrnd
    by_cases hlt_pre : ts < (runSteps pre tr).length
    · have hrnd₀ := randAt_invisible hinv
        (randAt_of_le_of_lt (DY.Trace.le_trans _ _ _ (step_le_next s _) (runSteps_le ss' _))
          hlt_pre hrnd)
      exact absurd (lt_of_randAt hrnd₀) (Nat.not_lt.mpr hlo)
    · by_cases hlt_s : ts < (s.next (runSteps pre tr)).length
      · have hrnd_s := randAt_of_le_of_lt (runSteps_le ss' _) hlt_s hrnd
        exact coinDrawn_mono
          (fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact List.mem_cons_self)
          (fun x hx => List.mem_append_left _ hx)
          (runMatches_coinDrawn hsz hrm (Nat.not_lt.mp hlt_pre) hrnd_s)
      · exact coinDrawn_mono (fun x hx => List.mem_cons_of_mem _ hx)
          (fun x hx => List.mem_append_right _ hx) (ih (Nat.not_lt.mp hlt_s) hrnd)

/-! ## Main Theorem (`not_nextEventCollides_pt`) -/

theorem not_nextEventCollides_pt
    {withOpk : Bool} {evs₁ : List CliEvent} {ev : RunEvent}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : ev.cmd = .send peer := by rfl)
    (hb_len : ev.input.length = 9 := by decide)
    (hb_mem : (109#8 : BitVec 8) ∈ ev.input := by decide)
    (h_coins : (evs₁.all fun e => match e with
      | .run rEv => !(rEv.coins.contains 109#8)
      | .env _ => true) = true := by decide)
    (hex : Explains myInterp (mkRecords withOpk) (mySem withOpk) g ss vis evs₁) :
    ¬ NextEventCollides myInterp (mkRecords withOpk) (mySem withOpk) g ss vis evs₁ ev := by
  unfold NextEventCollides
  rw [hcmd]
  rintro ⟨heme, hghosts⟩
  let tr := runTrace (mkRecords withOpk) ss
  have hgpt : gamma myInterp (mySem withOpk) g (randTerm tr.length 32) = ev.input := by
    unfold BytesMatchEntry ptEntryAt at heme
    dsimp only [List.map] at heme
    exact List.head_eq_of_cons_eq heme.2
  have hg_mem :
      g ∈ PrefixExplainingGhosts myInterp (mkRecords withOpk) (mySem withOpk) g ss evs₁ :=
    ⟨rfl, vis, hex⟩
  have hmcol := hghosts g hg_mem
  unfold MemoCollisionOn ptEntryAt at hmcol
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hmcol
  obtain ⟨x₁, hx₁_new, x₂, hx₂_terms, hsh_ne, _, hx₁_pts_imp, _, hbytes_eq⟩ := hmcol
  have ⟨hmemo_pt, hgam_pt_σ⟩ :=
    gamma'_randTerm_32 myInterp (mySem withOpk) g tr.length
  rw [hmemo_pt] at hx₁_new
  rcases List.mem_singleton.mp hx₁_new with rfl
  have hx₁_in_pts :
      randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨hx₂_not_pts, hx₂_inj, _⟩ := hx₁_pts_imp hx₁_in_pts
  have hb_sigma : g.σ tr.length 32 = ev.input := hgam_pt_σ.symm.trans hgpt
  have hx₂_bytes : x₂.2.2 = ev.input := hbytes_eq.symm.trans hb_sigma
  have hx₂_in_pre :
      x₂ ∈ (prefixTerms (mkRecords withOpk) tr vis).flatMap
        (fun t => (gamma' myInterp (mySem withOpk) g t).memo) := by
    rcases List.mem_append.mp hx₂_terms with hpre | hnew
    · exact hpre
    · rw [hmemo_pt] at hnew
      rcases List.mem_singleton.mp hnew with rfl
      exact absurd rfl hsh_ne
  obtain ⟨t₀, ht₀, hx₂_memo⟩ := List.mem_flatMap.mp hx₂_in_pre
  rcases x₂ with ⟨u, sh, v⟩
  dsimp only at hx₂_not_pts hx₂_inj hx₂_bytes
  cases hx₂_bytes
  obtain ⟨hgam_u, hss32⟩ := memo_entry_inv myInterp (mySem withOpk) g t₀ u sh ev.input hx₂_memo
  have hlen_u : (gamma myInterp (mySem withOpk) g u).length = 9 := hgam_u ▸ hb_len
  obtain ⟨rnd, hview, hsz_ne⟩ :=
    nonRandom_assumedInjective_len_ne_9 (mySem withOpk) g u hx₂_inj hss32 hlen_u
  have hpack_u : u = rnd.pack := pack_of_view_eq_some hview
  obtain ⟨hgam_rnd, hrnd_eq⟩ :=
    gamma_randTerm_of_ne_zero myInterp (mySem withOpk) g rnd hsz_ne
  have hb_eq_σ : ev.input = g.σ rnd.timestamp rnd.size := by
    rw [hgam_u, hpack_u, hgam_rnd]
  have hu_eq_rand : u = randTerm rnd.timestamp rnd.size := hpack_u.trans hrnd_eq
  have hNe : (mkRecords withOpk).alice ≠ (mkRecords withOpk).bob := by
    show "alice" ≠ "bob"; decide
  have hrnd : RandAt tr rnd.timestamp rnd.size :=
    prefixTerms_termRandAt hex ht₀ u sh ev.input rnd hx₂_memo hview
  by_cases hsetup : rnd.timestamp < (setupTrace (mkRecords withOpk)).length
  · have hrnd_s : RandAt (setupTrace (mkRecords withOpk)) rnd.timestamp rnd.size :=
      randAt_of_le_of_lt (runSteps_le ss _) hsetup hrnd
    have hsetup_mem := randAt_setupTrace_mem_setupRandomsAt hNe hrnd_s
    have hfresh_eq := hex.1.1 (rnd.timestamp, rnd.size) hsetup_mem
    dsimp only at hfresh_eq
    have hfresh_b : ev.input = Witness.freshBytes rnd.timestamp rnd.size :=
      hb_eq_σ.trans hfresh_eq
    rw [hfresh_b] at hb_mem
    exact not_mem_109_freshBytes rnd.timestamp rnd.size hb_mem
  · rcases matchesEvents_coinDrawn hsz_ne hex.2.2.2 (Nat.not_lt.mp hsetup) hrnd with
      hpt_mem | ⟨v_rng, hv_mem, hv_kind, hsz32, hv_term⟩ |
        ⟨rEv, hrEv_mem, p, hp_coins, v_rng, _, _, hv_lay, hv_terms, hbme⟩
    · exact hx₂_not_pts (List.mem_append_left _ (hu_eq_rand ▸ hpt_mem))
    · have hlen32 := hex.2.1.1 v_rng hv_mem hv_kind rnd.timestamp rnd.size hsz_ne hv_term
      have h9_eq_32 : 9 = rnd.size := by
        rw [← hb_len, hb_eq_σ, hlen32]
      omega
    · unfold BytesMatchEntry at hbme
      rw [hv_lay, hv_terms] at hbme
      dsimp only [List.map] at hbme
      have hp_eq : gamma myInterp (mySem withOpk) g (randTerm rnd.timestamp rnd.size) = p :=
        List.head_eq_of_cons_eq hbme.2
      have hb_eq_p : ev.input = p := by rw [hgam_u, hu_eq_rand, hp_eq]
      rw [hb_eq_p] at hb_mem
      have h109_coins : (109#8 : BitVec 8) ∈ rEv.coins := hp_coins _ hb_mem
      have hall := List.all_eq_true.mp h_coins (.run rEv) hrEv_mem
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hall
      exact hall h109_coins

end Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollision
