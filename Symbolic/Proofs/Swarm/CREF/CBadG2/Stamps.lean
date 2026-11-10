/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.CBadG2.StampsReach
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Stamp Premises from `MatchedPrefix`

Establishes `CBadStamps` on every prefix run `ms.take i` (and on `ms` itself) of a
`MatchedPrefix` at any bound `n ≥ (runTraceMoves r ms).length`, along with stamp bounds on
visible entries and setup terms.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg trMsgKeys)
open DY.Libsignal.TripleRatchet (computeMac consumeMessageKey recvChainFor skippedSeeds RecvChain)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt StateStampsLt VisStampsLt TraceEntriesLt
  PQEventStampsLt PQEvEntry TREntry TRSignalMsgStampsLt ChainStampsLt visStampsLt_of_terms
  stampsLt_rand_of_lt stampsLt_parseTrSignalMsg stampsLt_trMsgKeys stampsLt_computeMac
  stampsLt_symDec stampsLt_kdfCk stampsLt_chainKeyAt stampsLt_recvChainFor
  stampsLt_consumeMessageKey setupTrace_le_runTrace traceEntriesLt_knows traceEntriesLt_at?_tr
  traceEntriesLt_at?_pqev traceEntriesLt_of_reachable)

/-! ## Visible-trace and setup stamp bounds -/

private theorem cbadG2_stampsLt_of_mem_newRandoms {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr tr' : ExecTrace} (hlen : tr'.length ≤ ts) {p : DY.Bytes × Nat}
    (hp : p ∈ newRandoms tr tr') : StampsLt i S g ts p.1 := by
  unfold newRandoms at hp
  obtain ⟨idx, hidx, hmap⟩ := List.mem_filterMap.mp hp
  simp only [newIndices, List.mem_range'_1] at hidx
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
  exact stampsLt_rand_of_lt i S g e.length (by omega)

private theorem cbadG2_visStampsLt_of_mem_kyberCoinEntries {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {entropy : DY.Bytes} (he : StampsLt i S g ts entropy) {v : VisEntry}
    (hv : v ∈ kyberCoinEntries entropy) : VisStampsLt i S g ts v := by
  unfold kyberCoinEntries at hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]; exact he

private theorem cbadG2_visStampsLt_of_mem_aliceDraws {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} (done : Option Nat) :
    ∀ (L : List DY.Bytes), (∀ t ∈ L, StampsLt i S g ts t) →
      ∀ {v : VisEntry}, v ∈ aliceDraws done L → VisStampsLt i S g ts v
  | [], _, _, hv => by simp [aliceDraws] at hv
  | [ek], hL, v, hv => by
    rcases List.mem_singleton.mp hv with rfl
    refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
    exact hL ek (by simp)
  | ek :: entropy :: rest, hL, v, hv => by
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL ek (by simp)
    · exact cbadG2_visStampsLt_of_mem_kyberCoinEntries (hL entropy (by simp)) hv
    · obtain ⟨dhsA, hdhsA, rfl⟩ := List.mem_map.mp hv
      refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL dhsA
        (List.mem_cons_of_mem ek (List.mem_cons_of_mem entropy (List.mem_of_mem_take hdhsA)))

private theorem cbadG2_visStampsLt_of_mem_encDraws {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} :
    ∀ (L : List (DY.Bytes × Nat)), (∀ p ∈ L, StampsLt i S g ts p.1) →
      ∀ {v : VisEntry}, v ∈ encDraws L → VisStampsLt i S g ts v
  | [], _, _, hv => by simp [encDraws] at hv
  | (m, sz) :: rest, hL, v, hv => by
    simp only [encDraws, List.mem_cons] at hv
    rcases hv with rfl | hv
    · refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL (m, sz) (by simp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
      exact hL r (List.mem_cons_of_mem _ (List.mem_of_mem_filter hr))

private theorem cbadG2_stampsLt_of_receivedPlaintext {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {tr tr' T : ExecTrace} (hle : tr' ≤ T)
    (htr : TraceEntriesLt i S g ts T) {m : DY.Bytes}
    (h : receivedPlaintext tr tr' = some m) : StampsLt i S g ts m := by
  unfold receivedPlaintext at h
  obtain ⟨idx, _, hfind⟩ := List.exists_of_findSome?_eq_some h
  split at hfind
  · next me peer rk n msg hev =>
    cases hfind
    have hat' : (tr'.at? idx : Option TREntry) = some ⟨.Received me peer rk n m⟩ := by
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
      rcases he : (tr'.at? idx : Option TREntry) with _ | e
      · rw [he] at hev; cases hev
      · rw [he] at hev; injection hev with hev; cases e; subst hev; rfl
    have hatT := DY.Trace.at?_le (EntryT := TREntry) tr' T idx hle
    rw [hat'] at hatT
    exact traceEntriesLt_at?_tr htr hatT
  · cases hfind

private theorem cbadG2_pqEventStampsLt_of_at?_le {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {tr T : ExecTrace} (hle : tr ≤ T) (htr : TraceEntriesLt i S g ts T)
    {j : Nat} {e : PQEvEntry} (he : (tr.at? j : Option PQEvEntry) = some e) :
    PQEventStampsLt i S g ts e.ev := by
  have hatT := DY.Trace.at?_le (EntryT := PQEvEntry) tr T j hle
  rw [he] at hatT
  exact traceEntriesLt_at?_pqev htr hatT

private theorem cbadG2_stampsLt_of_mem_sessionBaseKeys {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ts : Nat} {tr T : ExecTrace} (hle : tr ≤ T) (htr : TraceEntriesLt i S g ts T)
    {stateIdx : Nat} {ek : DY.Bytes} (hek : ek ∈ sessionBaseKeys tr stateIdx) :
    StampsLt i S g ts ek := by
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hek
  split at hek
  · obtain ⟨ev, hev_mem, hfind⟩ := List.mem_filterMap.mp hek
    obtain ⟨idx, _, hget⟩ := List.mem_filterMap.mp hev_mem
    split at hfind
    · cases hfind
      split at hget
      · split at hget
        · simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
          rcases he : (tr.at? _ : Option PQEvEntry) with _ | e
          · rw [he] at hget; cases hget
          · rw [he] at hget; injection hget with hget; cases e; subst hget
            exact cbadG2_pqEventStampsLt_of_at?_le hle htr he
        · cases hget
      · cases hget
    · cases hfind
  · cases hek

private theorem cbadG2_visOf_visStampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} (m : Move) (tr : ExecTrace) (hs : OpkNetOK tr) {T : ExecTrace} (hle : m.next tr ≤ T)
    (hlen : T.length ≤ ts) (htr : TraceEntriesLt i S g ts T)
    {v : VisEntry} (hv : v ∈ m.vis tr) :
    VisStampsLt i S g ts v := by
  have hlen' : (m.next tr).length ≤ ts := Nat.le_trans (DY.Trace.length_le _ _ hle) hlen
  have hvk : VisKnown T v := (move_known m hs hv).mono hle
  have hobsT : (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) →
      ∀ t ∈ v.terms, StampsLt i S g ts t :=
    fun hk t ht => traceEntriesLt_knows htr (hvk hk t ht)
  have hobs : (v.kind = .send ∨ v.kind = .recv ∨ v.kind = .leak) →
      TR.FreshSigma.layoutKeys v.layout = [] → VisStampsLt i S g ts v :=
    fun hk hl => visStampsLt_of_terms hl (hobsT hk)
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hv | hv
  · cases m with
    | aliceStart _ _ _ _ h _ =>
      have hv' := List.mem_of_mem_take hv
      unfold aliceVis at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hobs (.inr (.inl rfl)) rfl
      · refine cbadG2_visStampsLt_of_mem_aliceDraws _ _ (fun t ht => ?_) hv'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact cbadG2_stampsLt_of_mem_newRandoms hlen' hp
    | bobStart _ _ _ _ mh _ _ _ =>
      have hv' := List.mem_of_mem_take hv
      unfold bobVis at hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hobs (.inr (.inl rfl)) rfl
      · rcases List.mem_append.mp hv' with hv' | hv'
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv'
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact cbadG2_stampsLt_of_mem_newRandoms hlen' hr
        · rcases hp : receivedPlaintext tr _ with _ | pt
          · rw [hp] at hv'; cases hv'
          · rw [hp] at hv'
            rcases List.mem_singleton.mp hv' with rfl
            refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
            exact cbadG2_stampsLt_of_receivedPlaintext hle htr hp
    | encrypt _ _ _ _ wrap =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact cbadG2_visStampsLt_of_mem_encDraws _
          (fun _ hp => cbadG2_stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp only [↓reduceIte] at hv; unfold encSend at hv
        split at hv
        · split at hv <;> (rcases List.mem_singleton.mp hv with rfl; exact hobs (.inl rfl) rfl)
        · cases hv
    | encryptAbort _ _ =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact cbadG2_visStampsLt_of_mem_encDraws _
          (fun _ hp => cbadG2_stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp at hv
    | encryptFail _ _ _ =>
      unfold encVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact cbadG2_visStampsLt_of_mem_encDraws _
          (fun _ hp => cbadG2_stampsLt_of_mem_newRandoms hlen' hp) hv
      · simp at hv
    | decrypt _ _ msgIdx _ _ wrapped =>
      unfold decVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · rcases hm : tr.getMessageSentAt msgIdx with _ | b
          · rw [hm] at hv; cases hv
          · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl
            refine ⟨hobsT (.inr (.inl rfl)), ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => cbadG2_stampsLt_of_mem_sessionBaseKeys
                (DY.Trace.le_trans _ _ _ (Move.le_next _ tr) hle) htr hek
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact cbadG2_stampsLt_of_mem_newRandoms hlen' hr
      · rcases hp : receivedPlaintext tr _ with _ | pt
        · rw [hp] at hv; cases hv
        · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact cbadG2_stampsLt_of_receivedPlaintext hle htr hp
    | decryptSkipped _ _ msgIdx _ _ _ wrapped =>
      unfold decVis at hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hv with hv | hv
        · rcases hm : tr.getMessageSentAt msgIdx with _ | b
          · rw [hm] at hv; cases hv
          · rw [hm] at hv; rcases List.mem_singleton.mp hv with rfl
            refine ⟨hobsT (.inr (.inl rfl)), ?_⟩
            cases wrapped
            · intro _ ht; cases ht
            · exact fun ek hek => cbadG2_stampsLt_of_mem_sessionBaseKeys
                (DY.Trace.le_trans _ _ _ (Move.le_next _ tr) hle) htr hek
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact cbadG2_stampsLt_of_mem_newRandoms hlen' hr
      · rcases hp : receivedPlaintext tr _ with _ | pt
        · rw [hp] at hv; cases hv
        · rw [hp] at hv; rcases List.mem_singleton.mp hv with rfl
          refine visStampsLt_of_terms rfl fun x hx => ?_; rw [List.mem_singleton.mp hx]
          exact cbadG2_stampsLt_of_receivedPlaintext hle htr hp
    | reject draws =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact visStampsLt_of_terms rfl fun _ ht => by cases ht
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
        exact visStampsLt_of_terms rfl fun _ ht => by cases ht
    | setup _ _ _ | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _
    | compromiseOPK _ _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
    | attackerSend _ => cases hv
    | brkDH =>
      cases hv
    | brkKEM =>
      cases hv
  · unfold exposures at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      unfold pqExposureAt at hj
      split at hj <;> (try cases hj) <;> exact hobs (.inr (.inr rfl)) rfl
    · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      unfold trExposureAt at hj
      split at hj <;> (try cases hj) <;> exact hobs (.inr (.inr rfl)) rfl

private theorem cbadG2_runMoves_visStampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} :
    ∀ (L : List Move) (tr : ExecTrace),
      OpkNetOK tr →
      (runMoves L tr).1.length ≤ ts →
      TraceEntriesLt i S g ts (runMoves L tr).1 →
      ∀ v ∈ (runMoves L tr).2, VisStampsLt i S g ts v
  | [], _, _, _, _, _, hv => by cases hv
  | m :: ms, tr, hs, hlen, htr, v, hv => by
    simp only [runMoves] at hv hlen htr
    rcases List.mem_append.mp hv with hm | hms
    · exact cbadG2_visOf_visStampsLt m tr hs (runMoves_le ms (m.next tr)) hlen htr hm
    · exact cbadG2_runMoves_visStampsLt ms (m.next tr) (hs.next m) hlen htr v hms

theorem cbadG2_runVis_visStampsLt {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat}
    {r₀ : ProtocolSetup} {ms : List Move} (hrun : ModelRun r₀ ms) (hts : (runTraceMoves r₀ ms).length ≤ ts)
    {v : VisEntry} (hv : v ∈ runVis r₀ ms) :
    VisStampsLt i S g ts v :=
  cbadG2_runMoves_visStampsLt (r₀.setupMove :: ms) DY.Trace.nil opkNetOK_nil hts
    (traceEntriesLt_of_reachable i S g ts hrun.2.2.1.1 hts) v hv

theorem cbadG2_fst_lt_of_mem_setupRandomsAt {r : ProtocolSetup} (hNe : r.alice ≠ r.bob) {p : Nat × Nat}
    (hp : p ∈ setupRandomsAt r) : p.1 < (setupTrace r).length := by
  have hlen : (setupTrace r).length = if r.withOpk then 26 else 22 := by
    rw [TR.setupTrace_eq r hNe]
    cases r.withOpk <;>
      simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2,
        TR.setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        Symbolic.DYBridge.DY.Trace.length_eq_1]
  rw [TR.setupRandomsAt_eq r hNe] at hp; rw [hlen]
  rcases p with ⟨p1, p2⟩
  cases hOpk : r.withOpk <;> simp_all <;> omega

private theorem cbadG2_setupTrace_length_pos (r : ProtocolSetup) : 0 < (setupTrace r).length := by
  change 0 < ((setupAct r.alice r.bob r.withOpk).run DY.Trace.nil).2.val.length
  unfold setupAct; rw [Traceful.run_bind]
  have ⟨ho1, htr1⟩ := TR.runs_registerIdentity_a r.alice
  have h1 : ((DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil).1 = some 4 ∧
      ((DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil).2.val.length = 5 := by
    refine ⟨ho1, ?_⟩
    rw [htr1]
    simp only [TR.setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rcases hrun1 : (DY.Libsignal.PQXDH.registerIdentity r.alice).run DY.Trace.nil with ⟨o1, tr1, _⟩
  rw [hrun1] at h1; dsimp only at h1; rcases h1 with ⟨rfl, hlen1⟩; dsimp only
  have hle := DY.Trace.length_le _ _ ((do
    let hB ← DY.Libsignal.PQXDH.registerIdentity r.bob
    let _ ← DY.Libsignal.PQXDH.genSignedPrekey r.bob hB
    let _ ← DY.Libsignal.PQXDH.genPQPrekey r.bob hB
    if r.withOpk then do let _ ← DY.Libsignal.PQXDH.genOneTimePrekey r.bob; pure ()
    else pure ()).run tr1).2.property
  exact Nat.lt_of_lt_of_le (by omega) hle

theorem cbadG2_stampsLt_setupPublic {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move} {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts)
    (htr : TraceEntriesLt i S g ts (runTraceMoves r₀ ms)) (k : Nat) :
    StampsLt i S g ts (setupPublic r₀ k) := by
  have hsetup_le : (setupTrace r₀).length ≤ ts :=
    Nat.le_trans (DY.Trace.length_le _ _ (Refinement.setupTrace_le_runTrace r₀ ms)) hts
  have hpos := cbadG2_setupTrace_length_pos r₀
  unfold setupPublic
  rcases hget : (setupSent r₀)[k]? with _ | t
  · exact stampsLt_rand_of_lt i S g 0 (by omega)
  · exact traceEntriesLt_knows htr (setupSent_known (List.mem_of_getElem? hget))

/-! ## Trial and salt stamp closure -/

section Closure

variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
  {ms : List Move} {n : Nat}

theorem cbadG2_stampsLt_skippedSeeds {c : RecvChain} {ctr : UInt32}
    (hc : ChainStampsLt interpretation S g n c) :
    ∀ u ∈ skippedSeeds c ctr, StampsLt interpretation S g n u := by
  intro u hu
  unfold skippedSeeds at hu
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hu
  exact (stampsLt_kdfCk (stampsLt_chainKeyAt j hc.2)).2

theorem cbadG2_stampsLt_saltTerms {peerIk myIk : DY.Bytes} {msg : TRSignalMsg}
    {seed salt : DY.Bytes}
    (hpeer : StampsLt interpretation S g n peerIk) (hmy : StampsLt interpretation S g n myIk)
    (hmsg : TRSignalMsgStampsLt interpretation S g n msg)
    (hseed : StampsLt interpretation S g n seed) (hsalt : StampsLt interpretation S g n salt) :
    ∀ u ∈ [(trMsgKeys salt seed).cipherKey, (trMsgKeys salt seed).macKey, (trMsgKeys salt seed).iv,
        computeMac (trMsgKeys salt seed).macKey peerIk myIk msg.wire] ++
        (DY.SymEnc.symDec (trMsgKeys salt seed).cipherKey (trMsgKeys salt seed).iv
          msg.ciphertext).toList,
      StampsLt interpretation S g n u := by
  obtain ⟨hck, hmk, hiv⟩ := stampsLt_trMsgKeys hsalt hseed
  intro u hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with ((rfl | rfl | rfl | rfl) | hu)
  · exact hck
  · exact hmk
  · exact hiv
  · exact stampsLt_computeMac hmk hpeer hmy hmsg.1
  · cases hdec : DY.SymEnc.symDec (trMsgKeys salt seed).cipherKey (trMsgKeys salt seed).iv
        msg.ciphertext with
    | none => rw [hdec] at hu; cases hu
    | some m =>
      rw [hdec] at hu
      obtain rfl := Option.some.inj (Option.mem_toList.mp hu)
      exact stampsLt_symDec hdec hmsg.2.2.2.1

theorem cbadG2_stampsLt_getMessageSentAt_of_entries {tr : ExecTrace}
    (htr : TraceEntriesLt interpretation S g n tr) {k : Nat} {u : DY.Bytes}
    (hu : tr.getMessageSentAt k = some u) : StampsLt interpretation S g n u := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hu
  cases h' : (tr.at? k : Option Network.ExecEntryT) with
  | none => simp [h'] at hu
  | some e =>
    have hlt := TR.FreshSigma.traceEntriesLt_at?_net htr h'
    cases e; simp [h'] at hu; subst hu; exact hlt

theorem cbadG2_stampsLt_skippedLogged_of_entries {tr : ExecTrace}
    (htr : TraceEntriesLt interpretation S g n tr) :
    ∀ i s pk ctr seed rIdx src,
      i < tr.length →
      tr.getEventAt TREvent i = some (.SkippedKeyStored s pk ctr seed rIdx src) →
      StampsLt interpretation S g n seed ∧ StampsLt interpretation S g n pk := by
  intro i s pk ctr seed rIdx src _ hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases he : (tr.at? i : Option TREntry) with _ | ⟨⟨ev⟩⟩ <;> rw [he] at hget
  · cases hget
  · injection hget with hEq; subst hEq
    exact traceEntriesLt_at?_tr htr he

theorem cbadG2_getMessageSentAt_le {tr tr' : ExecTrace} (hle : tr ≤ tr') {k : Nat} {u : DY.Bytes}
    (hu : tr.getMessageSentAt k = some u) : tr'.getMessageSentAt k = some u := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at hu ⊢
  cases h' : (tr.at? k : Option Network.ExecEntryT) with
  | none => simp [h'] at hu
  | some e =>
    rw [h'] at hu
    have h2 : (tr'.at? k : Option Network.ExecEntryT) = some e := by
      have h1 := DY.Trace.at?_le (EntryT := Network.ExecEntryT) tr tr' k hle
      rw [h'] at h1
      exact h1
    rw [h2]
    exact hu

theorem cbadG2_honestKeysFrom_sent : ∀ (ms : List Move) (tr : ExecTrace) (u : DY.Bytes),
    u ∈ honestKeysFrom tr ms → ∃ k, (runMoves ms tr).1.getMessageSentAt k = some u
  | [], _, _, hu => by simp [honestKeysFrom] at hu
  | m :: ms, tr, u, hu => by
    unfold honestKeysFrom at hu
    rcases List.mem_append.mp hu with hu | hu
    · refine ⟨tr.length + 2, cbadG2_getMessageSentAt_le (runMoves_le ms (m.next tr)) ?_⟩
      cases m <;> simp at hu
      all_goals exact hu
    · exact cbadG2_honestKeysFrom_sent ms (m.next tr) u hu

theorem cbadG2_stampsLt_honestSalts_of_entries
    (htr : TraceEntriesLt interpretation S g n (runTraceMoves r ms)) :
    ∀ s ∈ honestSalts r ms, StampsLt interpretation S g n s := by
  intro s hs
  unfold honestSalts at hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact TR.FreshSigma.stampsLt_zeroKey interpretation S g n
  · obtain ⟨k, hk⟩ := cbadG2_honestKeysFrom_sent ms (setupTrace r) s hs
    exact cbadG2_stampsLt_getMessageSentAt_of_entries htr hk

theorem cbadG2_stateStampsLt_availableStates {tr : ExecTrace}
    (htr : TraceEntriesLt interpretation S g n tr) {st : TRState}
    (hst : st ∈ availableStates r tr) : StateStampsLt interpretation S g n st := by
  unfold availableStates at hst
  obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hst
  unfold storedStates DY.ExecTrace.getLocalStateAt at hls
  obtain ⟨j, _, he⟩ := List.mem_filterMap.mp hls
  simp only [Option.map_eq_some_iff] at he
  obtain ⟨e, hat, rfl⟩ := he
  exact TR.FreshSigma.traceEntriesLt_at?_st htr hat

theorem cbadG2_stampsLt_ownKeys {tr : ExecTrace}
    (hstates : ∀ st ∈ availableStates r tr, StateStampsLt interpretation S g n st)
    (st : TRState) {msg : TRSignalMsg}
    (hmsg : TRSignalMsgStampsLt interpretation S g n msg) :
    ∀ k ∈ ownKeys r tr st msg, StampsLt interpretation S g n k := by
  intro k hk
  unfold ownKeys at hk
  obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hk
  have hst'' := hstates st' (List.mem_filter.mp hst').1
  exact (TR.FreshSigma.stampsLt_spqrRecvKey_pack interpretation S g n _).mpr
    ⟨hst''.2.2.2.2.2.1, hmsg.2.2.2.2⟩

theorem cbadG2_stampsLt_whisperTrials {tr : ExecTrace}
    (htr : TraceEntriesLt interpretation S g n tr)
    (hstates : ∀ st ∈ availableStates r tr, StateStampsLt interpretation S g n st)
    {msg : TRSignalMsg} (hmsg : TRSignalMsgStampsLt interpretation S g n msg) :
    ∀ ctx ∈ whisperTrials interpretation r S g tr msg,
      StampsLt interpretation S g n ctx.peerIk ∧
      StampsLt interpretation S g n ctx.myIk ∧
      (∀ u ∈ ctx.extra, StampsLt interpretation S g n u) ∧
      (∀ k ∈ ctx.ownSalts, StampsLt interpretation S g n k) ∧
      (∀ seed, ctx.seed? = some seed → StampsLt interpretation S g n seed) := by
  have hsk := cbadG2_stampsLt_skippedLogged_of_entries htr
  intro ctx hctx
  unfold whisperTrials at hctx
  split at hctx
  · obtain ⟨st, hst_mem, hctx_st⟩ := List.mem_flatMap.mp hctx
    have hst := hstates st hst_mem
    have hown := cbadG2_stampsLt_ownKeys hstates st hmsg
    rcases List.mem_append.mp hctx_st with hchain | hskip
    · obtain ⟨c, hc_mem, hctx_c⟩ := List.mem_map.mp hchain
      have hc : ChainStampsLt interpretation S g n c := by
        rcases List.mem_append.mp hc_mem with hc_filt | hc_fresh
        · exact hst.2.2.2.2.2.2 c (List.mem_of_mem_filter hc_filt)
        · have hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, true) := by
            unfold recvChainFor
            unfold DY.Libsignal.TripleRatchet.recvHalfStep at hc_fresh
            cases hfind : DY.Libsignal.TripleRatchet.findRecvChain st.recv msg.ratchetKey with
            | some _ => simp [hfind] at hc_fresh
            | none =>
              cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey with
              | true => simp [hfind, hlo] at hc_fresh
              | false =>
                simp only [hfind, hlo, Bool.false_eq_true, ↓reduceIte,
                  List.mem_singleton] at hc_fresh ⊢
                subst hc_fresh; rfl
          exact stampsLt_recvChainFor hst hmsg.2.2.1 hrc
      revert hctx_c
      cases hcm : consumeMessageKey c msg.counter with
      | none =>
        dsimp only; intro hEq; subst hEq
        refine ⟨hst.2.1, hst.1, ?_, ?_, ?_⟩
        · intro u hu; rcases List.mem_singleton.mp hu with rfl; exact hc.2
        · intro _ hk; cases hk
        · intro _ hs; cases hs
      | some sc =>
        rcases sc with ⟨seed, c'⟩
        dsimp only; intro hEq; subst hEq
        obtain ⟨hseed, hc'⟩ := stampsLt_consumeMessageKey hc hcm
        refine ⟨hst.2.1, hst.1, ?_, hown, ?_⟩
        · intro u hu
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with (rfl | rfl) | hu
          · exact hc.2
          · exact hc'.2
          · exact cbadG2_stampsLt_skippedSeeds hc u hu
        · intro seed' hs; injection hs with hs'; subst hs'; exact hseed
    · obtain ⟨idx, hidx_mem, hctx_idx⟩ := List.mem_filterMap.mp hskip
      have hlt : idx < tr.length := List.mem_range.mp hidx_mem
      revert hctx_idx
      cases hget : tr.getEventAt TREvent idx with
      | none => intro h; cases h
      | some ev =>
        cases ev with
        | SkippedKeyStored s pk ctr seed rIdx src =>
          dsimp only
          by_cases hhit : (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome ∧
              gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey ∧
              ctr = msg.counter
          · simp only [hhit]
            intro hEq; injection hEq with hEq'; subst hEq'
            have hseed_pk := hsk idx s pk ctr seed rIdx src hlt hget
            refine ⟨hst.2.1, hst.1, ?_, ?_, ?_⟩
            · intro _ hu; cases hu
            · intro k hk
              by_cases hs : st.sessionInfo s.me = s
              · simp only [hs, ↓reduceIte] at hk; exact hown k hk
              · simp only [hs, ↓reduceIte] at hk; cases hk
            · intro seed' hs; injection hs with hs'; subst hs'; exact hseed_pk.1
          · simp only [hhit, ↓reduceIte]
            intro h; cases h
        | _ => intro h; cases h
  · cases hctx

/-! ## Assembly on matched prefixes -/

theorem cbadG2_stamps_of_base (htr : TraceEntriesLt interpretation S g n (runTraceMoves r ms))
    (hvis : ∀ v ∈ runVis r ms, VisStampsLt interpretation S g n v)
    (hpre : ∀ t ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), StampsLt interpretation S g n t)
    (hbob : ∀ ek ∈ bobDoneBaseKeys (runTraceMoves r ms), StampsLt interpretation S g n ek) :
    CBadStamps interpretation r S g ms n := by
  have hstates := fun st (hst : st ∈ availableStates r (runTraceMoves r ms)) =>
    cbadG2_stateStampsLt_availableStates (S := S) (g := g) (n := n) htr hst
  have hsalts := cbadG2_stampsLt_honestSalts_of_entries htr
  have htrials := fun (msg : TRSignalMsg) (hmsg : TRSignalMsgStampsLt interpretation S g n msg) =>
    cbadG2_stampsLt_whisperTrials (r := r) htr hstates hmsg
  refine ⟨htr, hvis, hpre, hbob, hstates, hsalts,
    cbadG2_stampsLt_skippedLogged_of_entries htr,
    fun st _ hmsg => cbadG2_stampsLt_ownKeys hstates st hmsg,
    htrials, ?_⟩
  intro t msg ht hp u hu
  have hmsg := stampsLt_parseTrSignalMsg ht hp
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ht
  · obtain ⟨ctx, hctx, hu_ctx⟩ := List.mem_flatMap.mp hu
    have htr_ctx := htrials msg hmsg ctx hctx
    unfold trialTerms at hu_ctx
    rcases List.mem_append.mp hu_ctx with hu_ex | hu_rest
    · exact htr_ctx.2.2.1 u hu_ex
    · revert hu_rest
      cases hseed_eq : ctx.seed? with
      | none => intro h; cases h
      | some seed =>
        dsimp only; intro hu_flat
        obtain ⟨salt, hsalt, hu_salt⟩ := List.mem_flatMap.mp hu_flat
        exact cbadG2_stampsLt_saltTerms htr_ctx.1 htr_ctx.2.1 hmsg
          (htr_ctx.2.2.2.2 seed hseed_eq) (hsalts salt hsalt) u hu_salt

/-- Every prefix `ms.take i` of a `MatchedPrefix` satisfies `CBadStamps` at
`n ≥ (runTraceMoves r ms).length`. -/
theorem cbadG2_stamps_of_matched_take {who : List Participant} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) (hn : (runTraceMoves r ms).length ≤ n)
    (i : Nat) :
    CBadStamps interpretation r S g (ms.take i) n := by
  have hrun : ModelRun r ms := hmp.2.1
  have hreach : (runTraceMoves r (ms.take i)).Reachable reachability := hrun.2.2.1.2.2 i
  have hle : (runTraceMoves r (ms.take i)).length ≤ n := by
    have h := DY.Trace.length_le _ _ (runTrace_le_append r (ms.take i) (ms.drop i))
    rw [List.take_append_drop] at h
    omega
  have hvis : ∀ v ∈ runVis r (ms.take i), VisStampsLt interpretation S g n v := by
    intro v hv
    refine cbadG2_runVis_visStampsLt hrun hn ?_
    have h := runVis_append r (ms.take i) (ms.drop i)
    rw [List.take_append_drop] at h
    rw [h]; exact List.mem_append_left _ hv
  exact cbadG2_stamps_of_base (traceEntriesLt_of_reachable interpretation S g n hreach hle) hvis
    (cbadG2_stampsLt_prefixTerms interpretation S g r hreach hle hvis)
    (cbadG2_stampsLt_bobDoneBaseKeys_of_reachable interpretation S g hreach hle)

theorem cbadG2_stamps_of_matched {who : List Participant} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) (hn : (runTraceMoves r ms).length ≤ n) :
    CBadStamps interpretation r S g ms n := by
  have h := cbadG2_stamps_of_matched_take hmp hn ms.length
  rwa [List.take_of_length_le (Nat.le_refl _)] at h

theorem cbadG2_stampsLt_getMessageSentAt (h : CBadStamps interpretation r S g ms n)
    {k : Nat} {u : DY.Bytes} (hu : (runTraceMoves r ms).getMessageSentAt k = some u) :
    StampsLt interpretation S g n u :=
  cbadG2_stampsLt_getMessageSentAt_of_entries h.entries hu

theorem cbadG2_stampsLt_bobDoneBaseKeys_take {who : List Participant} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r S who g ms τ) (hn : (runTraceMoves r ms).length ≤ n) (i : Nat)
    {ek : DY.Bytes} (hek : ek ∈ bobDoneBaseKeys (runTraceMoves r (ms.take i))) :
    StampsLt interpretation S g n ek :=
  (cbadG2_stamps_of_matched_take hmp hn i).bobBaseKeys ek hek

end Closure

end Symbolic.Swarm.CREF
