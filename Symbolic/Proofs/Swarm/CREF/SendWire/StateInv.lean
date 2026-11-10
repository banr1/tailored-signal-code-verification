/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Batteries.Data.UInt
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import VCVio.Prelude.Core
import Symbolic.Proofs.Swarm.CREF.SendWire.GhostInvariance -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Model State, Bookkeeping, and Snapshot Invariance for `SendWire`

Proves `TRKeyShape`, `isCurrentSnapshot`, `TRNsBound`, `bobDoneBaseKeys`, and visible-entry lemmas
across `Move.encryptAbort` and `Move.encrypt` (with or without prekey wrapping).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.SendWire

cref_open
open DY
open DY.Libsignal
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvDec (at?_append_of_lt at?_append_non_entry
  isCurrentSnapshot_append_non_st)
open Symbolic.Swarm.CREF.TR.FreshSigma (getLocalState_fst)

theorem getLocalState_fst_append_non_st {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option StEntry) = none)
    (p : Participant) (idx : Nat) :
    ((PersistentLocalState.getLocalState p idx : Traceful TRState).run (tr.append e)).1 =
      ((PersistentLocalState.getLocalState p idx : Traceful TRState).run tr).1 := by
  rw [getLocalState_fst, getLocalState_fst]
  by_cases hlt : idx < tr.length
  · rw [at?_append_of_lt _ _ hlt]
  · by_cases heq : idx = tr.length
    · subst heq
      have h1 : ((tr.append e).at? tr.length : Option StEntry) = none := by
        simp [Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_2, hnone]
      rw [h1, at?_eq_none_of_not_lt tr hlt]
    · have hge : ¬ idx < (tr.append e).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [at?_eq_none_of_not_lt _ hge, at?_eq_none_of_not_lt tr hlt]

private theorem list_all_eq_of_mem {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

unseal DY.Bytes in
private instance subFunction_gKdf0 (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_hmac_eq (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (s m : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac s m) =
      ByteSpecs.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction interpretation)
        (gamma interpretation S g s) (gamma interpretation S g m) := by
  show (gamma' interpretation S g
    (({salt := s, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).bytes = _
  unfold gamma'
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]
  rfl

private theorem length_sha256With_32
    (F : ByteSpecs.ShaState → List (BitVec 8) → ByteSpecs.ShaState) (m : List (BitVec 8)) :
    (ByteSpecs.sha256With F m).length = 32 := by
  unfold ByteSpecs.sha256With
  generalize (ByteSpecs.chunks64 (ByteSpecs.sha256Pad m)).foldl F ByteSpecs.sha256IV = s
  rcases s with ⟨l, hl⟩
  simp [ByteSpecs.toBEBytes, List.length_flatMap, hl]

theorem gamma_kdfCk_fst_length (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (cks : DY.Bytes) :
    (gamma interpretation S g (TripleRatchet.kdfCk cks).1).length = 32 := by
  change (gamma interpretation S g
    (DY.Libsignal.TripleRatchet.hmac cks (DY.Libsignal.TripleRatchet.litByte 0x02))).length = 32
  rw [gamma_hmac_eq]
  exact length_sha256With_32 _ _

theorem trKeyShape_encSt {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} (hks : TRKeyShape interpretation S g st) (coinsLen ts : Nat) :
    TRKeyShape interpretation S g (encSt st coinsLen ts) :=
  ⟨hks.dhs_len, gamma_kdfCk_fst_length interpretation S g st.cks, hks.myIk_ser, hks.peerIk_ser⟩

private theorem newIndices_append_loc {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
  unfold newIndices
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [show (tr.length + 1) - tr0.length = (tr.length - tr0.length) + 1 by omega,
    List.range'_concat]
  congr 2; omega

private theorem mem_newIndices_loc {tr0 tr : ExecTrace} {i : Nat} :
    i ∈ newIndices tr0 tr ↔ tr0.length ≤ i ∧ i < tr.length := by
  simp only [newIndices, List.mem_range'_1]; omega

private theorem newRandoms_append_loc {E : Type} [ExecTraceTypes.Has E]
    {tr0 tr : ExecTrace} (h : tr0.length ≤ tr.length) (e : E) :
    newRandoms tr0 (tr.append e) = newRandoms tr0 tr ++
      (((tr.append e).at? tr.length : Option DY.Random.ExecEntryT).map
        fun r => (randTerm tr.length r.length, r.length)).toList := by
  unfold newRandoms
  rw [newIndices_append_loc h, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  refine List.filterMap_congr fun i hi => ?_
  rw [at?_append_of_lt tr e (mem_newIndices_loc.mp hi).2]

private theorem newRandoms_append_rnd_loc {tr0 tr : ExecTrace}
    (h : tr0.length ≤ tr.length) (n : Nat) :
    newRandoms tr0 (tr.append (DY.Random.ExecEntryT.mk n)) =
      newRandoms tr0 tr ++ [(randTerm tr.length n, n)] := by
  rw [newRandoms_append_loc h, at?_append_eq_some tr _ rfl]; rfl

private theorem exposures_eq_nil_loc {tr tr' : ExecTrace}
    (h : ∀ j ∈ newIndices tr tr', pqExposureAt tr' j = none ∧ trExposureAt tr' j = none) :
    exposures tr tr' = [] := by
  unfold exposures
  rw [List.filterMap_eq_nil_iff.mpr fun j hj => (h j hj).1,
    List.filterMap_eq_nil_iff.mpr fun j hj => (h j hj).2, List.nil_append]

private theorem getEventAt_append_non_pq {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none)
    (j : Nat) :
    (tr.append e).getEventAt PQXDH.PQXDHEvent j = tr.getEventAt PQXDH.PQXDHEvent j := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_non_entry tr e hnone]

private theorem getEventAt_append_non_tr_ev {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TREntry) = none)
    (j : Nat) :
    (tr.append e).getEventAt TREvent j = tr.getEventAt TREvent j := by
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_non_entry tr e hnone]

theorem visOf_encryptAbort_of_some {me : Participant} {stateIdx : Nat} {tr : ExecTrace}
    {st : TRState}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st) :
    (Move.encryptAbort me stateIdx).vis tr = [trEntry .pt (randTerm tr.length 32)] := by
  have hnext := encryptAbort_next_of_some hst
  rw [vis_encryptAbort hnext, newRandoms_append_rnd_loc (Nat.le_refl _) 32]
  have hself : newRandoms tr tr = [] := by simp [newRandoms, newIndices]
  rw [hself, List.nil_append]
  change (trEntry .pt (randTerm tr.length 32) :: []) ++
    exposures tr (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) = _
  have hexp : exposures tr (tr.append (⟨32⟩ : DY.Random.ExecEntryT)) = [] := by
    apply exposures_eq_nil_loc
    intro j hj
    have hj_nlt : ¬ j < tr.length := Nat.not_lt.mpr (mem_newIndices_loc.mp hj).1
    have hpq : (tr.append (⟨32⟩ : DY.Random.ExecEntryT)).getEventAt PQXDH.PQXDHEvent j = none := by
      rw [getEventAt_append_non_pq tr (⟨32⟩ : DY.Random.ExecEntryT) rfl]
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_eq_none_of_not_lt tr hj_nlt]
    have htr_e : (tr.append (⟨32⟩ : DY.Random.ExecEntryT)).getEventAt TREvent j = none := by
      rw [getEventAt_append_non_tr_ev tr (⟨32⟩ : DY.Random.ExecEntryT) rfl]
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_eq_none_of_not_lt tr hj_nlt]
    exact ⟨by simp [pqExposureAt, hpq], by simp [trExposureAt, htr_e]⟩
  rw [hexp, List.append_nil]

theorem eventLoggedAt_encTr_of_lt (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) {ev : TREvent} {i : Nat} (hi : i < tr.length) :
    (encTr tr me stateIdx coinsLen st).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_encTr_of_lt _ _ _ _ _ hi]

theorem getLocalState_fst_encTr_of_lt (tr : ExecTrace) (me q : Participant)
    (stateIdx coinsLen : Nat) (st : TRState) {i : Nat} (hi : i < tr.length) :
    ((PersistentLocalState.getLocalState q i : Traceful TRState).run
        (encTr tr me stateIdx coinsLen st)).1 =
      ((PersistentLocalState.getLocalState q i : Traceful TRState).run tr).1 := by
  rw [getLocalState_fst, getLocalState_fst, at?_encTr_of_lt _ _ _ _ _ hi]

theorem getLocalState_fst_encTr_new (tr : ExecTrace) (me : Participant)
    (stateIdx coinsLen : Nat) (st : TRState) :
    ((PersistentLocalState.getLocalState me (tr.length + 5) : Traceful TRState).run
        (encTr tr me stateIdx coinsLen st)).1 =
      some (encSt st coinsLen tr.length) := by
  rw [getLocalState_fst]
  unfold encTr; dsimp only
  rw [at?_append_of_lt _ _ (by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_eq_some _ _ (by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2])]
  simp

theorem getLocalState_fst_append_st_cases (tr : ExecTrace) (me q : Participant)
    (st st_q : TRState) (i : Nat)
    (h : ((PersistentLocalState.getLocalState q i : Traceful TRState).run
      (tr.append (⟨⟨me, st⟩⟩ : StEntry))).1 = some st_q) :
    ((PersistentLocalState.getLocalState q i : Traceful TRState).run tr).1 = some st_q ∨
      st_q = st := by
  rw [getLocalState_fst] at h
  by_cases hlt : i < tr.length
  · rw [at?_append_of_lt _ _ hlt, ← getLocalState_fst] at h; exact Or.inl h
  · by_cases heq : i = tr.length
    · rw [at?_append_eq_some _ _ heq] at h; dsimp only at h
      by_cases hq : me = q
      · rw [ite_eq_left_iff.mpr fun hc => absurd hq hc] at h
        exact Or.inr (Option.some.inj h).symm
      · rw [ite_eq_right_iff.mpr fun hc => absurd hc hq] at h; cases h
    · have hge : ¬ i < (tr.append (⟨⟨me, st⟩⟩ : StEntry)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [at?_eq_none_of_not_lt _ hge] at h; cases h

theorem getLocalState_fst_encTr_cases (tr : ExecTrace) (me q : Participant)
    (stateIdx coinsLen : Nat) (st st_q : TRState) (i : Nat)
    (h : ((PersistentLocalState.getLocalState q i : Traceful TRState).run
      (encTr tr me stateIdx coinsLen st)).1 = some st_q) :
    ((PersistentLocalState.getLocalState q i : Traceful TRState).run tr).1 = some st_q ∨
      st_q = encSt st coinsLen tr.length := by
  unfold encTr at h; dsimp only at h
  rw [getLocalState_fst_append_non_st _ _ rfl] at h
  rcases getLocalState_fst_append_st_cases _ me q
      (encSt st coinsLen tr.length) st_q i h with h1 | h2
  · rw [getLocalState_fst_append_non_st _ _ rfl, getLocalState_fst_append_non_st _ _ rfl,
        getLocalState_fst_append_non_st _ _ rfl, getLocalState_fst_append_non_st _ _ rfl,
        getLocalState_fst_append_non_st _ _ rfl] at h1
    exact Or.inl h1
  · exact Or.inr h2

theorem isCurrentSnapshot_append_st_self (tr : ExecTrace) (me : Participant) (st : TRState) :
    isCurrentSnapshot (tr.append (⟨⟨me, st⟩⟩ : StEntry)) tr.length = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  rw [at?_append_eq_some _ _ rfl]; dsimp only
  have hlen : (tr.append (⟨⟨me, st⟩⟩ : StEntry)).length - (tr.length + 1) = 0 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  rw [hlen]; rfl

theorem isCurrentSnapshot_append_st_of_ne (tr : ExecTrace) (me q : Participant)
    (st st_q : TRState) (stateIdx : Nat) (hq : q ≠ me)
    (ht : (tr.at? stateIdx : Option StEntry) = some ⟨⟨q, st_q⟩⟩)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    isCurrentSnapshot (tr.append (⟨⟨me, st⟩⟩ : StEntry)) stateIdx = true := by
  have hlt : stateIdx < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stateIdx
    rw [ht] at this; exact this
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?] at hcur ⊢
  rw [at?_append_of_lt _ _ hlt]; rw [ht] at hcur ⊢; dsimp only at hcur ⊢
  have hlen : (tr.append (⟨⟨me, st⟩⟩ : StEntry)).length - (stateIdx + 1) =
      (tr.length - (stateIdx + 1)) + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hsum : (stateIdx + 1) + 1 * (tr.length - (stateIdx + 1)) = tr.length := by omega
  rw [hlen, List.range'_concat, hsum, List.all_append, List.all_cons, List.all_nil,
      at?_append_eq_some _ _ rfl]; dsimp only
  rw [bne_iff_ne.mpr (Ne.symm hq), Bool.true_or, Bool.and_true, Bool.and_true]
  refine Eq.trans (list_all_eq_of_mem fun j hj => ?_) hcur
  have hj_lt : j < tr.length := by rw [List.mem_range'_1] at hj; omega
  rw [at?_append_of_lt _ _ hj_lt]

theorem isCurrentSnapshot_encTr_new (tr : ExecTrace) (me : Participant)
    (stateIdx coinsLen : Nat) (st : TRState) :
    isCurrentSnapshot (encTr tr me stateIdx coinsLen st) (tr.length + 5) = true := by
  unfold encTr; dsimp only
  rw [isCurrentSnapshot_append_non_st _ _ rfl]
  convert isCurrentSnapshot_append_st_self _ me _ using 2
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem isCurrentSnapshot_encTr_of_ne (tr : ExecTrace) (me q : Participant)
    (stateIdx coinsLen : Nat) (st st_q : TRState) (idx : Nat) (hq : q ≠ me)
    (ht : (tr.at? idx : Option StEntry) = some ⟨⟨q, st_q⟩⟩)
    (hcur : isCurrentSnapshot tr idx = true) :
    isCurrentSnapshot (encTr tr me stateIdx coinsLen st) idx = true := by
  have hlt : idx < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr idx
    rw [ht] at this; exact this
  unfold encTr; dsimp only
  rw [isCurrentSnapshot_append_non_st _ _ rfl]
  refine isCurrentSnapshot_append_st_of_ne _ me q _ st_q idx hq ?_ ?_
  · rw [at?_append_of_lt _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_of_lt _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_of_lt _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_of_lt _ _ (by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
            Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_of_lt _ _ hlt, ht]
  · rw [isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl,
        isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl,
        isCurrentSnapshot_append_non_st _ _ rfl]
    exact hcur

/-- `TRNsBound` step for `Move.encrypt` with optional prekey wrapping `wrap`. -/
theorem trNsBound_snoc_encrypt_wrap {r₀ : ProtocolSetup} {ms₁ : List Move} {sent : List HwBytes}
    {p : Participant} {stateIdx coinsLen : Nat} {wrap : Option (Nat × Nat)} {st : TRState}
    (body : HwBytes)
    (hnsBound : TRNsBound r₀ ms₁ sent)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    TRNsBound r₀
      (ms₁ ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms₁).length + 2) wrap])
      (sent ++ [body]) := by
  have htr : runTraceMoves r₀
      (ms₁ ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms₁).length + 2) wrap]) =
      encTr (runTraceMoves r₀ ms₁) p stateIdx coinsLen st := by
    rw [runTrace_snoc, encrypt_wrap_next_of_some (wrap := wrap) hst hns]
  intro q idx st_q hst_q
  rw [htr] at hst_q
  simp only [List.length_append, List.length_singleton]
  rcases getLocalState_fst_encTr_cases _ p q stateIdx coinsLen st st_q idx hst_q with h1 | rfl
  · have hb := hnsBound q idx st_q h1; omega
  · have hb := hnsBound p stateIdx st hst
    have hlt_max : st.ns.toNat < 4294967295 := by
      have hle : st.ns.toNat < 4294967296 := st.ns.toBitVec.isLt
      have hne : st.ns.toNat ≠ 4294967295 := fun heq => hns (UInt32.ext heq)
      omega
    have hadd : (st.ns + 1).toNat = st.ns.toNat + 1 :=
      Nat.mod_eq_of_lt (show st.ns.toNat + 1 < 4294967296 by omega)
    dsimp only [encSt]
    omega

theorem bobDoneBaseKeys_append_non_pq {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none) :
    bobDoneBaseKeys (tr.append e) = bobDoneBaseKeys tr := by
  unfold bobDoneBaseKeys
  have hlen : (tr.append e).length = tr.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen, List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  have hlast : (tr.append e).getEventAt PQXDH.PQXDHEvent tr.length = none := by
    rw [getEventAt_append_non_pq tr e hnone]
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_eq_none_of_not_lt tr (Nat.lt_irrefl _)]
  rw [hlast]; simp only [List.append_nil]
  refine List.filterMap_congr fun i _ => ?_
  rw [getEventAt_append_non_pq tr e hnone]

theorem bobDoneBaseKeys_encTr (tr : ExecTrace) (me : Participant) (stateIdx coinsLen : Nat)
    (st : TRState) :
    bobDoneBaseKeys (encTr tr me stateIdx coinsLen st) = bobDoneBaseKeys tr := by
  unfold encTr; dsimp only
  rw [bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl,
      bobDoneBaseKeys_append_non_pq _ _ rfl]

theorem bobDoneBaseKeys_snoc_encrypt_wrap {r₀ : ProtocolSetup} {ms : List Move}
    {p : Participant} {stateIdx coinsLen : Nat} {wrap : Option (Nat × Nat)} {st : TRState}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hns : st.ns ≠ TripleRatchet.u32Max) :
    bobDoneBaseKeys (runTraceMoves r₀
      (ms ++ [Move.encrypt p stateIdx coinsLen ((runTraceMoves r₀ ms).length + 2) wrap])) =
      bobDoneBaseKeys (runTraceMoves r₀ ms) := by
  rw [runTrace_snoc, encrypt_wrap_next_of_some (wrap := wrap) hst hns, bobDoneBaseKeys_encTr]

end Symbolic.Swarm.CREF.SendWire
