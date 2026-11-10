/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import

/-!
# Active Creation-Order `GapDhWithSign` Slot Maps and Pre-Sampling

Defines creation-order slot-at-ordinal maps and bad-event predicates for one-key `GapDhWithSign`
(`DH1`–`DH4`), and proves list-length monotonicity and pre-sampling distribution equalities.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleSpec OracleComp
open SignalPqxdh (
  Setup Bytes PrincipalEntry PreKeyBundleInput SessionId KeyIndQuery KeyIndResponse KeyIndState
  KeyIndInitiatorEntry KeyIndAdversary keyIndSpec Primitives sampleScalar32 sampleCoins32
  encodeEC encodeKEM resolveSigPk koskBundleOk
)
open SignalPqxdh.Security (opkSlotFlatIdx opkSlotFlatIdx_lt)
open SignalPqxdh.Security.FgGapDh (spkBundleFlatIdx initSessionSlotIdx)
open SignalPqxdh.Security.FgGapDh.Opk (opkFlatIdx)
open Proofs.SignalPqxdh.Security.FgGapDh (
  KeyIndFgCutoffState spkBundleFlatIdxVal
  initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt
  badKeyIndFgDh1At badKeyIndFgDh3At
  StateT_run_mk liftFgBase fgPreInitiate pqxdhKeyIndFgPreImpl
  fgPreInitiateAfterCoins fgPreInitiate_run_eq_afterCoins
  mem_support_liftFgBase mem_support_pqxdhKeyIndFgPreImpl_elim
  evalDist_simulateQ_preSample_slot_eq evalDist_simulateQ_preSample_slot_eq_c0
)
open Proofs.SignalPqxdh.Security.FgGapDh.Ik (badKeyIndFgDh2At)
open Proofs.SignalPqxdh.Security.FgGapDh.Opk (badKeyIndFgDh4At fgPreGenOPK pqxdhKeyIndFgPreImplOpk)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (
  pqxdhKeyIndFgImpl1Key runKeyIndFgSim1Key fgPreInitPrin1Key
  pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl1KeyIk pqxdhKeyIndFgPreImpl1KeyOpk
  pqxdhKeyIndFgPreImpl1Key_none_none_eq
  pqxdhKeyIndFgPreImpl1KeyIk_none_eq pqxdhKeyIndFgPreImpl1KeyOpk_none_eq
)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre

public section
/-! ## Creation-order slot maps and bad-event predicates -/

/-- Principal index created at ordinal `pOrd` (`0`-indexed from the oldest entry in
    `st.principals.reverse`), defaulting to the unreachable sentinel `S.N_id` before creation. -/
@[expose] def prinSlotAtOrd (S : Setup) (st : KeyIndState S) (pOrd : Nat) : Nat :=
  match st.principals.reverse[pOrd]? with
  | some (u, _) => u
  | none => S.N_id

/-- Flat SPK bundle index created at ordinal `spkOrd` in `st.spkBundles.reverse`, defaulting to
    the unreachable sentinel `S.N_spk_tot` before creation. -/
@[expose] def spkSlotAtOrd (S : Setup) (st : KeyIndState S) (spkOrd : Nat) : Nat :=
  match st.spkBundles.reverse[spkOrd]? with
  | some (k, _) => spkBundleFlatIdxVal S k
  | none => S.N_spk_tot

/-- Flat OPK slot index created at ordinal `opkOrd` in `st.opkEntries.reverse`, defaulting to
    the unreachable sentinel `S.N_opk_tot` before creation. -/
@[expose] def opkSlotAtOrd (S : Setup) (st : KeyIndState S) (opkOrd : Nat) : Nat :=
  match st.opkEntries.reverse[opkOrd]? with
  | some (k, _) => opkSlotFlatIdx S k
  | none => S.N_opk_tot

/-- Flat initiator session slot index created at ordinal `sOrd` in `st.sessions.reverse`,
    defaulting to the unreachable sentinel `S.N_send_tot` before creation. -/
@[expose] def sessSlotAtOrd (S : Setup) (st : KeyIndState S) (sOrd : Nat) : Nat :=
  match st.sessions.reverse[sOrd]? with
  | some s => initSessionSlotIdx s.sid
  | none => S.N_send_tot

@[expose] def isOpkInitSession {S : Setup} (s : KeyIndInitiatorEntry S) : Bool :=
  match s.sid with
  | .sendOPK _ _ => true
  | _ => false

@[expose] def opkSessions {S : Setup} (st : KeyIndState S) : List (KeyIndInitiatorEntry S) :=
  st.sessions.filter isOpkInitSession

/-- Flat initiator session slot index of the `sOpkOrd`-th created OPK-carrying initiator session,
    defaulting to the unreachable sentinel `S.N_send_tot` before creation. -/
@[expose] def sessOpkSlotAtOrd (S : Setup) (st : KeyIndState S) (sOpkOrd : Nat) : Nat :=
  match (opkSessions st).reverse[sOpkOrd]? with
  | some s => initSessionSlotIdx s.sid
  | none => S.N_send_tot

@[expose] def badKeyIndFgDh1OrdAt {S : Setup} (P : Primitives) (maxLen pOrd spkOrd : Nat)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  badKeyIndFgDh1At P maxLen (prinSlotAtOrd S st pOrd) (spkSlotAtOrd S st spkOrd) st advRoLog

@[expose] def badKeyIndFgDh3OrdAt {S : Setup} (P : Primitives) (maxLen sOrd spkOrd : Nat)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  badKeyIndFgDh3At P maxLen (sessSlotAtOrd S st sOrd) (spkSlotAtOrd S st spkOrd) st advRoLog

@[expose] def badKeyIndFgDh2OrdAt {S : Setup} (P : Primitives) (maxLen sOrd pOrd : Nat)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  badKeyIndFgDh2At P maxLen (sessSlotAtOrd S st sOrd) (prinSlotAtOrd S st pOrd) st advRoLog

@[expose] def badKeyIndFgDh4OrdAt {S : Setup} (P : Primitives) (maxLen sOpkOrd opkOrd : Nat)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  badKeyIndFgDh4At P maxLen (sessOpkSlotAtOrd S st sOpkOrd) (opkSlotAtOrd S st opkOrd) st advRoLog

/-! ## `ordLookup` helpers and pre-sampling -/

@[expose] def ordLookup {α β : Type} (proj : α → β) (dflt : β) (xs : List α) (ord : Nat) : β :=
  match xs.reverse[ord]? with
  | some a => proj a
  | none   => dflt

theorem prinSlotAtOrd_eq (S : Setup) (st : KeyIndState S) (pOrd : Nat) :
    prinSlotAtOrd S st pOrd = ordLookup Prod.fst S.N_id st.principals pOrd := by
  unfold prinSlotAtOrd ordLookup; cases st.principals.reverse[pOrd]? <;> rfl

theorem spkSlotAtOrd_eq (S : Setup) (st : KeyIndState S) (spkOrd : Nat) :
    spkSlotAtOrd S st spkOrd =
      ordLookup (fun kv => spkBundleFlatIdxVal S kv.1) S.N_spk_tot st.spkBundles spkOrd := by
  unfold spkSlotAtOrd ordLookup; cases st.spkBundles.reverse[spkOrd]? <;> rfl

theorem opkSlotAtOrd_eq (S : Setup) (st : KeyIndState S) (opkOrd : Nat) :
    opkSlotAtOrd S st opkOrd =
      ordLookup (fun kv => opkSlotFlatIdx S kv.1) S.N_opk_tot st.opkEntries opkOrd := by
  unfold opkSlotAtOrd ordLookup; cases st.opkEntries.reverse[opkOrd]? <;> rfl

theorem sessSlotAtOrd_eq (S : Setup) (st : KeyIndState S) (sOrd : Nat) :
    sessSlotAtOrd S st sOrd =
      ordLookup (fun s => initSessionSlotIdx s.sid) S.N_send_tot st.sessions sOrd := by
  unfold sessSlotAtOrd ordLookup; cases st.sessions.reverse[sOrd]? <;> rfl

theorem sessOpkSlotAtOrd_eq (S : Setup) (st : KeyIndState S) (sOpkOrd : Nat) :
    sessOpkSlotAtOrd S st sOpkOrd =
      ordLookup (fun s => initSessionSlotIdx s.sid) S.N_send_tot (opkSessions st) sOpkOrd := by
  unfold sessOpkSlotAtOrd ordLookup; cases (opkSessions st).reverse[sOpkOrd]? <;> rfl

theorem ordLookup_of_ge {α β : Type} {proj : α → β} {dflt : β} {xs : List α} {ord : Nat}
    (h : xs.length ≤ ord) : ordLookup proj dflt xs ord = dflt := by
  unfold ordLookup; rw [List.getElem?_eq_none (by simpa using h)]

theorem ordLookup_cons_eq {α β : Type} (proj : α → β) (dflt : β) (x : α) (xs : List α) :
    ordLookup proj dflt (x :: xs) xs.length = proj x := by
  unfold ordLookup; rw [List.reverse_cons, List.getElem?_append_right (by simp)]; simp

theorem ordLookup_cons_of_lt {α β : Type} (proj : α → β) (dflt : β) (x : α) {xs : List α}
    {ord : Nat} (h : ord < xs.length) :
    ordLookup proj dflt (x :: xs) ord = ordLookup proj dflt xs ord := by
  unfold ordLookup; rw [List.reverse_cons, List.getElem?_append_left (by simpa using h)]

theorem ordLookup_mem_of_lt {α β : Type} {proj : α → β} {dflt : β} {xs : List α} {ord : Nat}
    (h : ord < xs.length) : ∃ a ∈ xs, ordLookup proj dflt xs ord = proj a := by
  have hRev : ord < xs.reverse.length := by simpa using h
  refine ⟨xs.reverse[ord], List.mem_reverse.mp (List.getElem_mem hRev), ?_⟩
  unfold ordLookup; rw [List.getElem?_eq_getElem hRev]

theorem ordLookup_exists_of_mem {α β : Type} {proj : α → β} {dflt : β} {xs : List α} {a : α}
    (ha : a ∈ xs) : ∃ ord < xs.length, ordLookup proj dflt xs ord = proj a := by
  have haRev : a ∈ xs.reverse := List.mem_reverse.mpr ha
  obtain ⟨ord, hOrdLt, hGet⟩ := List.mem_iff_getElem.mp haRev
  refine ⟨ord, by simpa using hOrdLt, ?_⟩
  unfold ordLookup; rw [List.getElem?_eq_getElem hOrdLt, hGet]

theorem ordLookup_map_eq {α β : Type} {proj : α → β} {dflt : β} {f : α → α}
    (hf : ∀ a, proj (f a) = proj a) (xs : List α) (ord : Nat) :
    ordLookup proj dflt (xs.map f) ord = ordLookup proj dflt xs ord := by
  unfold ordLookup; rw [← List.map_reverse, List.getElem?_map]
  cases xs.reverse[ord]? with
  | none => rfl
  | some a => exact hf a

theorem opkSessions_cons {S : Setup} {st1 st2 : KeyIndState S} (s : KeyIndInitiatorEntry S)
    (h : st2.sessions = s :: st1.sessions) :
    opkSessions st2 = if isOpkInitSession s then s :: opkSessions st1 else opkSessions st1 := by
  unfold opkSessions; rw [h, List.filter_cons]

theorem opkSessions_of_sessions_map {S : Setup} {st1 st2 : KeyIndState S}
    {f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S}
    (hSid : ∀ s, (f s).sid = s.sid) (hMap : st2.sessions = st1.sessions.map f) :
    opkSessions st2 = (opkSessions st1).map f := by
  unfold opkSessions; rw [hMap, List.filter_map]
  have hPred : (isOpkInitSession ∘ f) = isOpkInitSession := by
    funext s; unfold Function.comp isOpkInitSession; rw [hSid s]
  rw [hPred]

@[expose] def curPrinSlot {S : Setup} (pOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .initPrin u => if hst.base.principals.length == pOrd then u.val else S.N_id
  | _ => S.N_id

@[expose] def curSpkSlot {S : Setup} (spkOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .genSPK u j =>
    if hst.base.spkBundles.length == spkOrd then spkBundleFlatIdx S u j else S.N_spk_tot
  | _ => S.N_spk_tot

@[expose] def curOpkSlot {S : Setup} (opkOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .genOPK u j o =>
    if hst.base.opkEntries.length == opkOrd then opkFlatIdx S u j o else S.N_opk_tot
  | _ => S.N_opk_tot

@[expose] def curSessSlot {S : Setup} (sOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .initiateOPK u i _ =>
    if hst.base.sessions.length == sOrd then initSessionSlotIdx (.sendOPK u i) else S.N_send_tot
  | .initiateNoOPK u i _ =>
    if hst.base.sessions.length == sOrd then initSessionSlotIdx (.sendNoOPK u i) else S.N_send_tot
  | _ => S.N_send_tot

@[expose] def curSessOpkSlot {S : Setup} (sOpkOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .initiateOPK u i _ =>
    if (opkSessions hst.base).length == sOpkOrd then initSessionSlotIdx (.sendOPK u i) else S.N_send_tot
  | _ => S.N_send_tot

@[expose] noncomputable def pqxdhKeyIndFgPreImpl1KeyOrd (useDh1 : Bool) (uOrd spkOrd : Nat)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp) :=
  fun q => StateT.mk fun hst =>
    let uSlot := if useDh1 then curPrinSlot uOrd q hst else curSessSlot uOrd q hst
    (pqxdhKeyIndFgPreImpl1Key useDh1 uSlot (curSpkSlot spkOrd q hst) optUsk optVsk S P q).run hst

@[expose] noncomputable def pqxdhKeyIndFgPreImpl1KeyOrdIk (sOrd pOrd : Nat)
    (optIkSk optEkSk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp) :=
  fun q => StateT.mk fun hst =>
    (pqxdhKeyIndFgPreImpl1KeyIk (curSessSlot sOrd q hst) (curPrinSlot pOrd q hst)
      optIkSk optEkSk S P q).run hst

@[expose] noncomputable def pqxdhKeyIndFgPreImpl1KeyOrdOpk (sOpkOrd opkOrd : Nat)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp) :=
  fun q => StateT.mk fun hst =>
    (pqxdhKeyIndFgPreImpl1KeyOpk (curSessOpkSlot sOpkOrd q hst) (curOpkSlot opkOrd q hst)
      optUsk optVsk S P q).run hst

theorem pqxdhKeyIndFgPreImpl1KeyOrd_none_none_eq {S : Setup} (useDh1 : Bool)
    (uOrd spkOrd : Nat) (P : Primitives) :
    pqxdhKeyIndFgPreImpl1KeyOrd useDh1 uOrd spkOrd none none S P = pqxdhKeyIndFgImpl1Key S P := by
  funext q; apply StateT.ext; intro hst
  simpa [pqxdhKeyIndFgPreImpl1KeyOrd] using
    congrArg (fun impl => (impl q).run hst)
      (pqxdhKeyIndFgPreImpl1Key_none_none_eq (S := S) useDh1 _ _ P)

theorem pqxdhKeyIndFgPreImpl1Key_spkSlot_irrel_of_none {S : Setup} (useDh1 : Bool)
    (uSlot spkSlot1 spkSlot2 : Nat) (optUsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) :
    pqxdhKeyIndFgPreImpl1Key useDh1 uSlot spkSlot1 optUsk none S P q =
      pqxdhKeyIndFgPreImpl1Key useDh1 uSlot spkSlot2 optUsk none S P q := by
  cases q <;> rfl

theorem pqxdhKeyIndFgPreImpl1KeyOrdIk_none_eq {S : Setup} (sOrd pOrd spkOrd : Nat)
    (optEkSk : Option Bytes) (P : Primitives) :
    pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd none optEkSk S P =
      pqxdhKeyIndFgPreImpl1KeyOrd false sOrd spkOrd optEkSk none S P := by
  funext q; apply StateT.ext; intro hst
  simp only [pqxdhKeyIndFgPreImpl1KeyOrdIk, pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk,
    Bool.false_eq_true, ↓reduceIte]
  rw [congrArg (fun impl => (impl q).run hst)
      (pqxdhKeyIndFgPreImpl1KeyIk_none_eq (curSessSlot sOrd q hst) (curPrinSlot pOrd q hst)
        optEkSk P),
    pqxdhKeyIndFgPreImpl1Key_spkSlot_irrel_of_none false _ _ (curSpkSlot spkOrd q hst) optEkSk P q]

theorem fgPre1Key_lengths_mono {S : Setup} (useDh1 : Bool) (uSlot spkSlot : Nat)
    (optUsk optVsk : Option Bytes) (P : Primitives) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl1Key useDh1 uSlot spkSlot optUsk optVsk S P q).run hst)) :
    hst.base.principals.length ≤ x.2.base.principals.length ∧
    hst.base.spkBundles.length ≤ x.2.base.spkBundles.length ∧
    x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 ∧
    hst.base.opkEntries.length ≤ x.2.base.opkEntries.length ∧
    hst.base.sessions.length ≤ x.2.base.sessions.length ∧
    (opkSessions hst.base).length ≤ (opkSessions x.2.base).length := by
  have hUnch : x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.opkEntries = hst.base.opkEntries →
      x.2.base.sessions = hst.base.sessions →
      hst.base.principals.length ≤ x.2.base.principals.length ∧
      hst.base.spkBundles.length ≤ x.2.base.spkBundles.length ∧
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 ∧
      hst.base.opkEntries.length ≤ x.2.base.opkEntries.length ∧
      hst.base.sessions.length ≤ x.2.base.sessions.length ∧
      (opkSessions hst.base).length ≤ (opkSessions x.2.base).length := by
    intro hP hSp hO hSe
    have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hSe]
    rw [hP, hSp, hO, hSe, hOpkS]; omega
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hB]
      rw [hOpkS, hB]; simp
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  | _ =>
    exact mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 uSlot spkSlot optUsk optVsk P _ hst x hx
      hUnch (fun _ _ hEq _ _ => by cases hEq)
      (fun _ _ _ _ _ hB => by
        have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hB]
        rw [hOpkS, hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by
        have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hB]
        rw [hOpkS, hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by
        have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hB]
        rw [hOpkS, hB]; simp)
      (fun s _ _ hB => by
        have hOpkS := opkSessions_cons (st1 := hst.base) (st2 := x.2.base) s (by rw [hB])
        rw [hOpkS, hB]; cases isOpkInitSession s <;> simp)
      (fun _ _ _ hP hSp hSe hO => by
        have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hSe]
        rw [hP, hSp, hO, hSe, hOpkS]; simp)
      (fun f hSid _ _ _ hP hSp hO hSe => by
        have hOpkS := opkSessions_of_sessions_map (st1 := hst.base) (st2 := x.2.base) hSid hSe
        rw [hP, hSp, hO, hSe, hOpkS]; simp)
      (fun _ _ hB => by
        have hOpkS : opkSessions x.2.base = opkSessions hst.base := by unfold opkSessions; rw [hB]
        rw [hOpkS, hB]; simp)

private theorem fgPreInitPrin1Key_ord_after {S : Setup} (pOrd : Nat) (P : Primitives)
    (u : Fin S.N_id) (s : KeyIndFgCutoffState S) (hFired : pOrd < s.base.principals.length)
    (uSk : Bytes) :
    (liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) (some uSk) S P u)).run s =
      (liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) none S P u)).run s := by
  have hNe : (s.base.principals.length == pOrd) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
  have hSlot : (u.val == S.N_id) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)
  unfold curPrinSlot fgPreInitPrin1Key liftFgBase
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hNe,
    Bool.false_eq_true, ↓reduceIte, Bool.true_and]
  cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]

private theorem fgPreInitPrin1Key_ord_before {S : Setup} (pOrd : Nat) (P : Primitives)
    (u : Fin S.N_id) (s : KeyIndFgCutoffState S) :
    (∀ uSk,
      (liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) (some uSk) S P u)).run s =
      (liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) none S P u)).run s) ∨
    ((∀ obs : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool,
        𝒟[sampleScalar32 >>= fun uSk =>
          (liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) (some uSk) S P u)).run s
            >>= obs] =
        𝒟[(liftFgBase (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) none S P u)).run s
            >>= obs]) ∧
     (∀ uSk x,
        x ∈ support ((liftFgBase
          (fgPreInitPrin1Key true (curPrinSlot pOrd (.initPrin u) s) (some uSk) S P u)).run s) →
        pOrd < x.2.base.principals.length)) := by
  by_cases hLen : (s.base.principals.length == pOrd) = true
  · unfold curPrinSlot fgPreInitPrin1Key liftFgBase
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hLen, ↓reduceIte,
      Bool.true_and, beq_self_eq_true]
    cases s.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨fun obs' => ?_, fun uSk x hx => ?_⟩
      · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
          monadLift_self, StateT.run_set, pure_bind, bind_assoc]
      · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
          monadLift_self, StateT.run_set, pure_bind, support_pure,
          Set.mem_singleton_iff] at hx
        have hB := (Prod.mk.inj hx).2
        rw [hB]; simp [beq_iff_eq.mp hLen]
    · exact Or.inl (fun _ => rfl)
  · refine Or.inl (fun uSk => ?_)
    have hSlot : (u.val == S.N_id) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)
    unfold curPrinSlot fgPreInitPrin1Key liftFgBase
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hLen,
      Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]

theorem evalDist_preSample_prinOrd_dh1_1Key {S : Setup} {α : Type}
    (pOrd spkOrd : Nat) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrd true pOrd spkOrd (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrd true pOrd spkOrd none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32 (fun s => pOrd < s.base.principals.length)
    (pqxdhKeyIndFgPreImpl1KeyOrd true pOrd spkOrd none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl1KeyOrd true pOrd spkOrd (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx => ?_⟩) (fun q s _ => ?_) oa hst obs
  · intro uSk; cases q with
    | initPrin u => exact fgPreInitPrin1Key_ord_after pOrd P u s hFired uSk
    | _ => rfl
  · dsimp only [pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk] at hx
    exact Nat.lt_of_lt_of_le hFired (fgPre1Key_lengths_mono true _ _ none optVsk P q s x hx).1
  · cases q with
    | initPrin u => exact fgPreInitPrin1Key_ord_before pOrd P u s
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_prinOrd_ik_1Key {S : Setup} {α : Type}
    (sOrd pOrd : Nat) (optEkSk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (ikSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) optEkSk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd none optEkSk S P
    𝒟[sampleScalar32 >>= fun ikSk => (simulateQ (fullPre ikSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32 (fun s => pOrd < s.base.principals.length)
    (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd none optEkSk S P)
    (fun ikSk => pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) optEkSk S P)
    (fun q s hFired => ⟨?_, fun x hx => ?_⟩) (fun q s _ => ?_) oa hst obs
  · intro ikSk; cases q with
    | initPrin u => exact fgPreInitPrin1Key_ord_after pOrd P u s hFired ikSk
    | _ => rfl
  · rw [congrArg (fun impl => (impl q).run s)
      (pqxdhKeyIndFgPreImpl1KeyOrdIk_none_eq sOrd pOrd 0 optEkSk P)] at hx
    dsimp only [pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk] at hx
    exact Nat.lt_of_lt_of_le hFired (fgPre1Key_lengths_mono false _ _ optEkSk none P q s x hx).1
  · cases q with
    | initPrin u => exact fgPreInitPrin1Key_ord_before pOrd P u s
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_opkOrd_1Key {S : Setup} {α : Type}
    (sOpkOrd opkOrd : Nat) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32 (fun s => opkOrd < s.base.opkEntries.length)
    (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx => ?_⟩) (fun q s _ => ?_) oa hst obs
  · intro vSk; cases q with
    | genOPK u j o =>
      have hNe : (s.base.opkEntries.length == opkOrd) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
      have hSlot : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
      unfold pqxdhKeyIndFgPreImpl1KeyOrdOpk curOpkSlot pqxdhKeyIndFgPreImpl1KeyOpk
        pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hNe,
        Bool.false_eq_true, ↓reduceIte]
      cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) <;> simp [hSlot]
    | _ => rfl
  · dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk] at hx
    rw [congrArg (fun impl => (impl q).run s)
      (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ optUsk P)] at hx
    exact Nat.lt_of_lt_of_le hFired
      (fgPre1Key_lengths_mono false _ _ optUsk none P q s x hx).2.2.2.1
  · cases q with
    | genOPK u j o =>
      by_cases hLen : (s.base.opkEntries.length == opkOrd) = true
      · unfold pqxdhKeyIndFgPreImpl1KeyOrdOpk curOpkSlot pqxdhKeyIndFgPreImpl1KeyOpk
          pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hLen, ↓reduceIte,
          beq_self_eq_true]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
          · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, support_pure,
              Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            rw [hB]; simp [beq_iff_eq.mp hLen]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        have hSlot : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
        unfold pqxdhKeyIndFgPreImpl1KeyOrdOpk curOpkSlot pqxdhKeyIndFgPreImpl1KeyOpk
          pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hLen,
          Bool.false_eq_true, ↓reduceIte]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

private theorem fgPreInitiate_ord_before_c0 {S : Setup} (q : KeyIndQuery S) (tIdx : Nat)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S)
    (hasFired : KeyIndFgCutoffState S → Prop)
    (hFireCons : (initSessionSlotIdx sid == tIdx) = true →
      ∀ (entry : KeyIndInitiatorEntry S) (roCache' : List (Bytes × SignalPqxdh.DRKey)),
        entry.sid = sid →
        hasFired { hst with base := { hst.base with
          roCache := roCache', sessions := entry :: hst.base.sessions } }) :
    (∀ uSk, (liftFgBase (fgPreInitiate false tIdx (some uSk) S P sid u bundle)).run hst =
      (liftFgBase (fgPreInitiate false tIdx none S P sid u bundle)).run hst) ∨
    ∃ (fPre : Bytes → Bytes → ProbComp ((keyIndSpec S).Range q × KeyIndFgCutoffState S)),
      (∀ uSk, (liftFgBase (fgPreInitiate false tIdx (some uSk) S P sid u bundle)).run hst =
        (sampleCoins32 >>= fPre uSk)) ∧
      (∀ obs : (keyIndSpec S).Range q × KeyIndFgCutoffState S → ProbComp Bool,
        𝒟[(liftFgBase (fgPreInitiate false tIdx none S P sid u bundle)).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun kemCoins => sampleScalar32 >>= fun uSk => fPre uSk kemCoins >>=
          obs]) ∧
      (∀ kemCoins,
        (∃ x0, ∀ uSk, fPre uSk kemCoins = pure x0) ∨
        (∀ uSk, ∀ x ∈ support (fPre uSk kemCoins), hasFired x.2)) := by
  by_cases hSlot : (initSessionSlotIdx sid == tIdx) = true
  · cases hSid : hst.base.sessions.any (fun e => e.sid == sid)
    · cases hP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        refine Or.inl (fun _ => ?_); unfold liftFgBase fgPreInitiate
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, hP,
          Bool.false_eq_true, ↓reduceIte]
      | some p =>
        rcases p with ⟨idx0, uEntry⟩
        by_cases hKosk : koskBundleOk P hst.base.principals hst.base.spkBundles
          hst.base.opkEntries hst.base.advKeys bundle = true
        · refine Or.inr ⟨fgPreInitiateAfterCoins P sid uEntry bundle hst,
            fun uSk => ?_, fun obs => ?_, fun kemCoins => ?_⟩
          · rw [fgPreInitiate_run_eq_afterCoins tIdx (some uSk) P sid u bundle hst hSid uEntry
              (Or.inr ⟨idx0, hP⟩) hKosk]
            simp [hSlot]
          · rw [fgPreInitiate_run_eq_afterCoins tIdx none P sid u bundle hst hSid uEntry
              (Or.inr ⟨idx0, hP⟩) hKosk]
            simp only [bind_assoc]
            exact evalDist_bind_bind_swap sampleScalar32 sampleCoins32 _
          · unfold fgPreInitiateAfterCoins; dsimp only
            by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                  (encodeEC bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · exact Or.inl ⟨(.noneResp, hst), fun _ => by simp [hSig]⟩
            · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => exact Or.inl ⟨(.noneResp, hst), fun _ => rfl⟩
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩; dsimp only
                refine Or.inr (fun uSk x hx => ?_)
                simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
                rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, drKeyRand, _, hEq⟩
                rcases x with ⟨rx, hx2⟩
                obtain ⟨_, rfl⟩ := Prod.mk.inj hEq
                exact hFireCons hSlot _ roCache' rfl
        · have hKoskF := Bool.eq_false_iff.mpr hKosk
          refine Or.inl (fun _ => ?_); unfold liftFgBase fgPreInitiate
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, hP, hKoskF,
            Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · refine Or.inl (fun _ => ?_); unfold liftFgBase fgPreInitiate
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, ↓reduceIte]
  · refine Or.inl (fun _ => ?_)
    have hSlotF : (!false && (initSessionSlotIdx sid == tIdx)) = false := by simp [hSlot]
    unfold fgPreInitiate; simp only [hSlotF, Bool.false_eq_true, ↓reduceIte]

theorem evalDist_preSample_sessOrd_1Key {S : Setup} {α : Type}
    (sOrd spkOrd : Nat) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrd false sOrd spkOrd (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrd false sOrd spkOrd none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32 sampleCoins32 (fun s => sOrd < s.base.sessions.length)
    (pqxdhKeyIndFgPreImpl1KeyOrd false sOrd spkOrd none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl1KeyOrd false sOrd spkOrd (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx => ?_⟩) (fun q s _ => ?_) oa hst obs
  · intro uSk
    have hNe : (s.base.sessions.length == sOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
    cases q with
    | initPrin u =>
      simp [pqxdhKeyIndFgPreImpl1KeyOrd, pqxdhKeyIndFgPreImpl1Key,
        Proofs.SignalPqxdh.Security.FgGapDh1Key.fgPreInitPrin1Key_false_eq]
    | initiateOPK u i bundle =>
      have hSlot : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)))
      unfold pqxdhKeyIndFgPreImpl1KeyOrd curSessSlot pqxdhKeyIndFgPreImpl1Key
        pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_eq_true,
        ↓reduceIte, hNe]
      cases bundle.opkB?.isNone <;> simp [hSlot]
    | initiateNoOPK u i bundle =>
      have hSlot : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
      unfold pqxdhKeyIndFgPreImpl1KeyOrd curSessSlot pqxdhKeyIndFgPreImpl1Key
        pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.false_eq_true,
        ↓reduceIte, hNe]
      cases bundle.opkB?.isSome <;> simp [hSlot]
    | _ => rfl
  · dsimp only [pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk] at hx
    exact Nat.lt_of_lt_of_le hFired
      (fgPre1Key_lengths_mono false _ _ none optVsk P q s x hx).2.2.2.2.1
  · cases q with
    | initPrin u =>
      exact Or.inl (fun _ => by simp [pqxdhKeyIndFgPreImpl1KeyOrd, pqxdhKeyIndFgPreImpl1Key,
        Proofs.SignalPqxdh.Security.FgGapDh1Key.fgPreInitPrin1Key_false_eq])
    | initiateOPK u i bundle =>
      simp only [pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk, Bool.false_eq_true, ↓reduceIte,
        pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgPreImpl]
      by_cases hOpt : bundle.opkB?.isNone = true
      · exact Or.inl (fun _ => by unfold liftFgBase; simp [hOpt])
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isNone then return .noneResp
            fgPreInitiate false (curSessSlot sOrd (.initiateOPK u i bundle) s) optU S P
              (.sendOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false (curSessSlot sOrd (.initiateOPK u i bundle) s) optU S P
              (.sendOPK u i) u bundle)).run s := fun _ => by
          unfold liftFgBase
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.eq_false_iff.mpr hOpt, Bool.false_eq_true, ↓reduceIte]
        simp_rw [hEqPre]
        refine fgPreInitiate_ord_before_c0 (.initiateOPK u i bundle) _ P (.sendOPK u i) u bundle s
          (fun h => sOrd < h.base.sessions.length) (fun hSlot _ _ _ => ?_)
        have hLen : (s.base.sessions.length == sOrd) = true := by
          by_contra hF
          have hF' : (s.base.sessions.length == sOrd) = false := Bool.eq_false_iff.mpr hF
          unfold curSessSlot at hSlot
          simp only [hF', Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hSlot
          exact absurd hSlot (Nat.ne_of_lt
            (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)))
        have hLenEq := beq_iff_eq.mp hLen
        dsimp only [List.length_cons]; omega
    | initiateNoOPK u i bundle =>
      simp only [pqxdhKeyIndFgPreImpl1KeyOrd, StateT_run_mk, Bool.false_eq_true, ↓reduceIte,
        pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgPreImpl]
      by_cases hOpt : bundle.opkB?.isSome = true
      · exact Or.inl (fun _ => by unfold liftFgBase; simp [hOpt])
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isSome then return .noneResp
            fgPreInitiate false (curSessSlot sOrd (.initiateNoOPK u i bundle) s) optU S P
              (.sendNoOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false (curSessSlot sOrd (.initiateNoOPK u i bundle) s) optU S P
              (.sendNoOPK u i) u bundle)).run s := fun _ => by
          unfold liftFgBase
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.eq_false_iff.mpr hOpt, Bool.false_eq_true, ↓reduceIte]
        simp_rw [hEqPre]
        refine fgPreInitiate_ord_before_c0 (.initiateNoOPK u i bundle) _ P (.sendNoOPK u i) u bundle
          s (fun h => sOrd < h.base.sessions.length) (fun hSlot _ _ _ => ?_)
        have hLen : (s.base.sessions.length == sOrd) = true := by
          by_contra hF
          have hF' : (s.base.sessions.length == sOrd) = false := Bool.eq_false_iff.mpr hF
          unfold curSessSlot at hSlot
          simp only [hF', Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hSlot
          exact absurd hSlot (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
        have hLenEq := beq_iff_eq.mp hLen
        dsimp only [List.length_cons]; omega
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_sessOpkOrd_1Key {S : Setup} {α : Type}
    (sOpkOrd opkOrd : Nat) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) none S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd none none S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32 sampleCoins32 (fun s => sOpkOrd < (opkSessions s.base).length)
    (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd none none S P)
    (fun uSk => pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) none S P)
    (fun q s hFired => ⟨?_, fun x hx => ?_⟩) (fun q s _ => ?_) oa hst obs
  · intro uSk
    dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk]
    rw [congrArg (fun impl => (impl q).run s) (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ (some uSk) P),
      congrArg (fun impl => (impl q).run s) (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ none P)]
    have hNe : ((opkSessions s.base).length == sOpkOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
    cases q with
    | initPrin u =>
      simp [pqxdhKeyIndFgPreImpl1Key,
        Proofs.SignalPqxdh.Security.FgGapDh1Key.fgPreInitPrin1Key_false_eq]
    | initiateOPK u i bundle =>
      have hSlot : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt
          (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)))
      unfold curSessOpkSlot pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hNe,
        Bool.false_eq_true, ↓reduceIte]
      cases bundle.opkB?.isNone <;> simp [hSlot]
    | initiateNoOPK u i bundle =>
      have hSlot : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
      unfold curSessOpkSlot pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome <;> simp [hSlot]
    | _ => rfl
  · dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk] at hx
    rw [congrArg (fun impl => (impl q).run s) (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ none P)] at hx
    exact Nat.lt_of_lt_of_le hFired
      (fgPre1Key_lengths_mono false _ _ none none P q s x hx).2.2.2.2.2
  · have hEqOpk : ∀ optU, (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd optU none S P q).run s =
        (pqxdhKeyIndFgPreImpl1Key false (curSessOpkSlot sOpkOrd q s)
          (SignalPqxdh.Security.FgGapDh.Opk.noSpkIdx S) optU none S P q).run s := fun optU => by
      dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk]
      exact congrArg (fun impl => (impl q).run s)
        (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ optU P)
    simp_rw [hEqOpk]
    cases q with
    | initPrin u =>
      exact Or.inl (fun _ => by simp [pqxdhKeyIndFgPreImpl1Key,
        Proofs.SignalPqxdh.Security.FgGapDh1Key.fgPreInitPrin1Key_false_eq])
    | initiateOPK u i bundle =>
      dsimp only [pqxdhKeyIndFgPreImpl1Key, pqxdhKeyIndFgPreImpl]
      by_cases hOpt : bundle.opkB?.isNone = true
      · exact Or.inl (fun _ => by unfold liftFgBase; simp [hOpt])
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isNone then return .noneResp
            fgPreInitiate false (curSessOpkSlot sOpkOrd (.initiateOPK u i bundle) s) optU S P
              (.sendOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false (curSessOpkSlot sOpkOrd (.initiateOPK u i bundle) s)
              optU S P (.sendOPK u i) u bundle)).run s := fun _ => by
          unfold liftFgBase
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.eq_false_iff.mpr hOpt, Bool.false_eq_true, ↓reduceIte]
        simp_rw [hEqPre]
        refine fgPreInitiate_ord_before_c0 (.initiateOPK u i bundle) _ P (.sendOPK u i) u bundle s
          (fun h => sOpkOrd < (opkSessions h.base).length) (fun hSlot entry _ hSidEq => ?_)
        have hLen : ((opkSessions s.base).length == sOpkOrd) = true := by
          by_contra hF
          have hF' : ((opkSessions s.base).length == sOpkOrd) = false := Bool.eq_false_iff.mpr hF
          unfold curSessOpkSlot at hSlot
          simp only [hF', Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hSlot
          exact absurd hSlot (Nat.ne_of_lt
            (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)))
        have hLenEq := beq_iff_eq.mp hLen
        have hIsOpk : isOpkInitSession entry = true := by unfold isOpkInitSession; rw [hSidEq]
        dsimp only
        rw [opkSessions_cons (st1 := s.base) entry rfl]
        simp only [hIsOpk, ↓reduceIte, List.length_cons]
        omega
    | initiateNoOPK u i bundle =>
      refine Or.inl (fun _ => ?_)
      have hSlot : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
      unfold curSessOpkSlot pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh2 {S : Setup}
    (sOrd pOrd : Nat) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (ikSk ekSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P
    𝒟[do
        let ikSk ← sampleScalar32
        let ekSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let (b', finalHst) ← (simulateQ (fullPre ikSk ekSk) A.run).run (KeyIndFgCutoffState.empty S secb)
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [evalDist_bind_bind_swap sampleScalar32 sampleScalar32 _]
  rw [evalDist_bind_congr_of_support sampleScalar32 _ _ (fun ekSk _ =>
    evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hIk : ∀ ekSk,
      𝒟[sampleScalar32 >>= fun ikSk =>
        (simulateQ (fullPre ikSk ekSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl1KeyOrd false sOrd 0 (some ekSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] := fun ekSk => by
    rw [← pqxdhKeyIndFgPreImpl1KeyOrdIk_none_eq sOrd pOrd 0 (some ekSk) P]
    exact evalDist_preSample_prinOrd_ik_1Key sOrd pOrd (some ekSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [evalDist_bind_congr_of_support sampleScalar32 _ _ (fun ekSk _ => hIk ekSk)]
  rw [evalDist_preSample_sessOrd_1Key sOrd 0 none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl1KeyOrd_none_none_eq]
  simp only [pure_bind]

theorem evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh4 {S : Setup}
    (sOpkOrd opkOrd : Nat) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb)
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  rw [evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    evalDist_preSample_opkOrd_1Key sOpkOrd opkOrd (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2)))]
  rw [evalDist_preSample_sessOpkOrd_1Key sOpkOrd opkOrd P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  have hNone : pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd none none S P =
      pqxdhKeyIndFgImpl1Key S P := by
    funext q; apply StateT.ext; intro hst
    dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk]
    rw [congrArg (fun impl => (impl q).run hst) (pqxdhKeyIndFgPreImpl1KeyOpk_none_eq _ _ none P),
      congrArg (fun impl => (impl q).run hst) (pqxdhKeyIndFgPreImpl1Key_none_none_eq false _ _ P)]
  rw [hNone]
  simp only [pure_bind]

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre
