/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkPre
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpk
import VCVio.EvalDist.Monad.Basic

/-!
# Case D (`DH4`) State Erasure, Invariant, and Terminal Win

Defines the Case D simulator projection `eraseStateFgOpk`, the per-index bad event
`badKeyIndFgDh4At` with its sticky death predicate `deadDh4`, and the coupling invariant
`FgSimInvDh4`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Opk

open Proofs.SignalPqxdh.Security.FgGapDh

def eraseOpkEntryFg (S : Setup) (oIdx : ℕ) (k : ℕ × ℕ × ℕ) (e : OpkEntry) : OpkEntry :=
  if opkSlotFlatIdx S k == oIdx then { e with opkSk := [] } else e

def eraseOpkEntriesFg (S : Setup) (oIdx : ℕ)
    (opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)) : List ((ℕ × ℕ × ℕ) × OpkEntry) :=
  opkEntries.map (fun (k, e) => (k, eraseOpkEntryFg S oIdx k e))

/-- Simulator view of a `KeyInd` state in Case D. -/
def eraseStateFgOpk {S : Setup} (sIdx oIdx : ℕ) (st : KeyIndState S) : KeyIndState S :=
  { st with
    opkEntries := eraseOpkEntriesFg S oIdx st.opkEntries
    sessions   := eraseSessionsFg sIdx st.sessions
    roCache    := [] }

@[simp]
theorem eraseOpkEntryFg_opkPk (S : Setup) (oIdx : ℕ) (k : ℕ × ℕ × ℕ) (e : OpkEntry) :
    (eraseOpkEntryFg S oIdx k e).opkPk = e.opkPk := by
  unfold eraseOpkEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseOpkEntryFg_consumed (S : Setup) (oIdx : ℕ) (k : ℕ × ℕ × ℕ) (e : OpkEntry) :
    (eraseOpkEntryFg S oIdx k e).consumed = e.consumed := by
  unfold eraseOpkEntryFg; split_ifs <;> rfl

theorem any_idx_eraseOpkEntriesFg (S : Setup) (oIdx : ℕ) (k0 : ℕ × ℕ × ℕ)
    (opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)) :
    (eraseOpkEntriesFg S oIdx opkEntries).any (fun (k, _) => k == k0) =
      opkEntries.any (fun (k, _) => k == k0) := by
  simp [eraseOpkEntriesFg, List.any_map, Function.comp_def]

theorem find?_idx_eraseOpkEntriesFg (S : Setup) (oIdx : ℕ) (k0 : ℕ × ℕ × ℕ)
    (opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)) :
    (eraseOpkEntriesFg S oIdx opkEntries).find? (fun (k, _) => k == k0) =
      (opkEntries.find? (fun (k, _) => k == k0)).map (fun (k, e) =>
        (k, eraseOpkEntryFg S oIdx k e)) := by
  simp [eraseOpkEntriesFg, List.find?_map]

theorem koskBundleOkTake_eraseOpk (S : Setup) (P : Primitives) (oIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOkTake S P principals spkBundles
      (eraseOpkEntriesFg S oIdx opkEntries) advKeyPows bundle =
      koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle := by
  unfold koskBundleOkTake eraseOpkEntriesFg
  cases bundle.opkB? with
  | none => rfl
  | some p =>
    rcases p with ⟨_, opkPk⟩
    simp [← List.map_take, List.any_map, Function.comp_def]

theorem checkBundleProvenanceTake_eraseOpk (S : Setup) (P : Primitives) (oIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenanceTake S P principals spkBundles
      (eraseOpkEntriesFg S oIdx opkEntries) bundle =
      checkBundleProvenanceTake S P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenanceTake eraseOpkEntriesFg
  cases findHonestPrincipal P (principals.take S.N_dh) bundle.ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨kk, _⟩
    cases bundle.opkB? with
    | none => rfl
    | some q =>
      rcases q with ⟨_, opkPk⟩
      simp [← List.map_take, List.any_map, Function.comp_def]

theorem consume_map_eraseOpkEntriesFg (S : Setup) (oIdx : ℕ) (key : ℕ × ℕ × ℕ)
    (opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)) :
    (eraseOpkEntriesFg S oIdx opkEntries).map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e)) =
    eraseOpkEntriesFg S oIdx (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))) := by
  unfold eraseOpkEntriesFg eraseOpkEntryFg
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
  dsimp only [Function.comp_def]
  by_cases hk : (opkSlotFlatIdx S idx == oIdx) = true <;>
    by_cases hu : (idx == key) = true <;> simp [hk, hu]

@[simp]
theorem isFreshKeyIndSession_eraseStateFgOpk {S : Setup} (sIdx oIdx : ℕ)
    (st : KeyIndState S) (sid : SessionId S) :
    isKeyIndSessionTestable (eraseStateFgOpk sIdx oIdx st) sid = isKeyIndSessionTestable st sid := by
  unfold isKeyIndSessionTestable eraseStateFgOpk
  simp only [find?_sid_eraseSessionsFg]
  cases st.sessions.find? (fun e => e.sid == sid) <;> simp

def FgSlotReps.ofDh4 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) : FgSlotReps P where
  Rep1 := FgPosRightRep P vSk
  Rep2 := FgPosLeftRep P uSk
  Rep3 := FgPosLeftRep P uSk
  Rep4 := FgOptRightRep P vSk
  len1 _ _ h := h.1
  len2 _ _ h := h.1
  len3 _ _ h := h.1
  len4 pos4? dh4? h d hd := by
    subst hd
    cases pos4? with
    | none => exact False.elim h
    | some _ => exact h.1
  eq1 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq2 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosLeftRep P hP huSk h1 h2
  eq3 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosLeftRep P hP huSk h1 h2
  eq4 _ _ _ _ h1 h2 := ddhEqOptPure_of_fgOptRightRep P hP hvSk h1 h2
  sec1 d hd := ⟨hd, Or.inl rfl⟩
  sec2 d hd := ⟨hd, Or.inl rfl⟩
  sec3 d hd := ⟨hd, Or.inl rfl⟩
  sec4 d? hd := by
    cases d? with
    | none => trivial
    | some d => exact ⟨hd d rfl, Or.inl rfl⟩

def opkTargetIsV {S : Setup} (oIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S) : Bool :=
  hst.base.opkEntries.all (fun (k, e) => !(opkSlotFlatIdx S k == oIdx) || (e.opkPk == V))

/-- Sticky Case D death: the target initiator session exists and its peer OPK is absent or does
    not match `V` modulo `pow8`. -/
def deadDh4 {S : Setup} (P : Primitives) (sIdx oIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Bool :=
  opkTargetIsV oIdx V hst &&
  match hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | some s => s.peerOpkPk?.map P.pow8 != some (P.pow8 V)
  | none   => false

/-- Case D (`DH4 = CDH(ek_U*, opk_V*)`) bad event at `(sIdx, oIdx)`: initiator session `sIdx` is
    fresh against OPK slot `oIdx` and `P.x25519 s.ekASk oEntry.opkPk` is queried in
    `advRoLog.take maxLen`. -/
def badKeyIndFgDh4At {S : Setup} (P : Primitives) (maxLen sIdx oIdx : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  match st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx),
        st.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) with
  | some s, some (_, oEntry) =>
    s.fresh &&
    (s.peerOpkPk?.map P.pow8 == some (P.pow8 oEntry.opkPk)) &&
    (advRoLog.take maxLen).any (fun sec =>
      extractDh4 sec == P.x25519 s.ekASk oEntry.opkPk)
  | _, _ => false

theorem badKeyIndFgDh4At_eq_false_of_deadDh4 {S : Setup} (P : Primitives)
    (maxLen sIdx oIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh4 P sIdx oIdx V hst = true) :
    badKeyIndFgDh4At P maxLen sIdx oIdx hst.base hst.advRoLog = false := by
  unfold deadDh4 opkTargetIsV at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hSess⟩
  unfold badKeyIndFgDh4At
  cases hF1 : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    rw [hF1] at hSess
    cases hF2 : hst.base.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) with
    | none => rfl
    | some ko =>
      rcases ko with ⟨k, oEntry⟩
      dsimp only
      have hMem : (k, oEntry) ∈ hst.base.opkEntries := List.mem_of_find?_eq_some hF2
      have hIdx : (opkSlotFlatIdx S k == oIdx) = true :=
        List.find?_some
          (p := fun (x : (Nat × Nat × Nat) × OpkEntry) => opkSlotFlatIdx S x.1 == oIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, oEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or, beq_iff_eq] at hItem
      rw [hItem]
      have hNe : (s.peerOpkPk?.map P.pow8 == some (P.pow8 V)) = false := by
        simpa [bne] using hSess
      simp [hNe]

theorem opkTargetIsV_consume (S : Setup) (oIdx : ℕ) (V : Bytes) (key : ℕ × ℕ × ℕ)
    (opkEntries : List ((ℕ × ℕ × ℕ) × OpkEntry)) :
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).all
        (fun (k, e) => !(opkSlotFlatIdx S k == oIdx) || (e.opkPk == V)) =
    opkEntries.all (fun (k, e) => !(opkSlotFlatIdx S k == oIdx) || (e.opkPk == V)) := by
  rw [List.all_map]
  congr 1
  funext x
  rcases x with ⟨idx, e⟩
  simp only [Function.comp_apply]
  by_cases h : (idx == key) = true <;> simp [h]

theorem deadDh4_eq_of_opk_sess {S : Setup} (P : Primitives) (sIdx oIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hOpk : hst2.base.opkEntries = hst1.base.opkEntries)
    (hSess : (hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerOpkPk? =
      (hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerOpkPk?) :
    deadDh4 P sIdx oIdx V hst2 = deadDh4 P sIdx oIdx V hst1 := by
  unfold deadDh4 opkTargetIsV
  rw [hOpk]
  congr 1
  cases h1 : hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) <;>
    cases h2 : hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)
  · rfl
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess
    simp only [Option.map_some, Option.some.injEq] at hSess
    dsimp only
    rw [hSess]

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh4 {S : Setup} (P : Primitives)
    (sIdx oIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk : Bytes) (V : Bytes)
    (q : KeyIndQuery S) (hq : ∀ u j o, q ≠ .genOPK u j o) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh4 P sIdx oIdx V hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P q).run hst),
      deadDh4 P sIdx oIdx V x.2 = true := by
  have hDead0 := hDead
  have hUnchanged : ∀ x : KeyIndResponse × KeyIndFgCutoffState S,
      x.2.base.opkEntries = hst.base.opkEntries →
      x.2.base.sessions = hst.base.sessions →
      deadDh4 P sIdx oIdx V x.2 = true := by
    intro x hOpk hSess
    unfold deadDh4 opkTargetIsV at hDead ⊢
    rw [hOpk, hSess]; exact hDead
  unfold deadDh4 at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hSessFind⟩
  cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rw [hFS] at hSessFind; cases hSessFind
  | some s0 =>
    rw [hFS] at hSessFind
    have hFired : hasFiredSess S sIdx hst := by
      unfold hasFiredSess
      exact List.any_eq_true.mpr ⟨s0, List.mem_of_find?_eq_some hFS,
        List.find?_some (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS⟩
    intro x hx
    refine mem_support_pqxdhKeyIndFgPreImpl_elim false sIdx (noSpkIdx S) (some uSk) none P q hst x hx
      (fun _ _ hO hSe => hUnchanged x hO hSe)
      (fun _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun u j o _ hEq _ _ _ => absurd hEq (hq u j o))
      (fun s _ hAnyF hB => ?_)
      (fun k j o _ _ hSe hO => ?_)
      (fun f hSid _ _ hPeer _ _ hO hSe => ?_)
      (fun _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
    · by_cases hSlot : (initSessionSlotIdx s.sid == sIdx) = true
      · have hAny : hst.base.sessions.any (fun e => e.sid == s.sid) = true :=
          sessions_any_of_hasFiredSess sIdx hst hFired s.sid hSlot
            (by rw [beq_iff_eq.mp hSlot]; exact hsIdx)
        rw [hAnyF] at hAny; cases hAny
      · have hSlotF : (initSessionSlotIdx s.sid == sIdx) = false := Bool.eq_false_iff.mpr hSlot
        unfold deadDh4
        have hOpkEq : opkTargetIsV oIdx V x.2 = opkTargetIsV oIdx V hst := by
          unfold opkTargetIsV; rw [hB]
        rw [hOpkEq, hB]
        simp [hAll, hSlotF, hFS, hSessFind]
    · unfold deadDh4
      have hOpkEq : opkTargetIsV oIdx V x.2 = opkTargetIsV oIdx V hst := by
        unfold opkTargetIsV; rw [hO]
        exact opkTargetIsV_consume S oIdx V (k.val, j.val, o.val) hst.base.opkEntries
      rw [hOpkEq, hSe, hFS]
      exact Bool.and_eq_true_iff.mpr ⟨hAll, hSessFind⟩
    · unfold deadDh4
      have hOpkEq : opkTargetIsV oIdx V x.2 = opkTargetIsV oIdx V hst := by
        unfold opkTargetIsV; rw [hO]
      rw [hOpkEq, hSe]
      have hPred : (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) ∘ f =
          (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) := by
        funext s; dsimp; rw [hSid s]
      rw [List.find?_map, hPred, hFS]
      dsimp only [Option.map_some]
      rw [hPeer s0]
      exact Bool.and_eq_true_iff.mpr ⟨hAll, hSessFind⟩

theorem pqxdhKeyIndFgPreImplOpk_preserves_deadDh4 {S : Setup} (P : Primitives)
    (sIdx oIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImplOpk sIdx oIdx (some uSk) (some vSk) S P q).run hst),
      deadDh4 P sIdx oIdx (P.x25519Base vSk) x.2 = true := by
  cases q
  case genOPK u j o =>
    intro x hx
    unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    unfold deadDh4 opkTargetIsV at hDead ⊢
    rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hSessF⟩
    cases hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨opkSk, hSk, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      rw [hB]
      dsimp only
      rw [List.all_cons, hAll, Bool.and_true, hSessF, Bool.and_true]
      by_cases hSlot : (opkFlatIdx S u j o == oIdx) = true
      · simp only [hSlot, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSk
        subst hSk
        have hSlotV : (opkSlotFlatIdx S (u.val, j.val, o.val) == oIdx) = true := hSlot
        simp [hSlotV]
      · have hSlotV : (opkSlotFlatIdx S (u.val, j.val, o.val) == oIdx) = false :=
          Bool.eq_false_iff.mpr hSlot
        simp [hSlotV]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      rw [hB]
      exact Bool.and_eq_true_iff.mpr ⟨hAll, hSessF⟩
  all_goals
    exact pqxdhKeyIndFgPreImpl_preserves_deadDh4 P sIdx oIdx hsIdx uSk (P.x25519Base vSk) _
      (fun _ _ _ h => by cases h) hst hDead

def FgSimInvDh4 (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (sIdx oIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S) : Prop :=
  st.base = eraseStateFgOpk sIdx oIdx hst.base ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel (FgSlotReps.ofDh4 P hP uSk vSk huSk hvSk) b.q_total
    st.fgL st.rawRoCache hst.base.roCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidKeyIndEcFg S hst.base ∧
  opkTargetIsV oIdx (P.x25519Base vSk) hst = true ∧
  (∀ kv ∈ hst.base.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0) ∧
  (∀ kv ∈ hst.base.spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk) ∧
  (∀ kv ∈ hst.base.opkEntries,
    kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk ∧
    ((opkSlotFlatIdx S kv.1 == oIdx) = true → kv.2.opkSk = vSk)) ∧
  (∀ s ∈ hst.base.sessions,
    s.ekASk.length = 32 ∧ s.hdr.ekAPk = P.x25519Base s.ekASk ∧
    ((initSessionSlotIdx s.sid == sIdx) = true → s.ekASk = uSk))

theorem fgSimInvDh4_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyIndSimState.empty S secb) := by
  refine ⟨rfl, ⟨rfl, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩,
    ⟨Nat.zero_le _, rfl, List.Forall₂.nil⟩,
    by change 0 + b.q_total ≤ b.q_total; omega, by simp [KeyIndFgCutoffState.empty],
    validKeyIndEcFg_empty S secb, rfl, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)

theorem fgSimInvDh4_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen sIdx oIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (_a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (_hDead : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh4 S b P hP sIdx oIdx uSk vSk huSk hvSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh4At P maxLen sIdx oIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdh4FromAdvRoLog P.isValidDhTriple b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st.advRoLog) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badKeyIndFgDh4At P maxLen sIdx oIdx hst.base hst.advRoLog = true
  · rcases hInv with ⟨_, hAdvEq, _, _, hAdvLen, _, _, _, _, hOpks, hSess⟩
    have hBad' := hBad
    unfold badKeyIndFgDh4At at hBad'
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => rw [hFS] at hBad'; cases hBad'
    | some s =>
      rw [hFS] at hBad'
      cases hFO : hst.base.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) with
      | none => rw [hFO] at hBad'; cases hBad'
      | some ko =>
        rcases ko with ⟨k, oEntry⟩
        rw [hFO] at hBad'
        dsimp only at hBad'
        rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have hsMem : s ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
        have hsIdx : (initSessionSlotIdx s.sid == sIdx) = true :=
          List.find?_some
            (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS
        have hoMem : (k, oEntry) ∈ hst.base.opkEntries := List.mem_of_find?_eq_some hFO
        have hoIdx : (opkSlotFlatIdx S k == oIdx) = true :=
          List.find?_some
            (p := fun (x : (Nat × Nat × Nat) × OpkEntry) => opkSlotFlatIdx S x.1 == oIdx) hFO
        have hsEq : s.ekASk = uSk := (hSess s hsMem).2.2 hsIdx
        have hoSkEq : oEntry.opkSk = vSk := (hOpks (k, oEntry) hoMem).2.2 hoIdx
        have hoPkEq : oEntry.opkPk = P.x25519Base vSk := by
          rw [(hOpks (k, oEntry) hoMem).2.1, hoSkEq]
        rw [hsEq, hoPkEq] at hAny
        rcases List.any_eq_true.mp hAny with ⟨sec, hSecTake, hSecEq⟩
        have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
        have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
          rw [hAdvEq.1, List.take_of_length_le (by omega)]
          exact hSecMem
        have hWin := pureExtractCdh4FromAdvRoLog_wins_of_mem P hP.toWellFormedPrimitivesδ
          b.q_total uSk vSk st.advRoLog ⟨sec, hSecMemTake, beq_iff_eq.mp hSecEq⟩
        rw [hBad, hWin]
  · have hBadF : badKeyIndFgDh4At P maxLen sIdx oIdx hst.base hst.advRoLog = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]
    simp

end Proofs.SignalPqxdh.Security.FgGapDh.Opk
