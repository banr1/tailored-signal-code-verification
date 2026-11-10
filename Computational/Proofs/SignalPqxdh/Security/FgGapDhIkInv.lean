/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkPre
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhF
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIk
import VCVio.EvalDist.Monad.Basic

/-!
# Case B (`DH2`) State Erasure, Invariant, and Terminal Win

Defines the Case B simulator projection `eraseStateFgIk`, the per-index bad event
`badKeyIndFgDh2At` with its sticky death predicate `deadDh2`, and the coupling invariant
`FgSimInvDh2`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Ik

open Proofs.SignalPqxdh.Security.FgGapDh

/-- Simulator view of a `KeyInd` state in Case B. -/
def eraseStateFgIk {S : Setup} (sIdx kIdx : ℕ) (st : KeyIndState S) : KeyIndState S :=
  { st with
    principals := erasePrincipalsFg kIdx st.principals
    sessions   := eraseSessionsFg sIdx st.sessions
    roCache    := [] }

@[simp]
theorem isFreshKeyIndSession_eraseStateFgIk {S : Setup} (sIdx kIdx : ℕ)
    (st : KeyIndState S) (sid : SessionId S) :
    isKeyIndSessionTestable (eraseStateFgIk sIdx kIdx st) sid = isKeyIndSessionTestable st sid := by
  unfold isKeyIndSessionTestable eraseStateFgIk
  simp only [find?_sid_eraseSessionsFg]
  cases st.sessions.find? (fun e => e.sid == sid) <;> simp

def FgSlotReps.ofDh2 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) : FgSlotReps P where
  Rep1 := FgPosLeftRep P uSk
  Rep2 := FgPosRightRep P vSk
  Rep3 := FgPosLeftRep P uSk
  Rep4 := FgOptLeftRep P uSk
  len1 _ _ h := h.1
  len2 _ _ h := h.1
  len3 _ _ h := h.1
  len4 pos4? dh4? h d hd := by
    subst hd
    cases pos4? with
    | none => exact False.elim h
    | some _ => exact h.1
  eq1 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosLeftRep P hP huSk h1 h2
  eq2 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq3 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosLeftRep P hP huSk h1 h2
  eq4 _ _ _ _ h1 h2 := ddhEqOptPure_of_fgOptLeftRep P hP huSk h1 h2
  sec1 d hd := ⟨hd, Or.inl rfl⟩
  sec2 d hd := ⟨hd, Or.inl rfl⟩
  sec3 d hd := ⟨hd, Or.inl rfl⟩
  sec4 d? hd := by
    cases d? with
    | none => trivial
    | some d => exact ⟨hd d rfl, Or.inl rfl⟩

/-- Case B (`DH2 = CDH(ek_U*, ik_V*)`) bad event at `(sIdx, kIdx)`: initiator session `sIdx` is
    fresh against uncorrupted principal `kIdx` and `P.x25519 s.ekASk kEntry.ikAPk` is queried in
    `advRoLog.take maxLen`. -/
def badKeyIndFgDh2At {S : Setup} (P : Primitives) (maxLen sIdx kIdx : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  match st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx),
        st.principals.find? (fun (u, _) => u == kIdx) with
  | some s, some (_, kEntry) =>
    s.fresh && !kEntry.corrupted &&
    (P.pow8 s.peerIkPk == P.pow8 kEntry.ikAPk) &&
    (advRoLog.take maxLen).any (fun sec =>
      extractDh2 sec == P.x25519 s.ekASk kEntry.ikAPk)
  | _, _ => false

def prinTargetIsV {S : Setup} (kIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S) : Bool :=
  hst.base.principals.all (fun (k, e) => !(k == kIdx) || (e.ikAPk == V))

def sessDeadIk {S : Setup} (P : Primitives) (sIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Bool :=
  match hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | some s => P.pow8 s.peerIkPk != P.pow8 V
  | none   => false

/-- Sticky Case B death: the target principal is corrupted, or the target initiator session
    exists with a peer identity key not matching `V`. -/
def deadDh2 {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Bool :=
  prinTargetIsV kIdx V hst && (deadDh1 kIdx hst || sessDeadIk P sIdx V hst)

theorem badKeyIndFgDh2At_eq_false_of_deadDh2 {S : Setup} (P : Primitives)
    (maxLen sIdx kIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh2 P sIdx kIdx V hst = true) :
    badKeyIndFgDh2At P maxLen sIdx kIdx hst.base hst.advRoLog = false := by
  unfold deadDh2 prinTargetIsV at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hOr⟩
  unfold badKeyIndFgDh2At
  cases hF1 : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    cases hF2 : hst.base.principals.find? (fun (u, _) => u == kIdx) with
    | none => rfl
    | some ke =>
      rcases ke with ⟨k, kEntry⟩
      dsimp only
      have hMem : (k, kEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hF2
      have hIdx : (k == kIdx) = true :=
        List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == kIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, kEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or, beq_iff_eq] at hItem
      rcases Bool.or_eq_true_iff.mp hOr with hD1 | hSD
      · unfold deadDh1 at hD1
        rw [hF2] at hD1
        dsimp only at hD1
        simp [hD1]
      · unfold sessDeadIk at hSD
        rw [hF1] at hSD
        rw [hItem]
        have hNe : (P.pow8 s.peerIkPk == P.pow8 V) = false := by
          simpa [bne] using hSD
        simp [hNe]

theorem sessDeadIk_eq_of_sess {S : Setup} (P : Primitives) (sIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hSess : (hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerIkPk =
      (hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerIkPk) :
    sessDeadIk P sIdx V hst2 = sessDeadIk P sIdx V hst1 := by
  unfold sessDeadIk
  cases h1 : hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) <;>
    cases h2 : hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)
  · rfl
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess
    simp only [Option.map_some, Option.some.injEq] at hSess
    dsimp only
    rw [hSess]

theorem deadDh2_eq_of_prin_sess {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSess : (hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerIkPk =
      (hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        KeyIndInitiatorEntry.peerIkPk) :
    deadDh2 P sIdx kIdx V hst2 = deadDh2 P sIdx kIdx V hst1 := by
  unfold deadDh2
  have hT : prinTargetIsV kIdx V hst2 = prinTargetIsV kIdx V hst1 := by
    unfold prinTargetIsV; rw [hPrin]
  rw [hT, deadDh1_eq_of_principals kIdx hPrin, sessDeadIk_eq_of_sess P sIdx V hSess]

theorem deadDh1_mono_map_corrupted {S : Setup} (kIdx u : ℕ)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hPrin : hst2.base.principals = hst1.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)))
    (hD : deadDh1 kIdx hst1 = true) :
    deadDh1 kIdx hst2 = true := by
  rw [deadDh1_eq_of_principals kIdx (hst1 := { hst1 with base := { hst1.base with
      principals := hst1.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } }) hPrin]
  by_cases hEqU : (u == kIdx) = true
  · have huEq : u = kIdx := beq_iff_eq.mp hEqU
    subst huEq
    unfold deadDh1 at hD
    cases hFP : hst1.base.principals.find? (fun (idx, _) => idx == u) with
    | none => rw [hFP] at hD; cases hD
    | some p =>
      rcases p with ⟨u1, e1⟩
      exact deadDh1_map_corrupted_eq_true_of_eq u u (beq_self_eq_true u) hst1 u1 e1 hFP
  · rw [deadDh1_map_corrupted_of_ne kIdx u (Bool.eq_false_iff.mpr hEqU) hst1]
    exact hD

theorem prinTargetIsV_map_corrupted {S : Setup} (kIdx u : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hPrin : hst2.base.principals = hst1.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e))) :
    prinTargetIsV kIdx V hst2 = prinTargetIsV kIdx V hst1 := by
  unfold prinTargetIsV
  rw [hPrin, List.all_map]
  congr 1
  funext x
  rcases x with ⟨idx, e⟩
  simp only [Function.comp_apply]
  by_cases h : (idx == u) = true <;> simp [h]

theorem deadDh2_map_corrupted {S : Setup} (P : Primitives) (sIdx kIdx u : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hPrin : hst2.base.principals = hst1.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)))
    (hSess : hst2.base.sessions = hst1.base.sessions)
    (hD : deadDh2 P sIdx kIdx V hst1 = true) :
    deadDh2 P sIdx kIdx V hst2 = true := by
  unfold deadDh2 at hD ⊢
  rcases Bool.and_eq_true_iff.mp hD with ⟨hT, hOr⟩
  rw [prinTargetIsV_map_corrupted kIdx u V hPrin, hT, Bool.true_and]
  have hSD : sessDeadIk P sIdx V hst2 = sessDeadIk P sIdx V hst1 :=
    sessDeadIk_eq_of_sess P sIdx V (by rw [hSess])
  rw [hSD]
  rcases Bool.or_eq_true_iff.mp hOr with h1 | h2
  · rw [deadDh1_mono_map_corrupted kIdx u hPrin h1]; rfl
  · rw [h2]; simp

theorem deadDh2_sess_cons {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (hsIdx : sIdx < S.N_send_tot)
    (V : Bytes) {hst1 hst2 : KeyIndFgCutoffState S} (e : KeyIndInitiatorEntry S)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = e :: hst1.base.sessions)
    (hNotAny : hst1.base.sessions.any (fun e' => e'.sid == e.sid) = false)
    (hD : deadDh2 P sIdx kIdx V hst1 = true) :
    deadDh2 P sIdx kIdx V hst2 = true := by
  unfold deadDh2 at hD ⊢
  rcases Bool.and_eq_true_iff.mp hD with ⟨hT, hOr⟩
  have hT' : prinTargetIsV kIdx V hst2 = prinTargetIsV kIdx V hst1 := by
    unfold prinTargetIsV; rw [hPrin]
  rw [hT', hT, Bool.true_and, deadDh1_eq_of_principals kIdx hPrin]
  rcases Bool.or_eq_true_iff.mp hOr with h1 | h2
  · rw [h1]; rfl
  · unfold sessDeadIk at h2 ⊢
    cases hFS : hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => rw [hFS] at h2; cases h2
    | some s0 =>
      rw [hFS] at h2
      have hFired : hasFiredSess S sIdx hst1 := by
        unfold hasFiredSess
        exact List.any_eq_true.mpr ⟨s0, List.mem_of_find?_eq_some hFS,
          List.find?_some
            (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS⟩
      have hSlotF : (initSessionSlotIdx e.sid == sIdx) = false := by
        cases hSl : (initSessionSlotIdx e.sid == sIdx)
        · rfl
        · have hAny := sessions_any_of_hasFiredSess sIdx hst1 hFired e.sid hSl
            (by rw [beq_iff_eq.mp hSl]; exact hsIdx)
          rw [hNotAny] at hAny; cases hAny
      rw [hSessEq, List.find?_cons, hSlotF]
      dsimp only
      rw [hFS]
      simp [h2]

theorem deadDh2_sess_map {S : Setup} (P : Primitives) (sIdx kIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S} (f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    (hfSid : ∀ s, (f s).sid = s.sid) (hfPeer : ∀ s, (f s).peerIkPk = s.peerIkPk)
    (hPrin : hst2.base.principals = hst1.base.principals)
    (hSessEq : hst2.base.sessions = hst1.base.sessions.map f)
    (hD : deadDh2 P sIdx kIdx V hst1 = true) :
    deadDh2 P sIdx kIdx V hst2 = true := by
  rw [deadDh2_eq_of_prin_sess P sIdx kIdx V hPrin]
  · exact hD
  · rw [hSessEq, List.find?_map]
    have hPred : (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) ∘ f =
        (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) := by
      funext s; simp [hfSid]
    rw [hPred, Option.map_map]
    congr 1
    funext s
    simp [hfPeer]

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh2 {S : Setup} (P : Primitives)
    (sIdx kIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk : Bytes) (V : Bytes)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh2 P sIdx kIdx V hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P q).run hst),
      deadDh2 P sIdx kIdx V x.2 = true := by
  have hUnchanged : ∀ x : KeyIndResponse × KeyIndFgCutoffState S,
      x.2.base.principals = hst.base.principals →
      x.2.base.sessions = hst.base.sessions →
      deadDh2 P sIdx kIdx V x.2 = true := by
    intro x hPrin hSess
    rw [deadDh2_eq_of_prin_sess P sIdx kIdx V hPrin (by rw [hSess])]
    exact hDead
  intro x hx
  refine mem_support_pqxdhKeyIndFgPreImpl_elim false sIdx (noSpkIdx S) (some uSk) none P q hst x hx
    (fun hP _ _ hSe => hUnchanged x hP hSe)
    (fun u _ hEq _ _ => absurd hEq (hq u))
    (fun u _ _ _ _ hB => deadDh2_map_corrupted P sIdx kIdx u.val V (by rw [hB]) (by rw [hB]) hDead)
    (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
    (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
    (fun s _ hAnyS hB => deadDh2_sess_cons P sIdx kIdx hsIdx V s (by rw [hB]) (by rw [hB]) hAnyS hDead)
    (fun _ _ _ hP _ hSe _ => hUnchanged x hP hSe)
    (fun f hSid hPeer _ _ hP _ _ hSe =>
      deadDh2_sess_map P sIdx kIdx V f hSid hPeer hP hSe hDead)
    (fun _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))

theorem pqxdhKeyIndFgPreImpl_initPrin_preserves_deadDh2 {S : Setup} (P : Primitives)
    (sIdx kIdx : ℕ) (vSk : Bytes) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl true kIdx (noSpkIdx S) (some vSk) none S P
        (.initPrin u)).run hst),
      deadDh2 P sIdx kIdx (P.x25519Base vSk) x.2 = true := by
  intro x hx
  unfold pqxdhKeyIndFgPreImpl fgPreInitPrin at hx
  rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  revert hb
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨sec, hSec, sgn, _, hEq⟩
    have hB := (Prod.mk.inj hEq).2
    unfold deadDh2 at hDead ⊢
    rcases Bool.and_eq_true_iff.mp hDead with ⟨hT, hOr⟩
    have hT' : prinTargetIsV kIdx (P.x25519Base vSk) x.2 = true := by
      unfold prinTargetIsV at hT ⊢
      rw [hB]
      dsimp only
      rw [List.all_cons, hT, Bool.and_true]
      by_cases hU : (u.val == kIdx) = true
      · simp only [hU, Bool.true_and, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSec
        subst hSec
        simp
      · simp [hU]
    rw [hT', Bool.true_and]
    have hSD : sessDeadIk P sIdx (P.x25519Base vSk) x.2 =
        sessDeadIk P sIdx (P.x25519Base vSk) hst :=
      sessDeadIk_eq_of_sess P sIdx _ (by rw [hB])
    rw [hSD]
    rcases Bool.or_eq_true_iff.mp hOr with h1 | h2
    · have h1' := h1
      unfold deadDh1 at h1'
      cases hFP : hst.base.principals.find? (fun (idx, _) => idx == kIdx) with
      | none => rw [hFP] at h1'; cases h1'
      | some p0 =>
        rcases p0 with ⟨u0, e0⟩
        have hu0Mem : (u0, e0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
        have hu0Eq : u0 = kIdx := beq_iff_eq.mp
          (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == kIdx) hFP)
        have hNe : (u.val == kIdx) = false := by
          cases hEqB : (u.val == kIdx)
          · rfl
          · have hT2 : (u0 == u.val) = true := by
              rw [beq_iff_eq] at hEqB ⊢; rw [hu0Eq, hEqB]
            have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
              List.any_eq_true.mpr ⟨(u0, e0), hu0Mem, hT2⟩
            rw [hAny] at hAnyT; cases hAnyT
        have hD1 : deadDh1 kIdx x.2 = true := by
          unfold deadDh1
          rw [hB]
          dsimp only [List.find?]
          rw [hNe, hFP]
          rw [hFP] at h1'
          exact h1'
        rw [hD1]; rfl
    · rw [h2]; simp
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; have hB := (Prod.mk.inj hEq).2
    rw [deadDh2_eq_of_prin_sess P sIdx kIdx _ (hst1 := hst) (hst2 := x.2) (by rw [hB]) (by rw [hB])]
    exact hDead

theorem pqxdhKeyIndFgPreImplIk_preserves_deadDh2 {S : Setup} (P : Primitives)
    (sIdx kIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImplIk sIdx kIdx (some uSk) (some vSk) S P q).run hst),
      deadDh2 P sIdx kIdx (P.x25519Base vSk) x.2 = true := by
  cases q
  case initPrin u =>
    exact pqxdhKeyIndFgPreImpl_initPrin_preserves_deadDh2 P sIdx kIdx vSk u hst hDead
  all_goals
    exact pqxdhKeyIndFgPreImpl_preserves_deadDh2 P sIdx kIdx hsIdx uSk (P.x25519Base vSk) _
      (fun _ h => by cases h) hst hDead

def FgSimInvDh2 (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (sIdx kIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S) : Prop :=
  st.base = eraseStateFgIk sIdx kIdx hst.base ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel (FgSlotReps.ofDh2 P hP uSk vSk huSk hvSk) b.q_total
    st.fgL st.rawRoCache hst.base.roCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidKeyIndEcFg S hst.base ∧
  prinTargetIsV kIdx (P.x25519Base vSk) hst = true ∧
  (∀ kv ∈ hst.base.principals,
    kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0 ∧
    ((kv.1 == kIdx) = true → kv.2.secIKA0 = vSk)) ∧
  (∀ kv ∈ hst.base.spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk) ∧
  (∀ kv ∈ hst.base.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ s ∈ hst.base.sessions,
    s.ekASk.length = 32 ∧ s.hdr.ekAPk = P.x25519Base s.ekASk ∧
    ((initSessionSlotIdx s.sid == sIdx) = true → s.ekASk = uSk))

theorem fgSimInvDh2_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyIndSimState.empty S secb) := by
  refine ⟨rfl, ⟨rfl, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩,
    ⟨Nat.zero_le _, rfl, List.Forall₂.nil⟩,
    by change 0 + b.q_total ≤ b.q_total; omega, by simp [KeyIndFgCutoffState.empty],
    validKeyIndEcFg_empty S secb, rfl, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)

theorem fgSimInvDh2_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen sIdx kIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (_a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (_hDead : deadDh2 P sIdx kIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh2 S b P hP sIdx kIdx uSk vSk huSk hvSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh2At P maxLen sIdx kIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st.advRoLog) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badKeyIndFgDh2At P maxLen sIdx kIdx hst.base hst.advRoLog = true
  · rcases hInv with ⟨_, hAdvEq, _, _, hAdvLen, _, _, hPrins, _, _, hSess⟩
    have hBad' := hBad
    unfold badKeyIndFgDh2At at hBad'
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => rw [hFS] at hBad'; cases hBad'
    | some s =>
      rw [hFS] at hBad'
      cases hFP : hst.base.principals.find? (fun (u, _) => u == kIdx) with
      | none => rw [hFP] at hBad'; cases hBad'
      | some kp =>
        rcases kp with ⟨k, kEntry⟩
        rw [hFP] at hBad'
        dsimp only at hBad'
        rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have hsMem : s ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
        have hsIdx : (initSessionSlotIdx s.sid == sIdx) = true :=
          List.find?_some
            (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS
        have hkMem : (k, kEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
        have hkIdx : (k == kIdx) = true :=
          List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == kIdx) hFP
        have hsEq : s.ekASk = uSk := (hSess s hsMem).2.2 hsIdx
        have hkSkEq : kEntry.secIKA0 = vSk := (hPrins (k, kEntry) hkMem).2.2 hkIdx
        have hkPkEq : kEntry.ikAPk = P.x25519Base vSk := by
          rw [(hPrins (k, kEntry) hkMem).2.1, hkSkEq]
        rw [hsEq, hkPkEq] at hAny
        rcases List.any_eq_true.mp hAny with ⟨sec, hSecTake, hSecEq⟩
        have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
        have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
          rw [hAdvEq.1, List.take_of_length_le (by omega)]
          exact hSecMem
        have hWin := pureExtractCdh2FromAdvRoLog_wins_of_mem P hP.toWellFormedPrimitivesδ
          b.q_total uSk vSk st.advRoLog ⟨sec, hSecMemTake, beq_iff_eq.mp hSecEq⟩
        rw [hBad, hWin]
  · have hBadF : badKeyIndFgDh2At P maxLen sIdx kIdx hst.base hst.advRoLog = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]
    simp

end Proofs.SignalPqxdh.Security.FgGapDh.Ik
