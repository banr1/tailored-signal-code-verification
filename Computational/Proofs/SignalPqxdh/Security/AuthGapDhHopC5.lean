/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC4
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhF
import Computational.Proofs.SignalPqxdh.Security.FgGapDh
import VCVio.EvalDist.Monad.Basic
/-!
# `Auth` hop `G3 → G3.5`: `GapDH` step coupling for `DH1`

Maintains the latched simulation invariant `FgAuthSimInvDh1Latched` across all `AuthQuery` steps to bound
the per-index sticky `DH1 = CDH(ik_U*, spk_V*)` bad event by `GapDH` (`prob_badAuthFgDh1LatchedAt_le_gapDh`).
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security OracleSpec OracleComp Proofs.SignalPqxdh.Security.FgGapDh
open scoped ENNReal
namespace Proofs.SignalPqxdh.Security
open AuthDh3
/-! ## Target abort flag `deadAuthDh1` -/
def badAuthFgDh1AtCore {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  badAuthFgDh1At P maxLen uIdx bIdx st advRoLog respRecs
/-- Sticky abort flag for `DH1`, set once target principal `uIdx` is corrupted. -/
def deadAuthDh1 {S : Setup} (uIdx : ℕ) (hst : AuthFgCutoffState S) : Bool :=
  match hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | some (_, uEntry) => uEntry.corrupted
  | none             => false
theorem badAuthFgDh1AtCore_eq_false_of_deadAuthDh1 {S : Setup} (P : Primitives) (maxLen uIdx bIdx :
  ℕ) (hst : AuthFgCutoffState S) (hDead : deadAuthDh1 uIdx hst = true) :
    badAuthFgDh1AtCore P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs = false := by
  unfold deadAuthDh1 at hDead; unfold badAuthFgDh1AtCore badAuthFgDh1At
  cases hF1 : hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hF1] at hDead
  | some ue =>
    rcases ue with ⟨_, uEntry⟩; rw [hF1] at hDead; dsimp only at hDead ⊢
    cases hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨_, bEntry⟩; simp [hDead]
theorem badAuthFgDh1At_eq_false_of_deadAuthDh1 {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
  (hst : AuthFgCutoffState S) (hDead : deadAuthDh1 uIdx hst = true) :
    badAuthFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs = false :=
  badAuthFgDh1AtCore_eq_false_of_deadAuthDh1 P maxLen uIdx bIdx hst hDead
theorem deadAuthDh1_eq_of_principals {S : Setup} (uIdx : ℕ) {hst1 hst2 : AuthFgCutoffState S} (hPrin
  : hst2.base.principals = hst1.base.principals) :
    deadAuthDh1 uIdx hst2 = deadAuthDh1 uIdx hst1 := by
  unfold deadAuthDh1; rw [hPrin]
theorem deadAuthDh1_map_corrupted_of_ne {S : Setup} (uIdx u : ℕ) (hNe : (u == uIdx) = false) (hst :
  AuthFgCutoffState S) :
    deadAuthDh1 uIdx { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } =
      deadAuthDh1 uIdx hst := by
  unfold deadAuthDh1
  have hMapFind : (List.map (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e))
        hst.base.principals).find? (fun (idx, _) => idx == uIdx) =
      (hst.base.principals.find? (fun (idx, _) => idx == uIdx)).map
        (fun (idx, e) => if idx == u then (idx, { e with corrupted := true }) else (idx, e)) := by
    have hPred : (fun (x : Nat × PrincipalEntry) => x.1 == uIdx) ∘ (fun ((idx, e) : Nat ×
      PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
        (fun (x : Nat × PrincipalEntry) => x.1 == uIdx) := by
      funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
    rw [List.find?_map, hPred]
  dsimp only; rw [hMapFind]; cases hF : hst.base.principals.find? (fun (idx, _) => idx == uIdx) with
  | none => rfl
  | some p =>
    rcases p with ⟨u0, uEntry⟩
    have hu0 : u0 = uIdx := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == uIdx) hF)
    subst hu0
    have hNeSymm : (u0 == u) = false := by rw [beq_eq_false_iff_ne] at hNe ⊢; exact Ne.symm hNe
    dsimp only [Option.map]; rw [hNeSymm]; rfl
theorem deadAuthDh1_map_corrupted_eq_true_of_eq {S : Setup} (uIdx u : ℕ) (hEq : (u == uIdx) = true)
  (hst : AuthFgCutoffState S) (u0 : ℕ) (uEntry : PrincipalEntry) (hF : hst.base.principals.find?
  (fun (idx, _) => idx == u) = some (u0, uEntry)) :
    deadAuthDh1 uIdx { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } = true := by
  have huEq : u = uIdx := beq_iff_eq.mp hEq; subst huEq; unfold deadAuthDh1
  have hMapFind : (List.map (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e))
        hst.base.principals).find? (fun (idx, _) => idx == u) =
      (hst.base.principals.find? (fun (idx, _) => idx == u)).map
        (fun (idx, e) => if idx == u then (idx, { e with corrupted := true }) else (idx, e)) := by
    have hPred : (fun (x : Nat × PrincipalEntry) => x.1 == u) ∘ (fun ((idx, e) : Nat ×
      PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
        (fun (x : Nat × PrincipalEntry) => x.1 == u) := by
      funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
    rw [List.find?_map, hPred]
  dsimp only; rw [hMapFind, hF]
  have hu0 : (u0 == u) = true := List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u)
    hF
  dsimp only [Option.map]; rw [hu0]; rfl
theorem pqxdhAuthFgPreImpl_preserves_deadAuthDh1 {S : Setup} (P : Primitives) (uIdx bIdx : ℕ) (uSk
  vSk : Bytes) (q : AuthQuery S) (hst : AuthFgCutoffState S) (hDead : deadAuthDh1 uIdx hst = true) :
  ∀ x ∈ support ((pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadAuthDh1 uIdx x.2 = true := by
  have hUnchanged : ∀ x : AuthResponse × AuthFgCutoffState S, x.2.base.principals =
    hst.base.principals →
      deadAuthDh1 uIdx x.2 = true := by
    intro x hPrin; rw [deadAuthDh1_eq_of_principals uIdx hPrin]; exact hDead
  have hDead0 := hDead; unfold deadAuthDh1 at hDead
  cases hFP : hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hFP] at hDead; cases hDead
  | some p0 =>
    rcases p0 with ⟨u0, uEntry0⟩; rw [hFP] at hDead; dsimp only at hDead
    have hu0Mem : (u0, uEntry0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
    have hu0Eq : u0 = uIdx := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == uIdx) hFP)
    subst hu0Eq; intro x hx; cases q with
    | initPrin u =>
      unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx; rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; unfold fgPreAuthInitPrin at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
      · have hNe : (u.val == u0) = false := by
          cases hEqB : (u.val == u0)
          · rfl
          · have hT : (u0 == u.val) = true := by rw [beq_iff_eq] at hEqB ⊢; exact hEqB.symm
            have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
              List.any_eq_true.mpr ⟨(u0, uEntry0), hu0Mem, hT⟩
            rw [hAny] at hAnyT; cases hAnyT
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, hEq⟩
        have hB := (Prod.mk.inj hEq).2; unfold deadAuthDh1; rw [hB]; dsimp only [List.find?]
        rw [hNe, hFP]; exact hDead
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2])
    | corruptIK u =>
      change x ∈ support ((liftAuthFgHybrid
        (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.corruptIK
            u)))).run hst) at hx
      rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; unfold pqxdhAuthImpl at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2])
      | some pu =>
        rcases pu with ⟨u1, entry1⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        have hPrinX : x.2.base.principals = hst.base.principals.map (fun (idx, e) =>
              if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) := by
          rw [hB]
        have hEq2 := deadAuthDh1_eq_of_principals u0 (hst2 := x.2)
          (hst1 := { hst with base := { hst.base with
            principals := hst.base.principals.map (fun (idx, e) =>
              if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } }) hPrinX
        rw [hEq2]
        by_cases hEqU : (u.val == u0) = true
        · exact deadAuthDh1_map_corrupted_eq_true_of_eq u0 u.val hEqU hst u1 entry1 hFU
        · rw [deadAuthDh1_map_corrupted_of_ne u0 u.val (Bool.eq_false_iff.mpr hEqU) hst]
          exact hDead0
    | genSPK u j =>
      unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx; rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩; unfold fgPreAuthGenSPK at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2])
        | some p =>
          rcases p with ⟨_, uEntry⟩
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff]
          rintro ⟨_, _, _, _, _, _, _, _, hEq⟩
          exact hUnchanged x (by rw [(Prod.mk.inj hEq).2])
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact hUnchanged x (by rw [(Prod.mk.inj hEq).2])
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl at hx
      by_cases hOpt : bundle.opkB?.isNone = true
      · unfold liftAuthFgHybrid mkG3Hybrid at hx
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        exact hUnchanged x (by rw [(Prod.mk.inj hx).2])
      · have hRunEq : (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isNone then return .noneResp
            fgPreAuthSendHybrid .g3 true true u0 (some uSk) S P (.sendOPK u i) u bundle m0 m1)).run
              hst =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true u0 (some uSk) S P (.sendOPK u i) u
              bundle m0 m1)).run hst := by
          unfold liftAuthFgHybrid; simp [hOpt]
        rw [hRunEq] at hx
        rcases fgPreAuthSendHybrid_support true u0 (some uSk) P (.sendOPK u i) u bundle m0 m1 hst x
          hx with
          ⟨hP, _, _⟩
        exact hUnchanged x hP
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl at hx
      by_cases hOpt : bundle.opkB?.isSome = true
      · unfold liftAuthFgHybrid mkG3Hybrid at hx
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        exact hUnchanged x (by rw [(Prod.mk.inj hx).2])
      · have hRunEq : (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isSome then return .noneResp
            fgPreAuthSendHybrid .g3 true true u0 (some uSk) S P (.sendNoOPK u i) u bundle m0
              m1)).run hst =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true u0 (some uSk) S P (.sendNoOPK u i) u
              bundle m0 m1)).run hst := by
          unfold liftAuthFgHybrid; simp [hOpt]
        rw [hRunEq] at hx
        rcases fgPreAuthSendHybrid_support true u0 (some uSk) P (.sendNoOPK u i) u bundle m0 m1 hst
          x hx with
          ⟨hP, _, _⟩
        exact hUnchanged x hP
    | genOPK u j o =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.genOPK u j o) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | recvOPK k j o msg =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvOPK k j o msg) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | recvNoOPK k j l msg =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvNoOPK k j l msg) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | roQuery secrets =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roQuery secrets) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | roRootQuery rk dh =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roRootQuery rk dh) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | revealDhSecrets =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P .revealDhSecrets (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
    | registerKey sk =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.registerKey sk) (fun _ h =>
        by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, _, _, _⟩
      exact hUnchanged x hP
theorem pureExtractCdhFromAuthSimState_dh1_wins_of_mem (S : Setup) (P : Primitives) (hWF :
  WellFormedPrimitivesδ P) (maxLen : ℕ) (u v : Bytes) (st : FgAuthSimState S) (h_mem : P.x25519 u
  (P.x25519Base v) ∈ (st.advRoLog.take maxLen).map extractDh1 ∨ P.x25519 u (P.x25519Base v) ∈
  (st.base.sessions.take S.N_dh).map (initAuthDh1Cand S P st.base.principals st.base.spkBundles
  st.advKeyPows) ∨ P.x25519 u (P.x25519Base v) ∈ (st.respRecs.take S.N_sess_tot).map
  (respAuthDh1Cand S P st.base.spkBundles)) : (P.pow8 (pureExtractCdhFromAuthSimState S P
  P.isValidDhTriple true maxLen (P.x25519Base u) (P.x25519Base v) st) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  unfold pureExtractCdhFromAuthSimState; simp only [↓reduceIte]
  exact find?_ddh_3way_wins_of_mem P hWF u v _ _ _ h_mem
/-! ## Simulation invariant `FgAuthSimInvDh1` -/
def FgAuthSimInvDh1 (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ
  P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) : Prop :=
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  FgAuthBaseRel true uIdx bIdx st.base hst.base ∧
  st.respRecs = hst.respRecs ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel R b.q_total st.fgL st.rawRoCache hst.base.roCache ∧
  FgRootCacheRel P vSk b.q_total st.fgRootL hst.base.rootRoCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  st.fgRootL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidAuthEcFg S P hst.base ∧
  (∀ kv ∈ hst.base.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0 ∧
    ((kv.1 == uIdx) = true → kv.2.secIKA0 = uSk)) ∧
  (∀ kv ∈ hst.base.spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk)) ∧
  (∀ kv ∈ hst.base.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ s ∈ hst.base.sessions, s.ekASk.length = 32 ∧ s.ephASk.length = 32)
theorem fgAuthSimInvDh1_empty (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (secb : Bool) : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk b.q_total
      (AuthFgCutoffState.empty S secb) (FgAuthSimState.empty S secb) := by
  refine ⟨fgAuthBaseRel_empty S true uIdx bIdx secb, rfl, ⟨rfl, rfl, fun _ h => False.elim
    (List.not_mem_nil h)⟩, ⟨by simp [FgAuthSimState.empty], rfl, List.Forall₂.nil⟩, ⟨by simp
    [FgAuthSimState.empty], List.Forall₂.nil⟩, by simp [FgAuthSimState.empty],
    by simp [FgAuthSimState.empty],
    by simp [AuthFgCutoffState.empty],
    validAuthEcFg_empty S P secb,
    ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
theorem fgAuthSimInvDh1_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32)
  (hvSk : vSk.length = 32) (_a : Bool) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (_hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk rem hst st) : 𝒟[(pure (badAuthFgDh1AtCore P maxLen uIdx bIdx hst.base hst.advRoLog
  hst.respRecs) : ProbComp Bool)] {true} ≤ 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
  P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badAuthFgDh1AtCore P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs = true
  · rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, _, _, _, _, hAdvLen, _, hPrins, hSpks, _, _⟩
    have hBad' := hBad; unfold badAuthFgDh1AtCore badAuthFgDh1At at hBad'
    cases hFP : hst.base.principals.find? (fun (u, _) => u == uIdx) with
    | none => rw [hFP] at hBad'; cases hBad'
    | some up =>
      rcases up with ⟨u0, uEntry⟩; rw [hFP] at hBad'
      cases hFB : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => rw [hFB] at hBad'; cases hBad'
      | some kb =>
        rcases kb with ⟨k, bEntry⟩; rw [hFB] at hBad'
        dsimp only at hBad'; rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have huMem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
        have huIdx : (u0 == uIdx) = true :=
          List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == uIdx) hFP
        have hbMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFB
        have hbIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1
            == bIdx) hFB
        have huEq : uEntry.secIKA0 = uSk := (hPrins (u0, uEntry) huMem).2.2 huIdx
        have hbSkEq : bEntry.spkSk = vSk := (hSpks (k, bEntry) hbMem).2.2 hbIdx
        have hbPkEq : bEntry.spkPk = P.x25519Base vSk := by
          rw [(hSpks (k, bEntry) hbMem).2.1, hbSkEq]
        rw [huEq, hbPkEq] at hAny
        have hPrinEq : st.base.principals = erasePrincipalsFg uIdx hst.base.principals :=
          hBaseRel.principals_eq
        have hSpkEq := hBaseRel.spkBundles_eq; have hSessEq := hBaseRel.sessions_eq
        have hMemDisj : P.x25519 uSk (P.x25519Base vSk) ∈ (st.advRoLog.take b.q_total).map
          extractDh1 ∨ P.x25519 uSk (P.x25519Base vSk) ∈ (st.base.sessions.take S.N_dh).map
          (initAuthDh1Cand S P st.base.principals st.base.spkBundles st.advKeyPows) ∨ P.x25519 uSk
          (P.x25519Base vSk) ∈
              (st.respRecs.take S.N_sess_tot).map (respAuthDh1Cand S P st.base.spkBundles) := by
          rcases Bool.or_eq_true_iff.mp hAny with hAny12 | hAny3
          · rcases Bool.or_eq_true_iff.mp hAny12 with hAny1 | hAny2
            · rcases List.any_eq_true.mp hAny1 with ⟨sec, hSecTake, hSecEq⟩
              have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
              have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
                rw [hAdvEq.1, List.take_of_length_le (by omega)]; exact hSecMem
              exact Or.inl (by rw [← beq_iff_eq.mp hSecEq]; exact List.mem_map_of_mem hSecMemTake)
            · rcases List.any_eq_true.mp hAny2 with ⟨s, hsTake, hsEq⟩; refine Or.inr (Or.inl ?_)
              rw [hSessEq, hPrinEq, hSpkEq, hAdvEq.2.1]; unfold eraseAuthSessionsOptFg
              rw [← List.map_take]
              have hCandEq : initAuthDh1Cand S P (erasePrincipalsFg uIdx hst.base.principals)
                (eraseSpkBundlesFg S bIdx hst.base.spkBundles) (hst.base.advKeys.map (fun (sk,
                pk) => (sk, P.pow8 pk))) (eraseAuthSessionEntryOptFg true uIdx s) =
                    P.x25519 uSk (P.x25519Base vSk) := by
                rw [← beq_iff_eq.mp hsEq]; unfold initAuthDh1Cand eraseAuthSessionEntryOptFg
                simp [lookupSenderIkPk_erasePrincipalsFg]
              rw [← hCandEq]; exact List.mem_map_of_mem (List.mem_map_of_mem hsTake)
          · rcases List.any_eq_true.mp hAny3 with ⟨r, hrTake, hrEq⟩; refine Or.inr (Or.inr ?_)
            rw [hRespEq, hSpkEq, ← beq_iff_eq.mp hrEq]; exact List.mem_map_of_mem hrTake
        have hWin := pureExtractCdhFromAuthSimState_dh1_wins_of_mem S P hP.toWellFormedPrimitivesδ
          b.q_total uSk vSk st hMemDisj
        rw [hBad, hWin]
  · have hBadF : badAuthFgDh1AtCore P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]; simp
/-! ## Step coupling for `FgAuthSimInvDh1` -/
theorem fgAuthStepCoupling_dh1_unchanged (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead :
  deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk (rem +
  1) hst st) (r : AuthResponse) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, h4, h5, by omega, by omega, by omega, h9, h10, h11, h12,
    h13⟩
theorem fgAuthStepCoupling_dh1_unchanged_resp (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (rRec :
  AuthRespRecord) (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx
  uSk vSk huSk hvSk (rem + 1) hst st) (r : AuthResponse) (k1 : AuthResponse × AuthFgCutoffState S →
  ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st',
  deadAuthDh1 uIdx hst' = false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst'
  st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, { hst with respRecs := rRec :: hst.respRecs })] {true} ≤
      𝒟[k2 (r, { st with respRecs := rRec :: st.respRecs })] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact hCont r _ _ hDead ⟨h1, by dsimp; rw [h2], h3, h4, h5, by dsimp; omega, by dsimp; omega,
    by dsimp; omega, h9, h10, h11, h12, h13⟩
theorem fgAuthStepCoupling_dh1_initPrin (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P
  (.initPrin u)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S
  b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hPrinAnyEq : st.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hBaseRel.principals_eq]; exact any_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  unfold pqxdhAuthFgPreImpl; dsimp only; rw [liftAuthFgHybrid_liftAuthBase_eq]
  unfold liftAuthFgBase fgPreAuthInitPrin fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and, hPrinAnyEq, bind_assoc,
    pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == uIdx) = true
    · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, evalDist_sampleScalar32_const]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := uSk, ikAPk := P.x25519Base uSk,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · unfold deadAuthDh1; dsimp only [List.find?]; rw [hTgt]
      · refine ⟨⟨hBaseRel.secb_eq, ?_, hBaseRel.spkBundles_eq, hBaseRel.opkEntries_eq,
          hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
          hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache,
          hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
          ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩,
          ?_, hSpks, hOpks, hSess⟩
        · dsimp only; rw [hBaseRel.principals_eq]; unfold erasePrincipalsOptFg
          simp [erasePrincipalsFg, erasePrincipalEntryFg, beq_iff_eq.mp hTgt]
        · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨huSk, rfl, fun _ => rfl⟩
          · exact hPrins kv hMem
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
      have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · unfold deadAuthDh1 at hDead ⊢; dsimp only [List.find?]; rw [hTgtF]; exact hDead
      · refine ⟨⟨hBaseRel.secb_eq, ?_, hBaseRel.spkBundles_eq, hBaseRel.opkEntries_eq,
          hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
          hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache,
          hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
          ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩,
          ?_, hSpks, hOpks, hSess⟩
        · dsimp only; rw [hBaseRel.principals_eq]; unfold erasePrincipalsOptFg
          simp [erasePrincipalsFg, erasePrincipalEntryFg, beq_eq_false_iff_ne.mp hTgtF]
        · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
          · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh1_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) (hDeadCont : ∀ r hst', deadAuthDh1 uIdx hst' = true → 𝒟[k1 (r, hst')]
  {true} = 0) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
  hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
    (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hBaseRel.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  change 𝒟[(liftAuthFgHybrid
    (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.corruptIK
        u)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  | some p =>
    rcases p with ⟨u0, entry⟩; dsimp only [Option.map]
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    have hu0 : u0 = u.val := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == u.val) hF)
    by_cases hTgt : (u.val == uIdx) = true
    · have hDead' : deadAuthDh1 uIdx { hst with base := { hst.base with
          principals := hst.base.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } } = true :=
        deadAuthDh1_map_corrupted_eq_true_of_eq uIdx u.val hTgt hst u0 entry hF
      rw [hDeadCont _ _ hDead']; exact zero_le
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      have hu0F : (u0 == uIdx) = false := by rw [hu0]; exact hTgtF
      have hEraseEq : erasePrincipalEntryFg uIdx u0 entry = entry := by
        unfold erasePrincipalEntryFg; simp [hu0F]
      rw [hEraseEq]; apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
      · rw [deadAuthDh1_map_corrupted_of_ne uIdx u.val hTgtF hst]; exact hDead
      · refine ⟨⟨hBaseRel.secb_eq, ?_, hBaseRel.spkBundles_eq, hBaseRel.opkEntries_eq,
          hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
          hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache,
          hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
          ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1, hValidEc.2.1,
            hValidEc.2.2.1, hValidEc.2.2.2⟩,
          ?_, hSpks, hOpks, hSess⟩
        · dsimp only; rw [hBaseRel.principals_eq]; unfold erasePrincipalsOptFg
          exact corrupt_map_erasePrincipalsFg uIdx u.val hst.base.principals
        · intro kv hkv; rw [List.mem_map] at hkv
          rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩; have hPr := hPrins (idx, e) heMem
          by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq
            <;> (subst hEq; exact hPr)
theorem fgAuthStepCoupling_dh1_genOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (rem : ℕ) (hst :
  AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh1 uIdx hst = false) (hInv :
  FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse ×
  AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont
  : ∀ r hst' st', deadAuthDh1 uIdx hst' = false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true
  uIdx bIdx (some uSk) (some vSk) S P (.genOPK u j o)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P
  P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  change 𝒟[(liftAuthFgHybrid
    (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.genOPK u j
        o)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpkEq, bind_assoc, pure_bind]
  cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun opkSk hOpk => ?_)
    have hLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }
    apply hCont (.pkResp (P.x25519Base opkSk))
    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
    · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        by dsimp, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
        hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
        ⟨hValidEc.1, hValidEc.2.1, (validOpkEntries_cons S u j o oEntry hst.base.opkEntries
          hValidEc.2.2.1 hAny).1, hValidEc.2.2.2⟩,
        hPrins, hSpks, ?_, hSess⟩
      intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hLen, rfl⟩
      · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh1_genSPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv) (rem : ℕ) (hst : AuthFgCutoffState S) (st :
  FgAuthSimState S) (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx
  bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
  (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx
  hst' = false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')]
  {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P
  (.genSPK u j)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S
  b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
    (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hBaseRel.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  have hSpkAnyEq : st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) =
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    rw [hBaseRel.spkBundles_eq]; exact any_idx_eraseSpkBundlesFg S bIdx (u.val, j.val)
      hst.base.spkBundles
  unfold pqxdhAuthFgPreImpl; dsimp only; rw [liftAuthFgHybrid_liftAuthBase_eq]
  unfold liftAuthFgBase fgPreAuthGenSPK fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkAnyEq, hPrinFind, bind_assoc,
    pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some p =>
      rcases p with ⟨u0, uEntry⟩; dsimp only [Option.map]
      simp only [erasePrincipalEntryFg_secIKAsign, erasePrincipalEntryFg_ikAPk]
      by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, evalDist_sampleScalar32_const]
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support (sampleKemKeyGen P) _ _ (fun ⟨pqspkPk, pqspkSk⟩
          _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        have hTgtVal : spkBundleFlatIdxVal S (u.val, j.val) = bIdx := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using beq_iff_eq.mp hTgt
        let bEntry : SpkBundleEntry := {
          spkSk := vSk, spkPk := P.x25519Base vSk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base vSk)) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        apply hCont (.bundleResp _)
        · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
        · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, ?_, hBaseRel.opkEntries_eq,
            hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
            hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache,
            hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_cons S u j bEntry hst.base.spkBundles hValidEc.2.1
              hAny).1, hValidEc.2.2⟩,
            hPrins, ?_, hOpks, hSess⟩
          · dsimp only [eraseSpkBundlesFg, List.map]; rw [hBaseRel.spkBundles_eq]
            unfold eraseSpkBundlesFg eraseSpkBundleEntryFg; simp; intro hNe; exact False.elim (hNe
              hTgtVal)
          · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hvSk, rfl, fun _ => rfl⟩
            · exact hSpks kv hMem
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hTgtValNe : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hTgtF
        simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpk => ?_)
        have hLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpk
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support (sampleKemKeyGen P) _ _ (fun ⟨pqspkPk, pqspkSk⟩
          _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let bEntry : SpkBundleEntry := {
          spkSk := spkSk, spkPk := P.x25519Base spkSk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        apply hCont (.bundleResp _)
        · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
        · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, ?_, hBaseRel.opkEntries_eq,
            hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
            hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache,
            hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_cons S u j bEntry hst.base.spkBundles hValidEc.2.1
              hAny).1, hValidEc.2.2⟩,
            hPrins, ?_, hOpks, hSess⟩
          · dsimp only [eraseSpkBundlesFg, List.map]; rw [hBaseRel.spkBundles_eq]
            unfold eraseSpkBundlesFg eraseSpkBundleEntryFg; simp; intro hEq; exact False.elim
              (beq_eq_false_iff_ne.mp hTgtValNe hEq)
          · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hLen, rfl, fun h => by rw [hTgtValNe] at h; cases h⟩
            · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh1_roQuery (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (secrets : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P
  (.roQuery secrets)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S
  b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl
    mkG3Hybrid fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    bind_assoc, pure_bind]
  rcases fgRoQueryAuthPure_eq_or_sample (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk) hCache with
    ⟨dk, hEval, hFg⟩ | ⟨newRaw, newFgL, hEval, hFg, hStep⟩
  · rw [hEval, hFg]; simp only [pure_bind]; apply hCont (.drKeyResp dk)
    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
    · exact ⟨hBaseRel, hRespEq, ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCache, hRootCache,
        by dsimp; omega, by dsimp; omega, by dsimp [List.length_cons]; omega,
        hValidEc, hPrins, hSpks, hOpks, hSess⟩
  · rw [hEval, hFg]; simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun dk _ => ?_)
    rcases hStep dk (by omega) with ⟨hLenNew, hCacheNew⟩; apply hCont (.drKeyResp dk)
    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
    · exact ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCacheNew, hRootCache, by dsimp; omega,
        by dsimp; omega, by dsimp [List.length_cons]; omega,
        validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩
theorem fgAuthStepCoupling_dh1_roRootQuery (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rk dh : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P
  (.roRootQuery rk dh)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx
  S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roRootQuery rk dh) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  change 𝒟[(liftAuthFgHybrid
    (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.roRootQuery rk
        dh)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc,
    pure_bind]
  rcases fgRoRootQueryAuthPure_eq_or_sample hP hvSk hRootCache (rk := rk) (dh := dh) with
    ⟨rk1, ck1_0, hEval, hFg⟩ | ⟨hEval, hFg, hStep⟩
  · rw [hEval, hFg]; simp only [pure_bind]; apply hCont (.rootKdfResp rk1 ck1_0)
    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
    · exact ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, by omega, by omega, by dsimp; omega,
        validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩
  · rw [hEval, hFg]; simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun rk1 _ => ?_)
    refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun ck1_0 _ => ?_)
    have hRootNew := hStep rk1 ck1_0 (by omega); apply hCont (.rootKdfResp rk1 ck1_0)
    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
    · exact ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        hAdvEq, hCache, hRootNew, by dsimp; omega, by dsimp [List.length_cons]; omega,
        by dsimp; omega,
        validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩
theorem fgAuthStepCoupling_dh1_recvNoOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (rem :
  ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh1 uIdx hst = false)
  (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse
  × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool)
  (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' = false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk
  huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl
  true uIdx bIdx (some uSk) (some vSk) S P (.recvNoOPK k j l msg)).run hst >>= k1] {true} ≤
  𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.recvNoOPK k j l msg) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk; have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hPrinEq : st.base.principals = erasePrincipalsFg uIdx hst.base.principals :=
    hBaseRel.principals_eq
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == k.val) =
    (hst.base.principals.find? (fun (idx, _) => idx == k.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hPrinEq]; exact find?_idx_erasePrincipalsFg uIdx k.val hst.base.principals
  have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
    (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
    rw [hBaseRel.spkBundles_eq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val)
      hst.base.spkBundles
  have hUsedEq : st.base.usedRecvNoOPK = hst.base.usedRecvNoOPK := hBaseRel.usedRecvNoOPK_eq
  have hKybEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := hBaseRel.usedKyberTriples_eq
  have hTakePrin : (erasePrincipalsFg uIdx hst.base.principals).take S.N_dh =
      erasePrincipalsFg uIdx hst.base.principals :=
    List.take_of_length_le (by rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk := by
    rw [hPrinEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P uIdx hst.base.principals st.advKeyPows
      hst.base.advKeys msg.hdr.ikAPk hLengths.1 hAdvEq.2.1
  let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl mkG3Hybrid fgAuthStepPure
    fgRunRecvNoOPKAuthPure
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, hSpkFind, hUsedEq, hKybEq,
    hKoskEq, bind_assoc, pure_bind]
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 && msg.hdr.ekAPk.length == 32 &&
    msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st rRec
      hDead hInv0 .noneResp k1 k2 hCont
  · rcases hdr_lengths_of_guard_false (Bool.eq_false_iff.mpr hHdr) with ⟨hIkLen, hEkLen, hEphLen⟩
    simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
        rRec hDead hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
          rRec hDead hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
          exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst
            st rRec hDead hInv0 .noneResp k1 k2 hCont
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩; dsimp only [Option.map]
          rcases hPrins (k0, kEntry) (List.mem_of_find?_eq_some hFK) with ⟨hkSkLen, hkPk, hkTgt⟩
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst
              st rRec hDead hInv0 .noneResp k1 k2 hCont
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩; dsimp only [Option.map]
            rcases hSpks (kb0, bEntry) (List.mem_of_find?_eq_some hFB) with ⟨hbSkLen, hbPk, hbTgt⟩
            simp only [eraseSpkBundleEntryFg_pqspkSk]
            by_cases hRep : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
              msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
              msg.ephAPk) = true
            · simp only [hRep, ↓reduceIte, StateT.run_pure, pure_bind]
              exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem
                hst st rRec hDead hInv0 .noneResp k1 k2 hCont
            · rcases canon_ek_eph_of_guard_false (Bool.eq_false_iff.mpr hRep) with ⟨hEkOnCurve,
                hEphOnCurve⟩
              simp only [hRep, Bool.false_eq_true, ↓reduceIte]
              cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none =>
                simp only [StateT.run_pure, pure_bind]
                exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem
                  hst st rRec hDead hInv0 .noneResp k1 k2 hCont
              | some ss =>
                have hIkOnCurve : onCurveKeyLocal P msg.hdr.ikAPk := onCurveKeyLocal_of_koskSenderOk
                  P hst.base.principals hst.base.advKeys msg.hdr.ikAPk (fun kv hkv => ⟨(hPrins kv
                  hkv).1, (hPrins kv hkv).2.1⟩) hAdvEq.2.2 hKosk
                have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.hdr.ikAPk) :=
                  computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                    msg.hdr.ikAPk ⟨hbSkLen, hbPk, hbTgt⟩ hIkOnCurve
                have hPos2 : FgPosRightRep P uSk (computeTwoSideOrPairPosPure P []
                  (erasePrincipalEntryFg uIdx k0 kEntry).secIKA0 msg.hdr.ekAPk kEntry.ikAPk)
                    (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) :=
                  computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP uIdx uSk k0 kEntry
                    msg.hdr.ekAPk ⟨hkSkLen, hkPk, hkTgt⟩ hEkOnCurve
                have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.hdr.ekAPk) :=
                  computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                    msg.hdr.ekAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEkOnCurve
                have hPosR : FgRootPosRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.ephAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.ephAPk) :=
                  fgRootPosRep_of_fgPosRightRep (computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep
                    P hP S bIdx vSk kb0 bEntry msg.ephAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEphOnCurve)
                have hTup : FgTupleRel R (computeTwoSideOrPairPosPure P [] (eraseSpkBundleEntryFg S
                  bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk) (computeTwoSideOrPairPosPure P
                  [] (erasePrincipalEntryFg uIdx k0 kEntry).secIKA0 msg.hdr.ekAPk kEntry.ikAPk)
                  (computeTwoSideOrPairPosPure P [] (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk
                  msg.hdr.ekAPk bEntry.spkPk) none (P.x25519 bEntry.spkSk msg.hdr.ikAPk) (P.x25519
                  kEntry.secIKA0 msg.hdr.ekAPk) (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                    none ss :=
                  ⟨hPos1, hPos2, hPos3, trivial, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
                unfold fgFinishRecvAuthPure fgFinishRecvStep2AuthPure
                simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
                  evalAuthHybridRecvSchedule_g3_true, erasePrincipalEntryFg_ikAPk,
                  eraseSpkBundleEntryFg_spkPk, hPrinEq, hTakePrin,
                  findHonestPrincipal_erasePrincipalsFg, bind_assoc, pure_bind]
                refine couple_fgPatch_and_fgRootPatch P hP R hvSk hCache hRootCache (by omega) (by
                  omega) hTup hPosR _ _ (fun drKey rk1 ck1_0 roCache' rootRoCache' fgL' fgRootL'
                  hCache' hRootCache' hFgLen' hRootLen' => ?_); dsimp only
                cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk
                    rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                | some spqr =>
                  rcases spqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                  cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?) (firstMsgAD
                    msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                  | none =>
                    simp only [StateT.run_pure, pure_bind]
                    exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk
                      rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                  | some pt =>
                    dsimp only; simp only [pure_bind]
                    cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | some sp =>
                      rcases sp with ⟨sIdx0, senderEntry⟩; dsimp only [Option.map]
                      cases !senderEntry.corrupted <;> (
                        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                          StateT.run_pure, pure_bind]
                        apply hCont .recvHonestResp
                        · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                        · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                            hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
                            hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
                            by dsimp; rw [hUsedEq], rfl⟩,
                            by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                            by dsimp; omega, by dsimp; omega, by dsimp; omega,
                            validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩)
                    | none =>
                      dsimp only [Option.map]
                      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                      apply hCont (.recvUnfreshResp drKey rk1 (P.chainKdfNext ck1_0) pt)
                      · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                      · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                          hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
                          hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
                          by dsimp; rw [hUsedEq], rfl⟩,
                          by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                          by dsimp; omega, by dsimp; omega, by dsimp; omega,
                          validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩
theorem fgAuthStepCoupling_dh1_recvOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) (rem : ℕ)
  (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh1 uIdx hst = false) (hInv :
  FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse ×
  AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont
  : ∀ r hst' st', deadAuthDh1 uIdx hst' = false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl true
  uIdx bIdx (some uSk) (some vSk) S P (.recvOPK k j o msg)).run hst >>= k1] {true} ≤
  𝒟[fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.recvOPK k j o msg) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk; have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hPrinEq : st.base.principals = erasePrincipalsFg uIdx hst.base.principals :=
    hBaseRel.principals_eq
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == k.val) =
    (hst.base.principals.find? (fun (idx, _) => idx == k.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hPrinEq]; exact find?_idx_erasePrincipalsFg uIdx k.val hst.base.principals
  have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
    (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
    rw [hBaseRel.spkBundles_eq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val)
      hst.base.spkBundles
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  have hUsedEq : st.base.usedRecvOPK = hst.base.usedRecvOPK := hBaseRel.usedRecvOPK_eq
  have hKybEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := hBaseRel.usedKyberTriples_eq
  have hTakePrin : (erasePrincipalsFg uIdx hst.base.principals).take S.N_dh =
      erasePrincipalsFg uIdx hst.base.principals :=
    List.take_of_length_le (by rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk := by
    rw [hPrinEq]
    exact koskSenderOkTake_erasePrincipalsFg_eq S P uIdx hst.base.principals st.advKeyPows
      hst.base.advKeys msg.hdr.ikAPk hLengths.1 hAdvEq.2.1
  let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl mkG3Hybrid fgAuthStepPure
    fgRunRecvOPKAuthPure
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, hSpkFind, hOpkEq, hUsedEq,
    hKybEq, hKoskEq, bind_assoc, pure_bind]
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
    msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st rRec
      hDead hInv0 .noneResp k1 k2 hCont
  · rcases hdr_lengths_of_guard_false (Bool.eq_false_iff.mpr hHdr) with ⟨hIkLen, hEkLen, hEphLen⟩
    simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.base.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
        rRec hDead hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
          rRec hDead hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
          exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst
            st rRec hDead hInv0 .noneResp k1 k2 hCont
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩; dsimp only [Option.map]
          rcases hPrins (k0, kEntry) (List.mem_of_find?_eq_some hFK) with ⟨hkSkLen, hkPk, hkTgt⟩
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst
              st rRec hDead hInv0 .noneResp k1 k2 hCont
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩; dsimp only [Option.map]
            rcases hSpks (kb0, bEntry) (List.mem_of_find?_eq_some hFB) with ⟨hbSkLen, hbPk, hbTgt⟩
            cases hFO : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
              with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem
                hst st rRec hDead hInv0 .noneResp k1 k2 hCont
            | some po =>
              rcases po with ⟨ko0, oEntry⟩; dsimp only
              rcases hOpks (ko0, oEntry) (List.mem_of_find?_eq_some hFO) with ⟨hoSkLen, hoPk⟩
              by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, StateT.run_pure, pure_bind]
                exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk rem
                  hst st rRec hDead hInv0 .noneResp k1 k2 hCont
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte, eraseSpkBundleEntryFg_pqspkSk]
                by_cases hRep : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk ||
                  !P.isCanonical msg.ephAPk) = true
                · simp only [hRep, ↓reduceIte, StateT.run_pure, pure_bind]
                  exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk
                    rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                · rcases canon_ek_eph_of_guard_false (Bool.eq_false_iff.mpr hRep) with ⟨hEkOnCurve,
                    hEphOnCurve⟩
                  simp only [hRep, Bool.false_eq_true, ↓reduceIte]
                  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none =>
                    simp only [StateT.run_pure, pure_bind]
                    exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk hvSk
                      rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                  | some ss =>
                    have hIkOnCurve : onCurveKeyLocal P msg.hdr.ikAPk :=
                      onCurveKeyLocal_of_koskSenderOk P hst.base.principals hst.base.advKeys
                      msg.hdr.ikAPk (fun kv hkv => ⟨(hPrins kv hkv).1, (hPrins kv hkv).2.1⟩)
                      hAdvEq.2.2 hKosk
                    have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.hdr.ikAPk) :=
                      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                        msg.hdr.ikAPk ⟨hbSkLen, hbPk, hbTgt⟩ hIkOnCurve
                    have hPos2 : FgPosRightRep P uSk (computeTwoSideOrPairPosPure P []
                      (erasePrincipalEntryFg uIdx k0 kEntry).secIKA0 msg.hdr.ekAPk kEntry.ikAPk)
                        (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) :=
                      computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep P hP uIdx uSk k0 kEntry
                        msg.hdr.ekAPk ⟨hkSkLen, hkPk, hkTgt⟩ hEkOnCurve
                    have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.hdr.ekAPk) :=
                      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                        msg.hdr.ekAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEkOnCurve
                    have hPos4 : FgOptRightRep P vSk (some (computeTwoSideOrPairPosPure P []
                      oEntry.opkSk msg.hdr.ekAPk oEntry.opkPk))
                        (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) := by
                      dsimp only [FgOptRightRep]
                      rw [computeTwoSideOrPairPosPure_nil_right_len32 P oEntry.opkSk msg.hdr.ekAPk
                        oEntry.opkPk hoSkLen]
                      exact ⟨hP.toWellFormedPrimitivesδ.x25519_len _ _, Or.inl rfl⟩
                    have hPosR : FgRootPosRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.ephAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.ephAPk) :=
                      fgRootPosRep_of_fgPosRightRep
                        (computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0
                        bEntry msg.ephAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEphOnCurve)
                    have hTup : FgTupleRel R (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk)
                      (computeTwoSideOrPairPosPure P [] (erasePrincipalEntryFg uIdx k0
                      kEntry).secIKA0 msg.hdr.ekAPk kEntry.ikAPk) (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                      (some (computeTwoSideOrPairPosPure P [] oEntry.opkSk msg.hdr.ekAPk
                      oEntry.opkPk)) (P.x25519 bEntry.spkSk msg.hdr.ikAPk) (P.x25519 kEntry.secIKA0
                      msg.hdr.ekAPk) (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss :=
                      ⟨hPos1, hPos2, hPos3, hPos4, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _
                        hDec⟩
                    have hValidOpk' : ValidOpkEntries S (hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                            (idx, e))) :=
                      (validOpkEntries_map_consumed S P (k.val, j.val, o.val) hst.base.opkEntries
                        hValidEc.2.2.1).1
                    have hOpks' : ∀ kv ∈ hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                          (idx, e)),
                        kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk := by
                      intro kv hkv; rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
                      have hO := hOpks (idx, e) heMem
                      by_cases hIdx : idx == (k.val, j.val, o.val) <;>
                        simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
                        (subst hEq; exact hO)
                    unfold fgFinishRecvAuthPure fgFinishRecvStep2AuthPure
                    simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                      monadLift_self, evalAuthHybridRecvSchedule_g3_true,
                      erasePrincipalEntryFg_ikAPk, eraseSpkBundleEntryFg_spkPk, hPrinEq, hTakePrin,
                      findHonestPrincipal_erasePrincipalsFg, bind_assoc, pure_bind]
                    refine couple_fgPatch_and_fgRootPatch P hP R hvSk hCache hRootCache (by omega)
                      (by omega) hTup hPosR _ _ (fun drKey rk1 ck1_0 roCache' rootRoCache' fgL'
                      fgRootL' hCache' hRootCache' hFgLen' hRootLen' => ?_); dsimp only
                    cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk
                        hvSk rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                    | some spqr =>
                      rcases spqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                      cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?) (firstMsgAD
                        msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                      | none =>
                        simp only [StateT.run_pure, pure_bind]
                        exact fgAuthStepCoupling_dh1_unchanged_resp S b P hP uIdx bIdx uSk vSk huSk
                          hvSk rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                      | some pt =>
                        dsimp only; simp only [pure_bind]
                        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                        | some sp =>
                          rcases sp with ⟨sIdx0, senderEntry⟩; dsimp only [Option.map]
                          cases !senderEntry.corrupted <;> (
                            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                              StateT.run_set, StateT.run_pure, pure_bind]
                            apply hCont .recvHonestResp
                            · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                            · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                                rfl, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
                                by dsimp; rw [hUsedEq], hBaseRel.usedRecvNoOPK_eq, rfl⟩,
                                by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                                by dsimp; omega, by dsimp; omega, by dsimp; omega,
                                ⟨hValidEc.1, hValidEc.2.1, hValidOpk', hValidEc.2.2.2⟩,
                                hPrins, hSpks, hOpks', hSess⟩)
                        | none =>
                          dsimp only [Option.map]
                          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                          apply hCont (.recvUnfreshResp drKey rk1 (P.chainKdfNext ck1_0) pt)
                          · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                          · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                              rfl, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
                              by dsimp; rw [hUsedEq], hBaseRel.usedRecvNoOPK_eq, rfl⟩,
                              by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                              by dsimp; omega, by dsimp; omega, by dsimp; omega,
                              ⟨hValidEc.1, hValidEc.2.1, hValidOpk', hValidEc.2.2.2⟩,
                              hPrins, hSpks, hOpks', hSess⟩
theorem fgAuthStepCoupling_dh1_send (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
  PreKeyBundleInput) (m0 m1 : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true uIdx (some uSk)
  S P sid u bundle m0 m1)).run hst >>= k1] {true} ≤ 𝒟[fgRunSendAuthPure P P.isValidDhTriple true
  uIdx S b.q_total
          (P.x25519Base uSk) sid u bundle m0 m1 st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk; have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hSecbEq : st.base.secb = hst.base.secb := hBaseRel.secb_eq
  have hPrinEq : st.base.principals = erasePrincipalsFg uIdx hst.base.principals :=
    hBaseRel.principals_eq
  have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
    (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hPrinEq]; exact find?_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  have hSpkEq : st.base.spkBundles = eraseSpkBundlesFg S bIdx hst.base.spkBundles :=
    hBaseRel.spkBundles_eq
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  have hUsedEq : st.base.usedSendSessions = hst.base.usedSendSessions :=
    hBaseRel.usedSendSessions_eq
  have hTakePrin : (erasePrincipalsFg uIdx hst.base.principals).take S.N_dh =
      erasePrincipalsFg uIdx hst.base.principals :=
    List.take_of_length_le (by rw [erasePrincipalsFg_length]; exact hLengths.1)
  have hKoskEq : koskBundleOkTake S P (erasePrincipalsFg uIdx hst.base.principals)
    (eraseSpkBundlesFg S bIdx hst.base.spkBundles) hst.base.opkEntries st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
          bundle :=
    koskBundleOkTake_erasePrin_eraseSpk_eq S P uIdx bIdx hst.base.principals hst.base.spkBundles
      hst.base.opkEntries st.advKeyPows hst.base.advKeys bundle hLengths.1 hLengths.2.1
      hLengths.2.2.1 hAdvEq.2.1
  by_cases hLen : (m0.length != m1.length) = true
  · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLen, ↓reduceIte, StateT.run_pure,
      pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  · have hLenF : (m0.length != m1.length) = false := Bool.eq_false_iff.mpr hLen
    by_cases hUsed : hst.base.usedSendSessions.contains sid = true
    · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsed,
        Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · have hUsedF : hst.base.usedSendSessions.contains sid = false := Bool.eq_false_iff.mpr hUsed
      cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF,
          hPrinFind, hFU, Option.map_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
          pure_bind]
        exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      | some pu =>
        rcases pu with ⟨u0, uEntry⟩
        rcases hPrins (u0, uEntry) (List.mem_of_find?_eq_some hFU) with ⟨huSkLen, huPk, huTgt⟩
        by_cases hUnf : (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
            | some (_, pEntry) => !pEntry.corrupted | none => false) && (m0 != m1)) = true
        · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF,
            hPrinFind, hFU, Option.map_some, hPrinEq, hTakePrin,
            findHonestPrincipal_erasePrincipalsFg, Bool.false_eq_true, ↓reduceIte, pure_bind]
          cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
          | none =>
            simp_all only [Option.map_none, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
          | some fp =>
            rcases fp with ⟨_, pEntry⟩
            simp_all only [Option.map_some, erasePrincipalEntryFg_corrupted, ↓reduceIte,
              StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
        · have hUnfF := Bool.eq_false_iff.mpr hUnf
          by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles
            hst.base.opkEntries hst.base.advKeys bundle) = true
          · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
            simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF,
              hPrinFind, hFU, Option.map_some, hPrinEq, hTakePrin,
              findHonestPrincipal_erasePrincipalsFg, hSpkEq, hOpkEq, hKoskEq, hKosk,
              Bool.false_eq_true, ↓reduceIte, pure_bind]
            cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
            | none =>
              simp_all only [Option.map_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                pure_bind]
              exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some fp =>
              rcases fp with ⟨_, pEntry⟩
              simp_all only [Option.map_some, erasePrincipalEntryFg_corrupted, Bool.false_eq_true,
                ↓reduceIte, StateT.run_pure, pure_bind]
              exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
          · have hKoskF := Bool.eq_false_iff.mpr hKosk
            have hKoskT : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
                hst.base.advKeys bundle = true := by
              simpa using hKoskF
            have hSpkReg : (isGameSpk P hst.base.spkBundles bundle.spkB || isAdvRegistered P
                hst.base.advKeys bundle.spkB) = true := by
              unfold koskBundleOk at hKoskT
              exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKoskT).1).2
            rw [fgPreAuthSendHybrid_run_eq_afterCoins true uIdx (some uSk) P sid u bundle m0 m1 hst
              hLenF hUsedF uEntry ⟨u0, hFU⟩ hUnfF hKoskT]
            have hIte : ∀ {α : Type} {c : Prop} [inst : Decidable c] (x y : α), ¬ c → @ite α c inst
                x y = y := by
              intro _ _ inst _ _ h
              cases inst with | isFalse _ => rfl | isTrue hp => exact False.elim (h hp)
            unfold fgRunSendAuthPure sampleAuthSendCoins
            simp only [hLenF, hUsedEq, hUsedF, hPrinFind, hFU, Option.map_some, hPrinEq, hTakePrin,
              hSpkEq, hOpkEq, hKoskEq, hKoskF, hSecbEq, erasePrincipalEntryFg_ikAPk,
              resolveSigPk_erasePrincipalsFg, findHonestPrincipal_erasePrincipalsFg_isSome,
              Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            rw [hIte _ _ (by
              rw [findHonestPrincipal_erasePrincipalsFg]
              cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
              | none => simp_all
              | some fp => rcases fp with ⟨_, pEntry⟩; simp_all [erasePrincipalEntryFg_corrupted])]
            simp only [bind_assoc]
            refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekASk hEk => ?_)
            have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hEk
            refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
            refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ephASk hEph => ?_)
            have hEphLen : ephASk.length = 32 := length_of_mem_support_sampleScalar32 hEph
            refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun spqrCoins _ => ?_)
            unfold fgPreAuthSendAfterCoins; dsimp only
            by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
              bundle.spkB) bundle.spkSig && P.sigVerify (resolveSigPk P hst.base.principals
              bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [hSig, ↓reduceIte, pure_bind]
              exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
              cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                simp only [pure_bind]
                exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst
                  st hDead hInv0 .noneResp k1 k2 hCont
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩; dsimp only
                let spkSk := lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
                    st.advKeyPows bundle.spkB
                have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P
                  (erasePrincipalEntryFg uIdx u0 uEntry).secIKA0 spkSk uEntry.ikAPk bundle.spkB)
                    (P.x25519 uEntry.secIKA0 bundle.spkB) :=
                  computeTwoSideOrPairPosPure_erasePrin_lookupSpkSkTake_fgPosRightRep S P hP uIdx
                    bIdx uSk vSk hst.base.spkBundles st.advKeyPows hst.base.advKeys u0 uEntry
                    bundle.spkB ⟨huSkLen, huPk, huTgt⟩ hSpks hLengths.2.1 hAdvEq.2.1 hAdvEq.2.2
                    hSpkReg
                have hPos2 : FgPosRightRep P uSk (computeTwoSideOrPairPosPure P ekASk []
                  (P.x25519Base ekASk) bundle.ikB)
                    (P.x25519 ekASk bundle.ikB) := by
                  rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] (P.x25519Base ekASk)
                    bundle.ikB hEkLen]
                  exact R.sec2 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P ekASk []
                  (P.x25519Base ekASk) bundle.spkB)
                    (P.x25519 ekASk bundle.spkB) := by
                  rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] (P.x25519Base ekASk)
                    bundle.spkB hEkLen]
                  exact R.sec3 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                have hPos4 : FgOptRightRep P vSk (computeOptPosPure P ekASk (P.x25519Base ekASk)
                  (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk))))
                    (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) :=
                  computeOptPosPure_left_len32_fgOptRightRep P hP.toWellFormedPrimitivesδ vSk ekASk
                    (P.x25519Base ekASk) hEkLen bundle.opkB?
                have hPosR : FgRootPosRep P vSk (mkSecretPosPure P (P.x25519 ephASk bundle.spkB))
                    (P.x25519 ephASk bundle.spkB) :=
                  fgRootPosRep_mkSecret P vSk _
                have hTup : FgTupleRel R (computeTwoSideOrPairPosPure P (erasePrincipalEntryFg uIdx
                  u0 uEntry).secIKA0 spkSk uEntry.ikAPk bundle.spkB) (computeTwoSideOrPairPosPure P
                  ekASk [] (P.x25519Base ekASk) bundle.ikB) (computeTwoSideOrPairPosPure P ekASk []
                  (P.x25519Base ekASk) bundle.spkB) (computeOptPosPure P ekASk (P.x25519Base ekASk)
                  (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))) (P.x25519 uEntry.secIKA0
                  bundle.spkB) (P.x25519 ekASk bundle.ikB) (P.x25519 ekASk bundle.spkB)
                    (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss :=
                  ⟨hPos1, hPos2, hPos3, hPos4, (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _
                    hEnc).1⟩
                simp only [bind_assoc]
                refine couple_fgPatch_and_fgRootPatch P hP R hvSk hCache hRootCache (by omega) (by
                  omega) hTup hPosR _ _ (fun drKey rk1 ck1_0 roCache' rootRoCache' fgL' fgRootL'
                  hCache' hRootCache' hFgLen' hRootLen' => ?_); dsimp only
                cases P.spqrInitSend drKey.pqrKey spqrCoins with
                | none =>
                  simp only [pure_bind]
                  exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem
                    hst st hDead hInv0 .noneResp k1 k2 hCont
                | some spqr =>
                  rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                  simp only [pure_bind]; rw [findHonestPrincipal_erasePrincipalsFg]
                  cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
                  | none =>
                    simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
                    apply hCont _
                    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                    · refine ⟨⟨rfl, rfl, rfl,
                        rfl, ?_, rfl,
                        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
                          hBaseRel.usedKyberTriples_eq⟩,
                        hRespEq, hAdvEq, hCache', hRootCache',
                        by dsimp; omega, by dsimp; omega, by dsimp; omega,
                        validAuthEcFg_cons_session hValidEc hSend hUsedF rfl rfl rfl rfl rfl rfl,
                        hPrins, hSpks, hOpks, ?_⟩
                      · dsimp only; rw [hBaseRel.sessions_eq]
                        unfold eraseAuthSessionsOptFg eraseAuthSessionEntryOptFg
                          checkBundleProvenanceExact
                        simp [hFP]
                      · intro s hs; rcases List.mem_cons.mp hs with rfl | hMem
                        · exact ⟨hEkLen, hEphLen⟩
                        · exact hSess s hMem
                  | some fp =>
                    rcases fp with ⟨k, pEntry⟩
                    simp only [Option.map_some, Option.isSome_some, erasePrincipalEntryFg_corrupted,
                      ↓reduceIte]
                    apply hCont _
                    · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
                    · refine ⟨⟨rfl, rfl, rfl,
                        rfl, ?_, rfl,
                        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
                          hBaseRel.usedKyberTriples_eq⟩,
                        hRespEq, hAdvEq, hCache', hRootCache',
                        by dsimp; omega, by dsimp; omega, by dsimp; omega,
                        validAuthEcFg_cons_session hValidEc hSend hUsedF rfl rfl rfl rfl rfl rfl,
                        hPrins, hSpks, hOpks, ?_⟩
                      · dsimp only; rw [hBaseRel.sessions_eq]
                        unfold eraseAuthSessionsOptFg eraseAuthSessionEntryOptFg
                          checkBundleProvenanceExact
                        simp [hFP]
                      · intro s hs; rcases List.mem_cons.mp hs with rfl | hMem
                        · exact ⟨hEkLen, hEphLen⟩
                        · exact hSess s hMem
theorem fgAuthStepCoupling_dh1 (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh1 uIdx hst = false) (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk
  hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 :
  AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh1 uIdx hst' =
  false → FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true}
  ≤ 𝒟[k2 (r, st')] {true}) (hDeadCont : ∀ r hst', deadAuthDh1 uIdx hst' = true → 𝒟[k1 (r, hst')]
  {true} = 0) : 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
  {true} ≤ 𝒟[(fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hFind0 : st.base.principals.find? (fun (u, _) => u == uIdx) = (hst.base.principals.find? (fun
    (u, _) => u == uIdx)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
    rw [hInv.1.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx uIdx hst.base.principals
  have hCorrF : isTargetPrinCorrupted uIdx st = false := by
    unfold isTargetPrinCorrupted; unfold deadAuthDh1 at hDead; rw [hFind0]
    cases hF : hst.base.principals.find? (fun (u, _) => u == uIdx) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, _⟩; rw [hF] at hDead; simpa [erasePrincipalEntryFg_corrupted] using hDead
  have hRhs : (fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total (P.x25519Base uSk)
    (P.x25519Base vSk) q).run st = fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q st := by
    unfold fgAuthSimImpl fgAuthStepHalt; simp [hCorrF]
  rw [hRhs]; cases q with
  | initPrin u =>
    exact fgAuthStepCoupling_dh1_initPrin S b P hP uIdx bIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont
  | corruptIK u =>
    exact fgAuthStepCoupling_dh1_corruptIK S b P hP uIdx bIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont hDeadCont
  | genSPK u j =>
    exact fgAuthStepCoupling_dh1_genSPK S b P hP uIdx bIdx uSk vSk huSk hvSk u j rem hst st hDead
      hInv k1 k2 hCont
  | genOPK u j o =>
    exact fgAuthStepCoupling_dh1_genOPK S b P hP uIdx bIdx uSk vSk huSk hvSk u j o rem hst st hDead
      hInv k1 k2 hCont
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl fgAuthStepPure; cases hOpt : bundle.opkB?.isNone
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isNone then return .noneResp
          fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendOPK u i) u bundle m0 m1)).run
            hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq]; simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
      exact fgAuthStepCoupling_dh1_send S b P hP uIdx bIdx uSk vSk huSk hvSk (.sendOPK u i) trivial
        u bundle m0 m1 rem hst st hDead hInv k1 k2 hCont
    · unfold liftAuthFgHybrid mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpt, ↓reduceIte, StateT.run_pure,
        pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl fgAuthStepPure; cases hOpt : bundle.opkB?.isSome
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isSome then return .noneResp
          fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendNoOPK u i) u bundle m0
            m1)).run hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true true uIdx (some uSk) S P (.sendNoOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq]; simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
      exact fgAuthStepCoupling_dh1_send S b P hP uIdx bIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle m0 m1 rem hst st hDead hInv k1 k2 hCont
    · unfold liftAuthFgHybrid mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpt, ↓reduceIte, StateT.run_pure,
        pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | recvOPK k j o msg =>
    exact fgAuthStepCoupling_dh1_recvOPK S b P hP uIdx bIdx uSk vSk huSk hvSk k j o msg rem hst st
      hDead hInv k1 k2 hCont
  | recvNoOPK k j l msg =>
    exact fgAuthStepCoupling_dh1_recvNoOPK S b P hP uIdx bIdx uSk vSk huSk hvSk k j l msg rem hst st
      hDead hInv k1 k2 hCont
  | roQuery secrets =>
    exact fgAuthStepCoupling_dh1_roQuery S b P hP uIdx bIdx uSk vSk huSk hvSk secrets rem hst st
      hDead hInv k1 k2 hCont
  | roRootQuery rk dh =>
    exact fgAuthStepCoupling_dh1_roRootQuery S b P hP uIdx bIdx uSk vSk huSk hvSk rk dh rem hst st
      hDead hInv k1 k2 hCont
  | revealDhSecrets =>
    have hInv0 := hInv
    change 𝒟[(liftAuthFgHybrid
      (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P
          .revealDhSecrets))).run hst >>= k1] {true} ≤ _
    rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  | registerKey sk =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
      hValidEc, hPrins, hSpks, hOpks, hSess⟩
    change 𝒟[(liftAuthFgHybrid
      (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true S P (.registerKey
          sk)))).run hst >>= k1] {true} ≤ _
    rw [liftAuthFgHybrid_liftAuthBase_eq]
    unfold liftAuthFgBase pqxdhAuthImpl registerAdvKey fgAuthStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    by_cases hLen : (sk.length != 32) = true
    · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh1_unchanged S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · have hSkLen32 : sk.length = 32 := by
        cases hEq : (sk.length == 32)
        · simp [bne, hEq] at hLen
        · exact beq_iff_eq.mp hEq
      simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind]
      apply hCont (.pkResp (P.x25519Base sk))
      · rw [deadAuthDh1_eq_of_principals uIdx rfl]; exact hDead
      · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
          hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
          hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
          hRespEq, ⟨hAdvEq.1, by dsimp; rw [hAdvEq.2.1]; rfl, ?_⟩,
          hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
          validAuthEcFg_of_fields_eq hValidEc, hPrins, hSpks, hOpks, hSess⟩
        intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hSkLen32, rfl⟩
        · exact hAdvEq.2.2 kv hMem
/-! ## Sticky-latch `DH1` `GapDH` bound -/
theorem initAuthDh1Cand_eq_corrupt {S : Setup} (P : Primitives) (uVal : ℕ) (principals : List (Nat ×
  PrincipalEntry)) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (advKeyPows : List (Bytes ×
  Bytes)) : initAuthDh1Cand S P (principals.map (fun (idx, e) =>
      if idx == uVal then (idx, { e with corrupted := true }) else (idx, e)))
      spkBundles advKeyPows = initAuthDh1Cand S P principals spkBundles advKeyPows := by
  funext s; unfold initAuthDh1Cand; rw [lookupSenderIkPk_map_corrupt]
theorem pureExtractCdhFromAuthSimState_corruptIK_eq {S : Setup} (P : Primitives) (ddh : Bytes →
  Bytes → Bytes → Bool) (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (uVal : ℕ) (st : FgAuthSimState
  S) : pureExtractCdhFromAuthSimState S P ddh useDh1 maxLen U V
      { st with base := { st.base with principals := st.base.principals.map (fun (idx, e) =>
          if idx == uVal then (idx, { e with corrupted := true }) else (idx, e)) } } =
    pureExtractCdhFromAuthSimState S P ddh useDh1 maxLen U V st := by
  unfold pureExtractCdhFromAuthSimState; dsimp only; rw [initAuthDh1Cand_eq_corrupt]
theorem isTargetPrinCorrupted_map_corrupted_eq_true_of_eq {S : Setup} (uIdx u : ℕ) (hEq : (u ==
  uIdx) = true) (st : FgAuthSimState S) (u0 : ℕ) (entry : PrincipalEntry) (hF :
  st.base.principals.find? (fun (idx, _) => idx == u) = some (u0, entry)) :
    isTargetPrinCorrupted uIdx { st with base := { st.base with
      principals := st.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } = true :=
  deadAuthDh1_map_corrupted_eq_true_of_eq uIdx u hEq
    { base := st.base, advRoLog := [], respRecs := [] } u0 entry hF
theorem evalDist_bind_true_eq_const_of_support {α : Type} (mx : ProbComp α) (k : α → ProbComp Bool)
  (c : ℝ≥0∞) (h : ∀ x ∈ support mx, 𝒟[k x] {true} = c) :
    𝒟[mx >>= k] {true} = c := by
  rw [evalDist_bind_true_eq_probExpect_comp]; refine le_antisymm ?_ ?_
  · refine le_trans (probExpect_mono_of_support _ _ (fun _ => c) (fun x hx => le_of_eq (h x hx)))
      ?_; simp [probExpect_const]
  · refine le_trans ?_ (probExpect_mono_of_support _ (fun _ => c) _ (fun x hx => le_of_eq (h x
      hx).symm)); simp [probExpect_const]
theorem evalDist_simulateQ_fgAuthSimImpl_halted {S : Setup} (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (uIdx bIdx maxLen : ℕ) (U V : Bytes) {α : Type} (oa : OracleComp (unifSpec +
  authSpec S) α) (obs : FgAuthSimState S → ProbComp Bool) (st : FgAuthSimState S) (hCorr :
  isTargetPrinCorrupted uIdx st = true) :
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (FgAuthSimState S)
        ProbComp) + fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V
    𝒟[(simulateQ full2 oa).run st >>= fun x => obs x.2] {true} = 𝒟[obs st] {true} := by
  intro full2; induction oa using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full2]; rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_const_of_support _ _ (𝒟[obs st] {true}) (fun u _ => ih u)
    · dsimp only [full2]
      have hHalt : (fgAuthSimImpl P ddh true uIdx bIdx S maxLen U V gq).run st =
          pure (.noneResp, st) := by unfold fgAuthSimImpl fgAuthStepHalt; simp [hCorr]
      rw [simulateQ_run_query_inr, hHalt, pure_bind]; exact ih .noneResp
theorem evalDist_simulateQ_le_of_step_or_dead_or_halt {ι α St1 St2 : Type} {QSpec : OracleSpec.{0,
  0} ι} (Dead : St1 → Bool) (Halted : St2 → Bool) (Rel : ℕ → St1 → St2 → Prop) (impl1 : QueryImpl
  QSpec (StateT St1 ProbComp)) (impl2 : QueryImpl QSpec (StateT St2 ProbComp)) (obs1 : α × St1 →
  ProbComp Bool) (obs2 : St2 → ProbComp Bool) (hDeadPres : ∀ q s1, Dead s1 = true → ∀ x ∈ support
  ((impl1 q).run s1), Dead x.2 = true) (hHaltEq : ∀ {β : Type} (oa : OracleComp (unifSpec + QSpec)
  β) (s2 : St2), Halted s2 = true →
      let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
      𝒟[(simulateQ full2 oa).run s2 >>= fun x => obs2 x.2] {true} = 𝒟[obs2 s2] {true})
    (hStep : ∀ (q : ι) (rem : ℕ) (s1 : St1) (s2 : St2), Dead s1 = false → Rel (rem + 1) s1 s2 → ∀
      (k1 : QSpec.Range q × St1 → ProbComp Bool) (k2 : QSpec.Range q × St2 → ProbComp Bool), (∀ r
      s1' s2', Dead s1' = false → Rel rem s1' s2' → 𝒟[k1 (r, s1')] {true} ≤ 𝒟[k2 (r, s2')] {true}) →
      (∀ r s1', Dead s1' = true → 𝒟[k1 (r, s1')] {true} = 0) → (∀ r s2', Halted s2' = true → 𝒟[k2
      (r, s2')] {true} = 𝒟[obs2 s2'] {true}) → 𝒟[(impl1 q).run s1 >>= k1] {true} ≤ 𝒟[(impl2 q).run
      s2 >>= k2] {true})
    (hDeadObs : ∀ a s1, Dead s1 = true → 𝒟[obs1 (a, s1)] {true} = 0)
    (hObs : ∀ a rem s1 s2, Dead s1 = false → Rel rem s1 s2 → 𝒟[obs1 (a, s1)] {true} ≤ 𝒟[obs2 s2]
      {true})
    (oa : OracleComp (unifSpec + QSpec) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ ι => isGameQuery q = true) rem)
    (s1 : St1) (s2 : St2) (hRel : Rel rem s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run s1 >>= obs1] {true} ≤
      𝒟[(simulateQ full2 oa).run s2 >>= fun x => obs2 x.2] {true} := by
  intro full1 full2; induction oa using OracleComp.inductionOn generalizing rem s1 s2 with
  | pure a =>
    by_cases hD : Dead s1 = true
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind, hDeadObs a s1 hD, zero_le]
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs a rem s1 s2 (Bool.eq_false_iff.mpr hD) hRel
  | query_bind q mx ih =>
    by_cases hD : Dead s1 = true
    · rw [evalDist_simulateQ_eq_zero_of_dead_preserved Dead impl1 hDeadPres obs1 hDeadObs _ s1 hD]
      exact zero_le
    · have hDF : Dead s1 = false := Bool.eq_false_iff.mpr hD
      rw [isQueryBoundP_query_bind_iff] at hQb; rcases q with uq | gq
      · rcases hQb with ⟨_, hCont⟩; simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
        dsimp only [full1, full2]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ => ih u rem (hCont u) s1 s2 hRel)
      · rcases hQb with ⟨hAbs | hPos, hCont⟩
        · exfalso; exact hAbs rfl
        · obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at hCont
          dsimp only [full1, full2]
          rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
          exact hStep gq rem' s1 s2 hDF hRel (fun x => (simulateQ full1 (mx x.1)).run x.2 >>= obs1)
            (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= fun y => obs2 y.2) (fun r s1' s2' hDF'
            hRel' => ih r rem' (hCont r) s1' s2' hRel') (fun r s1' hDT =>
            evalDist_simulateQ_eq_zero_of_dead_preserved Dead impl1 hDeadPres obs1 hDeadObs (mx r)
            s1' hDT) (fun r s2' hHT => hHaltEq (mx r) s2' hHT)
def deadAndUnlatchedDh1 {S : Setup} (uIdx bIdx : ℕ) (hst : AuthFgCutoffState S) : Bool :=
  deadAuthDh1 uIdx hst && !hst.latchedDh1.contains (uIdx, bIdx)
def FgAuthSimInvDh1Latched (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuthSimState S) : Prop :=
  FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst st ∧
  hst.latchedDh1.contains (uIdx, bIdx) = false
theorem badAuthFgDh1LatchedAt_eq_false_of_deadAndUnlatchedDh1 {S : Setup} (P : Primitives) (maxLen
  uIdx bIdx : ℕ) (hst : AuthFgCutoffState S) (hD : deadAndUnlatchedDh1 uIdx bIdx hst = true) :
    badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst = false := by
  unfold deadAndUnlatchedDh1 at hD; rcases Bool.and_eq_true_iff.mp hD with ⟨hDead, hNotC⟩
  have hC : hst.latchedDh1.contains (uIdx, bIdx) = false := by
    cases h : hst.latchedDh1.contains (uIdx, bIdx) with
    | false => rfl | true => rw [h] at hNotC; cases hNotC
  have hAt := badAuthFgDh1At_eq_false_of_deadAuthDh1 P maxLen uIdx bIdx hst hDead
  unfold badAuthFgDh1LatchedAt; rw [hC, hAt]; rfl
theorem contains_latchDh1ForPrincipal_of_false {S : Setup} (P : Primitives) (uIdx bIdx : ℕ) (st :
  AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) (latched : List (Nat × Nat))
  (hFalse : badAuthFgDh1At P advRoLog.length uIdx bIdx st advRoLog respRecs = false) :
  (latchDh1ForPrincipal S P uIdx st advRoLog respRecs latched).contains (uIdx, bIdx) =
      latched.contains (uIdx, bIdx) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem, mem_latchDh1ForPrincipal_iff]
  refine ⟨fun h => ?_, fun hL => Or.inr hL⟩
  rcases h with ⟨_, _, hBad⟩ | hL; · rw [hFalse] at hBad; cases hBad
  · exact hL
theorem contains_latchDh1ForPrincipal_of_deadAuthDh1 {S : Setup} (P : Primitives) (uVal uIdx bIdx :
  ℕ) (hst : AuthFgCutoffState S) (hDead : deadAuthDh1 uIdx hst = true) : (latchDh1ForPrincipal S P
  uVal hst.base hst.advRoLog hst.respRecs
      hst.latchedDh1).contains (uIdx, bIdx) = hst.latchedDh1.contains (uIdx, bIdx) := by
  by_cases hEq : uIdx = uVal
  · subst hEq; exact contains_latchDh1ForPrincipal_of_false P uIdx bIdx hst.base hst.advRoLog
      hst.respRecs hst.latchedDh1 (badAuthFgDh1AtCore_eq_false_of_deadAuthDh1 P _ uIdx bIdx _ hDead)
  · exact contains_latchDh1ForPrincipal_of_ne P hEq bIdx hst.base hst.advRoLog hst.respRecs _
theorem pqxdhAuthFgPreImpl_preserves_latchedDh1 {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx
  : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives) (q : AuthQuery S) (hst : AuthFgCutoffState S)
  (x : AuthResponse × AuthFgCutoffState S) (hx : x ∈ support ((pqxdhAuthFgPreImpl useDh1 targetIdx
  targetSpkIdx optUsk optVsk S P q).run hst)) :
    x.2.latchedDh1 = hst.latchedDh1 := by
  cases q <;> (
    unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl liftAuthFgHybrid at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      at hx; rcases hx with ⟨_, _, rfl⟩; rfl)
theorem pqxdhAuthFgLatchedPreImpl_preserves_deadAndUnlatchedDh1 {S : Setup} (P : Primitives) (uIdx
  bIdx : ℕ) (uSk vSk : Bytes) (q : AuthQuery S) (hst : AuthFgCutoffState S) (hD :
  deadAndUnlatchedDh1 uIdx bIdx hst = true) : ∀ x ∈ support ((pqxdhAuthFgLatchedPreImpl true uIdx
  bIdx (some uSk) (some vSk) S P q).run hst),
      deadAndUnlatchedDh1 uIdx bIdx x.2 = true := by
  unfold deadAndUnlatchedDh1 at hD; rcases Bool.and_eq_true_iff.mp hD with ⟨hDead, hNotC⟩
  intro x hx
  rcases exists_support_pqxdhAuthFgPreImpl_of_latched true uIdx bIdx (some uSk) (some vSk) P q hst x
    hx with ⟨x0, hx0, _, hBaseEq, _, _⟩
  have hDead0 := pqxdhAuthFgPreImpl_preserves_deadAuthDh1 P uIdx bIdx uSk vSk q hst hDead x0 hx0
  have hDeadX : deadAuthDh1 uIdx x.2 = true := by
    rw [deadAuthDh1_eq_of_principals uIdx (congrArg AuthState.principals hBaseEq.symm)]
    exact hDead0
  cases q with
  | corruptIK u =>
    unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgLatchedImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      at hx
    rcases hx with ⟨_, _, rfl⟩; unfold deadAndUnlatchedDh1; rw [hDeadX, Bool.true_and]; dsimp only
    rw [contains_latchDh1ForPrincipal_of_deadAuthDh1 P u.val uIdx bIdx hst hDead]; exact hNotC
  | _ =>
    have hL := pqxdhAuthFgPreImpl_preserves_latchedDh1 true uIdx bIdx (some uSk) (some vSk) P _ hst
      x hx
    unfold deadAndUnlatchedDh1; rw [hDeadX, hL, hNotC]; rfl
theorem fgAuthStepCoupling_dh1_of_bind_unlatched (S : Setup) (b : QueryBudget) (P : Primitives) (hP
  : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (latched' : List (Nat × Nat)) (hUnl' : latched'.contains (uIdx, bIdx) = false) (k1 : AuthResponse
  × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool)
  (hBind : 𝒟[(pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
  {true} ≤ 𝒟[(pqxdhAuthFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>=
        fun p => k1 (p.1, { p.2 with latchedDh1 := latched' })] {true})
    (hDead : deadAuthDh1 uIdx hst = false)
    (hInv : FgAuthSimInvDh1 S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false → FgAuthSimInvDh1Latched S b P
      hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true}
      ≤ 𝒟[(fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  refine le_trans hBind (fgAuthStepCoupling_dh1 S b P hP uIdx bIdx uSk vSk huSk hvSk
    q rem hst st hDead hInv (fun p => k1 (p.1, { p.2 with latchedDh1 := latched' })) k2 ?_ ?_)
  · intro r hst' st' hDF hI; refine hCont r { hst' with latchedDh1 := latched' } st' ?_ ⟨hI, hUnl'⟩
    unfold deadAndUnlatchedDh1; dsimp only
    rw [show deadAuthDh1 uIdx { hst' with latchedDh1 := latched' } = deadAuthDh1 uIdx hst' from rfl,
      hDF, Bool.false_and]
  · intro r hst' hDT; refine hDeadCont r { hst' with latchedDh1 := latched' } ?_
    unfold deadAndUnlatchedDh1; dsimp only
    rw [show deadAuthDh1 uIdx { hst' with latchedDh1 := latched' } = deadAuthDh1 uIdx hst' from rfl,
      hDT, hUnl']; rfl
theorem fgAuthStepCoupling_dh1_latched (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDeadU : deadAndUnlatchedDh1 uIdx bIdx hst = false) (hInvL : FgAuthSimInvDh1Latched S b P hP uIdx
  bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
  (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAndUnlatchedDh1
  uIdx bIdx hst' = false → FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst'
  st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) (hDeadCont : ∀ r hst', deadAndUnlatchedDh1
  uIdx bIdx hst' = true → 𝒟[k1 (r, hst')] {true} = 0) (hHaltCont : ∀ r st', isTargetPrinCorrupted
  uIdx st' = true → 𝒟[k2 (r, st')] {true} = 𝒟[(pure (P.pow8 (pureExtractCdhFromAuthSimState S P
  P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) st') == P.pow8 (P.x25519
  uSk (P.x25519Base vSk))) : ProbComp Bool)] {true}) : 𝒟[(pqxdhAuthFgLatchedPreImpl true uIdx bIdx
  (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤ 𝒟[(fgAuthSimImpl P P.isValidDhTriple true
  uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hDead : deadAuthDh1 uIdx hst = false := by
    unfold deadAndUnlatchedDh1 at hDeadU; rw [hInvL.2, Bool.not_false, Bool.and_true] at hDeadU
    exact hDeadU
  cases q with
  | corruptIK u =>
    let latched' := latchDh1ForPrincipal S P u.val hst.base hst.advRoLog hst.respRecs hst.latchedDh1
    cases hL : latched'.contains (uIdx, bIdx) with
    | false =>
      refine fgAuthStepCoupling_dh1_of_bind_unlatched S b P hP uIdx bIdx uSk vSk huSk hvSk
        (.corruptIK u) rem hst st latched' hL k1 k2 (le_of_eq (congrArg (fun m => 𝒟[m] {true}) ?_))
        hDead hInvL.1 hCont hDeadCont
      unfold pqxdhAuthFgLatchedPreImpl pqxdhAuthFgLatchedImpl pqxdhAuthFgPreImpl pqxdhAuthFgImpl
      simp; rfl
    | true =>
      have hMemL := (mem_latchDh1ForPrincipal_iff P u.val hst.base hst.advRoLog hst.respRecs
        hst.latchedDh1 uIdx bIdx).mp (List.contains_iff_mem.mp hL)
      have hNotOld : (uIdx, bIdx) ∉ hst.latchedDh1 := fun hm => by
        have h := hInvL.2; rw [List.contains_iff_mem.mpr hm] at h; cases h
      rcases hMemL with ⟨huEq, _, hBadNow⟩ | hOld
      · subst huEq
        have hPrinFind : st.base.principals.find? (fun (idx, _) => idx == u.val) =
          (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
              (fun (idx, e) => (idx, erasePrincipalEntryFg u.val idx e)) := by
          rw [hInvL.1.1.principals_eq]; exact find?_idx_erasePrincipalsFg u.val u.val _
        have hCorrF : isTargetPrinCorrupted u.val st = false := by
          unfold isTargetPrinCorrupted; unfold deadAuthDh1 at hDead; rw [hPrinFind]
          cases hF : hst.base.principals.find? (fun (u0, _) => u0 == u.val) with
          | none => rfl | some p =>
            rcases p with ⟨_, _⟩; rw [hF] at hDead
            simpa [erasePrincipalEntryFg_corrupted] using hDead
        have hRhs : (fgAuthSimImpl P P.isValidDhTriple true u.val bIdx S b.q_total (P.x25519Base
          uSk) (P.x25519Base vSk) (.corruptIK u)).run st = fgAuthStepPure P P.isValidDhTriple true
          u.val bIdx S b.q_total
              (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st := by
          unfold fgAuthSimImpl fgAuthStepHalt; simp [hCorrF]
        rw [hRhs]; cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none => unfold badAuthFgDh1At at hBadNow; rw [hF] at hBadNow; cases hBadNow
        | some p =>
          rcases p with ⟨u0, entry⟩
          have hFSt : st.base.principals.find? (fun (idx, _) => idx == u.val) =
              some (u0, erasePrincipalEntryFg u.val u0 entry) := by rw [hPrinFind, hF]; rfl
          unfold fgAuthStepPure; dsimp only; rw [hFSt]; dsimp only; simp only [pure_bind]
          let st' : FgAuthSimState S := { st with base := { st.base with
              principals := st.base.principals.map (fun (idx, e) =>
                if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } }
          have hCorr' : isTargetPrinCorrupted u.val st' = true :=
            isTargetPrinCorrupted_map_corrupted_eq_true_of_eq u.val u.val (beq_self_eq_true u.val)
            st u0 (erasePrincipalEntryFg u.val u0 entry) hFSt
          rw [hHaltCont _ st' hCorr', pureExtractCdhFromAuthSimState_corruptIK_eq P
            P.isValidDhTriple true b.q_total (P.x25519Base uSk) (P.x25519Base vSk) u.val st]
          have hTerm := fgAuthSimInvDh1_terminal_le S b P hP hst.advRoLog.length u.val bIdx uSk vSk
            huSk hvSk true (rem + 1) hst st hDead hInvL.1
          have hBadCore : badAuthFgDh1AtCore P hst.advRoLog.length u.val bIdx
              hst.base hst.advRoLog hst.respRecs = true := hBadNow
          rw [hBadCore] at hTerm
          exact le_trans MeasureTheory.prob_le_one (le_trans (by simp) hTerm)
      · exact False.elim (hNotOld hOld)
  | _ =>
    refine fgAuthStepCoupling_dh1_of_bind_unlatched S b P hP uIdx bIdx uSk vSk huSk hvSk _ rem hst
      st hst.latchedDh1 hInvL.2 k1 k2 ?_ hDead hInvL.1 hCont hDeadCont
    refine evalDist_bind_true_mono_of_support _ _ _ (fun x hx => ?_)
    have hL := pqxdhAuthFgPreImpl_preserves_latchedDh1 true uIdx bIdx (some uSk) (some vSk) P _ hst
      x hx
    have hEta : { x.2 with latchedDh1 := hst.latchedDh1 } = x.2 := by rw [← hL]
    rw [hEta]
theorem prob_badAuthFgDh1LatchedAt_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b) (uIdx : ℕ) (_huIdx : uIdx ∈
  Finset.range S.N_id) (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
  (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x => pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)]
  {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt true uIdx bIdx S b A) := by
  unfold GapDH; refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runAuthFgLatchedSim_eq_preSample_dh1 uIdx bIdx P A.1 (fun x => pure
    (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2.2)), gapDhExp_fgAuthGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  let obs2 : FgAuthSimState S → ProbComp Bool := fun s2 => pure (P.pow8
      (pureExtractCdhFromAuthSimState S P P.isValidDhTriple true b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk) s2) == P.pow8 (P.x25519 uSk (P.x25519Base vSk)))
  exact evalDist_simulateQ_le_of_step_or_dead_or_halt (deadAndUnlatchedDh1 uIdx bIdx)
      (isTargetPrinCorrupted uIdx) (FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huLen hvLen)
      (pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) (some vSk) S P) (fgAuthSimImpl P
      P.isValidDhTriple true uIdx bIdx S b.q_total (P.x25519Base uSk) (P.x25519Base vSk)) (fun x =>
      pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx x.2)) obs2 (fun q s1 hD x hx =>
      pqxdhAuthFgLatchedPreImpl_preserves_deadAndUnlatchedDh1 P uIdx bIdx uSk vSk q s1 hD x hx) (fun
      oa s2 hCorr => evalDist_simulateQ_fgAuthSimImpl_halted P P.isValidDhTriple uIdx bIdx b.q_total
      (P.x25519Base uSk) (P.x25519Base vSk) oa obs2 s2 hCorr) (fun q rem s1 s2 hDF hInv k1 k2 hCont
      hDeadCont hHaltCont => fgAuthStepCoupling_dh1_latched S b P hP uIdx bIdx uSk vSk huLen hvLen q
      rem s1 s2 hDF hInv k1 k2 hCont hDeadCont hHaltCont) (fun a s1 hD => by
      simp [badAuthFgDh1LatchedAt_eq_false_of_deadAndUnlatchedDh1 P b.q_ro uIdx bIdx s1 hD])
    (fun a rem s1 s2 hDF hInvL => by
      have hDead : deadAuthDh1 uIdx s1 = false := by
        unfold deadAndUnlatchedDh1 at hDF; rw [hInvL.2, Bool.not_false, Bool.and_true] at hDF
        exact hDF
      have hLatchEq : badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx s1 =
          badAuthFgDh1AtCore P b.q_ro uIdx bIdx s1.base s1.advRoLog s1.respRecs := by
        unfold badAuthFgDh1LatchedAt; rw [hInvL.2, Bool.false_or]; rfl
      rw [hLatchEq]
      exact fgAuthSimInvDh1_terminal_le S b P hP b.q_ro uIdx bIdx uSk vSk huLen hvLen a rem s1 s2
        hDead hInvL.1)
    A.1.run b.q_total (QueryBounded.auth_total A.2)
    (AuthFgCutoffState.empty S secb) (FgAuthSimState.empty S secb)
    ⟨fgAuthSimInvDh1_empty S b P hP uIdx bIdx uSk vSk huLen hvLen secb, rfl⟩
end Proofs.SignalPqxdh.Security
