/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdA
public import Computational.Proofs.SignalPqxdh.Security.SigHop1KeyA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` step coupling for the bad-signature hop

**Checked by Lean.** Instantiates the one-key Case A simulator coupling at `bIdx = S.N_spk_tot`
(where no SPK bundle is a `DH1` target and no `(uIdx, bIdx)` latch can arise) to prove the per-step
coupling `fgAuthStepCoupling_sig1Key` and invariant projections for the bad-signature hop.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

open AuthDh3

theorem spkBundleFlatIdx_lt_N_spk_tot_sig1Key (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    spkBundleFlatIdx S u j < S.N_spk_tot := by
  unfold spkBundleFlatIdx Setup.N_spk_tot
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hj : j.val < S.N_recv := j.isLt
  have h2 : (u.val + 1) * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hu
  nlinarith

theorem fgPreAuthGenSPK_N_spk_tot_optVsk (S : Setup) (P : Primitives) (v : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    fgPreAuthGenSPK S.N_spk_tot (some v) S P u j = fgPreAuthGenSPK S.N_spk_tot none S P u j := by
  have hNe : (spkBundleFlatIdx S u j == S.N_spk_tot) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkBundleFlatIdx_lt_N_spk_tot_sig1Key S u j))
  unfold fgPreAuthGenSPK
  simp only [hNe, Bool.false_eq_true, ↓reduceIte]

theorem pqxdhAuthFgLatchedPreImpl1Key_N_spk_tot_optVsk {S : Setup} (useDh1 : Bool)
    (targetIdx : ℕ) (optUsk : Option Bytes) (v : Bytes) (P : Primitives) (q : AuthQuery S) :
    pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx S.N_spk_tot optUsk none S P q =
      pqxdhAuthFgLatchedPreImpl1Key useDh1 targetIdx S.N_spk_tot optUsk (some v) S P q := by
  cases q with
  | genSPK u j =>
    unfold pqxdhAuthFgLatchedPreImpl1Key pqxdhAuthFgLatchedPreImpl pqxdhAuthFgPreImpl
    simp only [fgPreAuthGenSPK_N_spk_tot_optVsk S P v u j]
  | _ => rfl

/-! ## Step couplings without halted continuation -/

theorem fgAuthStepCoupling_dh1_latched_noHalt (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (hbIdx : S.N_spk_tot ≤ bIdx)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (q : AuthQuery S)
    (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
    (hDeadU : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInvL : FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total
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
      rcases hMemL with ⟨_, hLt, _⟩ | hOld
      · exact absurd hLt (Nat.not_lt.mpr hbIdx)
      · exact False.elim (hNotOld hOld)
  | _ =>
    refine fgAuthStepCoupling_dh1_of_bind_unlatched S b P hP uIdx bIdx uSk vSk huSk hvSk _ rem hst
      st hst.latchedDh1 hInvL.2 k1 k2 ?_ hDead hInvL.1 hCont hDeadCont
    refine evalDist_bind_true_mono_of_support _ _ _ (fun x hx => ?_)
    have hL := pqxdhAuthFgPreImpl_preserves_latchedDh1 true uIdx bIdx (some uSk) (some vSk) P _ hst
      x hx
    have hEta : { x.2 with latchedDh1 := hst.latchedDh1 } = x.2 := by rw [← hL]
    rw [hEta]

theorem fgAuthStepCoupling_dh1_delegated_1Key_noHalt (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (hbIdx : S.N_spk_tot ≤ bIdx) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (q : AuthQuery S)
    (hDel : isDelegatedAuth1KeyQuery uIdx q = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hNeInit : ∀ u, q ≠ .initPrin u := by
    intro u h; subst h; cases hDel
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>=
        k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      q hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    q hNeInit, fgAuth1KeySimImpl_true_run_delegated P uSk P.isValidDhTriple uIdx bIdx b.q_total
    (P.x25519Base uSk) (P.x25519Base vSk) q hDel st stGhost hSimEq]
  simp only [bind_assoc, pure_bind]
  refine fgAuthStepCoupling_dh1_latched_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk q rem hst
    stGhost hDF hInvL k1' (fun p => k2 (p.1, { st with sim := clearAuthSecSign uIdx p.2 }))
    (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
  · dsimp only [k1']
    split_ifs with hAux
    · exact hCont r hst' { st with sim := clearAuthSecSign uIdx stGhost' } hDF'
        ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2.1 uIdx; omega, hAux.1 hSecEq⟩
    · simp
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp

theorem evalDist_fgAuth1KeySimImpl_corruptIK_tgt_bind_ge (S : Setup) (b : QueryBudget)
    (P : Primitives) (uSk : Bytes) (uIdx bIdx : ℕ) (U V : Bytes) (u : Fin S.N_id)
    (hTgt : (u.val == uIdx) = true) (st : FgAuth1KeySimState S) (stGhost : FgAuthSimState S)
    (hSimEq : st.sim = clearAuthSecSign uIdx stGhost)
    (hNC : isTargetPrinCorrupted uIdx stGhost = false)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool) :
    𝒟[(fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)).run
          stGhost >>= fun p => if isTargetPrinCorrupted uIdx p.2 then (pure false : ProbComp Bool)
          else k2 (p.1, { st with sim := clearAuthSecSign uIdx p.2 })] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total U V
        (.corruptIK u)).run st >>= k2] {true} := by
  have hNC1 : isTargetPrinCorrupted uIdx st.sim = false := by
    rw [hSimEq, isTargetPrinCorrupted_clearAuthSecSign, hNC]
  have hL : (fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total U V
      (.corruptIK u)).run st =
      (AuthDh3.fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)
        st.sim >>= fun p => pure (p.1, { st with sim := p.2 })) := by
    unfold fgAuth1KeySimImpl fgAuth1KeyStepHaltPure fgAuth1KeyStepPure
    simp [hNC1]
  have hR : (fgAuthSimImpl P P.isValidDhTriple true uIdx bIdx S b.q_total U V (.corruptIK u)).run
      stGhost = AuthDh3.fgAuthStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total U V
        (.corruptIK u) stGhost := by
    unfold fgAuthSimImpl fgAuthStepHalt; simp [hNC]
  rw [hL, hR, hSimEq]
  cases hF : stGhost.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    have hFc : (clearAuthSecSign uIdx stGhost).base.principals.find?
        (fun (idx, _) => idx == u.val) = none := by
      rw [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign, hF]; rfl
    unfold AuthDh3.fgAuthStepPure; dsimp only; rw [hFc, hF]; simp only [pure_bind]
    simp [hNC]
  | some p =>
    rcases p with ⟨u0, entry⟩
    have hFc : (clearAuthSecSign uIdx stGhost).base.principals.find?
        (fun (idx, _) => idx == u.val) = some (u0, clearTargetPrinSecSign uIdx u0 entry) := by
      rw [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign, hF]; rfl
    unfold AuthDh3.fgAuthStepPure; dsimp only; rw [hFc, hF]; simp only [pure_bind]
    set_option linter.deprecated false in
    rw [if_pos (isTargetPrinCorrupted_map_corrupted_eq_true_of_eq uIdx u.val hTgt stGhost u0
      entry hF)]
    simp

theorem fgAuthStepCoupling_dh1_corruptIK_tgt_1Key_noHalt (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (hbIdx : S.N_spk_tot ≤ bIdx) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (u : Fin S.N_id)
    (hTgt : (u.val == uIdx) = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u)).run st >>= k2] {true} := by
  have hNeInit : ∀ u', (AuthQuery.corruptIK u : AuthQuery S) ≠ .initPrin u' := by
    intro u' h; cases h
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  have hNC := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk
    (rem + 1) hst stGhost hDF hInvL
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run
        hst >>= k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      _ hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    _ hNeInit]
  refine le_trans ?_ (evalDist_fgAuth1KeySimImpl_corruptIK_tgt_bind_ge S b P uSk uIdx bIdx
    (P.x25519Base uSk) (P.x25519Base vSk) u hTgt st stGhost hSimEq hNC k2)
  refine fgAuthStepCoupling_dh1_latched_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk _ rem hst
    stGhost hDF hInvL k1' _ (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
  · have hNC' := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk
      hvSk rem hst' stGhost' hDF' hGInv'
    dsimp only [k1']
    rw [hNC']; simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hAux
    · exact hCont r hst' { st with sim := clearAuthSecSign uIdx stGhost' } hDF'
        ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2.1 uIdx; omega, hAux.1 hSecEq⟩
    · simp
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp

theorem fgAuthStepCoupling_dh1_genSPK_tgt_1Key_noHalt (S : Setup) (b : QueryBudget)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (hbIdx : S.N_spk_tot ≤ bIdx) (uSk vSk : Bytes)
    (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hTgt : (u.val == uIdx) = true) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1] {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j)).run st >>= k2] {true} := by
  have hNeInit : ∀ u', (AuthQuery.genSPK u j : AuthQuery S) ≠ .initPrin u' := by
    intro u' h; cases h
  have huEq : u.val = uIdx := beq_iff_eq.mp hTgt
  rcases hInv with ⟨stGhost, hSimEq, hInvL, hBudget, hSecEq⟩
  have hNC := isTargetPrinCorrupted_eq_false_of_invDh1Latched S b P hP uIdx bIdx uSk vSk huSk hvSk
    (rem + 1) hst stGhost hDF hInvL
  rcases hInvL.1 with ⟨hBR, -, -, -, -, -, -, -, hValid, hPrins, -⟩
  have hAnyG : ∀ (stG : FgAuthSimState S) (h : AuthFgCutoffState S),
      FgAuthBaseRel true uIdx bIdx stG.base h.base →
      stG.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) =
        h.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    intro stG h hR; rw [hR.spkBundles_eq]; exact any_idx_eraseSpkBundlesFg S bIdx _ _
  have hA0 := hAnyG stGhost hst hBR
  have hSign : ∀ u0 e, stGhost.base.principals.find? (fun (idx, _) => idx == u.val) =
      some (u0, e) → e.secIKAsign = uSk := by
    intro u0 e hF
    have hPrinFind : stGhost.base.principals.find? (fun (idx, _) => idx == u.val) =
        (hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
          (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e)) := by
      rw [hBR.principals_eq]; exact find?_idx_erasePrincipalsFg uIdx u.val _
    rw [hPrinFind] at hF
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rw [hFP] at hF; cases hF
    | some q =>
      rcases q with ⟨u1, e1⟩
      rw [hFP] at hF
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at hF
      rcases hF with ⟨rfl, rfl⟩
      have hMem := List.mem_of_find?_eq_some hFP
      have hu1 : u1 = u.val := beq_iff_eq.mp
        (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
      rw [erasePrincipalEntryFg_secIKAsign, hSecEq _ hMem]
      exact (hPrins _ hMem).2.2 (by dsimp only; rw [hu1]; exact hTgt)
  have hBudgetPos : stGhost.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) = false →
      0 < st.sigBudget := by
    intro hF
    rw [hA0] at hF
    let dummyB : SpkBundleEntry :=
      { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
    have hLen := bundleSignedMessages_length_add_two_le S u j dummyB hst.base.spkBundles
      hValid.2.1 hF
    rw [huEq] at hLen
    omega
  let k1' : AuthResponse × AuthFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun p => if PreStepPreservesAuth1KeyAux hst p.2 then k1 p else pure false
  have hLhsEq :
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1] =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run
        hst >>= k1'] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    have hAux := pqxdhAuthFgLatchedPreImpl1Key_preserves_1KeyAux_of_ne_initPrin P uIdx bIdx uSk vSk
      _ hNeInit hst x hx
    simp only [k1', hAux, ↓reduceIte]
  rw [hLhsEq, pqxdhAuthFgLatchedPreImpl1Key_of_not_initPrin true uIdx bIdx (some uSk) (some vSk) P
    _ hNeInit, fgAuth1KeySimImpl_genSPK_tgt_run_eq P uSk P.isValidDhTriple uIdx bIdx b.q_total
    (P.x25519Base uSk) (P.x25519Base vSk) u j hTgt st stGhost hSimEq hNC hSign hBudgetPos]
  simp only [bind_assoc, pure_bind]
  refine fgAuthStepCoupling_dh1_latched_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk _ rem hst
    stGhost hDF hInvL k1' _ (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
  · dsimp only [k1']
    by_cases hAux : PreStepPreservesAuth1KeyAux hst hst'
    · simp only [hAux, ↓reduceIte]
      refine hCont r hst' _ hDF' ⟨stGhost', rfl, hGInv', ?_, hAux.1 hSecEq⟩
      dsimp only
      have hA1 := hAnyG stGhost' hst' hGInv'.1.1
      have hMono := hAux.2.1 uIdx
      split_ifs with h1 h2
      · omega
      · rw [hA0] at h1; rw [hA1] at h2
        have h2' := hAux.2.2 u.val j.val (Bool.eq_false_iff.mpr h1) h2
        rw [huEq] at h2'
        omega
      · omega
    · simp [hAux]
  · dsimp only [k1']
    split_ifs with hAux
    · exact hDeadCont r hst' hDF'
    · simp

theorem fgAuthStepCoupling_dh1_1Key_noHalt (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ) (hbIdx : S.N_spk_tot ≤ bIdx)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (q : AuthQuery S)
    (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : FgAuth1KeySimState S) (hDF : deadAndUnlatchedDh1 uIdx bIdx hst = false)
    (hInv : FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAndUnlatchedDh1 uIdx bIdx hst' = false →
      FgAuthSimInvDh1Latched1Key S b P hP uIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAndUnlatchedDh1 uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  cases q with
  | initPrin u =>
    exact fgAuthStepCoupling_dh1_initPrin_1Key S b P hP uIdx bIdx uSk vSk huSk hvSk u rem hst st
      hDF hInv k1 k2 hCont
  | corruptIK u =>
    by_cases hT : (u.val == uIdx) = true
    · exact fgAuthStepCoupling_dh1_corruptIK_tgt_1Key_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk
        hvSk u hT rem hst st hDF hInv k1 k2 hCont hDeadCont
    · exact fgAuthStepCoupling_dh1_delegated_1Key_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk
        _ (by simpa [isDelegatedAuth1KeyQuery] using hT) rem hst st hDF hInv k1 k2 hCont hDeadCont
  | genSPK u j =>
    by_cases hT : (u.val == uIdx) = true
    · exact fgAuthStepCoupling_dh1_genSPK_tgt_1Key_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk
        hvSk u j hT rem hst st hDF hInv k1 k2 hCont hDeadCont
    · exact fgAuthStepCoupling_dh1_delegated_1Key_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk
        _ (by simpa [isDelegatedAuth1KeyQuery] using hT) rem hst st hDF hInv k1 k2 hCont hDeadCont
  | _ =>
    exact fgAuthStepCoupling_dh1_delegated_1Key_noHalt S b P hP uIdx bIdx hbIdx uSk vSk huSk hvSk _
      rfl rem hst st hDF hInv k1 k2 hCont hDeadCont

/-! ## Bad-signature hop coupling -/

/-- Coupling invariant for the one-key bad-signature hop (`bIdx = S.N_spk_tot`, `uSk = vSk = sk`). -/
def FgAuthSimInvSig1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S) : Prop :=
  FgAuthSimInvDh1Latched1Key S b P hP k S.N_spk_tot sk sk hsk hsk rem hst st

theorem fgAuthSimInvSig1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32)
    (secb : Bool) :
    FgAuthSimInvSig1Key S b P hP k sk hsk b.q_total (AuthFgCutoffState.empty S secb)
      (FgAuth1KeySimState.empty S secb) :=
  fgAuthSimInvDh1Latched1Key_empty S b P hP k S.N_spk_tot sk sk hsk hsk secb

theorem eraseSpkBundlesFg_N_spk_tot_of_valid (S : Setup)
    (L : List ((Nat × Nat) × SpkBundleEntry)) (hV : ∀ e ∈ L, e.1.1 < S.N_id ∧ e.1.2 < S.N_recv) :
    eraseSpkBundlesFg S S.N_spk_tot L = L := by
  unfold eraseSpkBundlesFg
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨⟨k1, k2⟩, bE⟩
    have ⟨h1, h2⟩ := hV _ List.mem_cons_self
    have hLt : k1 * S.N_recv + k2 < S.N_spk_tot := by
      unfold Setup.N_spk_tot
      have h3 : (k1 + 1) * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv h1
      nlinarith
    rw [List.map_cons, ih (fun e he => hV e (List.mem_cons_of_mem _ he))]
    unfold eraseSpkBundleEntryFg
    have hNe : (FgGapDh.spkBundleFlatIdxVal S (k1, k2) == S.N_spk_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hLt)
    simp only [hNe, Bool.false_eq_true, ↓reduceIte]

theorem fgAuthSimInvSig1Key_bases (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hInv : FgAuthSimInvSig1Key S b P hP k sk hsk rem hst st) :
    st.sim.base.principals = clearPrincipalsTargetSign k (erasePrincipalsFg k hst.base.principals) ∧
    st.sim.base.spkBundles = hst.base.spkBundles ∧
    ValidPrincipals S hst.base.principals := by
  rcases hInv with ⟨stGhost, hSimEq, hInvL, -, -⟩
  have hBR := hInvL.1.1
  have hValid := hInvL.1.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, hValid.1⟩
  · rw [hSimEq, clearAuthSecSign_base_principals, hBR.principals_eq]
    unfold erasePrincipalsOptFg clearPrincipalsTargetSign
    simp only [↓reduceIte]
    congr 1; funext ⟨idx, e⟩
    unfold clearTargetPrinSecSign
    by_cases h : (idx == k) = true <;> simp [h]
  · rw [hSimEq, clearAuthSecSign_base_spkBundles, hBR.spkBundles_eq]
    exact eraseSpkBundlesFg_N_spk_tot_of_valid S _ hValid.2.1.1

theorem fgAuthSimInvSig1Key_prinLen (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hInv : FgAuthSimInvSig1Key S b P hP k sk hsk rem hst st) :
    st.sim.base.principals.length ≤ S.N_dh := by
  rcases fgAuthSimInvSig1Key_bases S b P hP k sk hsk rem hst st hInv with ⟨hP1, -, hV⟩
  rw [hP1, length_clearPrincipalsTargetSign]
  unfold erasePrincipalsFg; rw [List.length_map]
  have hSub : hst.base.principals.map Prod.fst ⊆ List.range S.N_id := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    exact List.mem_range.mpr (hV.1 e he)
  have hLen := (hV.2.subperm hSub).length_le
  simp only [List.length_map, List.length_range] at hLen
  unfold Setup.N_dh; omega

theorem fgAuthSimInvSig1Key_ext (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hInv : FgAuthSimInvSig1Key S b P hP k sk hsk rem hst st) (bundle : PreKeyBundleInput) :
    extractBundleForgery P k (P.sigPkGen sk) st.sim.base.principals st.sim.base.spkBundles
        bundle none =
      extractBundleForgery P k (P.sigPkGen sk) hst.base.principals hst.base.spkBundles bundle
        none := by
  rcases fgAuthSimInvSig1Key_bases S b P hP k sk hsk rem hst st hInv with ⟨hP1, hS1, -⟩
  rw [hP1, hS1]
  unfold extractBundleForgery
  rw [isHonestUncorruptedPeer_clearPrincipalsTargetSign, isHonestUncorruptedPeer_erasePrincipalsFg]

theorem fgAuthSimInvSig1Key_signed (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32) (rem : ℕ)
    (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hInv : FgAuthSimInvSig1Key S b P hP k sk hsk rem hst st) :
    ∀ m ∈ bundleSignedMessages k st.sim.base.spkBundles,
      m ∈ bundleSignedMessages k hst.base.spkBundles := by
  rcases fgAuthSimInvSig1Key_bases S b P hP k sk hsk rem hst st hInv with ⟨-, hS1, -⟩
  rw [hS1]; exact fun _ h => h

/-- Per-step coupling for the one-key bad-signature hop with invariant `FgAuthSimInvSig1Key`. -/
theorem fgAuthStepCoupling_sig1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (hsk : sk.length = 32)
    (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S)
    (hDead : deadAuthDh1 k hst = false)
    (hInv : FgAuthSimInvSig1Key S b P hP k sk hsk (rem + 1) hst st)
    (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
    (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadAuthDh1 k hst' = false →
      FgAuthSimInvSig1Key S b P hP k sk hsk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadAuthDh1 k hst' = true → 𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot (some sk) none S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P sk P.isValidDhTriple true k S.N_spk_tot S b.q_total
          (P.sigPkGen sk) (P.sigPkGen sk) q).run st >>= k2] {true} := by
  have hPk : P.sigPkGen sk = P.x25519Base sk :=
    congrFun hP.toWellFormedPrimitivesδ.sigPkGen_eq_x25519Base sk
  rw [pqxdhAuthFgLatchedPreImpl1Key_N_spk_tot_optVsk true k (some sk) sk P q, hPk]
  have hUnl : ∀ hst' st' rem', FgAuthSimInvSig1Key S b P hP k sk hsk rem' hst' st' →
      deadAndUnlatchedDh1 k S.N_spk_tot hst' = deadAuthDh1 k hst' := by
    intro hst' st' rem' hI
    rcases hI with ⟨_, _, hIL, _, _⟩
    unfold deadAndUnlatchedDh1; rw [hIL.2, Bool.not_false, Bool.and_true]
  refine fgAuthStepCoupling_dh1_1Key_noHalt S b P hP k S.N_spk_tot (Nat.le_refl _) sk sk hsk hsk q
    rem hst st (by rw [hUnl hst st (rem + 1) hInv]; exact hDead) hInv k1 k2
    (fun r hst' st' hDF' hI' => hCont r hst' st' (by rw [← hUnl hst' st' rem hI']; exact hDF') hI')
    (fun r hst' hDT' => hDeadCont r hst' ?_)
  unfold deadAndUnlatchedDh1 at hDT'
  exact (Bool.and_eq_true_iff.mp hDT').1

end Proofs.SignalPqxdh.Security
