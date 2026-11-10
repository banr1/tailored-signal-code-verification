/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.KeyInd1RealRedsCosted
public import Computational.Proofs.E2E.BhKindCouplingV1
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import VCVio.EvalDist.Monad.Basic

/-!
# Polymorphic `KeyInd` E2E query bounds and `bhKindRedWith` coupling

**Checked by Lean.** Combined `KeyInd` and Stage-2 `SM` query bounds (`bhCostedRedsWith_queryBounds`)
and the `bhKindRedWith` coupling and advantage bound (`boolBias_bhE2EExpWithKi_true_le`) for an
arbitrary `KeyInd` oracle handler `ki`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open ReductionDsl CryptoVerification.E2E.Costed
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

/-! ## Stage-2 prefix and combined query bounds -/

section PrefixAndCombinedQueryBoundsWith

open KeyInd1RealRedsAux

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
variable (P : SignalPqxdh.Primitives)
variable (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
variable (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
variable (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

private theorem isQueryBoundP_bhFwdU_sm (n : ℕ) :
    (bhFwdU (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n).IsQueryBoundP
      (isSmTargetQuery ℓ) 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])

private theorem isQueryBoundP_bhLiftP_sm {α : Type} (p : ProbComp α) :
    (bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) p).IsQueryBoundP
      (isSmTargetQuery ℓ) 0 := by
  unfold bhLiftP
  induction p using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n mx ih =>
    rw [simulateQ_query_bind]
    exact (isQueryBoundP_bind (isQueryBoundP_bhFwdU_sm n) (fun u _ => ih u)).mono (by omega)

theorem isQueryBoundP_bhPrefixHandlePostWith_eval (k : ℕ)
    (s : BHE2EDrvState S ℓ) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    (Prefix1Key.bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k s (bhTargetQenc t)).IsQueryBoundP
      (isSmTargetQuery ℓ)
      (if bhClassifyTargetOnly (fun _ => false) (fun _ => false) (fun i => i == k) t then 1 else 0) := by
  rcases t with (kq | ⟨sid⟩) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      Prefix1Key.bhPrefixHandlePostWith]
    exact isQueryBoundP_bhLiftP_sm _
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      Prefix1Key.bhPrefixHandlePostWith]
    exact isQueryBoundP_bhLiftP_sm _
  · simp only [bhClassifyTargetOnly, bhTargetQenc, Prefix1Key.bhPrefixHandlePostWith]
    by_cases hp : (i == k) = true
    · simp only [hp, ↓reduceIte]
      cases bhShallowCheckExtSm k s i sq with
      | inl _ => exact (isQueryBoundP_bhLiftP_sm _).mono (Nat.zero_le 1)
      | inr sq' =>
        dsimp only
        have hq1 :
            (liftM ((unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query
              (.inr sq')) :
              OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) _).IsQueryBoundP
            (isSmTargetQuery ℓ) 1 :=
          (isQueryBoundP_query_iff (isSmTargetQuery ℓ) (Sum.inr sq') 1).2 (fun _ => Nat.zero_lt_one)
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind hq1 (fun _ _ => isQueryBoundP_pure (isSmTargetQuery ℓ) _ 0)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hne : (i != k) = true := by
        rw [bne_iff_ne]
        exact beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hp)
      have hcheck : bhShallowCheckExtSm k s i sq = .inl (.inr (none, none, none)) := by
        simp [bhShallowCheckExtSm, hne]
      rw [hcheck]
      exact isQueryBoundP_bhLiftP_sm _

/-- Target-level Stage-2 SM query bound for `Prefix1Key.bhPrefixRedWith S ℓ P ki ... k` on an
arbitrary `B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool`. -/
theorem bhPrefixRedWith_makesAtMostQueries_of_B
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (k q_k : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      q_k)
    (qTot : ℕ)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx)
    (ho : o ∈ support (stageOneAsProbComp
      ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1 (fun _ => B_A) () qTot false)))
    (flip : Bool) :
    SM.MakesAtMostQueries
      ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2 o.2 flip qTot false)
      q_k := by
  have hfin : ∀ (s_out : BHE2EDrvState S ℓ) (b_out : Bool),
      ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).finish s_out b_out flip).IsQueryBoundP
        (isSmTargetQuery ℓ) 0 := by
    intro s_out b_out
    dsimp only [Prefix1Key.bhPrefixRedWith]
    exact isQueryBoundP_bhLiftP_sm _
  unfold SM.MakesAtMostQueries
  refine isQueryBoundP_congr_pred_with
    (p := isSmTargetQuery ℓ) (by rintro (_ | _) <;> rfl) ?_
  rcases o with ⟨c0, m⟩
  dsimp only
  cases m with
  | done b_out s_out =>
    simp only [BhShallowTwoStageRed.eval2, pure_bind]
    exact (hfin s_out b_out).mono (Nat.zero_le _)
  | paused t c p s_p cont =>
    have hcont : ∀ v,
        (cont v).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
          q_k :=
      isQueryBoundP_paused_of_mem_support_simulateQ_shallow_eval1
        (Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k)
        _ (fun _ => B_A) () qTot false q_k (fun _ => hB)
        c0 t c p s_p cont ho
    have hres :
        ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).resume s_p p flip).IsQueryBoundP
          (isSmTargetQuery ℓ) 0 := by
      dsimp only [Prefix1Key.bhPrefixRedWith]
      exact isQueryBoundP_pure (isSmTargetQuery ℓ) _ 0
    simp only [BhShallowTwoStageRed.eval2]
    exact (isQueryBoundP_bind hres
      (fun ⟨v, s₁⟩ _ =>
        isQueryBoundP_bind
          (bhShallowRunFuel_queryBound_of_step_le
            bhTargetQenc bhTargetRdec
            (Prefix1Key.bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k)
            isQueryBoundP_bhFwdU_sm
            (fun t' s' => isQueryBoundP_bhPrefixHandlePostWith_eval P ki C K qep decT encT k s' t')
            false
            (q := q_k)
            (isQueryBoundP_congr_pred_with (by rintro (_ | _) <;> rfl)
              (hcont (bhTargetRdec t v)))
            qTot s₁)
          (fun ⟨b_out, s_out⟩ _ => hfin s_out b_out))).mono (by omega)

/-- Combined `KeyInd` and Stage-2 `SM` query bounds for `bhKindRedWith` and
`Prefix1Key.bhPrefixRedWith` on a bounded target-game adversary `B_A`. -/
theorem bhCostedRedsWith_queryBounds_of_B
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hRo : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro)
    (hSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot)
    (hRecv : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot)
    (hTot : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total)
    (hOn : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on)
    (hCtl : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot)
    (hCtlStart : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart)
    (hInst : ∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    let kindRed := bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT
    let prefRed := Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT
    let b_ki := keyIndReductionBudget S qStart b
    let advK : SignalPqxdh.KeyIndAdversary S := ⟨kindRed.eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK b_ki ∧
    (∀ k < qStart,
      ∀ o ∈ support (stageOneAsProbComp ((prefRed k).eval1 (fun _ => B_A) () qTot false)),
      ∀ flip,
      SM.MakesAtMostQueries ((prefRed k).eval2 o.2 flip qTot false) (qs k)) := by
  intro qDR qTot kindRed prefRed b_ki advK
  exact ⟨bhKindRedWith_queryBounded_of_B P ki C K qep decT encT B_A b qStart
      hRo hSend hRecv hTot hOn hCtl hCtlStart,
    fun k hk o ho flip =>
      bhPrefixRedWith_makesAtMostQueries_of_B P ki C K qep decT encT B_A k (qs k) (hInst k hk)
        qTot o ho flip⟩

/-- Combined query bounds for `L_bh`, `bhKindRedWith`, and `Prefix1Key.bhPrefixRedWith` under
`CliGameAdversaryPerInstanceBounded`. -/
theorem bhCostedRedsWith_queryBounds
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    let kindRed := bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT
    let prefRed := Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT
    let b_ki := keyIndReductionBudget S qStart b
    let advK : SignalPqxdh.KeyIndAdversary S := ⟨kindRed.eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK b_ki ∧
    (∀ k < qStart,
      ∀ o ∈ support (stageOneAsProbComp ((prefRed k).eval1 (fun _ => B_A) () qTot false)),
      ∀ flip,
      SM.MakesAtMostQueries ((prefRed k).eval2 o.2 flip qTot false) (qs k)) := by
  rcases hA with ⟨⟨hRo, hSend, hRecv, hTot, hOn, hCtl, _⟩, hStart, hInst⟩
  exact bhCostedRedsWith_queryBounds_of_B P ki C K qep decT encT
    ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ())
    b qStart qs
    (isQueryBoundP_L_bh_eval decT encT
      (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) A b.q_ro
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hRo))
    (isQueryBoundP_L_bh_eval decT encT
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hSend))
    (isQueryBoundP_L_bh_eval decT encT
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_recv_tot
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hRecv))
    (isQueryBoundP_L_bh_eval decT encT
      (fun _ => true) (fun _ => false) (fun _ => false) A b.q_total
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hTot))
    (isQueryBoundP_L_bh_eval decT encT
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) A b.q_on
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [rfl; (cases kq <;> rfl); rfl; rfl]) hOn))
    (isQueryBoundP_L_bh_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hCtl))
    (isQueryBoundP_L_bh_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A qStart
      (isQueryBoundP_congr_pred_with
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) hStart))
    (fun k hk =>
      isQueryBoundP_L_bh_eval decT encT
        (fun _ => false) (fun _ => false) (fun i => i == k) A (qs k)
        (isQueryBoundP_congr_pred_with
          (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> rfl) (hInst k hk)))

end PrefixAndCombinedQueryBoundsWith

/-! ## Polymorphic `bhKindRedWith` coupling and advantage bound -/

/-- Polymorphic model-state E2E experiment parameterized over `ki` and the `KeyInd` challenge bit
`secb : Bool` (`true` = real `DRKey`s, `false` = uniform `DRKey`s). -/
def bhE2EExpWithKi (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σ) ← (simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) B).run
    { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
  if !allTestedSessionsFresh P σ.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σ b)

abbrev keyIndFullImplWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)) :
    QueryImpl (unifSpec + SignalPqxdh.keyIndSpec S)
      (StateT (SignalPqxdh.KeyIndState S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SignalPqxdh.KeyIndState S) ProbComp) + ki

section CouplingWith

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

theorem simulateQ_keyIndFullImplWith_bhLiftP_run {α : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (mx : ProbComp α) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (keyIndFullImplWith S ki)
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) mx)).run st =
    (mx >>= fun a => pure (a, st)) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp [bhLiftP, simulateQ_pure, StateT.run_pure]
  | query_bind t m ih =>
    simp only [bhLiftP, simulateQ_bind, StateT.run_bind]
    show ((query (spec := unifSpec) t >>= fun u => pure (u, st)) >>= fun y =>
        (simulateQ (keyIndFullImplWith S ki)
          (simulateQ (bhFwdU (G := SignalPqxdh.keyIndSpec S)) (m y.1))).run y.2) =
      ((query (spec := unifSpec) t >>= m) >>= fun a => pure (a, st))
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun u => ih u st

@[simp]
private theorem simulateQ_keyIndFullImplWith_query_inr
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (kq : SignalPqxdh.KeyIndQuery S) :
    simulateQ (keyIndFullImplWith S ki)
      (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) =
    ki kq :=
  QueryImpl.simulateQ_add_query_right _ _ kq

@[simp]
private theorem stateT_run_liftM_with {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem bhE2EDrvImplWith_run_inl
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (n : ℕ) (σ : BHE2EDrvState S ℓ) :
    (bhE2EDrvImplWith P ki C K qep decT encT (.inl n)).run σ =
      ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, σ)) := rfl

private def bhKiNoOpkRefused (instMeta : List (ModelDriverInstanceMeta S))
    (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  match kq with
  | .corruptIK u => bhNoOpkRespPromoted instMeta u
  | _ => false

@[simp]
private theorem bhE2EDrvImplWith_run_ki
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kq : SignalPqxdh.KeyIndQuery S) (σ : BHE2EDrvState S ℓ) :
    (bhE2EDrvImplWith P ki C K qep decT encT (.inr (.inl (.inl kq)))).run σ =
      if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
        pure (.noneResp, σ)
      else if bhKiNoOpkRefused σ.instMeta kq then
        pure (.noneResp, σ)
      else
        ((ki kq).run σ.st >>= fun p =>
          pure (p.1, bhE2EMirror { σ with st := p.2 } kq p.1)) := by
  unfold bhE2EDrvImplWith bhKiNoOpkRefused
  cases h : bhDrvKiQueryOk P σ.toModelDriverBase kq
  · simp only [h, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind]
  · cases kq with
    | corruptIK u =>
      cases hRef : bhNoOpkRespPromoted σ.instMeta u <;>
        simp only [h, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
          bind_assoc, pure_bind]
    | _ =>
      simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
        bind_assoc, pure_bind]

@[simp]
private theorem bhE2EDrvImplWith_run_startDR
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (sid : SignalPqxdh.SessionId S) (σ : BHE2EDrvState S ℓ) :
    (bhE2EDrvImplWith P ki C K qep decT encT (.inr (.inl (.inr (.startDR sid))))).run σ =
      compositionLocalStart ki C K (some σ.b) σ sid := by
  unfold bhE2EDrvImplWith
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
    bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

@[simp]
private theorem bhE2EDrvImplWith_run_sm
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ : BHE2EDrvState S ℓ) :
    (bhE2EDrvImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run σ =
      (bhE2EStepLocalSm C K qep decT encT σ i sq >>= fun p =>
        pure (bhUnpackSmResp sq p.1, p.2)) := by
  unfold bhE2EDrvImplWith
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, stateT_run_liftM_with, StateT.run_set,
    bind_assoc, pure_bind]

private theorem bhKindHandleWith_impl_run_ki
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kq : SignalPqxdh.KeyIndQuery S) (σ : BHE2EDrvState S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
      (.inr (.inl (.inl kq)))).run σ) =
      (if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
        pure (SignalPqxdh.KeyIndResponse.noneResp, σ)
      else if bhKiNoOpkRefused σ.instMeta kq then
        pure (SignalPqxdh.KeyIndResponse.noneResp, σ)
      else
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr =>
          pure (kr, bhE2EMirror σ kq kr)) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWith, bhTargetQenc, bhTargetRdec, bhKiNoOpkRefused]
  cases bhDrvKiQueryOk P σ.toModelDriverBase kq
  · simp only [Bool.false_and, Bool.false_eq_true, Bool.not_false, ↓reduceIte, pure_bind]
  · cases kq with
    | corruptIK u =>
      dsimp only
      by_cases hRef : bhNoOpkRespPromoted σ.instMeta u = true
      · simp only [hRef, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
      · have hRefF : bhNoOpkRespPromoted σ.instMeta u = false := Bool.eq_false_iff.mpr hRef
        simp only [hRefF, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_eq_true,
          ↓reduceIte, bind_assoc, pure_bind]
    | _ =>
      simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, pure_bind]

private theorem bhKindHandleWith_impl_run_startDR
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (sid : SignalPqxdh.SessionId S) (σ : BHE2EDrvState S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
      (.inr (.inl (.inr (.startDR sid))))).run σ) =
      match (bhE2EGuard σ sid).map (fun x => x.2.2) with
      | none => pure (none, σ)
      | some (u, j) =>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr1 =>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) >>= fun kr2 =>
        bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256) >>= fun ac =>
        pure (bhE2EFinishStartSpk C K (some σ.b) σ sid kr1 kr2 ac) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWith, bhTargetQenc, bhTargetRdec]
  cases (bhE2EGuard σ sid).map (fun x => x.2.2) with
  | none => simp only [pure_bind]
  | some uj =>
    rcases uj with ⟨u, j⟩
    simp only [bind_assoc, pure_bind, Prod.mk.eta]

private theorem bhKindHandleWith_impl_run_sm
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ : BHE2EDrvState S ℓ) :
    ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
      (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)
      (.inr (.inr ⟨i, sq⟩))).run σ) =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) (bhE2EStepLocalSm C K qep decT encT σ i sq) >>=
        fun p => pure (bhUnpackSmResp sq p.1, p.2)) := by
  dsimp [bhShallowImplOfHandle, bhKindHandleWith, bhTargetQenc, bhTargetRdec]
  simp only [bind_assoc, pure_bind]

theorem simulateQ_bhKindRedWith_impl_step
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) :
    (simulateQ (keyIndFullImplWith S ki)
      ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
        (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT) q).run
        { σ with st := bhKindDummySt S })).run σ.st =
    (fun p => ((p.1, { p.2 with st := bhKindDummySt S }), p.2.st)) <$>
      ((bhE2EDrvImplWith P ki C K qep decT encT q).run σ) ∧
    (fun p => (p.1, { p.2 with b := σ.b })) <$>
      ((bhE2EDrvImplWith P ki C K qep decT encT q).run σ) =
      ((bhE2EDrvImplWith P ki C K qep decT encT q).run σ) := by
  match q with
  | .inl n =>
    refine ⟨?_, ?_⟩
    · change (simulateQ (keyIndFullImplWith S ki)
          (bhFwdU (G := SignalPqxdh.keyIndSpec S) n >>= fun u =>
            pure (u, { σ with st := bhKindDummySt S }))).run σ.st = _
      rw [bhE2EDrvImplWith_run_inl]
      simp only [bhFwdU, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        map_eq_bind_pure_comp, Function.comp_def]
      rfl
    · rw [bhE2EDrvImplWith_run_inl]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  | .inr (.inl (.inl kq)) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWith_impl_run_ki, bhE2EDrvImplWith_run_ki]
      dsimp only
      cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq
      · simp only [Bool.not_false, ↓reduceIte, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      · cases hRef : bhKiNoOpkRefused σ.instMeta kq
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
            simulateQ_keyIndFullImplWith_query_inr, simulateQ_pure, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, bhE2EMirror_with_st]
          rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure,
            map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    · rw [bhE2EDrvImplWith_run_ki]
      cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq
      · simp only [Bool.not_false, ↓reduceIte, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      · cases hRef : bhKiNoOpkRefused σ.instMeta kq
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, Function.comp_def, pure_bind]
  | .inr (.inl (.inr (.startDR sid))) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWith_impl_run_startDR, bhE2EDrvImplWith_run_startDR]
      unfold compositionLocalStart
      simp only [bhE2EGuard_with_st]
      cases hG : bhE2EGuard σ sid with
      | none =>
        simp only [Option.map_none, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
        simp only [Option.map_some, bind_assoc, pure_bind,
          simulateQ_bind, StateT.run_bind, simulateQ_keyIndFullImplWith_query_inr,
          simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def]
        refine bind_congr fun p1 => ?_
        refine bind_congr fun p2 => ?_
        refine bind_congr fun ac => ?_
        have hFin := bhE2EFinishStartSpk_with_st C K (some σ.b) { σ with st := p2.2 }
          (bhKindDummySt S) sid p1.1 p2.1 ac
        have hSt2 := bhE2EFinishStartSpk_st_eq C K (some σ.b) { σ with st := p2.2 }
          sid p1.1 p2.1 ac
        dsimp only at hFin hSt2 ⊢
        rw [hFin, hSt2]
    · rw [bhE2EDrvImplWith_run_startDR]
      unfold compositionLocalStart
      cases hG : bhE2EGuard σ sid with
      | none =>
        simp only [map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun p1 => ?_
        refine bind_congr fun p2 => ?_
        refine bind_congr fun ac => ?_
        exact congrArg pure (bhE2EFinishStartSpk_b_eq C K (some σ.b)
          { σ with st := p2.2 } σ.b rfl sid p1.1 p2.1 ac)
  | .inr (.inr ⟨i, sq⟩) =>
    refine ⟨?_, ?_⟩
    · rw [bhKindHandleWith_impl_run_sm, bhE2EDrvImplWith_run_sm]
      simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
        simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure]
      have hDummy := bhE2EStepLocalSm_with_st C K qep decT encT σ (bhKindDummySt S) i sq
      have hSelf := (bhE2EStepLocalSm_with_st C K qep decT encT σ σ.st i sq).symm
      rw [hDummy, ← hSelf]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    · rw [bhE2EDrvImplWith_run_sm]
      have hB := bhE2EStepLocalSm_preserves_b C K qep decT encT σ i sq
      conv_rhs => rw [← hB]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem simulateQ_bhKindRedWith_impl_run {α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) :
    (simulateQ (keyIndFullImplWith S ki)
      ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
        (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)) oa).run
        { σ with st := bhKindDummySt S })).run σ.st =
    (fun p => ((p.1, { p.2 with st := bhKindDummySt S }), p.2.st)) <$>
      ((simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) oa).run σ) ∧
    (fun p => (p.1, { p.2 with b := σ.b })) <$>
      ((simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) oa).run σ) =
      ((simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) oa).run σ) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    exact ⟨trivial, trivial⟩
  | query_bind q mx ih =>
    have ⟨hStep, hStepB⟩ := simulateQ_bhKindRedWith_impl_step P ki C K qep decT encT q σ
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind]
    refine ⟨?_, ?_⟩
    · rw [hStep]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨r, σ'⟩ => ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using (ih r σ').1
    · conv_lhs => rw [← hStepB]
      conv_rhs => rw [← hStepB]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨r, σ'⟩ => ?_
      have hih := (ih r { σ' with b := σ.b }).2
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using hih

private theorem evalDist_uniformBool_beq_with (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

@[simp]
private theorem bhE2EDrvWon_with_b_aux (σ : BHE2EDrvState S ℓ) (b' b : Bool) :
    bhE2EDrvWon { σ with b := b' } b = bhE2EDrvWon σ b := rfl

end CouplingWith

theorem evalDist_bhKindRedWith_branch (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[do
      let (w, finalSt) ← (simulateQ (keyIndFullImplWith S ki)
        ((bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B) ())).run
        (SignalPqxdh.KeyIndState.empty S secb)
      if !allTestedSessionsFresh P finalSt then
        let coin ← $ᵗ Bool
        return coin
      else
        return (w == secb)] =
    𝒟[do
      let z ← bhE2EExpWithKi secb S P ki C K ℓ qep decT encT B
      return (secb == z)] := by
  unfold bhE2EExpWithKi
  dsimp only [BhShallowRed.eval, bhKindRedWith]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_keyIndFullImplWith_bhLiftP_run, simulateQ_pure, StateT.run_pure]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  let σ0 : BHE2EDrvState S ℓ := { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
  have hInit : ({ b := b } : BHE2EDrvState S ℓ) = { σ0 with st := bhKindDummySt S } := rfl
  have ⟨hRun, hRunB⟩ := simulateQ_bhKindRedWith_impl_run P ki C K qep decT encT B σ0
  rw [hInit]
  change 𝒟[(simulateQ (keyIndFullImplWith S ki)
        ((simulateQ (bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhKindHandleWith (S := S) (ℓ := ℓ) P ki C K qep decT encT)) B).run
          { σ0 with st := bhKindDummySt S })).run σ0.st >>=
      fun x =>
        if !allTestedSessionsFresh P x.2 then $ᵗ Bool >>= fun coin => pure coin
        else pure ((x.1.1 == x.1.2.b || bhE2EDrvWon x.1.2 x.1.2.b) == secb)] =
    𝒟[(simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) B).run σ0 >>=
      fun x =>
        (if !allTestedSessionsFresh P x.2.st then $ᵗ Bool else pure (x.1 == b || bhE2EDrvWon x.2 b)) >>=
          fun z => pure (secb == z)]
  rw [hRun, ← hRunB]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    bhE2EDrvWon_with_b_aux]
  refine evalDist_bind_congr ((simulateQ (bhE2EDrvImplWith P ki C K qep decT encT) B).run σ0) _ _
    fun ⟨b', σ'⟩ => ?_
  have hSt : ({ σ' with b := σ0.b } : BHE2EDrvState S ℓ).st = σ'.st := rfl
  have hB : ({ σ' with b := σ0.b, st := bhKindDummySt S } : BHE2EDrvState S ℓ).b = b := rfl
  have hWon : bhE2EDrvWon ({ σ' with b := σ0.b, st := bhKindDummySt S } : BHE2EDrvState S ℓ) b =
      bhE2EDrvWon σ' b := rfl
  dsimp only
  rw [hSt, hB, hWon]
  by_cases hClean : allTestedSessionsFresh P σ'.st = true
  · simp [hClean, Bool.beq_comm]
  · have hNotClean : (!allTestedSessionsFresh P σ'.st) = true := by
      cases hc : allTestedSessionsFresh P σ'.st <;> simp_all
    simp only [hNotClean, ↓reduceIte, bind_pure]
    exact (evalDist_uniformBool_beq_with secb).symm

/-- `pqxdhKeyIndExpForHandshake S P ki` on `bhKindRedWith` has the distribution of the uniform-bit
distinguishing game between `bhE2EExpWithKi true` and `bhE2EExpWithKi false`. -/
theorem evalDist_pqxdhKeyIndExpWith_bhKindRedWith (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[pqxdhKeyIndExpForHandshake S P ki
        ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B) ()⟩] =
    𝒟[do
      let secb ← $ᵗ Bool
      let z ← if secb then bhE2EExpWithKi true S P ki C K ℓ qep decT encT B
               else bhE2EExpWithKi false S P ki C K ℓ qep decT encT B
      return (secb == z)] := by
  unfold pqxdhKeyIndExpForHandshake
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun secb => ?_
  cases secb
  · exact evalDist_bhKindRedWith_branch false S P ki C K ℓ qep decT encT B
  · exact evalDist_bhKindRedWith_branch true S P ki C K ℓ qep decT encT B

theorem boolBias_pqxdhKeyIndExpWith_bhKindRedWith (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[pqxdhKeyIndExpForHandshake S P ki
        ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B) ()⟩].boolBias =
      𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B].boolDist
        𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B] := by
  rw [evalDist_pqxdhKeyIndExpWith_bhKindRedWith, evalDist_boolBias_bind_uniformBool]

theorem keyIndAdvantageWith_bhKindRedWith (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    KeyIndAdvantageForHandshake S P ki
        ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B) ()⟩ =
      𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B].boolDist
        𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B] :=
  boolBias_pqxdhKeyIndExpWith_bhKindRedWith S P ki C K ℓ qep decT encT B

/-- For any `KeyInd` handler `ki`, the `boolBias` of `bhE2EExpWithKi true` is at most twice
`KeyIndAdvantageForHandshake` on `bhKindRedWith` plus the `boolBias` of `bhE2EExpWithKi false`. -/
theorem boolBias_bhE2EExpWithKi_true_le (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B].boolBias ≤
      2 * KeyIndAdvantageForHandshake S P ki
            ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B].boolBias := by
  rw [keyIndAdvantageWith_bhKindRedWith, add_comm]
  exact SM.Construction.boolBias_le_add_two_mul_boolDist
    𝒟[bhE2EExpWithKi true S P ki C K ℓ qep decT encT B]
    𝒟[bhE2EExpWithKi false S P ki C K ℓ qep decT encT B]

@[simp]
theorem pqxdhKeyIndExpWith_1KeyReal_eq (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (A : SignalPqxdh.KeyIndAdversary S) :
    pqxdhKeyIndExpForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) A =
      SignalPqxdh.pqxdhKeyInd1KeyRealExp S P A := rfl

@[simp]
theorem keyIndAdvantageWith_1KeyReal_eq (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (A : SignalPqxdh.KeyIndAdversary S) :
    KeyIndAdvantageForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) A =
      SignalPqxdh.KeyInd1KeyRealAdvantage S P A := rfl

/-- Specialization of `boolBias_bhE2EExpWithKi_true_le` to `SignalPqxdh.pqxdhKeyIndImpl1KeyReal`. -/
theorem boolBias_bhE2EExpWithKi_1KeyReal_true_le (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT B].boolBias ≤
      2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P
            ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
              C K qep decT encT).eval (fun _ => B) ()⟩ +
        𝒟[bhE2EExpWithKi false S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT B].boolBias := by
  rw [← keyIndAdvantageWith_1KeyReal_eq]
  exact boolBias_bhE2EExpWithKi_true_le S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT B

end CryptoVerification.E2E
