/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness

/-!
# One-Stage Simulation Engine for Atomic Handshake Reductions

Proves `simulateQ`, `.eval`, and `pqxdhKeyIndExpForHandshake` distribution equivalence between a
one-stage `CostedReduction` over `e2eKeyIndTargetIface` and a shallow `BhShallowRed` reference
reduction under a per-step driver invariant.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.KindRedHaltedEval

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp CostedReduction atomicSig
  e2eKeyIndTargetIface keyIndRenc keyIndRdec smRT smRdec recvResultEnc recvResultDec GhostStT)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (Bytes BHE2ESmResp BHTargetQuery BHTargetResp BhShallowRed
  bhShallowImplOfHandle bhTargetGameSpec e2eTargetGameCodec bhTargetQenc bhTargetRdec
  bhUnpackSmResp bhFwdU bhLiftP pqxdhKeyIndExpForHandshake bhClassifyTarget bhClassifyTargetOnly)

/-! ## Response codecs and lift helpers -/

@[simp] private theorem recvResultDec_recvResultEnc {ℓ : ℕ} {Pt : Type}
    (rr : CryptoGames.SM.RecvResult (Plain ℓ)) :
    recvResultDec (ℓ := ℓ) (Pt := Pt) (recvResultEnc rr) = rr := by
  cases rr <;> rfl

@[expose] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

@[simp] theorem smRdec_id_packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (br : BHE2ESmResp ℓ) :
    smRdec (ℓ := ℓ) (Pt := Pt) (stT := GhostStT) id sq (packAtomicSmRespEnc br) =
      bhUnpackSmResp sq br := by
  rcases br with ⟨w, rr?, st?⟩
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases st? <;> rfl

@[simp] private theorem keyIndRdec_keyIndRenc {ℓ : ℕ} {Pt : Type}
    (kr : SignalPqxdh.KeyIndResponse) :
    keyIndRdec (ℓ := ℓ) (Pt := Pt) (keyIndRenc kr) = kr := by
  cases kr <;> rfl

@[expose] def atomicKindRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} :
    BHTargetResp ℓ → (e2eTargetGameCodec S ℓ Pt).R.denote
  | .inl (.inl kr) => .inl (.inl (keyIndRenc kr))
  | .inl (.inr idx?) => .inl (.inr idx?)
  | .inr sr => .inr (packAtomicSmRespEnc sr)

@[simp] theorem e2eTargetGameCodec_rdec_atomicKindRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type} (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (r : BHTargetResp ℓ) :
    (e2eTargetGameCodec S ℓ Pt).rdec t (atomicKindRespEnc (S := S) (Pt := Pt) r) =
      bhTargetRdec t r := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · rcases r with (kr | idx?) | sr
    · exact keyIndRdec_keyIndRenc kr
    · rfl
    · rfl
  · rcases cq with ⟨sid⟩
    rcases r with (kr | idx?) | sr <;> rfl
  · rcases r with (kr | idx?) | sr
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · exact smRdec_id_packAtomicSmRespEnc sq sr

@[simp] theorem atomicKeyIndTargetIface_fwdU_eq_bhFwdU {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (n : unifSpec.Domain) :
    (e2eKeyIndTargetIface S ℓ Pt).fwdU n = bhFwdU n := rfl

@[simp] theorem atomicKeyIndTargetIface_liftP_eq_bhLiftP {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {α : Type} (p : ProbComp α) :
    (e2eKeyIndTargetIface S ℓ Pt).liftP p = bhLiftP p := rfl

theorem mem_support_of_bhLiftP {κ α : Type} {G : OracleSpec κ} (p : ProbComp α) {x : α}
    (hx : x ∈ support (bhLiftP (G := G) p)) : x ∈ support p := by
  induction p using OracleComp.inductionOn generalizing x with
  | pure a => simpa [bhLiftP] using hx
  | query_bind n mx ih =>
    simp only [bhLiftP, simulateQ_query_bind, mem_support_bind_iff] at hx ⊢
    rcases hx with ⟨v, -, hxv⟩
    exact ⟨v, mem_support_query n v, ih v hxv⟩

/-! ## Simulation specification -/

@[expose] def StepBudgetOk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (b : SignalPqxdh.QueryBudget) (qStart qDR qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) : Prop :=
  match t with
  | .inl (.inl _) => qKiDone + 1 ≤ b.q_total
  | .inl (.inr _) => qStartDone + 1 ≤ qStart
  | .inr _ => qDrDone + 1 ≤ qDR

@[expose] def StepNextInv {S : SignalPqxdh.Setup} {ℓ : ℕ} {DrvSt : Type}
    (Inv : ℕ → ℕ → ℕ → DrvSt → Prop)
    (qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (σ1 : DrvSt) : Prop :=
  match t with
  | .inl (.inl _) => Inv (qKiDone + 1) qStartDone qDrDone σ1
  | .inl (.inr _) => Inv qKiDone (qStartDone + 1) qDrDone σ1
  | .inr _ => Inv qKiDone qStartDone (qDrDone + 1) σ1

structure OneStageTargetBounded (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) : Prop where
  tot : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
    b.q_total
  start : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    qStart
  dr : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    qDR

/-- Step-level simulation contract between a costed one-stage reduction and a `BhShallowRed` reference reduction. -/
structure OneStageAtomicSimSpec (S : SignalPqxdh.Setup) (Pt : Type) (ℓ : ℕ)
    (O : Ops (atomicSig ℓ Pt))
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) (DrvSt : Type) where
  R : CostedReduction O (e2eKeyIndTargetIface S ℓ Pt)
    (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
    .unit .unit .bool .bool
  handleRef : DrvSt → BHTargetQuery S ℓ (BitVec 512) →
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) (BHTargetResp ℓ × DrvSt)
  R_ref : BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
    (unifSpec + SignalPqxdh.keyIndSpec S) Unit Bool Unit Bool DrvSt
  drvEnc : DrvSt → R.σ.denote
  Inv : ℕ → ℕ → ℕ → DrvSt → Prop
  impl_eq : R_ref.impl = bhShallowImplOfHandle bhTargetQenc bhTargetRdec handleRef
  init_eq : R.init.eval (.cons () .nil) = Prod.map id drvEnc <$> R_ref.init ()
  init_inv : ∀ us ∈ support (R_ref.init ()), Inv 0 0 0 us.2
  step_eq : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      R.handle.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        Prod.map atomicKindRespEnc drvEnc <$> handleRef σ (bhTargetQenc t)
  step_inv : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      ∀ rs ∈ support (handleRef σ (bhTargetQenc t)),
        StepNextInv Inv qKiDone qStartDone qDrDone t rs.2
  finish_eq : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ_out : DrvSt},
    Inv qKiDone qStartDone qDrDone σ_out →
    ∀ b_out : Bool,
      R.finish.eval (.cons (drvEnc σ_out) (.cons b_out .nil)) =
        R_ref.finish σ_out b_out

/-! ## Evaluation and handshake experiment equivalence -/

section SimProofs

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {O : Ops (atomicSig ℓ Pt)}
  {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ} {DrvSt : Type}

theorem oneStage_simulateQ_eq_and_inv
    (spec : OneStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt) :
    ∀ {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ) (σ : DrvSt),
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
        qKiRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStartRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
        qDrRem →
      qKiDone + qKiRem ≤ b.q_total →
      qStartDone + qStartRem ≤ qStart →
      qDrDone + qDrRem ≤ qDR →
      spec.Inv qKiDone qStartDone qDrDone σ →
      ((simulateQ spec.R.impl oa).run (spec.drvEnc σ) =
        Prod.map id spec.drvEnc <$> (simulateQ spec.R_ref.impl oa).run σ) ∧
      (∀ p ∈ support ((simulateQ spec.R_ref.impl oa).run σ),
        ∃ qKi1 qSt1 qDr1, spec.Inv qKi1 qSt1 qDr1 p.2) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qKiDone _ qStartDone _ qDrDone _ σ _ _ _ _ _ _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map_apply], fun p hp => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    intro qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      hTot hStart hDr hqKi hqSt hqDr hInv
    rw [isQueryBoundP_query_bind_iff] at hTot hStart hDr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    cases q with
    | inl n =>
      have hStepDsl : ((spec.R.impl (.inl n)).run (spec.drvEnc σ)) =
          (bhFwdU n >>= fun u => pure (u, spec.drvEnc σ)) := rfl
      have hStepRef : ((spec.R_ref.impl (.inl n)).run σ) =
          (bhFwdU n >>= fun u => pure (u, σ)) := by
        rw [spec.impl_eq]; rfl
      rw [hStepDsl, hStepRef]
      simp only [bind_assoc, pure_bind]
      refine ⟨bind_congr fun u => ?_, fun p hp => ?_⟩
      · exact (ih u qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          ((hTot.2 u).mono (by simp [bhClassifyTarget]))
          ((hStart.2 u).mono (by simp [bhClassifyTarget]))
          ((hDr.2 u).mono (by simp [bhClassifyTarget]))
          hqKi hqSt hqDr hInv).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨u, -, hpu⟩
        exact (ih u qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          ((hTot.2 u).mono (by simp [bhClassifyTarget]))
          ((hStart.2 u).mono (by simp [bhClassifyTarget]))
          ((hDr.2 u).mono (by simp [bhClassifyTarget]))
          hqKi hqSt hqDr hInv).2 p hpu
    | inr t =>
      have htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t := by
        rcases ht : t with (kq | cq) | ⟨i, sq⟩
        · dsimp only [StepBudgetOk]
          have hpos : 0 < qKiRem :=
            hTot.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
          omega
        · dsimp only [StepBudgetOk]
          have hpos : 0 < qStartRem :=
            hStart.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
          omega
        · dsimp only [StepBudgetOk]
          have hpos : 0 < qDrRem :=
            hDr.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
          omega
      have hStepDsl : ((spec.R.impl (.inr t)).run (spec.drvEnc σ)) =
          (spec.R.handle.eval
            (.cons (spec.drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ Pt).rdec t p.1, p.2)) := rfl
      have hStepRef : ((spec.R_ref.impl (.inr t)).run σ) =
          (spec.handleRef σ (bhTargetQenc t) >>=
            fun rs => pure (bhTargetRdec t rs.1, rs.2)) := by
        rw [spec.impl_eq]; rfl
      rw [hStepDsl, hStepRef, spec.step_eq hInv t htBound]
      simp only [bind_map_left, bind_assoc, pure_bind]
      have hResInv := spec.step_inv hInv t htBound
      refine ⟨bind_congr_of_forall_mem_support _ fun rs hrs => ?_, fun p hp => ?_⟩
      · have hAns := e2eTargetGameCodec_rdec_atomicKindRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t rs.1
        dsimp only [Prod.map, e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
        rw [hAns]
        have hR := hResInv rs hrs
        rcases t with (kq | cq) | ⟨i, sq⟩
        · have hpos : 0 < qKiRem :=
            hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (by omega) hqSt hqDr hR).1
        · have hpos : 0 < qStartRem :=
            hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi (by omega) hqDr hR).1
        · have hpos : 0 < qDrRem :=
            hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqSt (by omega) hR).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨rs, hrs, hprs⟩
        have hR := hResInv rs hrs
        rcases t with (kq | cq) | ⟨i, sq⟩
        · have hpos : 0 < qKiRem :=
            hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            (by omega) hqSt hqDr hR).2 p hprs
        · have hpos : 0 < qStartRem :=
            hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi (by omega) hqDr hR).2 p hprs
        · have hpos : 0 < qDrRem :=
            hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
          exact (ih _ qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) rs.2
            ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
            hqKi hqSt (by omega) hR).2 p hprs

/-- Evaluation equivalence between `spec.R` and `spec.R_ref` on any `OneStageTargetBounded` adversary. -/
theorem oneStage_eval_eq
    (spec : OneStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : OneStageTargetBounded S B_A b qStart qDR) :
    spec.R.eval (fun _ => B_A) () = spec.R_ref.eval (fun _ => B_A) () := by
  unfold CostedReduction.eval BhShallowRed.eval
  rw [spec.init_eq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun ⟨_, σ0⟩ hσ0 => ?_
  dsimp only [Prod.map, id_eq]
  have ⟨hSimEq, hSimInv⟩ := oneStage_simulateQ_eq_and_inv spec B_A
    0 b.q_total 0 qStart 0 qDR σ0
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega)
    (spec.init_inv _ hσ0)
  rw [hSimEq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
  rcases hSimInv (b_out, σ_out) hout with ⟨qKi1, qSt1, qDr1, hInvOut⟩
  dsimp only [Prod.map, id_eq]
  exact spec.finish_eq hInvOut b_out

/-- Handshake experiment distribution equality between `spec.R` and `spec.R_ref` for any `KeyInd` handler `ki`. -/
theorem evalDist_pqxdhKeyIndExp_oneStage_eq
    (spec : OneStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : OneStageTargetBounded S B_A b qStart qDR) :
    𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨spec.R.eval (fun _ => B_A) ()⟩] =
      𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨spec.R_ref.eval (fun _ => B_A) ()⟩] := by
  rw [oneStage_eval_eq spec B_A hB]

end SimProofs

end Computational.Proofs.E2E.Dsl.KindRedHaltedEval
