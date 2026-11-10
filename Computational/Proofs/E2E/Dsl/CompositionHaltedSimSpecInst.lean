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
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Per-Instance One-Stage and Two-Stage Simulation Engines

Proves one-stage and two-stage `ReductionDsl` simulation theorems over `atomicSig ℓ Pt` under
per-instance query bounds `HaltedTargetAdvPerInstanceBounded`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction runFuel atomicSig e2eKeyIndTargetIface e2eSessionTargetIface prefixCtxT)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (GhostState IdentityKey)
open CryptoVerification.E2E (BHTargetQuery BHTargetResp BHPrefixCtx BhShallowRed
  BhShallowTwoStageRed Bytes bhFwdU bhShallowImplOfHandle bhShallowRunFuel bhShallowRunFuel_pure
  bhShallowRunFuel_query_inl bhShallowRunFuel_query_inr_zero bhShallowRunFuel_query_inr_succ
  bhTargetGameSpec bhTargetQenc bhTargetRdec e2eTargetGameCodec isSmTargetQuery
  pqxdhKeyIndExpForHandshake stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (bhClassifyTarget bhClassifyTargetOnly)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedTargetAdvPerInstanceBounded)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (isQueryBoundP_min isSendKiQuery
  nextSendDone nextSessDone)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval (atomicKindRespEnc
  e2eTargetGameCodec_rdec_atomicKindRespEnc)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval (atomicGameRespEnc atomicPrefixCtxEnc
  atomicSessionTargetIface_fwdU_eq_bhFwdU e2eTargetGameCodec_rdec_atomicGameRespEnc
  mapMidEnc mapOut1Enc mapPreEnc mem_support_of_mem_support_stageOneAsProbComp)

private theorem run1_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (pure a) f s = pure (.done a s) := by
  simp only [TwoStageCostedReduction.run1, construct_pure]

private theorem run1_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (.done dflt s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (R.handlePre.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun res =>
        match res with
        | .inl (v, s') => R.run1 dflt (mx (C0.rdec t v)) f s'
        | .inr (c, p, s') => pure (.paused t c p s' mx)) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]
  refine bind_congr fun res => ?_
  rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl

private theorem runFuel_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (pure a) f s = pure (a, s) := by
  simp only [runFuel, construct_pure]

private theorem runFuel_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => runFuel (C := C0) h dflt (mx u) f s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (dflt, s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (h.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun p =>
        runFuel (C := C0) h dflt (mx (C0.rdec t p.1)) f p.2) := by
  simp only [runFuel, construct_query_bind]

private theorem isQueryBoundP_atomicSessionTargetIface_fwdU {ℓ : ℕ} {Pt : Type} (n : ℕ) :
    ((e2eSessionTargetIface ℓ Pt).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
  dsimp only [e2eSessionTargetIface]
  exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (by simp [isSmTargetQuery])

/-! ## One-stage simulation -/

@[expose] def StepBudgetOkInst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) : Prop :=
  match t with
  | .inl (.inl kq) =>
    qKiDone + 1 ≤ b.q_total ∧
    (isSendKiQuery kq = true → qSendDone + 1 ≤ S.N_send_tot)
  | .inl (.inr _) =>
    qStartDone + 1 ≤ min qStart S.N_send_tot
  | .inr (i, _) =>
    i < qStart → qSessDone i + 1 ≤ qs i

@[expose] def StepNextInvInst {S : SignalPqxdh.Setup} {ℓ : ℕ} {DrvSt : Type}
    (Inv : ℕ → ℕ → ℕ → (ℕ → ℕ) → DrvSt → Prop)
    (qStart qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (σ1 : DrvSt) : Prop :=
  match t with
  | .inl (.inl kq) =>
    Inv (qKiDone + 1) (nextSendDone qSendDone kq) qStartDone qSessDone σ1
  | .inl (.inr _) =>
    Inv qKiDone qSendDone (qStartDone + 1) qSessDone σ1
  | .inr (i, _) =>
    Inv qKiDone qSendDone qStartDone (nextSessDone qStart qSessDone i) σ1

def nextSessRem (qStart : ℕ) (qSessRem : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  fun j => if i < qStart ∧ j = i then qSessRem j - 1 else qSessRem j

abbrev isKiQ {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
  fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true

abbrev isSendQ {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
  fun q => bhClassifyTarget
    (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
    (fun _ => false) (fun _ => false) q = true

abbrev isStartQ {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
  fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true

abbrev isSessQ {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) :
    (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
  fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true

private instance {S : SignalPqxdh.Setup} {ℓ : ℕ} : DecidablePred (isKiQ (S := S) (ℓ := ℓ)) :=
  fun _ => inferInstanceAs (Decidable (_ = true))
private instance {S : SignalPqxdh.Setup} {ℓ : ℕ} : DecidablePred (isSendQ (S := S) (ℓ := ℓ)) :=
  fun _ => inferInstanceAs (Decidable (_ = true))
private instance {S : SignalPqxdh.Setup} {ℓ : ℕ} : DecidablePred (isStartQ (S := S) (ℓ := ℓ)) :=
  fun _ => inferInstanceAs (Decidable (_ = true))
private instance {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) :
    DecidablePred (isSessQ (S := S) (ℓ := ℓ) k) :=
  fun _ => inferInstanceAs (Decidable (_ = true))

theorem isSendQ_inl_inl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (kq : SignalPqxdh.KeyIndQuery S) :
    isSendQ (S := S) (ℓ := ℓ) (.inr (.inl (.inl kq))) ↔ isSendKiQuery kq = true := by
  cases kq <;> simp [isSendQ, isSendKiQuery, bhClassifyTarget, bhClassifyTargetOnly]

/-- One-stage costed simulation contract indexed by per-instance query counters. -/
structure OneStageAtomicSimSpecInst (S : SignalPqxdh.Setup) (Pt : Type) (ℓ : ℕ)
    (O : Ops (atomicSig ℓ Pt))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (DrvSt : Type) where
  R : CostedReduction O (e2eKeyIndTargetIface S ℓ Pt)
    (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
    .unit .unit .bool .bool
  handleRef : DrvSt → BHTargetQuery S ℓ (BitVec 512) →
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) (BHTargetResp ℓ × DrvSt)
  R_ref : BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
    (unifSpec + SignalPqxdh.keyIndSpec S) Unit Bool Unit Bool DrvSt
  drvEnc : DrvSt → R.σ.denote
  Inv : ℕ → ℕ → ℕ → (ℕ → ℕ) → DrvSt → Prop
  impl_eq : R_ref.impl = bhShallowImplOfHandle bhTargetQenc bhTargetRdec handleRef
  init_eq : R.init.eval (.cons () .nil) = Prod.map id drvEnc <$> R_ref.init ()
  init_inv : ∀ us ∈ support (R_ref.init ()), Inv 0 0 0 (fun _ => 0) us.2
  step_eq : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      R.handle.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        Prod.map atomicKindRespEnc drvEnc <$> handleRef σ (bhTargetQenc t)
  step_inv : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      ∀ rs ∈ support (handleRef σ (bhTargetQenc t)),
        StepNextInvInst Inv qStart qKiDone qSendDone qStartDone qSessDone t rs.2
  finish_eq : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ_out : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ_out →
    ∀ b_out : Bool,
      R.finish.eval (.cons (drvEnc σ_out) (.cons b_out .nil)) =
        R_ref.finish σ_out b_out

section OneStageSimProofs

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {O : Ops (atomicSig ℓ Pt)}
  {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ} {DrvSt : Type}

theorem stepBudgetOkInst_of_bounds {α : Type}
    {q : (bhTargetGameSpec S ℓ (BitVec 512)).Domain}
    {mx : (bhTargetGameSpec S ℓ (BitVec 512)).Range q →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α}
    {qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ}
    {qSessDone qSessRem : ℕ → ℕ}
    (hTot : (isKiQ (.inr q) → 0 < qKiRem ∧ ∀ v, (mx v).IsQueryBoundP isKiQ (qKiRem - 1)) ∧
      (¬isKiQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isKiQ qKiRem))
    (hSend : (isSendQ (.inr q) → 0 < qSendRem ∧ ∀ v, (mx v).IsQueryBoundP isSendQ (qSendRem - 1)) ∧
      (¬isSendQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isSendQ qSendRem))
    (hStart : (isStartQ (.inr q) → 0 < qStartRem ∧ ∀ v, (mx v).IsQueryBoundP isStartQ (qStartRem - 1)) ∧
      (¬isStartQ (.inr q) → ∀ v, (mx v).IsQueryBoundP isStartQ qStartRem))
    (hSess : ∀ k < qStart,
      (isSessQ k (.inr q) → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
      (¬isSessQ k (.inr q) → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)))
    (hqKi : qKiDone + qKiRem ≤ b.q_total)
    (hqSend : qSendDone + qSendRem ≤ S.N_send_tot)
    (hqSt : qStartDone + qStartRem ≤ min qStart S.N_send_tot)
    (hqSess : ∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) :
    StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone q := by
  rcases hq : q with (kq | cq) | ⟨i, sq⟩
  · dsimp only [StepBudgetOkInst]
    have hpos : 0 < qKiRem :=
      (hTot.1 (by rw [hq]; simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly])).1
    refine ⟨by omega, fun hsk => ?_⟩
    have hposS : 0 < qSendRem :=
      (hSend.1 (by rw [hq]; exact (isSendQ_inl_inl kq).mpr hsk)).1
    omega
  · dsimp only [StepBudgetOkInst]
    have hpos : 0 < qStartRem :=
      (hStart.1 (by rw [hq]; simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])).1
    omega
  · dsimp only [StepBudgetOkInst]
    intro hi
    have hpos : 0 < qSessRem i :=
      ((hSess i hi).1 (by rw [hq]; simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).1
    have hle := hqSess i hi
    omega

private theorem unpack_qb {ι : Type} {spec : OracleSpec ι} {α : Type}
    {P : ι → Prop} [DecidablePred P] {q : ι} {mx : spec.Range q → OracleComp spec α} {n : ℕ}
    (h : (liftM (OracleSpec.query (spec := spec) q) >>= mx).IsQueryBoundP P n) :
    (P q → 0 < n ∧ ∀ v, (mx v).IsQueryBoundP P (n - 1)) ∧
    (¬P q → ∀ v, (mx v).IsQueryBoundP P n) := by
  rw [isQueryBoundP_query_bind_iff] at h
  refine ⟨fun hp => ⟨h.1.resolve_left (fun hnp => hnp hp), fun v => ?_⟩, fun hnp v => ?_⟩
  · simpa [hp] using h.2 v
  · simpa [hnp] using h.2 v

theorem oneStage_simulateQ_eq_and_inv_inst
    (spec : OneStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt) :
    ∀ {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ) (σ : DrvSt),
      oa.IsQueryBoundP isKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k < qStart, oa.IsQueryBoundP (isSessQ k) (qSessRem k)) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) →
      spec.Inv qKiDone qSendDone qStartDone qSessDone σ →
      ((simulateQ spec.R.impl oa).run (spec.drvEnc σ) =
        Prod.map id spec.drvEnc <$> (simulateQ spec.R_ref.impl oa).run σ) ∧
      (∀ p ∈ support ((simulateQ spec.R_ref.impl oa).run σ),
        ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 p.2) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qKiDone _ qSendDone _ qStartDone _ qSessDone _ σ _ _ _ _ _ _ _ _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map_apply], fun p hp => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv
    have hTot := unpack_qb hTot0
    have hSend := unpack_qb hSend0
    have hStart := unpack_qb hStart0
    have hSess' : ∀ k < qStart,
        (isSessQ k q → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
        (¬isSessQ k q → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)) :=
      fun k hk => unpack_qb (hSess k hk)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    cases q with
    | inl n =>
      have hStepDsl : ((spec.R.impl (.inl n)).run (spec.drvEnc σ)) =
          (bhFwdU n >>= fun u => pure (u, spec.drvEnc σ)) := rfl
      have hStepRef : ((spec.R_ref.impl (.inl n)).run σ) =
          (bhFwdU n >>= fun u => pure (u, σ)) := by rw [spec.impl_eq]; rfl
      rw [hStepDsl, hStepRef]
      simp only [bind_assoc, pure_bind]
      have hcKi : ∀ u, (mx u).IsQueryBoundP isKiQ qKiRem :=
        hTot.2 (by simp [isKiQ, bhClassifyTarget])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClassifyTarget])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClassifyTarget])
      have hcSess : ∀ u k, k < qStart → (mx u).IsQueryBoundP (isSessQ k) (qSessRem k) :=
        fun u k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget]) u
      refine ⟨bind_congr fun u => ?_, fun p hp => ?_⟩
      · exact (ih u qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨u, -, hpu⟩
        exact (ih u qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).2 p hpu
    | inr t =>
      have htBound := stepBudgetOkInst_of_bounds hTot hSend hStart hSess' hqKi hqSend hqSt hqSess
      have hStepDsl : ((spec.R.impl (.inr t)).run (spec.drvEnc σ)) =
          (spec.R.handle.eval
            (.cons (spec.drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ Pt).rdec t p.1, p.2)) := rfl
      have hStepRef : ((spec.R_ref.impl (.inr t)).run σ) =
          (spec.handleRef σ (bhTargetQenc t) >>=
            fun rs => pure (bhTargetRdec t rs.1, rs.2)) := by rw [spec.impl_eq]; rfl
      rw [hStepDsl, hStepRef, spec.step_eq hInv t htBound]
      simp only [bind_map_left, bind_assoc, pure_bind]
      have hResInv := spec.step_inv hInv t htBound
      have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t) (σ1 : DrvSt),
          StepNextInvInst spec.Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1 →
          ((simulateQ spec.R.impl (mx v)).run (spec.drvEnc σ1) =
            Prod.map id spec.drvEnc <$> (simulateQ spec.R_ref.impl (mx v)).run σ1) ∧
          (∀ p ∈ support ((simulateQ spec.R_ref.impl (mx v)).run σ1),
            ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 p.2) := by
        intro v σ1 hR
        rcases t with (kq | cq) | ⟨i, sq⟩
        · have hKi1 := hTot.1 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
            fun k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          by_cases hsk : isSendKiQuery kq = true
          · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
            have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
            dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
            exact ih v (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
              qStartDone qStartRem qSessDone qSessRem σ1
              (hKi1.2 v) (hSend1.2 v) hcSt hcSess
              (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR
          · have hSend0 := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
            have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
            dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
            exact ih v (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ1
              (hKi1.2 v) hSend0 hcSt hcSess
              (by have := hKi1.1; omega) hqSend hqSt hqSess hR
        · have hSt1 := hStart.1 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
            fun k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          exact ih v qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
            qSessDone qSessRem σ1
            hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR
        · have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart,
              (mx v).IsQueryBoundP (isSessQ k) (nextSessRem qStart qSessRem i k) := by
            intro k hk
            dsimp only [nextSessRem]
            split_ifs with hki
            · rcases hki with ⟨_, rfl⟩
              exact ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).2 v
            · have hne : i ≠ k := fun h => hki ⟨h ▸ hk, h.symm⟩
              exact (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly, hne]) v
          have hqSess' : ∀ k < qStart,
              nextSessDone qStart qSessDone i k + nextSessRem qStart qSessRem i k ≤ qs k := by
            intro k hk
            dsimp only [nextSessDone, nextSessRem]
            split_ifs with hki
            · rcases hki with ⟨_, rfl⟩
              have hpos :=
                ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).1
              have hle := hqSess k hk
              omega
            · exact hqSess k hk
          exact ih v qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
            (nextSessDone qStart qSessDone i) (nextSessRem qStart qSessRem i) σ1
            hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR
      refine ⟨bind_congr_of_forall_mem_support _ fun rs hrs => ?_, fun p hp => ?_⟩
      · have hAns := e2eTargetGameCodec_rdec_atomicKindRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t rs.1
        dsimp only [Prod.map, e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
        rw [hAns]
        exact (hCont (bhTargetRdec t rs.1) rs.2 (hResInv rs hrs)).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨rs, hrs, hprs⟩
        exact (hCont (bhTargetRdec t rs.1) rs.2 (hResInv rs hrs)).2 p hprs

/-- Evaluation equivalence between `spec.R` and `spec.R_ref` for any bounded adversary. -/
theorem oneStage_eval_eq_inst
    (spec : OneStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    spec.R.eval (fun _ => B_A) () = spec.R_ref.eval (fun _ => B_A) () := by
  rcases hB with ⟨_, hSend, _, hTot, _, hStSend, hStQ, _, hSess⟩
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  unfold CostedReduction.eval BhShallowRed.eval
  rw [spec.init_eq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun ⟨_, σ0⟩ hσ0 => ?_
  dsimp only [Prod.map, id_eq]
  have ⟨hSimEq, hSimInv⟩ := oneStage_simulateQ_eq_and_inv_inst spec B_A
    0 b.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs σ0
    hTot hSend hStMin hSess (by omega) (by omega) (by omega) (fun k _ => by omega)
    (spec.init_inv _ hσ0)
  rw [hSimEq, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
  rcases hSimInv (b_out, σ_out) hout with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
  dsimp only [Prod.map, id_eq]
  exact spec.finish_eq hInvOut b_out

theorem evalDist_pqxdhKeyIndExp_oneStage_eq_inst
    (spec : OneStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨spec.R.eval (fun _ => B_A) ()⟩] =
      𝒟[pqxdhKeyIndExpForHandshake S P ki ⟨spec.R_ref.eval (fun _ => B_A) ()⟩] := by
  rw [oneStage_eval_eq_inst spec B_A hB]

end OneStageSimProofs

/-! ## Two-stage simulation -/

/-- Two-stage costed simulation contract indexed by per-instance query counters. -/
structure TwoStageAtomicSimSpecInst (S : SignalPqxdh.Setup) (Pt : Type) (ℓ : ℕ)
    (O : Ops (atomicSig ℓ Pt))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (DrvSt π_ref : Type) where
  R : TwoStageCostedReduction O (e2eSessionTargetIface ℓ Pt)
    (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
    .unit .unit .bool (prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool
  R_ref : BhShallowTwoStageRed
    (bhTargetGameSpec S ℓ (BitVec 512))
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (BHTargetQuery S ℓ (BitVec 512)) (BHTargetResp ℓ)
    Unit Unit Bool BHPrefixCtx Bool Bool DrvSt π_ref
  drvEnc : DrvSt → R.σ.denote
  πEnc : π_ref → R.π.denote
  σ0 : DrvSt
  Inv : ℕ → ℕ → ℕ → (ℕ → ℕ) → DrvSt → Prop
  PausedInv : DrvSt → Prop
  qenc_eq : ∀ t, R_ref.qenc t = bhTargetQenc t
  rdec_eq : ∀ t r, R_ref.rdec t r = bhTargetRdec t r
  stage1_queries_zero :
    R.init.queries (fun _ => 1) (fun _ => 0) +
      R.handlePre.queries (fun _ => 1) (fun _ => 0) +
      R.chDone.queries (fun _ => 1) (fun _ => 0) = 0
  init_inv : Inv 0 0 0 (fun _ => 0) σ0
  init_costed : R.init.eval (.cons () .nil) = pure ((), drvEnc σ0)
  init_ref : R_ref.init () = pure ((), σ0)
  chDone_eq : ∀ {qKi1 qSend1 qSt1 : ℕ} {qSess1 : ℕ → ℕ} {σ_out : DrvSt},
    Inv qKi1 qSend1 qSt1 qSess1 σ_out →
    ∀ b_out : Bool,
      R.chDone.eval (.cons (drvEnc σ_out) (.cons b_out .nil)) =
        atomicPrefixCtxEnc <$> R_ref.chDone σ_out b_out
  resume_eq : ∀ {qKi1 qSend1 qSt1 : ℕ} {qSess1 : ℕ → ℕ} {σ_p : DrvSt},
    Inv qKi1 qSend1 qSt1 qSess1 σ_p → PausedInv σ_p →
    ∀ (p : π_ref) (flip : Bool),
      R.resume.eval (.cons (drvEnc σ_p) (.cons (πEnc p) (.cons flip .nil))) =
        Prod.map atomicGameRespEnc drvEnc <$> R_ref.resume σ_p p flip
  resume_inv : ∀ {qKi1 qSend1 qSt1 : ℕ} {qSess1 : ℕ → ℕ} {σ_p : DrvSt},
    Inv qKi1 qSend1 qSt1 qSess1 σ_p → PausedInv σ_p →
    ∀ (p : π_ref) (flip : Bool),
      ∀ rs ∈ support (R_ref.resume σ_p p flip),
        Inv qKi1 qSend1 qSt1 qSess1 rs.2 ∧ PausedInv rs.2
  stepPre_eq : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      R.handlePre.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        mapPreEnc drvEnc πEnc <$> R_ref.handlePre σ (bhTargetQenc t)
  stepPre_inv : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      ∀ res ∈ support (R_ref.handlePre σ (bhTargetQenc t)),
        match res with
        | .inl (_, σ1) => StepNextInvInst Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1
        | .inr (_, _, σ1) =>
          (∃ cq, t = .inl (.inr cq)) ∧
          Inv qKiDone qSendDone (qStartDone + 1) qSessDone σ1 ∧
          PausedInv σ1
  stepPost_eq : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ → PausedInv σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      R.handlePost.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        Prod.map atomicGameRespEnc drvEnc <$> R_ref.handlePost σ (bhTargetQenc t)
  stepPost_inv : ∀ {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ} {σ : DrvSt},
    Inv qKiDone qSendDone qStartDone qSessDone σ → PausedInv σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t →
      ∀ p ∈ support (R_ref.handlePost σ (bhTargetQenc t)),
        PausedInv p.2 ∧ StepNextInvInst Inv qStart qKiDone qSendDone qStartDone qSessDone t p.2
  finish_eq : ∀ {qKi2 qSend2 qSt2 : ℕ} {qSess2 : ℕ → ℕ} {σ_out : DrvSt},
    Inv qKi2 qSend2 qSt2 qSess2 σ_out →
    ∀ (b_out flip : Bool),
      R.finish.eval (.cons (drvEnc σ_out) (.cons b_out (.cons flip .nil))) =
        R_ref.finish σ_out b_out flip

section TwoStageSimProofs

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {O : Ops (atomicSig ℓ Pt)}
  {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ} {DrvSt π_ref : Type}

theorem twoStage_run1_eq_and_inv_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    {α : Type} (dflt : α) :
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ) (σ : DrvSt),
      oa.IsQueryBoundP isKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k < qStart, oa.IsQueryBoundP (isSessQ k) (qSessRem k)) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) →
      spec.Inv qKiDone qSendDone qStartDone qSessDone σ →
      (spec.R.run1 dflt oa fuel (spec.drvEnc σ) =
        mapMidEnc spec.drvEnc spec.πEnc <$> spec.R_ref.run1 dflt oa fuel σ) ∧
      (∀ m ∈ support (spec.R_ref.run1 dflt oa fuel σ),
        match m with
        | .done _ σ_out =>
          ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 σ_out
        | .paused _ _ _ σ_p cont =>
          ∃ (qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 : ℕ) (qSess1 qSessR1 : ℕ → ℕ),
            qKi1 + qKiR1 ≤ b.q_total ∧
            qSend1 + qSendR1 ≤ S.N_send_tot ∧
            qSt1 + qStR1 ≤ min qStart S.N_send_tot ∧
            (∀ k < qStart, qSess1 k + qSessR1 k ≤ qs k) ∧
            spec.Inv qKi1 qSend1 qSt1 qSess1 σ_p ∧
            spec.PausedInv σ_p ∧
            ∀ v,
              (cont v).IsQueryBoundP isKiQ qKiR1 ∧
              (cont v).IsQueryBoundP isSendQ qSendR1 ∧
              (cont v).IsQueryBoundP isStartQ qStR1 ∧
              (∀ k < qStart, (cont v).IsQueryBoundP (isSessQ k) (qSessR1 k))) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone _ qSendDone _ qStartDone _ qSessDone _ σ _ _ _ _ _ _ _ _ hInv
    refine ⟨by rw [run1_pure, BhShallowTwoStageRed.run1_pure, map_pure]; rfl, ?_⟩
    intro m hm
    rw [BhShallowTwoStageRed.run1_pure] at hm
    simp only [support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv
    have hTot := unpack_qb hTot0
    have hSend := unpack_qb hSend0
    have hStart := unpack_qb hStart0
    have hSess' : ∀ k < qStart,
        (isSessQ k q → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
        (¬isSessQ k q → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)) :=
      fun k hk => unpack_qb (hSess k hk)
    cases q with
    | inl n =>
      have hcKi : ∀ u, (mx u).IsQueryBoundP isKiQ qKiRem :=
        hTot.2 (by simp [isKiQ, bhClassifyTarget])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClassifyTarget])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClassifyTarget])
      have hcSess : ∀ u k, k < qStart → (mx u).IsQueryBoundP (isSessQ k) (qSessRem k) :=
        fun u k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget]) u
      refine ⟨?_, ?_⟩
      · rw [run1_query_inl, BhShallowTwoStageRed.run1_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
            (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).1
      · intro m hm
        rw [BhShallowTwoStageRed.run1_query_inl, mem_support_bind_iff] at hm
        rcases hm with ⟨u, -, hmu⟩
        exact (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).2 m hmu
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [run1_query_inr_zero, BhShallowTwoStageRed.run1_query_inr_zero, map_pure]; rfl,
          ?_⟩
        intro m hm
        rw [BhShallowTwoStageRed.run1_query_inr_zero] at hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
      | succ f =>
        have htBound := stepBudgetOkInst_of_bounds hTot hSend hStart hSess' hqKi hqSend hqSt hqSess
        have hStepEq := spec.stepPre_eq hInv t htBound
        have hResInv := spec.stepPre_inv hInv t htBound
        have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t) (σ1 : DrvSt),
            StepNextInvInst spec.Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1 →
            (spec.R.run1 dflt (mx v) f (spec.drvEnc σ1) =
              mapMidEnc spec.drvEnc spec.πEnc <$> spec.R_ref.run1 dflt (mx v) f σ1) ∧
            (∀ m ∈ support (spec.R_ref.run1 dflt (mx v) f σ1),
              match m with
              | .done _ σ_out =>
                ∃ qKi1 qSend1 qSt1 qSess1, spec.Inv qKi1 qSend1 qSt1 qSess1 σ_out
              | .paused _ _ _ σ_p cont =>
                ∃ (qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 : ℕ) (qSess1 qSessR1 : ℕ → ℕ),
                  qKi1 + qKiR1 ≤ b.q_total ∧
                  qSend1 + qSendR1 ≤ S.N_send_tot ∧
                  qSt1 + qStR1 ≤ min qStart S.N_send_tot ∧
                  (∀ k < qStart, qSess1 k + qSessR1 k ≤ qs k) ∧
                  spec.Inv qKi1 qSend1 qSt1 qSess1 σ_p ∧
                  spec.PausedInv σ_p ∧
                  ∀ w,
                    (cont w).IsQueryBoundP isKiQ qKiR1 ∧
                    (cont w).IsQueryBoundP isSendQ qSendR1 ∧
                    (cont w).IsQueryBoundP isStartQ qStR1 ∧
                    (∀ k < qStart, (cont w).IsQueryBoundP (isSessQ k) (qSessR1 k))) := by
          intro v σ1 hR
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hKi1 := hTot.1 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly])
            have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
              fun k hk => (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            by_cases hsk : isSendKiQuery kq = true
            · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
              have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
              dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
              exact ih v f (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
                qStartDone qStartRem qSessDone qSessRem σ1
                (hKi1.2 v) (hSend1.2 v) hcSt hcSess
                (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR
            · have hSend0 := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
              have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
              dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
              exact ih v f (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
                qStartDone qStartRem qSessDone qSessRem σ1
                (hKi1.2 v) hSend0 hcSt hcSess
                (by have := hKi1.1; omega) hqSend hqSt hqSess hR
          · have hSt1 := hStart.1 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
            have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
              fun k hk => (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            exact ih v f qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
              qSessDone qSessRem σ1
              hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR
          · have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart,
                (mx v).IsQueryBoundP (isSessQ k) (nextSessRem qStart qSessRem i k) := by
              intro k hk
              dsimp only [nextSessRem]
              split_ifs with hki
              · rcases hki with ⟨_, rfl⟩
                exact ((hSess' k hk).1
                  (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).2 v
              · have hne : i ≠ k := fun h => hki ⟨h ▸ hk, h.symm⟩
                exact (hSess' k hk).2
                  (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly, hne]) v
            have hqSess' : ∀ k < qStart,
                nextSessDone qStart qSessDone i k + nextSessRem qStart qSessRem i k ≤ qs k := by
              intro k hk
              dsimp only [nextSessDone, nextSessRem]
              split_ifs with hki
              · rcases hki with ⟨_, rfl⟩
                have hpos :=
                  ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).1
                have hle := hqSess k hk
                omega
              · exact hqSess k hk
            exact ih v f qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
              (nextSessDone qStart qSessDone i) (nextSessRem qStart qSessRem i) σ1
              hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR
        refine ⟨?_, ?_⟩
        · rw [run1_query_inr_succ, BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun res hres => ?_
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · dsimp only [mapPreEnc]
            have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
            dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
            rw [hAns, spec.rdec_eq t r_ans]
            exact (hCont (bhTargetRdec t r_ans) σ1 hR).1
          · simp [mapPreEnc, mapMidEnc]
        · intro m hm
          rw [BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hm
          rcases hm with ⟨res, hres, hm_cont⟩
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · dsimp only at hm_cont
            rw [spec.rdec_eq t r_ans] at hm_cont
            exact (hCont (bhTargetRdec t r_ans) σ1 hR).2 m hm_cont
          · simp only [support_pure, Set.mem_singleton_iff] at hm_cont
            subst hm_cont
            rcases hR with ⟨⟨cq, rfl⟩, hInv1, hPaused1⟩
            have hSt1 := hStart.1 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
            refine ⟨qKiDone, qKiRem, qSendDone, qSendRem, qStartDone + 1, qStartRem - 1,
              qSessDone, qSessRem, hqKi, hqSend, by have := hSt1.1; omega, hqSess, hInv1, hPaused1,
              fun v => ⟨?_, ?_, hSt1.2 v, ?_⟩⟩
            · exact hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            · exact hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            · exact fun k hk => (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v

theorem twoStage_eval1_eq_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) (fuel : ℕ) (dflt : Bool) :
    spec.R.eval1 (fun _ => B_A) () fuel dflt =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        spec.R_ref.eval1 (fun _ => B_A) () fuel dflt := by
  rcases hB with ⟨_, hSend, _, hTot, _, hStSend, hStQ, _, hSess⟩
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  have hRun1 := twoStage_run1_eq_and_inv_inst spec dflt B_A fuel
    0 b.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs spec.σ0
    hTot hSend hStMin hSess (by omega) (by omega) (by omega) (fun k _ => by omega) spec.init_inv
  simp only [TwoStageCostedReduction.eval1, BhShallowTwoStageRed.eval1]
  rw [spec.init_costed, spec.init_ref, pure_bind, pure_bind, hRun1.1, bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun m hm => ?_
  have hInvM := hRun1.2 m hm
  cases m with
  | done b_out σ_out =>
    rcases hInvM with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
    dsimp only [mapMidEnc]
    rw [spec.chDone_eq hInvOut b_out, bind_map_left, map_bind]
    refine bind_congr fun c => ?_
    simp [mapOut1Enc, mapMidEnc]
  | paused t c p σ_p cont =>
    simp [mapMidEnc, mapOut1Enc]

theorem twoStage_runFuel_eq_and_inv_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    {α : Type} (dflt : α) :
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ) (σ : DrvSt),
      oa.IsQueryBoundP isKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k < qStart, oa.IsQueryBoundP (isSessQ k) (qSessRem k)) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) →
      spec.Inv qKiDone qSendDone qStartDone qSessDone σ →
      spec.PausedInv σ →
      (runFuel (C := e2eTargetGameCodec S ℓ Pt)
          spec.R.handlePost dflt oa fuel (spec.drvEnc σ) =
        Prod.map id spec.drvEnc <$>
          bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ) ∧
      (∀ out ∈ support
          (bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ),
        ∃ qKi2 qSend2 qSt2 qSess2, spec.Inv qKi2 qSend2 qSt2 qSess2 out.2) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone _ qSendDone _ qStartDone _ qSessDone _ σ _ _ _ _ _ _ _ _ hInv _
    refine ⟨by rw [runFuel_pure, bhShallowRunFuel_pure, map_pure]; rfl, ?_⟩
    intro out hout
    rw [bhShallowRunFuel_pure] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv hPaused
    have hTot := unpack_qb hTot0
    have hSend := unpack_qb hSend0
    have hStart := unpack_qb hStart0
    have hSess' : ∀ k < qStart,
        (isSessQ k q → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
        (¬isSessQ k q → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)) :=
      fun k hk => unpack_qb (hSess k hk)
    cases q with
    | inl n =>
      have hcKi : ∀ u, (mx u).IsQueryBoundP isKiQ qKiRem :=
        hTot.2 (by simp [isKiQ, bhClassifyTarget])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClassifyTarget])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClassifyTarget])
      have hcSess : ∀ u k, k < qStart → (mx u).IsQueryBoundP (isSessQ k) (qSessRem k) :=
        fun u k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget]) u
      refine ⟨?_, ?_⟩
      · rw [runFuel_query_inl, bhShallowRunFuel_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
            (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv hPaused).1
      · intro out hout
        rw [bhShallowRunFuel_query_inl, mem_support_bind_iff] at hout
        rcases hout with ⟨u, -, hout'⟩
        exact (ih u fuel qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σ
          (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv hPaused).2 out hout'
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [runFuel_query_inr_zero, bhShallowRunFuel_query_inr_zero, map_pure]; rfl, ?_⟩
        intro out hout
        rw [bhShallowRunFuel_query_inr_zero] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
      | succ f =>
        have htBound := stepBudgetOkInst_of_bounds hTot hSend hStart hSess' hqKi hqSend hqSt hqSess
        have hStepEq := spec.stepPost_eq hInv hPaused t htBound
        have hPostInv := spec.stepPost_inv hInv hPaused t htBound
        have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t) (σ1 : DrvSt),
            spec.PausedInv σ1 →
            StepNextInvInst spec.Inv qStart qKiDone qSendDone qStartDone qSessDone t σ1 →
            (runFuel (C := e2eTargetGameCodec S ℓ Pt)
                spec.R.handlePost dflt (mx v) f (spec.drvEnc σ1) =
              Prod.map id spec.drvEnc <$>
                bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
                  spec.R_ref.handlePost dflt (mx v) f σ1) ∧
            (∀ out ∈ support
                (bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
                  spec.R_ref.handlePost dflt (mx v) f σ1),
              ∃ qKi2 qSend2 qSt2 qSess2, spec.Inv qKi2 qSend2 qSt2 qSess2 out.2) := by
          intro v σ1 hP1 hR
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hKi1 := hTot.1 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly])
            have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
              fun k hk => (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            by_cases hsk : isSendKiQuery kq = true
            · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
              have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
              dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
              exact ih v f (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
                qStartDone qStartRem qSessDone qSessRem σ1
                (hKi1.2 v) (hSend1.2 v) hcSt hcSess
                (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR hP1
            · have hSend0 := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
              have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
              dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
              exact ih v f (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
                qStartDone qStartRem qSessDone qSessRem σ1
                (hKi1.2 v) hSend0 hcSt hcSess
                (by have := hKi1.1; omega) hqSend hqSt hqSess hR hP1
          · have hSt1 := hStart.1 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
            have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
              fun k hk => (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            exact ih v f qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
              qSessDone qSessRem σ1
              hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR hP1
          · have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
            have hcSess : ∀ k < qStart,
                (mx v).IsQueryBoundP (isSessQ k) (nextSessRem qStart qSessRem i k) := by
              intro k hk
              dsimp only [nextSessRem]
              split_ifs with hki
              · rcases hki with ⟨_, rfl⟩
                exact ((hSess' k hk).1
                  (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).2 v
              · have hne : i ≠ k := fun h => hki ⟨h ▸ hk, h.symm⟩
                exact (hSess' k hk).2
                  (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly, hne]) v
            have hqSess' : ∀ k < qStart,
                nextSessDone qStart qSessDone i k + nextSessRem qStart qSessRem i k ≤ qs k := by
              intro k hk
              dsimp only [nextSessDone, nextSessRem]
              split_ifs with hki
              · rcases hki with ⟨_, rfl⟩
                have hpos :=
                  ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).1
                have hle := hqSess k hk
                omega
              · exact hqSess k hk
            exact ih v f qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
              (nextSessDone qStart qSessDone i) (nextSessRem qStart qSessRem i) σ1
              hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR hP1
        refine ⟨?_, ?_⟩
        · rw [runFuel_query_inr_succ, bhShallowRunFuel_query_inr_succ, spec.qenc_eq t]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun ⟨r_ans, σ1⟩ hp => ?_
          have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          dsimp only [Prod.map]
          have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
          dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
          rw [hAns, spec.rdec_eq t r_ans]
          exact (hCont (bhTargetRdec t r_ans) σ1 hP1 hInv1).1
        · intro out hout
          rw [bhShallowRunFuel_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hout
          rcases hout with ⟨⟨r_ans, σ1⟩, hp, hout'⟩
          have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          dsimp only at hout'
          rw [spec.rdec_eq t r_ans] at hout'
          exact (hCont (bhTargetRdec t r_ans) σ1 hP1 hInv1).2 out hout'

theorem twoStage_eval2_eq_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    (fuel1 fuel2 : ℕ) (dflt : Bool) :
    ∀ o ∈ support (stageOneAsProbComp
        (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt)),
      ∀ flip : Bool,
        spec.R.eval2 (mapMidEnc spec.drvEnc spec.πEnc o.2) flip fuel2 dflt =
          spec.R_ref.eval2 o.2 flip fuel2 dflt := by
  intro o ho flip
  have hEval1Eq := twoStage_eval1_eq_inst spec B_A hB fuel1 dflt
  have hZero := spec.stage1_queries_zero
  have hQb1Costed :
      (spec.R.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    have hU := isQueryBoundP_atomicSessionTargetIface_fwdU (ℓ := ℓ) (Pt := Pt)
    exact (TwoStageCostedReduction.eval1_queryBound spec.R (isSmTargetQuery ℓ)
      (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) hU (fun _ => B_A) () fuel1 dflt).mono
      (by
        have hinit : spec.R.init.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hpre : spec.R.handlePre.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hch : spec.R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        simp [hinit, hpre, hch])
  have hQb1Ref :
      (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    rw [hEval1Eq] at hQb1Costed
    exact (OracleComp.isQueryBoundP_map_iff (p := isSmTargetQuery ℓ) _ _ 0).mp hQb1Costed
  have ho_raw : o ∈ support (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) :=
    mem_support_of_mem_support_stageOneAsProbComp _ ho hQb1Ref
  have hm_raw : o.2 ∈ support (spec.R_ref.run1 dflt B_A fuel1 spec.σ0) := by
    simp only [BhShallowTwoStageRed.eval1, spec.init_ref, pure_bind, mem_support_bind_iff] at ho_raw
    rcases ho_raw with ⟨m, hm, hrest⟩
    cases m with
    | done b_out σ_out =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrest
      rcases hrest with ⟨_, -, rfl⟩
      exact hm
    | paused t c p σ_p cont =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst hrest
      exact hm
  rcases hB with ⟨_, hSend, _, hTot, _, hStSend, hStQ, _, hSess⟩
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  have hInvM := (twoStage_run1_eq_and_inv_inst spec dflt B_A fuel1
    0 b.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs spec.σ0
    hTot hSend hStMin hSess (by omega) (by omega) (by omega) (fun k _ => by omega)
    spec.init_inv).2 o.2 hm_raw
  rcases hm_case : o.2 with ⟨b_out, σ_out⟩ | ⟨t, c_p, p_p, σ_p, cont⟩
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2, pure_bind]
    exact spec.finish_eq hInvOut b_out flip
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qKiR1, qSend1, qSendR1, qSt1, qStR1, qSess1, qSessR1,
      hqKi1, hqSend1, hqSt1, hqSess1, hInvP, hPausedP, hContB⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2]
    rw [spec.resume_eq hInvP hPausedP p_p flip, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨v_ans, σ_res⟩ hrs => ?_
    have ⟨hInvRes, hPausedRes⟩ := spec.resume_inv hInvP hPausedP p_p flip (v_ans, σ_res) hrs
    dsimp only [Prod.map]
    have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t v_ans
    dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
    rw [hAns, spec.rdec_eq t v_ans]
    let ans := bhTargetRdec t v_ans
    have ⟨hCB1, hCB2, hCB3, hCB4⟩ := hContB ans
    have ⟨hFuelEq, hFuelInv⟩ := twoStage_runFuel_eq_and_inv_inst spec dflt
      (cont ans) fuel2 qKi1 qKiR1 qSend1 qSendR1 qSt1 qStR1 qSess1 qSessR1 σ_res
      hCB1 hCB2 hCB3 hCB4 hqKi1 hqSend1 hqSt1 hqSess1 hInvRes hPausedRes
    rw [hFuelEq, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
    rcases hFuelInv (b_out, σ_out) hout with ⟨qKi2, qSend2, qSt2, qSess2, hInvOut⟩
    exact spec.finish_eq hInvOut b_out flip

/-- Two-stage `ProbComp` equivalence between `spec.R` and `spec.R_ref` for any bounded adversary. -/
theorem twoStage_stage12_comp_eq_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {β : Type}
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (fuel1 fuel2 : ℕ) (dflt flip : Bool) :
    (stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (spec.R.eval2 o.2 flip fuel2 dflt)) =
    (stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (spec.R_ref.eval2 o.2 flip fuel2 dflt)) := by
  have h1 := twoStage_eval1_eq_inst spec B_A hB fuel1 dflt
  have h1s :
      stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) := by
    unfold stageOneAsProbComp
    rw [h1, simulateQ_map]
  rw [h1s, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun o ho => ?_
  have h2 := twoStage_eval2_eq_inst spec B_A hB fuel1 fuel2 dflt o ho flip
  dsimp only [Function.comp_def, mapOut1Enc, atomicPrefixCtxEnc]
  rw [h2]

theorem evalDist_twoStage_stage12_eq_inst
    (spec : TwoStageAtomicSimSpecInst S Pt ℓ O b qStart qs DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {β : Type} [MeasurableSpace β]
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (fuel1 fuel2 : ℕ) (dflt flip : Bool) :
    𝒟[stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (spec.R.eval2 o.2 flip fuel2 dflt)] =
    𝒟[stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (spec.R_ref.eval2 o.2 flip fuel2 dflt)] :=
  congrArg evalDist (twoStage_stage12_comp_eq_inst spec B_A hB game2 fuel1 fuel2 dflt flip)

end TwoStageSimProofs

end Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
