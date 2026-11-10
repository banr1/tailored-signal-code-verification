/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Per-Kind Cost and Query Bounds for Halted E2E Composition Reductions

Splits `bhE2ECostBudgetByKind` into the online-clamped `bhE2ECostBudget` and a random-oracle
lookup-table term, and provides generic `GRedCostByKind` and `GRed2CostByKind` constructors under
`bhQueryKind`. Specializes these bounds to `kindRedHalted` and `prefixRedHalted`.
-/

public section

set_option autoImplicit false

open scoped BigOperators

namespace Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind

open OracleSpec
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp CostedReduction
  TwoStageCostedReduction bits atomicSig atomicE2EOps e2eKeyIndTargetIface e2eSessionTargetIface
  prefixCtxT keyIndQT keyIndQenc keyIndRT sidT smQT E2EKeyIndTag)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSession (GRedCostByKind GRed2CostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes bhTargetGameSpec e2eTargetGameCodec bhQueryKind bhKindCounts
  bhE2ECostBudget bhE2ECostBudgetByKind)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono)
open Computational.Proofs.E2E.Dsl.KindRedHalted (HaltedKindSubprograms drvKindHaltedTy
  kindHandleHalted kindRedHalted haltedKindEndpointCost haltedKindStepCost
  kindHandleHalted_cost_le kindRedHalted_totalQueries_le)
open Computational.Proofs.E2E.Dsl.PrefixRedHalted (HaltedPrefixSubprograms drvHaltedTy
  prefixKiStepHaltedC prefixHandlePreHalted prefixHandlePostHalted prefixRedHalted
  haltedPrefixEndpointCost haltedPrefixStepCost prefixHandlePreHalted_cost_le
  prefixHandlePostHalted_cost_le prefixRedHalted_stage1Queries prefixRedHalted_totalQueries_le)

/-- Query budget with `q_total` clamped to the online count `min b.q_on b.q_total`. -/
@[expose] def onlineClampedBudget (b : SignalPqxdh.QueryBudget) : SignalPqxdh.QueryBudget :=
  { b with q_total := min b.q_on b.q_total }

@[simp] theorem onlineClampedBudget_q_total (b : SignalPqxdh.QueryBudget) :
    (onlineClampedBudget b).q_total = min b.q_on b.q_total := rfl

theorem onlineClampedBudget_q_total_le (b : SignalPqxdh.QueryBudget) :
    (onlineClampedBudget b).q_total ≤ b.q_total :=
  Nat.min_le_right _ _

private theorem list_ofFn_fin2_sum_local (f : Fin 2 → ℕ) :
    (List.ofFn f).sum = f 0 + f 1 := by
  simp [List.ofFn_succ]

theorem bhKindCounts_zero (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    bhKindCounts b qStart qDR 0 = min b.q_on b.q_total + qStart + qDR := rfl

theorem bhKindCounts_one (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    bhKindCounts b qStart qDR 1 = min b.q_ro b.q_total := rfl

theorem bhKindCounts_sum (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (List.ofFn (bhKindCounts b qStart qDR)).sum =
      (min b.q_on b.q_total + qStart + qDR) + min b.q_ro b.q_total :=
  list_ofFn_fin2_sum_local (bhKindCounts b qStart qDR)

/-- Decomposes `bhE2ECostBudgetByKind` into `bhE2ECostBudget` at `onlineClampedBudget b` plus the random-oracle lookup-table term. -/
theorem bhE2ECostBudgetByKind_eq_online_add_roTable
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep ℓ : ℕ) :
    let M_on := min b.q_on b.q_total
    let M_ro := min b.q_ro b.q_total
    let Q_on := M_on + qStart + qDR
    bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ =
      bhE2ECostBudget S (onlineClampedBudget b) qStart qDR qInst qep ℓ +
        2 ^ 13 * (M_ro + Q_on) * (bits (M_ro + 2 * Q_on + 1) + 4) := by
  dsimp only [bhE2ECostBudgetByKind, bhE2ECostBudget, onlineClampedBudget]
  omega

theorem bhE2ECostBudget_mono_qTotal (S : SignalPqxdh.Setup)
    {b₁ b₂ : SignalPqxdh.QueryBudget} (hb : b₁.q_total ≤ b₂.q_total)
    (qStart qDR qInst qep ℓ : ℕ) :
    bhE2ECostBudget S b₁ qStart qDR qInst qep ℓ ≤
      bhE2ECostBudget S b₂ qStart qDR qInst qep ℓ := by
  dsimp only [bhE2ECostBudget]
  have hId : min b₁.q_total S.N_id ≤ min b₂.q_total S.N_id :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hSpk : min b₁.q_total S.N_spk_tot ≤ min b₂.q_total S.N_spk_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hOpk : min b₁.q_total S.N_opk_tot ≤ min b₂.q_total S.N_opk_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hSend : min b₁.q_total S.N_send_tot ≤ min b₂.q_total S.N_send_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hRecv : min b₁.q_total S.N_recv_tot ≤ min b₂.q_total S.N_recv_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hInst : min qStart (min b₁.q_total S.N_send_tot) ≤
      min qStart (min b₂.q_total S.N_send_tot) :=
    Nat.le_min.mpr ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans hSend⟩
  refine Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 10) (by omega)) (by omega))
    (Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 13) hInst) (by omega))

theorem roStep_mul_le_roTableTerm (M_on M_ro qStart qDR roStep : ℕ)
    (hRo : roStep ≤ 2 ^ 13 * (bits M_on + 4)) :
    let Q_on := M_on + qStart + qDR
    M_ro * roStep ≤ 2 ^ 13 * (M_ro + Q_on) * (bits (M_ro + 2 * Q_on + 1) + 4) := by
  intro Q_on
  have hbits : bits M_on ≤ bits (M_ro + 2 * Q_on + 1) := bits_mono (by omega)
  have h1 : roStep ≤ 2 ^ 13 * (bits (M_ro + 2 * Q_on + 1) + 4) :=
    hRo.trans (Nat.mul_le_mul_left (2 ^ 13) (by omega))
  calc
    M_ro * roStep ≤ M_ro * (2 ^ 13 * (bits (M_ro + 2 * Q_on + 1) + 4)) :=
      Nat.mul_le_mul_left M_ro h1
    _ ≤ (M_ro + Q_on) * (2 ^ 13 * (bits (M_ro + 2 * Q_on + 1) + 4)) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ 13 * (M_ro + Q_on) * (bits (M_ro + 2 * Q_on + 1) + 4) := by
      rw [Nat.mul_left_comm, Nat.mul_assoc]

theorem bhQueryKind_eq_one_iff {S : SignalPqxdh.Setup} {ι : Type}
    (t : (SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι) :
    bhQueryKind t = 1 ↔ ∃ sec : SignalPqxdh.Bytes, t = .inl (.inl (.roQuery sec)) := by
  rcases t with (kq | ctl) | sm
  · cases kq <;> simp [bhQueryKind]
  · simp [bhQueryKind]
  · simp [bhQueryKind]

theorem costBoundedByKind_bhQueryKind_of_online_and_ro
    {S0 : Sig} {O : Ops S0} {ι₀ ι : Type} {T : OracleSpec ι₀} {I : Iface S0 T}
    {S : SignalPqxdh.Setup}
    {G : OracleSpec ((SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι)}
    {C0 : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C0 rIn aIn aOut out)
    (qKind : Fin 2 → ℕ) (h₀ h₁ B : ℕ)
    (hOn : R.handle.cost ≤ h₀)
    (hRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handle.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hTot : R.init.cost +
      qKind 0 * max I.uCost (h₀ + C0.codecCost) +
      qKind 1 * max I.uCost (h₁ + C0.codecCost) +
      R.finish.cost ≤ B) :
    R.CostBoundedByKind bhQueryKind qKind B := by
  refine ⟨![h₀, h₁], ?_, ?_⟩
  · intro s t
    rcases t with (kq | ctl) | sm
    · cases kq with
      | roQuery sec =>
        simpa [bhQueryKind] using hRo s sec
      | _ =>
        exact (Comp.costAt_le_cost R.handle _).trans (by simpa [bhQueryKind] using hOn)
    · exact (Comp.costAt_le_cost R.handle _).trans (by simpa [bhQueryKind] using hOn)
    · exact (Comp.costAt_le_cost R.handle _).trans (by simpa [bhQueryKind] using hOn)
  · dsimp only [CostedReduction.totalCostByKind]
    rw [list_ofFn_fin2_sum_local]
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.add_assoc] using hTot

/-- Assemble one-stage `GRedCostByKind` under `bhQueryKind` from online static and `.roQuery` `costAt` bounds. -/
theorem gRedCostByKind_bhQueryKind_of_online_and_ro
    {S0 : Sig} {O : Ops S0} {ι₀ ι : Type} {T : OracleSpec ι₀} {I : Iface S0 T}
    {S : SignalPqxdh.Setup}
    {G : OracleSpec ((SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι)}
    {C0 : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C0 rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (qKind : Fin 2 → ℕ) (qOut h₀ h₁ B : ℕ)
    (hOn : R.handle.cost ≤ h₀)
    (hRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handle.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hTot : R.init.cost +
      qKind 0 * max I.uCost (h₀ + C0.codecCost) +
      qKind 1 * max I.uCost (h₁ + C0.codecCost) +
      R.finish.cost ≤ B)
    (hQ : R.totalQueries wTag wSamp (List.ofFn qKind).sum ≤ qOut) :
    GRedCostByKind R wTag wSamp bhQueryKind qKind qOut B :=
  ⟨costBoundedByKind_bhQueryKind_of_online_and_ro R qKind h₀ h₁ B hOn hRo hTot, hQ⟩

theorem twoStageCostBoundedByKind_bhQueryKind_of_online_and_ro
    {S0 : Sig} {O : Ops S0} {ι₀ ι : Type} {T : OracleSpec ι₀} {I : Iface S0 T}
    {S : SignalPqxdh.Setup}
    {G : OracleSpec ((SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι)}
    {C0 : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    (qKind : Fin 2 → ℕ) (h₀ h₁ B : ℕ)
    (hPreOn : R.handlePre.cost ≤ h₀)
    (hPostOn : R.handlePost.cost ≤ h₀)
    (hPreRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePre.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hPostRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePost.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hTot : R.init.cost +
      qKind 0 * max I.uCost (h₀ + C0.codecCost) +
      qKind 1 * max I.uCost (h₁ + C0.codecCost) +
      max R.chDone.cost R.resume.cost + R.finish.cost ≤ B) :
    R.CostBoundedByKind bhQueryKind qKind B := by
  refine ⟨![h₀, h₁], ?_, ?_⟩
  · intro s t
    rcases t with (kq | ctl) | sm
    · cases kq with
      | roQuery sec =>
        exact ⟨by simpa [bhQueryKind] using hPreRo s sec,
          by simpa [bhQueryKind] using hPostRo s sec⟩
      | _ =>
        exact ⟨(Comp.costAt_le_cost R.handlePre _).trans (by simpa [bhQueryKind] using hPreOn),
          (Comp.costAt_le_cost R.handlePost _).trans (by simpa [bhQueryKind] using hPostOn)⟩
    · exact ⟨(Comp.costAt_le_cost R.handlePre _).trans (by simpa [bhQueryKind] using hPreOn),
        (Comp.costAt_le_cost R.handlePost _).trans (by simpa [bhQueryKind] using hPostOn)⟩
    · exact ⟨(Comp.costAt_le_cost R.handlePre _).trans (by simpa [bhQueryKind] using hPreOn),
        (Comp.costAt_le_cost R.handlePost _).trans (by simpa [bhQueryKind] using hPostOn)⟩
  · dsimp only [TwoStageCostedReduction.totalCostByKind]
    rw [list_ofFn_fin2_sum_local]
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.add_assoc] using hTot

/-- Assemble two-stage `GRed2CostByKind` under `bhQueryKind` from online static and `.roQuery` `costAt` bounds. -/
theorem gRed2CostByKind_bhQueryKind_of_online_and_ro
    {S0 : Sig} {O : Ops S0} {ι₀ ι : Type} {T : OracleSpec ι₀} {I : Iface S0 T}
    {S : SignalPqxdh.Setup}
    {G : OracleSpec ((SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι)}
    {C0 : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (qKind : Fin 2 → ℕ) (qOut h₀ h₁ B : ℕ)
    (hPreOn : R.handlePre.cost ≤ h₀)
    (hPostOn : R.handlePost.cost ≤ h₀)
    (hPreRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePre.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hPostRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePost.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hTot : R.init.cost +
      qKind 0 * max I.uCost (h₀ + C0.codecCost) +
      qKind 1 * max I.uCost (h₁ + C0.codecCost) +
      max R.chDone.cost R.resume.cost + R.finish.cost ≤ B)
    (hStage1Q : R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp +
      R.chDone.queries wTag wSamp = 0)
    (hQ : R.totalQueries wTag wSamp (List.ofFn qKind).sum ≤ qOut) :
    GRed2CostByKind R wTag wSamp bhQueryKind qKind qOut B :=
  ⟨twoStageCostBoundedByKind_bhQueryKind_of_online_and_ro R qKind h₀ h₁ B
      hPreOn hPostOn hPreRo hPostRo hTot,
    hStage1Q, hQ⟩

section HaltedByKind

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {SessH : Type}

theorem kindHandleHalted_roQuery_costAt_le
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep okRoCost mirRoCost : ℕ)
    (hOkRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiQueryOkE b qStart σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + okRoCost)
    (hMirRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))),
      (subs.mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirRoCost)
    (s : (drvKindHaltedTy subs).denote) (sec : SignalPqxdh.Bytes) :
    (kindHandleHalted subs b qStart qDR qep).costAt
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤
      okRoCost + mirRoCost + 160 := by
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let Γ_kr : List (Ty (atomicSig ℓ Pt)) :=
    (e2eKeyIndTargetIface S ℓ Pt).cod E2EKeyIndTag.keyInd :: Γ_ki
  let qKi :
      Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ_ki
        ((e2eKeyIndTargetIface S ℓ Pt).cod E2EKeyIndTag.keyInd) :=
    .query E2EKeyIndTag.keyInd .v0
  let kMir :
      Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ_kr
        (.prod (e2eTargetGameCodec S ℓ Pt).R (drvKindHaltedTy subs)) :=
    .ret (.pair (.inl (.inl .v0))
      (.pair (subs.mirrorE (.fst .v3) .v1 .v0) (.snd .v3)))
  let ρ0 : Env [drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
    .cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)
  let ρ_ki : Env Γ_ki :=
    .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec))) ρ0)
  have hok :
      (subs.kiQueryOkE b qStart (.fst .v2) .v0).costAt ρ_ki ≤ okRoCost + 3 :=
    (hOkRo (Γ := Γ_ki) (.fst .v2) .v0 ρ_ki sec rfl).trans
      (by simp only [Expr.costAt, Expr.v0, Expr.v2]; omega)
  have hkCost : kMir.cost ≤ mirRoCost + 15 := by
    have hmir := hMirRo (Γ := Γ_kr) (.fst .v3) .v1 .v0
    simp only [kMir, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v3] at hmir ⊢
    omega
  have hqCost : qKi.costAt ρ_ki ≤ 130 := by
    simp only [qKi, Comp.costAt, Expr.costAt, Expr.v0, e2eKeyIndTargetIface]
    omega
  change 1 + (1 + (Comp.ite (I := e2eKeyIndTargetIface S ℓ Pt)
      (subs.kiQueryOkE b qStart (.fst .v2) .v0)
      (.bind qKi kMir)
      (.ret (.pair (.inl (.inl (.inl .unit))) .v2))).costAt ρ_ki + 1) + 1 ≤ _
  dsimp only [Comp.costAt]
  split_ifs
  · unfold Comp.costAt
    rcases qKi.pureEval? ρ_ki with _ | y
    · dsimp only
      change 1 + (1 + ((subs.kiQueryOkE b qStart (.fst .v2) .v0).costAt ρ_ki +
        (qKi.costAt ρ_ki + kMir.cost + 1) + 1) + 1) + 1 ≤ _
      omega
    · dsimp only
      have hle := (Comp.costAt_le_cost kMir (.cons y ρ_ki)).trans hkCost
      change 1 + (1 + ((subs.kiQueryOkE b qStart (.fst .v2) .v0).costAt ρ_ki +
        (qKi.costAt ρ_ki + kMir.costAt (.cons y ρ_ki) + 1) + 1) + 1) + 1 ≤ _
      omega
  · simp only [Expr.costAt, Expr.v0, Expr.v2] at hok ⊢
    omega

theorem kindRedHalted_costBoundedByKind
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep okRoCost mirRoCost : ℕ)
    (qKind : Fin 2 → ℕ) (costBudget : ℕ)
    (hOkRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiQueryOkE b qStart σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + okRoCost)
    (hMirRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))),
      (subs.mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirRoCost)
    (hBudget :
      haltedKindEndpointCost subs qStart +
        qKind 0 * haltedKindStepCost subs b qStart qDR qep +
        qKind 1 * (okRoCost + mirRoCost + 224) ≤ costBudget) :
    (kindRedHalted subs b qStart qDR qep).CostBoundedByKind bhQueryKind qKind costBudget := by
  have hinit := subs.initKindC_cost (Γ := [.unit])
  have hfin := subs.finishKindE_cost qStart (Γ := [drvKindHaltedTy subs, .bool]) (.fst .v0) .v1
  have hhand := kindHandleHalted_cost_le subs b qStart qDR qep
  have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost = 64 := rfl
  have hu : (e2eKeyIndTargetIface S ℓ Pt).uCost = 1 := rfl
  refine costBoundedByKind_bhQueryKind_of_online_and_ro
    (kindRedHalted subs b qStart qDR qep) qKind
    (kindHandleHalted subs b qStart qDR qep).cost (okRoCost + mirRoCost + 160) costBudget
    le_rfl
    (kindHandleHalted_roQuery_costAt_le subs b qStart qDR qep okRoCost mirRoCost hOkRo hMirRo)
    ?_
  rw [hu, hcc]
  have hmul0 :
      qKind 0 * max 1 ((kindHandleHalted subs b qStart qDR qep).cost + 64) ≤
        qKind 0 * haltedKindStepCost subs b qStart qDR qep := by
    refine Nat.mul_le_mul_left (qKind 0) ?_
    have hpos : 1 ≤ haltedKindStepCost subs b qStart qDR qep := by
      unfold haltedKindStepCost; omega
    omega
  have hmul1 :
      qKind 1 * max 1 (okRoCost + mirRoCost + 160 + 64) ≤
        qKind 1 * (okRoCost + mirRoCost + 224) := by
    refine Nat.mul_le_mul_left (qKind 1) ?_
    omega
  dsimp only [kindRedHalted, haltedKindEndpointCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1] at hinit hfin hBudget ⊢
  omega

/-- Per-kind `GRedCostByKind` certificate for `kindRedHalted`. -/
theorem kindRedHalted_gRedCostByKind
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep okRoCost mirRoCost : ℕ)
    (qKind : Fin 2 → ℕ) (costBudget : ℕ)
    (hOkRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiQueryOkE b qStart σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + okRoCost)
    (hMirRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))),
      (subs.mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirRoCost)
    (hBudget :
      haltedKindEndpointCost subs qStart +
        qKind 0 * haltedKindStepCost subs b qStart qDR qep +
        qKind 1 * (okRoCost + mirRoCost + 224) ≤ costBudget) :
    GRedCostByKind (kindRedHalted subs b qStart qDR qep)
      (fun _ => 1) (fun _ => 0) bhQueryKind qKind (2 * (List.ofFn qKind).sum) costBudget :=
  ⟨kindRedHalted_costBoundedByKind subs b qStart qDR qep okRoCost mirRoCost qKind costBudget
      hOkRo hMirRo hBudget,
    kindRedHalted_totalQueries_le subs b qStart qDR qep (List.ofFn qKind).sum⟩

theorem prefixKiStepHaltedC_costAt_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (roKiCost : ℕ)
    (hKi :
      (subs.kiStepC b (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ)
          (.fst (.fst .v0)) (.snd .v0)).costAt
        (.cons (σHE.eval ρ, kqE.eval ρ) ρ) ≤ 5 + roKiCost) :
    (prefixKiStepHaltedC subs b σHE kqE).costAt ρ ≤
      σHE.costAt ρ + kqE.costAt ρ + roKiCost + 19 := by
  let kRet :
      Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
        (Ty.prod (e2eTargetGameCodec S ℓ Pt).R subs.drvTy ::
          Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ)
        (.prod (e2eTargetGameCodec S ℓ Pt).R (drvHaltedTy subs)) :=
    .ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v1))))
  have hkCost : kRet.cost = 10 := rfl
  dsimp only [prefixKiStepHaltedC, Comp.costAt, Comp.pureEval?, Expr.costAt, Expr.eval]
  rcases (subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).pureEval?
      (.cons (σHE.eval ρ, kqE.eval ρ) ρ) with _ | x
  · dsimp only
    change σHE.costAt ρ + kqE.costAt ρ + 1 + 1 +
      ((subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).costAt (.cons (σHE.eval ρ, kqE.eval ρ) ρ) +
        kRet.cost + 1) + 1 ≤ _
    omega
  · dsimp only
    have hle := (Comp.costAt_le_cost kRet (.cons x (.cons (σHE.eval ρ, kqE.eval ρ) ρ))).trans
      (le_of_eq hkCost)
    change σHE.costAt ρ + kqE.costAt ρ + 1 + 1 +
      ((subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).costAt (.cons (σHE.eval ρ, kqE.eval ρ) ρ) +
        kRet.costAt (.cons x (.cons (σHE.eval ρ, kqE.eval ρ) ρ)) + 1) + 1 ≤ _
    omega

theorem prefixHandlePreHalted_roQuery_costAt_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k roKiCost : ℕ)
    (hKiRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiStepC b σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + roKiCost)
    (s : (drvHaltedTy subs).denote) (sec : SignalPqxdh.Bytes) :
    (prefixHandlePreHalted subs b qStart qDR qep k).costAt
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤
      roKiCost + 29 := by
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let ρ0 : Env [drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
    .cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)
  let ρ_ki : Env Γ_ki :=
    .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec))) ρ0)
  have hKi1 :
      (subs.kiStepC b (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ki)
          (.fst (.fst .v0)) (.snd .v0)).costAt
        (.cons (s, keyIndQenc (.roQuery sec)) ρ_ki) ≤ 5 + roKiCost := by
    have h := hKiRo
      (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ki)
      (.fst (.fst .v0)) (.snd .v0) (.cons (s, keyIndQenc (.roQuery sec)) ρ_ki) sec rfl
    dsimp only [Expr.costAt, Expr.v0] at h ⊢
    omega
  have hStep := prefixKiStepHaltedC_costAt_le subs b (Γ := Γ_ki) .v2 .v0 ρ_ki roKiCost hKi1
  dsimp only [Expr.costAt, Expr.v0, Expr.v2] at hStep
  change 1 + (1 + (Comp.bind (prefixKiStepHaltedC subs b .v2 .v0)
      (.ret (.inl .v0))).costAt ρ_ki + 1) + 1 ≤ _
  unfold Comp.costAt
  rcases (prefixKiStepHaltedC subs b (Γ := Γ_ki) .v2 .v0).pureEval? ρ_ki with _ | y
  · simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v2] at hStep ⊢; omega
  · simp only [Comp.costAt, Expr.costAt, Expr.v0, Expr.v2] at hStep ⊢; omega

theorem prefixHandlePostHalted_roQuery_costAt_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k roKiCost : ℕ)
    (hKiRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiStepC b σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + roKiCost)
    (s : (drvHaltedTy subs).denote) (sec : SignalPqxdh.Bytes) :
    (prefixHandlePostHalted subs b qStart qDR qep k).costAt
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤
      roKiCost + 29 := by
  let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
    [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
  let ρ0 : Env [drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
    .cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl (.roQuery sec)))) .nil)
  let ρ_ki : Env Γ_ki :=
    .cons (keyIndQenc (.roQuery sec)) (.cons (.inl (keyIndQenc (.roQuery sec))) ρ0)
  have hKi1 :
      (subs.kiStepC b (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ki)
          (.fst (.fst .v0)) (.snd .v0)).costAt
        (.cons (s, keyIndQenc (.roQuery sec)) ρ_ki) ≤ 5 + roKiCost := by
    have h := hKiRo
      (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ki)
      (.fst (.fst .v0)) (.snd .v0) (.cons (s, keyIndQenc (.roQuery sec)) ρ_ki) sec rfl
    dsimp only [Expr.costAt, Expr.v0] at h ⊢
    omega
  have hStep := prefixKiStepHaltedC_costAt_le subs b (Γ := Γ_ki) .v2 .v0 ρ_ki roKiCost hKi1
  dsimp only [Expr.costAt, Expr.v0, Expr.v2] at hStep
  change 1 + (1 + (prefixKiStepHaltedC subs b .v2 .v0).costAt ρ_ki + 1) + 1 ≤ _
  dsimp only [Expr.v0, Expr.v2] at hStep ⊢
  omega

theorem prefixRedHalted_costBoundedByKind
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep roKiCost : ℕ)
    (qKind : Fin 2 → ℕ) (costBudget : ℕ) {k : ℕ} (hk : k < qStart)
    (hKiRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiStepC b σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + roKiCost)
    (hBudget :
      haltedPrefixEndpointCost subs b qStart +
        qKind 0 * haltedPrefixStepCost subs b qStart qDR qep +
        qKind 1 * (roKiCost + 93) ≤ costBudget) :
    (prefixRedHalted subs b qStart qDR qep k).CostBoundedByKind bhQueryKind qKind costBudget := by
  let h₀ := max (prefixHandlePreHalted subs b qStart qDR qep k).cost
    (prefixHandlePostHalted subs b qStart qDR qep k).cost
  have hempty := subs.emptyDrvStateE_cost (Γ := [.unit]) (.bool false)
  have hch := subs.defaultPrefixCtxE_cost (Γ := [drvHaltedTy subs, .bool])
  have hres := subs.drvSetBitE_cost (Γ := [drvHaltedTy subs, .opt .nat, .bool]) (.fst .v0) .v2
  have hfin := subs.finishPrefixC_cost b qStart
    (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2
  have hpre := prefixHandlePreHalted_cost_le subs b qStart qDR qep hk
  have hpost := prefixHandlePostHalted_cost_le subs b qStart qDR qep hk
  have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost = 64 := rfl
  have hu : (e2eSessionTargetIface ℓ Pt).uCost = 1 := rfl
  refine twoStageCostBoundedByKind_bhQueryKind_of_online_and_ro
    (prefixRedHalted subs b qStart qDR qep k) qKind h₀ (roKiCost + 29) costBudget
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (prefixHandlePreHalted_roQuery_costAt_le subs b qStart qDR qep k roKiCost hKiRo)
    (prefixHandlePostHalted_roQuery_costAt_le subs b qStart qDR qep k roKiCost hKiRo)
    ?_
  rw [hu, hcc]
  have hmul0 :
      qKind 0 * max 1 (h₀ + 64) ≤
        qKind 0 * haltedPrefixStepCost subs b qStart qDR qep := by
    refine Nat.mul_le_mul_left (qKind 0) ?_
    have hpos : 1 ≤ haltedPrefixStepCost subs b qStart qDR qep := by
      unfold haltedPrefixStepCost; omega
    dsimp only [h₀]
    omega
  have hmul1 :
      qKind 1 * max 1 (roKiCost + 29 + 64) ≤
        qKind 1 * (roKiCost + 93) := by
    refine Nat.mul_le_mul_left (qKind 1) ?_
    omega
  dsimp only [prefixRedHalted, haltedPrefixEndpointCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hempty hch hres hfin hBudget ⊢
  omega

/-- Per-kind `GRed2CostByKind` certificate for `prefixRedHalted` at `k < qStart`. -/
theorem prefixRedHalted_gRed2CostByKind
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep roKiCost : ℕ)
    (qKind : Fin 2 → ℕ) (costBudget : ℕ) {k : ℕ} (hk : k < qStart)
    (hKiRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiStepC b σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + roKiCost)
    (hBudget :
      haltedPrefixEndpointCost subs b qStart +
        qKind 0 * haltedPrefixStepCost subs b qStart qDR qep +
        qKind 1 * (roKiCost + 93) ≤ costBudget) :
    GRed2CostByKind (prefixRedHalted subs b qStart qDR qep k)
      (fun _ => 1) (fun _ => 0) bhQueryKind qKind (List.ofFn qKind).sum costBudget :=
  ⟨prefixRedHalted_costBoundedByKind subs b qStart qDR qep roKiCost qKind costBudget hk
      hKiRo hBudget,
    prefixRedHalted_stage1Queries subs b qStart qDR qep k,
    prefixRedHalted_totalQueries_le subs b qStart qDR qep k (List.ofFn qKind).sum⟩

end HaltedByKind

end Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind
