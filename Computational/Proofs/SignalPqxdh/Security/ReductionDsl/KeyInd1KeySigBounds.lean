/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemProofs
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.Size

/-!
# Cost and Query Bounds for `sigKeyInd1KeyProg`

**Checked by Lean.** Syntactic step-cost, syntactic query-count, and semantic query-bound
guarantees for `sigKeyInd1KeyProg` and `sigKeyInd1KeyDslProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleSpec

theorem Expr.rename_cost_aux {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (e.rename ρ).cost = e.cost := by
  induction e <;> intro Δ ρ <;> simp [Expr.rename, Expr.cost, *]

@[simp] theorem Expr.rename_cost {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (e : Expr O Γ t) :
    (e.rename ρ).cost = e.cost :=
  Expr.rename_cost_aux e ρ

theorem Expr.rename_costUB_aux {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (e.rename ρ).costUB = e.costUB := by
  induction e <;> intro Δ ρ <;> simp [Expr.rename, Expr.costUB, *]

@[simp] theorem Expr.rename_costUB {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (e : Expr O Γ t) :
    (e.rename ρ).costUB = e.costUB :=
  Expr.rename_costUB_aux e ρ

theorem Comp.rename_cost_aux {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (c.rename ρ).cost = c.cost := by
  induction c <;> intro Δ ρ <;> simp [Comp.rename, Comp.cost, *]

@[simp] theorem Comp.rename_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp O I Γ t) :
    (c.rename ρ).cost = c.cost :=
  Comp.rename_cost_aux c ρ

theorem Comp.rename_costUB_aux {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ), (c.rename ρ).costUB = c.costUB := by
  induction c <;> intro Δ ρ <;> simp [Comp.rename, Comp.costUB, *]

@[simp] theorem Comp.rename_costUB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp O I Γ t) :
    (c.rename ρ).costUB = c.costUB :=
  Comp.rename_costUB_aux c ρ

theorem Comp.rename_queries_aux {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (c.rename ρ).queries w ws = c.queries w ws := by
  induction c <;> intro Δ ρ <;> simp [Comp.rename, Comp.queries, *]

@[simp] theorem Comp.rename_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp O I Γ t) :
    (c.rename ρ).queries w ws = c.queries w ws :=
  Comp.rename_queries_aux w ws c ρ

theorem Comp.rename_queriesUB_aux {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (c.rename ρ).queriesUB w ws = c.queriesUB w ws := by
  induction c <;> intro Δ ρ <;> simp [Comp.rename, Comp.queriesUB, *]

@[simp] theorem Comp.rename_queriesUB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List (Ty S)} {t : Ty S}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp O I Γ t) :
    (c.rename ρ).queriesUB w ws = c.queriesUB w ws :=
  Comp.rename_queriesUB_aux w ws c ρ

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle
  pqSamplers

/-! ## Interface lifter cost and query lemmas -/

@[simp] theorem chalIfacePrimQueryWeight_inl {C : ChallengerOracle} (g : PTag) :
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (C := C) (Sum.inl g) = 1 := rfl

@[simp] theorem chalIfacePrimQueryWeight_inr {C : ChallengerOracle} (g : C.Tag) :
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight (C := C) (Sum.inr g) = 0 := rfl

@[simp] theorem chalIfaceSigQueryWeight_inl (g : PTag) :
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight (Sum.inl g) = 0 := rfl

@[simp] theorem chalIfaceSigQueryWeight_inr_inl (m : ℕ+) :
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight (Sum.inr (Sum.inl m)) = 1 := rfl

@[simp] theorem chalIfaceSigQueryWeight_inr_inr (u : Unit) :
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight (Sum.inr (Sum.inr u)) = 0 := rfl

@[simp] theorem chalIfaceDdhQueryWeight_inl (g : PTag) :
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (Sum.inl g) = 0 := rfl

@[simp] theorem chalIfaceDdhQueryWeight_inr_inl (m : ℕ+) :
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (Sum.inr (Sum.inl m)) = 0 := rfl

@[simp] theorem chalIfaceDdhQueryWeight_inr_inr (u : Unit) :
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight (Sum.inr (Sum.inr u)) = 1 := by
  cases u; rfl

@[simp] theorem samplerZeroQueryWeight_apply (s : PSamp) :
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight s = 0 := rfl

@[simp] theorem liftGdhToSigDdh_cost {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).cost = c.cost := by
  induction c with
  | query g e =>
    rcases g with g | u
    · simp [liftGdhToSigDdh, Comp.cost, pqSigAndDdhIface, pqGapDhIface, pqChalIface]
    · cases (u : Unit)
      simp [liftGdhToSigDdh, Comp.cost, pqSigAndDdhIface, pqGapDhIface, pqChalIface,
        ChallengerOracle.qCost, sigAndDdhOracle, gapDhDdhOracle]
  | _ => simp_all [liftGdhToSigDdh, Comp.cost, pqSigAndDdhIface, pqGapDhIface, pqChalIface]

@[simp] theorem liftGdhToSigDdh_costUB {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).costUB = c.costUB := by
  induction c with
  | query g e =>
    rcases g with g | u
    · simp [liftGdhToSigDdh, Comp.costUB, pqSigAndDdhIface, pqGapDhIface, pqChalIface]
    · cases (u : Unit)
      simp [liftGdhToSigDdh, Comp.costUB, pqSigAndDdhIface, pqGapDhIface, pqChalIface,
        ChallengerOracle.qCost, sigAndDdhOracle, gapDhDdhOracle]
  | _ => simp_all [liftGdhToSigDdh, Comp.costUB, pqSigAndDdhIface, pqGapDhIface, pqChalIface]

@[simp] theorem liftGdhToSigDdh_sigQueries {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  induction c with
  | query g e =>
    rcases g with g | u
    · rfl
    · cases (u : Unit); rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] theorem liftGdhToSigDdh_ddhQueries {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queries wDdhGdh KeyIndGapDh.wsZero := by
  induction c with
  | query g e =>
    rcases g with g | u
    · rfl
    · cases (u : Unit); rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] theorem liftGdhToSigDdh_primQueries {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queries wPrimGdh KeyIndGapDh.wsZero := by
  induction c with
  | query g e =>
    rcases g with g | u
    · rfl
    · cases (u : Unit); rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] theorem liftGdhToSigDdh_primUB {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queriesUB wPrimGdh KeyIndGapDh.wsZero := by
  induction c with
  | query g e =>
    rcases g with g | u
    · rfl
    · cases (u : Unit); rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queriesUB]

@[simp] theorem s1Prim_cost {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).cost = c.cost := by
  unfold s1Prim
  induction c <;> simp_all [liftBase, Comp.cost, pqChalIface, pqPrimIface, pqSigAndDdhIface]

@[simp] theorem s1Prim_costUB {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).costUB = c.costUB :=
  liftBase_costUB (C := sigAndDdhOracle) c

@[simp] theorem s1Prim_sigQueries {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  rw [s1Prim, liftBase_queries (C := sigAndDdhOracle)]
  exact Comp_queries_zero c

@[simp] theorem s1Prim_ddhQueries {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  rw [s1Prim, liftBase_queries (C := sigAndDdhOracle)]
  exact Comp_queries_zero c

@[simp] theorem s1Prim_primQueries {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queries wPrimBase wsZeroBase :=
  liftBase_queries (C := sigAndDdhOracle) SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight c

@[simp] theorem s1Prim_primUB {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      c.queriesUB wPrimBase wsZeroBase :=
  liftBase_queriesUB (C := sigAndDdhOracle) SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight c

@[simp] theorem qSigDdhSign_costUB (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).costUB = msg.costUB + (1 + m.val + 64) := rfl

@[simp] theorem qSigDdhSign_sigQueries (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 1 := rfl

@[simp] theorem qSigDdhSign_ddhQueries (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := rfl

@[simp] theorem qSigDdhSign_primQueries (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := rfl

@[simp] theorem qSigDdhSign_primUB (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := rfl

@[simp] theorem widenEC_costUB {Γ : List PT} (e : Expr pqxdhOps Γ (B 33)) :
    (widenEC e).costUB = e.costUB + 1569 := rfl

/-! ## Syntactic query bounds -/

theorem sig1KeyPreDispatchC_sigQueries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      2 := by
  simp [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB, sig1KeyInitiateCheckC,
    extract1KeyC, Comp.queries]

theorem delegateFgC_sigQueries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
  simp [delegateFgC, Comp.queries]

theorem sig1KeyHandleC_sigQueries (S : Setup) (K : Nat) :
    (sig1KeyHandleC S K).queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 2 := by
  simp [sig1KeyHandleC, sig1KeyPreDispatchC_sigQueries, delegateFgC_sigQueries, Comp.queries]

theorem sigKeyInd1KeyProg_totalSigQueries (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q =
      2 * q := by
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyProg, keyIndCodec]
  rw [sig1KeyHandleC_sigQueries]
  simp only [bindV_queries, s1Prim_sigQueries, Comp.queries]
  ring

theorem sigKeyInd1KeyDslProg_sigQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  rw [sigKeyInd1KeyDslProg, sigKeyInd1KeyProg_totalSigQueries]

theorem sig1KeyPreDispatchC_ddhQueries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      0 := by
  simp [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB, sig1KeyInitiateCheckC,
    extract1KeyC, Comp.queries]

@[local simp] private theorem s1_wrapBase2_chal {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries wDdhGdh KeyIndGapDh.wsZero = 0 := by
  simp [wrapBase2, Comp.queries]

@[local simp] private theorem s1_wrapSim2_chal {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries wDdhGdh KeyIndGapDh.wsZero = c.queries wDdhGdh KeyIndGapDh.wsZero := by
  simp [wrapSim2, Comp.queries]

@[local simp] private theorem s1_wrapBase2_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queriesUB wPrimGdh KeyIndGapDh.wsZero =
      c.queriesUB wPrimBase KeyIndGapDh.wsZeroBase := by
  simp [wrapBase2, bindV_queriesUB, gPrim_queriesUB_wPrimGdh, Comp.queriesUB]

@[local simp] private theorem s1_wrapSim2_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queriesUB wPrimGdh KeyIndGapDh.wsZero =
      c.queriesUB wPrimGdh KeyIndGapDh.wsZero := by
  simp [wrapSim2, bindV_queriesUB, Comp.queriesUB]

private theorem s1_gdhHandle2_chalQueries (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries wDdhGdh KeyIndGapDh.wsZero = 4 * K := by
  simp [gdhHandle2, initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B,
    finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB, roParsedC, roRawFallbackC,
    registerGdhB, Comp.queries]

private theorem s1_gdhHandle2_primUB (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queriesUB wPrimGdh KeyIndGapDh.wsZero =
      153 + 72 * (min K S.N_dh) + 16 * (min K S.N_sess_tot) := by
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    s1_wrapBase2_primUB, s1_wrapSim2_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, koskBundleOkPowsC_primUB, koskSenderOkPowsC_primUB,
    resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
    findHonestC_primUB, chooseInitRandC_primUB, chooseRespRandC_primUB,
    computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519_queriesUB, qX25519Base_queriesUB, qIsCanonical_queriesUB, qPow8_queriesUB,
    qSigPkGen_queriesUB, qSigSign_queriesUB, qSigVerify_queriesUB,
    qKemKeyGen_queriesUB, qKemEncaps_queriesUB, qKemDecaps_queriesUB,
    Comp.queriesUB]
  ring

theorem delegateFgC_ddhQueries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      4 * K := by
  simp [delegateFgC, Comp.queries, s1_gdhHandle2_chalQueries]

theorem sig1KeyHandleC_ddhQueries (S : Setup) (K : Nat) :
    (sig1KeyHandleC S K).queries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 4 * K := by
  simp [sig1KeyHandleC, sig1KeyPreDispatchC_ddhQueries, delegateFgC_ddhQueries, Comp.queries]

theorem sigKeyInd1KeyProg_totalDdhQueries (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q =
      4 * q * K := by
  dsimp only [CostedReduction.totalQueries, sigKeyInd1KeyProg, keyIndCodec]
  rw [sig1KeyHandleC_ddhQueries]
  simp only [bindV_queries, s1Prim_ddhQueries, Comp.queries]
  ring

theorem sigKeyInd1KeyDslProg_ddhQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [sigKeyInd1KeyDslProg, sigKeyInd1KeyProg_totalDdhQueries]
  refine le_trans ?_ (fgKeyIndGapDhProg_totalChalQueries_le S b)
  rw [fgKeyIndGapDhProg_totalChalQueries_eq]
  omega

theorem extract1KeyC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (bu : Var Γ₂ preKeyBundleTy) :
    (extract1KeyC S K (Δ := Δ) s bu).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      2 * min K S.N_dh + 2 := by
  simp only [extract1KeyC, bindV_queriesUB, s1Prim_primUB, letV_queriesUB,
    honestPeerC_primUB, qSigVerify_queriesUB, Comp.queriesUB]

theorem sig1KeyPreDispatchC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).queriesUB
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 4 * min K S.N_dh + 7 := by
  simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB, sig1KeyInitiateCheckC,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    s1Prim_primUB, extract1KeyC_primUB, qSigDdhSign_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, qX25519Base_queriesUB, qKemKeyGen_queriesUB,
    Comp.queriesUB]
  ring

theorem delegateFgC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      153 + 72 * min K S.N_dh + 16 * min K S.N_sess_tot := by
  simp [delegateFgC, Comp.queriesUB, s1_gdhHandle2_primUB]

theorem sig1KeyHandleC_primQueries_le (S : Setup) (K : Nat) :
    (sig1KeyHandleC S K).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤
      160 + 76 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    (sig1KeyHandleC S K)
  have hUB : (sig1KeyHandleC S K).queriesUB SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight =
      160 + 76 * min K S.N_dh + 16 * min K S.N_sess_tot := by
    simp only [sig1KeyHandleC, bindV_queriesUB, caseSumV_queriesUB,
      sig1KeyPreDispatchC_primUB, delegateFgC_primUB, Comp.queriesUB]
    ring
  rw [hUB] at h
  have h1 := Nat.min_le_right K S.N_dh
  have h2 := Nat.min_le_right K S.N_sess_tot
  omega

theorem sigKeyInd1KeyProg_totalPrimQueries_poly_le (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q ≤
      q * (160 + 76 * S.N_dh + 16 * S.N_sess_tot) := by
  have hInit : (sigKeyInd1KeyProg S K).init.queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
    simp [sigKeyInd1KeyProg, sIndex, sBool, Comp.queries]
  have hFin : (sigKeyInd1KeyProg S K).finish.queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := by
    simp [sigKeyInd1KeyProg, Comp.queries]
  have hH := Nat.mul_le_mul_left q (sig1KeyHandleC_primQueries_le S K)
  dsimp only [CostedReduction.totalQueries]
  rw [hInit, hFin]
  change 0 + q * (sig1KeyHandleC S K).queries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight +
    0 ≤ _
  omega

theorem sigKeyInd1KeyDslProg_primQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  have hp := sigKeyInd1KeyProg_totalPrimQueries_poly_le S b.q_total b.q_total
  unfold sigKeyInd1KeyDslProg primQueryBudget
  nlinarith

end

/-! ## Syntactic step-cost bounds -/

theorem sig1KeyPreDispatchC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).cost ≤ 412 * S.N_dh + 6612 * K + 26000 := by
  refine le_trans (sig1KeyPreDispatchC S K (Δ := Δ) s q).cost_le_costUB ?_
  simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyInitiateCheckC, extract1KeyC,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
    peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq,
    encEC_costUB, encKEM_costUB, widenEC_costUB,
    letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
    s1Prim_costUB, honestPeerC_costUB, qSigVerify_costUB, qSigDdhSign_costUB,
    sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qKemKeyGen_costUB,
    eCaseOpt_costUB, eAny_costUB, eFind_costUB, eqB_costUB, litB_costUB, u32OfNat_costUB,
    v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
  omega

@[local simp] private theorem s1_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[local simp] private theorem s1_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

set_option maxRecDepth 100000 in
private theorem s1_gdhHandle2_cost_le_min (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 61050 := by
  refine le_trans (gdhHandle2 S K).cost_le_costUB ?_
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC_costUB, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    s1_wrapBase2_costUB, s1_wrapSim2_costUB,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
    stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
    smMk, smUpd, qKJO, rs, slice32_costUB,
    qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
    rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
    rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
    eLet2, reMk,
    letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
    eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eAny_costUB, eMap_costUB,
    gPrim_costUB, koskBundleOkPowsC_costUB, koskSenderOkPowsC_costUB,
    resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB,
    findHonestC_costUB, chooseInitRandC_costUB,
    computePosC_costUB, computeOptPosInitC_costUB, mkSecretPosC_costUB, fgPatchC_costUB,
    sBytes32_costUB, sRandom64_costUB, sDrKey96_costUB,
    qX25519_costUB, qX25519Base_costUB, qIsCanonical_costUB, qPow8_costUB,
    qSigPkGen_costUB, qSigSign_costUB, qSigVerify_costUB,
    qKemKeyGen_costUB, qKemEncaps_costUB, qKemDecaps_costUB,
    litB_costUB, takeKB_costUB, lenB_costUB, eqB_costUB,
    u32OfNat_costUB, eqU32_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_nil, List.length_replicate, F_X25519_length', PNat.val_ofNat,
    bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  linarith

private theorem delegateFgC_cost_le_min (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 15 * bits S.N_dh + 61200 := by
  have hH := s1_gdhHandle2_cost_le_min S K
  have hLit : (litB (Γ := Δ) 32 []).cost ≤ 40 := by
    simp [litB, Expr.cost, pqxdhOps, pqBytesOps, Ops.sum]
  simp only [delegateFgC, pa2Zero, pa2Mk, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery,
    s1Mk, s1Upd, letV, bindV, liftGdhToSigDdh_cost, Comp.rename_cost,
    v, Comp.cost, Expr.cost, bits_1]
  omega

theorem delegateFgC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (delegateFgC S K (Δ := Δ) s q).cost ≤
      28015 * K + 27200 * S.N_dh + 14742 * S.N_sess_tot + 61200 := by
  have h1 := Nat.min_le_right K S.N_dh
  have h2 := Nat.min_le_right K S.N_sess_tot
  have hH := s1_gdhHandle2_cost_le_min S K
  have hLit : (litB (Γ := Δ) 32 []).cost ≤ 40 := by
    simp [litB, Expr.cost, pqxdhOps, pqBytesOps, Ops.sum]
  simp only [delegateFgC, pa2Zero, pa2Mk, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery,
    s1Mk, s1Upd, letV, bindV, liftGdhToSigDdh_cost, Comp.rename_cost,
    v, Comp.cost, Expr.cost, bits_1]
  omega

theorem sig1KeyHandleC_cost_le (S : Setup) (K : Nat) :
    (sig1KeyHandleC S K).cost ≤
      34627 * K + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87300 := by
  have hPre := sig1KeyPreDispatchC_cost_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hDel := delegateFgC_cost_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  simp only [sig1KeyHandleC, bindV, caseSumV, v, Comp.cost, Expr.cost]
  omega

theorem sigKeyInd1KeyProg_init_cost_le (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).init.cost ≤ 2 * S.N_dh + 100 := by
  refine le_trans (sigKeyInd1KeyProg S K).init.cost_le_costUB ?_
  have b1 := bits_le_succ S.N_id
  have b2 := bits_le_succ (min K (min S.N_spk_tot S.N_recv))
  have bm1 := Nat.min_le_right K (min S.N_spk_tot S.N_recv)
  have bm2 := Nat.min_le_left S.N_spk_tot S.N_recv
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  dsimp only [sigKeyInd1KeyProg]
  simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
    bindV_costUB, s1Prim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
    Comp.costUB, Expr.costUB]
  omega

theorem sigKeyInd1KeyProg_finish_cost_le (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).finish.cost ≤ 1700 := by
  refine le_trans (sigKeyInd1KeyProg S K).finish.cost_le_costUB ?_
  dsimp only [sigKeyInd1KeyProg]
  simp only [s1Forgery, eCaseOpt_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

theorem sigKeyInd1KeyProg_totalCost_poly_le (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalCost q ≤
      q * (34627 * K + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87332) + 2 * S.N_dh + 1800 := by
  have hI := sigKeyInd1KeyProg_init_cost_le S K
  have hH := sig1KeyHandleC_cost_le S K
  have hF := sigKeyInd1KeyProg_finish_cost_le S K
  have hmax : max 1 ((sig1KeyHandleC S K).cost + 32) ≤
      34627 * K + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87332 := by omega
  have hq : q * max 1 ((sig1KeyHandleC S K).cost + 32) ≤
      q * (34627 * K + 27612 * S.N_dh + 14742 * S.N_sess_tot + 87332) :=
    Nat.mul_le_mul_left q hmax
  change (sigKeyInd1KeyProg S K).init.cost + q * max 1 ((sig1KeyHandleC S K).cost + 32) +
    (sigKeyInd1KeyProg S K).finish.cost ≤ _
  linarith

theorem sigKeyInd1KeyDslProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  have hp := sigKeyInd1KeyProg_totalCost_poly_le S b.q_total b.q_total
  unfold sigKeyInd1KeyDslProg _root_.SignalPqxdh.LegacyCosted.stepCostBudget
  nlinarith

private theorem sigKeyInd1KeyProg_init_cost_le_tight (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).init.cost ≤ 2 * bits S.N_dh + 100 := by
  refine le_trans (sigKeyInd1KeyProg S K).init.cost_le_costUB ?_
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have bId : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
  have bSpk : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits S.N_dh :=
    (bits_mono ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))).trans (bits_mono (by omega))
  dsimp only [sigKeyInd1KeyProg]
  simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
    bindV_costUB, s1Prim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
    Comp.costUB, Expr.costUB]
  omega

private theorem sig1KeyPreDispatchC_cost_le_min (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    (sig1KeyPreDispatchC S K (Δ := Δ) s q).cost ≤ 412 * min K S.N_dh + 6612 * K + 26000 := by
  refine le_trans (sig1KeyPreDispatchC S K (Δ := Δ) s q).cost_le_costUB ?_
  simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyInitiateCheckC, extract1KeyC,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
    peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq,
    encEC_costUB, encKEM_costUB, widenEC_costUB,
    letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
    s1Prim_costUB, honestPeerC_costUB, qSigVerify_costUB, qSigDdhSign_costUB,
    sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qKemKeyGen_costUB,
    eCaseOpt_costUB, eAny_costUB, eFind_costUB, eqB_costUB, litB_costUB, u32OfNat_costUB,
    v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
  omega

private theorem sig1KeyHandleC_cost_le_min (S : Setup) (K : Nat) :
    (sig1KeyHandleC S K).cost ≤
      34627 * K + 27612 * min K S.N_dh + 14742 * min K S.N_sess_tot + 15 * bits S.N_dh + 87300 := by
  have hPre := sig1KeyPreDispatchC_cost_le_min S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hDel := delegateFgC_cost_le_min S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  simp only [sig1KeyHandleC, bindV, caseSumV, v, Comp.cost, Expr.cost]
  omega

private theorem sigKeyInd1KeyProg_totalCost_poly_le_min (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalCost q ≤
      q * (34627 * K + 27612 * min K S.N_dh + 14742 * min K S.N_sess_tot + 15 * bits S.N_dh + 87332) +
        2 * bits S.N_dh + 1800 := by
  have hI := sigKeyInd1KeyProg_init_cost_le_tight S K
  have hH := sig1KeyHandleC_cost_le_min S K
  have hF := sigKeyInd1KeyProg_finish_cost_le S K
  have hmax : max 1 ((sig1KeyHandleC S K).cost + 32) ≤
      34627 * K + 27612 * min K S.N_dh + 14742 * min K S.N_sess_tot + 15 * bits S.N_dh + 87332 := by
    omega
  have hq := Nat.mul_le_mul_left q hmax
  change (sigKeyInd1KeyProg S K).init.cost + q * max 1 ((sig1KeyHandleC S K).cost + 32) +
    (sigKeyInd1KeyProg S K).finish.cost ≤ _
  linarith

theorem sigKeyInd1KeyDslProg_totalCost_le_securityStepCostBudget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyDslProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hp := sigKeyInd1KeyProg_totalCost_poly_le_min S b.q_total b.q_total
  have hbits : bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  unfold sigKeyInd1KeyDslProg
  refine hp.trans ?_
  rw [hbits]
  dsimp only [_root_.SignalPqxdh.Security.stepCostBudget]
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hdiff :
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (md + ms) +
        2 ^ 10 * (q + 1) * (ld + ls) + 2 ^ 11 * md ^ 2 + 2 ^ 8 * md * ms =
      (q * (34627 * q + 27612 * md + 14742 * ms + 15 * (ld + 1) + 87332) +
        2 * (ld + 1) + 1800) +
      (30909 * q ^ 2 + 43725 * q + 63734 + 5156 * q * md + 32768 * md +
        18026 * q * ms + 32768 * ms + 1009 * q * ld + 1022 * ld +
        1024 * q * ls + 1024 * ls + 2048 * md ^ 2 + 256 * md * ms) := by ring
  omega

/-! ## Semantic query bounds -/

section SemanticSigBound

set_option allowUnsafeReducibility true
attribute [local implicit_reducible] pqChalIface pqPrimIface sigAndDdhOracle pqSamplers
attribute [local simp] Expr.eval Env.get Ext.step_wk Ext.refl_wk

@[reducible] def isSigChal1KeyQ : (PrimBaseSpec + sigAndDdhSpec).Domain → Prop :=
  fun q => isSigChalQuery q = true

instance : DecidablePred isSigChal1KeyQ :=
  fun q => inferInstanceAs (Decidable (isSigChalQuery q = true))

theorem hwSigChal1Key : ∀ g x, isSigChal1KeyQ (pqSigAndDdhIface.enc g x) →
    1 ≤ SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight g
  | .inl _, _, h => by simp [isSigChal1KeyQ, isSigChalQuery, pqSigAndDdhIface, pqChalIface] at h
  | .inr (.inl _), _, _ => le_rfl
  | .inr (.inr ()), _, h => by
    simp [isSigChal1KeyQ, isSigChalQuery, pqSigAndDdhIface, pqChalIface, sigAndDdhOracle] at h

theorem hUSigChal1Key (n : ℕ) : (pqSigAndDdhIface.fwdU n).IsQueryBoundP isSigChal1KeyQ 0 := by
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) :
      OracleComp (PrimBaseSpec + sigAndDdhSpec) _)
    isSigChal1KeyQ 0
  rw [isQueryBoundP_query_iff]
  simp [isSigChal1KeyQ, isSigChalQuery]

theorem potC_s1_ret {Γ : List PT} {τ : PT} {Pot : τ.denote → ℕ}
    (e : Expr pqxdhOps Γ τ) (env : Env Γ) {n : ℕ} (h : Pot (e.eval env) ≤ n) :
    PotOK isSigChal1KeyQ Pot ((Comp.ret e : Comp pqxdhOps pqSigAndDdhIface Γ τ).eval env) n :=
  potC_ret e env h

theorem potC_s1_ite {Γ : List PT} {τ : PT} {Pot : τ.denote → ℕ}
    (c : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps pqSigAndDdhIface Γ τ) (env : Env Γ) {n : ℕ}
    (ht : c.eval env = true → PotOK isSigChal1KeyQ Pot (t.eval env) n)
    (he : c.eval env = false → PotOK isSigChal1KeyQ Pot (e.eval env) n) :
    PotOK isSigChal1KeyQ Pot ((Comp.ite c t e).eval env) n :=
  potC_ite c t e env ht he

theorem potC_s1_caseOpt {Γ : List PT} {τ₁ τ : PT} {Pot : τ.denote → ℕ}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqSigAndDdhIface Γ τ)
    (ks : Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ) (env : Env Γ) {n : ℕ}
    (hn : o.eval env = none → PotOK isSigChal1KeyQ Pot (kn.eval env) n)
    (hs : ∀ a, o.eval env = some a → PotOK isSigChal1KeyQ Pot (ks.eval (.cons a env)) n) :
    PotOK isSigChal1KeyQ Pot ((Comp.caseOpt o kn ks).eval env) n := by
  simp only [Comp.eval]
  split
  · next h => exact hn h
  · next a h => exact hs a h

theorem potC_s1_caseSum {Γ : List PT} {τ₁ τ₂ τ : PT} {Pot : τ.denote → ℕ}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ)
    (kr : Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hl : ∀ a, s.eval env = .inl a → PotOK isSigChal1KeyQ Pot (kl.eval (.cons a env)) n)
    (hr : ∀ b, s.eval env = .inr b → PotOK isSigChal1KeyQ Pot (kr.eval (.cons b env)) n) :
    PotOK isSigChal1KeyQ Pot ((Comp.caseSum s kl kr).eval env) n :=
  potC_caseSum s kl kr env hl hr

theorem potC_s1_bind0 {Γ : List PT} {τ₁ τ₂ : PT} {Pot : τ₂.denote → ℕ}
    (m : Comp pqxdhOps pqSigAndDdhIface Γ τ₁) (k : Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ) {n : ℕ}
    (hm : m.queries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0)
    (hk : ∀ x, PotOK isSigChal1KeyQ Pot (k.eval (.cons x env)) n) :
    PotOK isSigChal1KeyQ Pot ((Comp.bind m k).eval env) n :=
  potC_bind SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight hwSigChal1Key hUSigChal1Key
    m k env hk (by omega)

theorem potC_s1_bind1 (m : ℕ+) {Γ : List PT} {τ₂ : PT} {Pot : τ₂.denote → ℕ}
    (arg : Expr pqxdhOps Γ (B m)) (k : Comp pqxdhOps pqSigAndDdhIface (B 64 :: Γ) τ₂)
    (env : Env Γ) {r n : ℕ}
    (hk : ∀ x, PotOK isSigChal1KeyQ Pot (k.eval (.cons x env)) r) (hmn : 1 + r ≤ n) :
    PotOK isSigChal1KeyQ Pot ((Comp.bind (qSigDdhSign m arg) k).eval env) n :=
  potC_bind SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight hwSigChal1Key hUSigChal1Key
    _ k env hk (by simpa [qSigDdhSign_sigQueries] using hmn)

/-- Potential of a `sig1KeyStTy` state: twice its remaining signing budget `st.2.2.2.1`. -/
def sigPot1Key (st : sig1KeyStTy.denote) : ℕ := 2 * st.2.2.2.1

def prePot1Key (m : ℕ) : (S1RS.denote ⊕ Unit) → ℕ
  | .inl r => sigPot1Key r.2
  | .inr () => m

theorem sig1KeyInitPrinB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (u : Var Γ₂ .nat) (env : Env Δ) {n : ℕ}
    (hn : sigPot1Key ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env) ≤ n) :
    PotOK isSigChal1KeyQ (fun r : S1RS.denote => sigPot1Key r.2)
      ((sig1KeyInitPrinB K s u).eval env) n := by
  unfold sig1KeyInitPrinB bindV
  refine @potC_s1_ite _ _ _ _ _ _ env _
    (fun _ => @potC_s1_ret _ _ _ _ env _ (by simpa [sigPot1Key, v] using hn)) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ _ _ _ _ env _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  exact @potC_s1_ret _ _ _ _ _ _ (by simpa [sigPot1Key, s1Upd, s1Mk, s1Budget, v] using hn)

theorem sig1KeyTargetGenSpkB_potOK (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) {n : ℕ}
    (hn : sigPot1Key ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env) ≤ n) :
    PotOK isSigChal1KeyQ (fun r : S1RS.denote => sigPot1Key r.2)
      ((sig1KeyTargetGenSpkB K s x).eval env) n := by
  unfold sig1KeyTargetGenSpkB bindV caseOptV
  refine @potC_s1_ite _ _ _ _ _ _ env _
    (fun _ => @potC_s1_ret _ _ _ _ env _ (by simpa [sigPot1Key, v] using hn)) (fun _ => ?_)
  refine @potC_s1_caseOpt _ _ _ _ _ _ _ env _
    (fun _ => @potC_s1_ret _ _ _ _ env _ (by simpa [sigPot1Key, v] using hn)) (fun uE _ => ?_)
  refine @potC_s1_ite _ _ _ _ _ _ _ _
    (fun _ => @potC_s1_ret _ _ _ _ _ _ (by simpa [sigPot1Key, v] using hn)) (fun hb => ?_)
  let bud : ℕ := (env.get (Ext.wk s)).2.2.2.1
  have hb' : bud ≠ 0 := by simpa [bud, natEq, s1Budget, v] using hb
  have hn' : 2 * bud ≤ n := by simpa [bud, sigPot1Key, v, Expr.eval] using hn
  have h2 : 2 ≤ n := by omega
  refine @potC_s1_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind1 33 _ _ _ _ _ _ (n - 1) _ (fun _ => ?_) (by omega)
  refine @potC_s1_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind1 1569 _ _ _ _ _ _ (n - 2) _ (fun _ => ?_) (by omega)
  refine @potC_s1_ret _ _ _ _ _ _ ?_
  change 2 * (bud - 1) ≤ n - 2
  omega

theorem sig1KeyInitiateCheckC_potOK (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (x : Var Γ₂ initQTy) (env : Env Δ) {n : ℕ}
    (hn : sigPot1Key ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env) ≤ n) :
    PotOK isSigChal1KeyQ (prePot1Key n) ((sig1KeyInitiateCheckC S K s x).eval env) n := by
  unfold sig1KeyInitiateCheckC letV bindV
  refine @potC_s1_bind0 _ _ (.sum S1RS .unit) (prePot1Key n) _ _ env n
    (by simp [Comp.queries]) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ n
    (by simp [extract1KeyC, bindV, Comp.queries]) (fun _ => ?_)
  refine @potC_s1_ite _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n
      (by simpa [prePot1Key, sigPot1Key, s1Upd, s1Mk, s1Budget, v] using hn))
    (fun _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n (by simp [prePot1Key]))

theorem sig1KeyPreDispatchC_potOK (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ) {n : ℕ}
    (hn : sigPot1Key ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env) ≤ n) :
    PotOK isSigChal1KeyQ (prePot1Key n) ((sig1KeyPreDispatchC S K s q).eval env) n := by
  unfold sig1KeyPreDispatchC caseSumV bindV
  refine @potC_s1_ite _ (.sum S1RS .unit) (prePot1Key n) _ _ _ env n
    (fun _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ env n
      (by simpa [prePot1Key, sigPot1Key, v] using hn)) (fun _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ env n
    (fun u _ => PotOK.bindPot
      (sig1KeyInitPrinB_potOK K s .zero (.cons u env) (by simpa [sigPot1Key, v] using hn))
      (fun r => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ _ (by simp [prePot1Key, v])))
    (fun q1 _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun _ _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n (by simp [prePot1Key]))
    (fun q2 _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun x _ => @potC_s1_ite _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
      (fun _ => PotOK.bindPot
        (sig1KeyTargetGenSpkB_potOK K s .zero (.cons x (.cons q2 (.cons q1 env)))
          (by simpa [sigPot1Key, v] using hn))
        (fun r => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ _ (by simp [prePot1Key, v])))
      (fun _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n (by simp [prePot1Key])))
    (fun q3 _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun _ _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n (by simp [prePot1Key]))
    (fun q4 _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun x _ => sig1KeyInitiateCheckC_potOK S K s .zero _ (by simpa [sigPot1Key, v] using hn))
    (fun q5 _ => ?_)
  refine @potC_s1_caseSum _ _ _ (.sum S1RS .unit) (prePot1Key n) _ _ _ _ n
    (fun x _ => sig1KeyInitiateCheckC_potOK S K s .zero _ (by simpa [sigPot1Key, v] using hn))
    (fun _ _ => @potC_s1_ret _ (.sum S1RS .unit) (prePot1Key n) _ _ n (by simp [prePot1Key]))

theorem delegateFgC_potOK (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ) {n : ℕ}
    (hn : sigPot1Key ((v s : Expr pqxdhOps Δ sig1KeyStTy).eval env) ≤ n) :
    PotOK isSigChal1KeyQ (fun r : S1RS.denote => sigPot1Key r.2)
      ((delegateFgC S K s q).eval env) n := by
  unfold delegateFgC letV bindV
  refine @potC_s1_bind0 _ _ _ _ _ _ env n (by simp [Comp.queries]) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ _ _ _ _ _ n (by simp) (fun _ => ?_)
  exact @potC_s1_ret _ _ _ _ _ n (by simpa [sigPot1Key, s1Upd, s1Mk, s1Budget, v] using hn)

theorem sig1KeyHandleC_potOK (S : Setup) (K : ℕ)
    (st : sig1KeyStTy.denote) (q : keyIndQueryTy.denote) :
    PotOK isSigChal1KeyQ (fun r : S1RS.denote => sigPot1Key r.2)
      ((sig1KeyHandleC S K).eval (.cons st (.cons q .nil))) (sigPot1Key st) := by
  unfold sig1KeyHandleC bindV caseSumV
  refine PotOK.bindPot
    (sig1KeyPreDispatchC_potOK S K .zero (.succ .zero) (.cons st (.cons q .nil)) le_rfl)
    (fun pre => ?_)
  refine @potC_s1_caseSum _ _ _ S1RS (fun r => sigPot1Key r.2) _ _ _ _ (prePot1Key (sigPot1Key st) pre)
    (fun res hres => ?_)
    (fun u hu => ?_)
  · simp only [Expr.eval, v, Ext.refl_wk] at hres
    subst hres
    exact @potC_s1_ret _ S1RS (fun r => sigPot1Key r.2) _ _ _ (by simp [prePot1Key, v])
  · simp only [Expr.eval, v, Ext.refl_wk] at hu
    subst hu
    cases u
    exact delegateFgC_potOK S K (Γ₁ := [sig1KeyStTy, keyIndQueryTy])
      (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
      (Δ := .unit :: .sum S1RS .unit :: [sig1KeyStTy, keyIndQueryTy])
      .zero (.succ .zero)
      (.cons () (.cons (Sum.inr () : (Ty.sum S1RS .unit).denote) (.cons st (.cons q .nil))))
      (n := sigPot1Key st) (by simp [sigPot1Key, v])

theorem sigKeyInd1KeyProg_init_potOK (S : Setup) (K : ℕ) (pk : Bytes) :
    PotOK isSigChal1KeyQ (fun p : Unit × sig1KeyStTy.denote => sigPot1Key p.2)
      ((sigKeyInd1KeyProg S K).init.eval (.cons pk .nil)) (2 * min S.N_spk_tot S.N_recv) := by
  dsimp only [sigKeyInd1KeyProg]
  unfold bindV
  refine @potC_s1_bind0 _ _ (.prod .unit sig1KeyStTy) _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_bind0 _ _ (.prod .unit sig1KeyStTy) _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_s1_ret _ (.prod .unit sig1KeyStTy) _ _ _ _ ?_
  have hle := Nat.min_le_right K (min S.N_spk_tot S.N_recv)
  simp only [sigPot1Key, Expr.eval]
  omega

/-- `(sigKeyInd1KeyProg S K).eval A pk` makes at most `2 * min S.N_spk_tot S.N_recv`
    signing-oracle queries for every adversary `A`. -/
theorem sigKeyInd1KeyProg_sigBounded (S : Setup) (K : ℕ)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (P := isSigChal1KeyQ) (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot (sigKeyInd1KeyProg_init_potOK S K pk) (fun as => ?_)
  refine PotOK.bindPot (B₁ := fun x : Bool × sig1KeyStTy.denote => sigPot1Key x.2)
    (potOK_simulateQ_handlerImpl sigPot1Key hUSigChal1Key (sigKeyInd1KeyProg S K).handle
      (fun gq st => sig1KeyHandleC_potOK S K st gq) (A as.1) as.2)
    (fun bs => ?_)
  exact @potC_s1_ret _ _ _ _ _ _ (Nat.zero_le _)

end SemanticSigBound

theorem sigKeyInd1KeyProg_ddhBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (4 * q * K) := by
  rw [← sigKeyInd1KeyProg_totalDdhQueries S K q]
  refine CostedReduction.queryBound_eval (sigKeyInd1KeyProg S K)
    (fun q => isDdhChalQuery q = true) SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    ?_ ?_ A q hA pk
  · intro g x hx
    rcases g with t | (m | ⟨⟩)
    · simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
    · simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
    · simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) :
        OracleComp (PrimBaseSpec + sigAndDdhSpec) _)
      (fun q => isDdhChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isDdhChalQuery]

theorem sigKeyInd1KeyProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (pk : Bytes) :
    ((sigKeyInd1KeyProg S K).eval A pk).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((sigKeyInd1KeyProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (sigKeyInd1KeyProg S K)
    (fun q => isPrimQuery q = true) SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    ?_ ?_ A q hA pk
  · intro g x hx
    rcases g with t | c
    · simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    · simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhSpec) (.inl (.inl n))) :
        OracleComp (PrimBaseSpec + sigAndDdhSpec) _)
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

end SignalPqxdh.Security.ReductionDsl.KeyInd
