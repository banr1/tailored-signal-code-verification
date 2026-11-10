/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSigEval
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game

/-!
# Cost and Query Bounds for `sigReductionAuthDslAdv` and `sigReductionAuthDslAdv2`

Establishes step-cost, AST-size, and primitive/signing query-budget bounds (`SigEufCmaAdv.Bounded`)
for the `ReductionDsl` `SigEufCma` reductions `sigReductionAuthProg` and `sigReductionAuthProg2`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

abbrev sigReductionAuthDslProg (S : Setup) (b : QueryBudget) :=
  sigReductionAuthProg S b.q_total

theorem sigReductionAuthDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (sigReductionAuthDslProg S b).totalCost b.q_total ≤ stepCostBudget S b :=
  sigReductionAuthProg_totalCost_le S b

theorem sigReductionAuthProg_primQueries_le_budget (S : Setup) (b : QueryBudget) (K : Nat) :
    (sigReductionAuthProg S K).totalQueries sigPrimW sigWS b.q_total ≤ primQueryBudget S b := by
  have h := sigReductionAuthProg_totalQueries_prim_le S K b.q_total
  unfold primQueryBudget
  nlinarith

theorem sigReductionAuthDslProg_totalPrimQueries_le (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (sigReductionAuthDslProg S b).totalQueries sigPrimW sigWS b.q_total ≤
      (sigReductionAuthDslAdv S b A).q_prim :=
  sigReductionAuthProg_primQueries_le_budget S b b.q_total

theorem sigReductionAuthProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) q)
    (pk : Bytes) :
    ((sigReductionAuthProg S K).eval A pk).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery q = true)
      ((sigReductionAuthProg S K).totalQueries sigPrimW sigWS q) :=
  CostedReduction.queryBound_eval (sigReductionAuthProg S K)
    (fun q => SignalPqxdh.isPrimQuery q = true) sigPrimW sigWS
    (fun g _ hg => by cases g with | inl _ => exact le_rfl | inr _ => cases hg)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec + eufCmaSignOracle.spec)
      (fun q => SignalPqxdh.isPrimQuery q = true) (Sum.inl (Sum.inl n)) 0).2
      (fun h => by cases h))
    A q hA pk

/-- `sigReductionAuthDslAdv` respects its declared signing and primitive query budgets. -/
theorem sigReductionAuthDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (sigReductionAuthDslAdv S b A).Bounded := by
  have hA : ∀ u : Unit,
      A.1.run.IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro _
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;>
      simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  refine ⟨fun pk => ?_, fun pk => ?_⟩
  · exact sigReductionAuthProg_chalBounded S b.q_total (fun _ => A.1.run) pk
  · exact (sigReductionAuthProg_primBounded S b.q_total b.q_total (fun _ => A.1.run) hA pk).mono
      (sigReductionAuthDslProg_totalPrimQueries_le S b A)

abbrev sigReductionAuthDslProg2 (S : Setup) (b : QueryBudget) :=
  sigReductionAuthProg2 S b.q_total

theorem sigHandleDsl_cost_le_tight (S : Setup) (K : Nat) :
    (sigHandleDsl S K).cost ≤ 76355 + 16915 * K + 3296 * min K S.N_dh := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    sigHandleDsl, sigStepC,
    extractC_costUB, wrapC_costUB,
    initPrinB_costUB, corruptB_costUB, genSpkB_costUB, genOpkB_costUB, registerB_costUB,
    roB_costUB, roRootB_costUB, sendB_costUB, recvB_true_costUB, recvB_false_costUB,
    bindV, letV, caseOptV, caseSumV, eFind, eAny, eMap,
    natEq, nat2Eq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peMk, peUpd,
    sbMk, buMk, aNone, aInitPrin, aBundle,
    Comp.costUB_liftChal, Comp.costUB_letC,
    costUB_encEC, costUB_encKEM, costUB_litBytes, costUB_u32OfNat,
    costUB_sampleBytes32, costUB_sampleRandom64C,
    costUB_queryPrim, costUB_queryPrimC, costUB_queryChal_sigFrag,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_0, bits_1,
    v, Comp.costUB, Expr.costUB]
  omega

theorem sigInit2Dsl_cost_le (S : Setup) (K : Nat) :
    (sigInit2Dsl S K).cost ≤ 60 + Nat.log 2 S.N_dh + K := by
  unfold sigInit2Dsl
  split_ifs with h0
  · simp only [emptyAuthStE, stMk, Comp.cost, Expr.cost, bits_0]
    omega
  · have hLogId : Nat.log 2 S.N_id ≤ Nat.log 2 S.N_dh :=
      Nat.log_mono_right (by unfold Setup.N_dh; omega)
    have hLogMin : Nat.log 2 (min K S.N_spk_tot) ≤ K :=
      le_trans (Nat.log_mono_right (Nat.min_le_left K S.N_spk_tot)) (Nat.log_le_self 2 K)
    simp only [emptyAuthStE, stMk, bindV, cost_sampleIndexC, cost_sampleBoolC,
      cost_v, Comp.cost, Expr.cost, bits]
    omega

theorem sigFinish2Dsl_cost_le (S : Setup) :
    (sigFinish2Dsl S).cost ≤ 1650 := by
  unfold sigFinish2Dsl
  split_ifs with h0
  · simp only [cost_litBytes, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
    omega
  · simp only [eCaseOpt, cost_litBytes, cost_v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil]
    omega

/-- Step-cost bound for `sigReductionAuthDslProg2` with 2x headroom for atomic lifting. -/
theorem sigReductionAuthDslProg2_two_mul_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    2 * (sigReductionAuthDslProg2 S b).totalCost b.q_total + 4000 * b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  dsimp only [sigReductionAuthDslProg2, CostedReduction.totalCost, sigReductionAuthProg2, authCodec]
  simp only [pqChalIface_uCost]
  have hI := sigInit2Dsl_cost_le S b.q_total
  have hH := sigHandleDsl_cost_le_tight S b.q_total
  have hF := sigFinish2Dsl_cost_le S
  generalize (sigInit2Dsl S b.q_total).cost = cI at hI ⊢
  generalize (sigHandleDsl S b.q_total).cost = cH at hH ⊢
  generalize (sigFinish2Dsl S).cost = cF at hF ⊢
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize min b.q_total S.N_dh = M_dh at hH ⊢
  generalize min b.q_total S.N_sess_tot = M_sess
  generalize Nat.log 2 S.N_dh = L_dh at hI ⊢
  generalize Nat.log 2 S.N_sess_tot = L_sess
  generalize b.q_total = q at hI hH ⊢
  have hMax : max 1 (cH + 32) ≤ 76387 + 16915 * q + 3296 * M_dh := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  cases q with
  | zero => omega
  | succ m =>
    nlinarith [Nat.zero_le (m * M_dh), Nat.zero_le (m * M_sess),
      Nat.zero_le (M_dh ^ 2), Nat.zero_le (M_dh * M_sess),
      Nat.zero_le (m * L_dh), Nat.zero_le (m * L_sess)]

theorem sigReductionAuthDslProg2_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigReductionAuthDslProg2 S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have := sigReductionAuthDslProg2_two_mul_totalCost_le_stepCostBudget S b
  omega

private theorem ah2_bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

section Ah2SizeHelpers

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] eufCmaSignOracle

@[simp] private theorem ah2_pqxdhOps_opSize (o : pqxdhOps.Op) : pqxdhOps.opSize o = 0 := by
  cases o <;> rfl
@[simp] private theorem ah2_ops_sum_opSize_inl {S : Sig} (O₁ O₂ : Ops S) (o : O₁.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inl o) = O₁.opSize o := rfl
@[simp] private theorem ah2_ops_sum_opSize_inr {S : Sig} (O₁ O₂ : Ops S) (o : O₂.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inr o) = O₂.opSize o := rfl
@[simp] private theorem ah2_pqBytesOps_opSize (o : pqBytesOps.Op) : pqBytesOps.opSize o = 0 := rfl
@[simp] private theorem ah2_pqU32Ops_opSize (o : pqU32Ops.Op) : pqU32Ops.opSize o = 0 := rfl

@[simp] private theorem ah2_liftChal_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (Comp.liftChal (C := C) c).size = c.size := by
  induction c <;> simp_all [Comp.liftChal, Comp.size, pqChalIface, pqPrimIface]

section Ah2AtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List (Ty pqSig)} {τ τ₁ τ₂ : Ty pqSig}

@[simp] private theorem ah2_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem ah2_letC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem ah2_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .vz).size + 1 := rfl
@[simp] private theorem ah2_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .vz).size + 1 := rfl
@[simp] private theorem ah2_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem ah2_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem ah2_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).size =
      xs.size + init.size + (f .vz (.vs .vz)).size + bits K + 1 := rfl
@[simp] private theorem ah2_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .vz).size + 1 := rfl
@[simp] private theorem ah2_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem ah2_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem ah2_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem ah2_litBytes_size (w : ℕ+) (bs : Bytes) :
    (Expr.litBytes w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_bytesAppend_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesAppend a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah2_bytesCons_size {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesCons b a).size = a.size + 1 := rfl
@[simp] private theorem ah2_bytesWiden_size (w d : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesWiden w d a).size = a.size + 1 := rfl
@[simp] private theorem ah2_bytesTakeK_size {w : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesTakeK k a).size = a.size + 1 := rfl
@[simp] private theorem ah2_bytesDrop_size {w : ℕ+} (n : Expr pqxdhOps Γ .nat)
    (a : Expr pqxdhOps Γ (B w)) : (Expr.bytesDrop n a).size = n.size + a.size + 2 := rfl
@[simp] private theorem ah2_bytesLen_size {w : ℕ+} (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesLen a).size = a.size + 1 := rfl
@[simp] private theorem ah2_bytesBeq_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesBeq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah2_bytesVarint_size (n : Expr pqxdhOps Γ .nat) :
    (Expr.bytesVarint n).size = n.size + 1 := rfl
@[simp] private theorem ah2_u32OfNat_size (n : Expr pqxdhOps Γ .nat) :
    (Expr.u32OfNat n).size = n.size + 1 := rfl
@[simp] private theorem ah2_u32Beq_size (a b : Expr pqxdhOps Γ U32) :
    (Expr.u32Beq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah2_sampleBool_size : (Comp.sampleBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleBytes32_size : (Comp.sampleBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleRandom64_size : (Comp.sampleRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleDrKey96_size : (Comp.sampleDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleIndex_size (N : ℕ) : (Comp.sampleIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_queryPrim_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).size = e.size + 1 := rfl
@[simp] private theorem ah2_sampleBoolC_size : (Comp.sampleBoolC (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleBytes32C_size : (Comp.sampleBytes32C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleRandom64C_size : (Comp.sampleRandom64C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleDrKey96C_size : (Comp.sampleDrKey96C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_sampleIndexC_size (N : ℕ) :
    (Comp.sampleIndexC (C := C) N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah2_queryPrimC_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem ah2_queryChal_size (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    (Comp.queryChal (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem ah2_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem ah2_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) :
    (encKEM e).size = e.size + 1 := rfl

end Ah2AtomicSizeSimp

set_option linter.unusedSimpArgs false in
private theorem ah2_firstMsgADE_size {Γ : List (Ty pqSig)}
    (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    (firstMsgADE ikA ikB eph pq).size =
      ikA.size + ikB.size + eph.size + 3 * pq.size + 36 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [firstMsgADE, pbBytesField, encEC,
    Expr.bytesAppend, Expr.bytesCons, Expr.litBytes, Expr.bytesVarint, Expr.bytesLen,
    Expr.litNat, Expr.size, ah2_ops_sum_opSize_inl, ah2_ops_sum_opSize_inr,
    ah2_pqBytesOps_opSize, ah2_pqU32Ops_opSize, ah2_pqxdhOps_opSize, hb0]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Syntactic AST size bound for `sigReductionAuthProg2`, independent of `S`. -/
theorem sigReductionAuthProg2_size_le (S : Setup) (K : Nat) :
    (sigReductionAuthProg2 S K).size ≤ 85 * bits K + 12000 := by
  have hI : (sigInit2Dsl S K).size ≤ bits K + 60 := by
    have hb : bits (min K S.N_spk_tot) ≤ bits K := ah2_bits_mono (Nat.min_le_left K S.N_spk_tot)
    unfold sigInit2Dsl
    split_ifs <;>
      simp only [emptyAuthStE, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
        Expr.noneE, Expr.listNil, ah2_v_size, ah2_bindV_size,
        ah2_sampleIndexC_size, ah2_sampleBoolC_size,
        Comp.size, Expr.size, ah2_pqxdhOps_opSize, bits_0] <;>
      omega
  have hF : (sigFinish2Dsl S).size ≤ 30 := by
    unfold sigFinish2Dsl
    split_ifs <;>
      simp only [ah2_eCaseOpt_size, ah2_litBytes_size, ah2_v_size,
        Comp.size, Expr.size, ah2_pqxdhOps_opSize] <;>
      omega
  have hH : (sigHandleDsl S K).size ≤ 80 * bits K + 11900 := by
    have hb1 : bits (min K S.N_dh) ≤ bits K := ah2_bits_mono (Nat.min_le_left K S.N_dh)
    have hb2 : bits (K.min S.N_dh) ≤ bits K := ah2_bits_mono (Nat.min_le_left K S.N_dh)
    have hb_consts :
        bits 32 = 6 ∧ bits 64 = 7 ∧ bits 96 = 7 ∧ bits 128 = 8 ∧ bits 160 = 8 ∧ bits 192 = 8 := by
      decide
    simp (config := { maxSteps := 2000000 }) only [
      sigHandleDsl, sigStepC, extractC, wrapC,
      initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
      seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seEphASk, seFresh, seChal, seMk,
      pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, rs, ah2_firstMsgADE_size, bytes2Eq, emptyAuthStE,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
      natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      ah2_liftChal_size, ah2_v_size, ah2_letC_size, ah2_bindV_size, ah2_letV_size,
      ah2_caseOptV_size, ah2_caseSumV_size, ah2_findMV_size, ah2_anyMV_size, ah2_mapMV_size,
      ah2_foldMV_size, ah2_eLet_size, ah2_eCaseOpt_size, eCaseOpt, ah2_eCaseSum_size,
      ah2_eFind_size, ah2_eAny_size, ah2_eMap_size,
      ah2_litBytes_size, Expr.litBytes, ah2_bytesAppend_size, Expr.bytesAppend,
      ah2_bytesCons_size, ah2_bytesWiden_size, Expr.bytesWiden,
      ah2_bytesTakeK_size, ah2_bytesDrop_size, ah2_bytesLen_size, ah2_bytesBeq_size, ah2_bytesVarint_size,
      ah2_u32OfNat_size, ah2_u32Beq_size,
      ah2_sampleBool_size, ah2_sampleBytes32_size, ah2_sampleRandom64_size, ah2_sampleDrKey96_size,
      ah2_sampleIndex_size, ah2_queryPrim_size,
      ah2_sampleBoolC_size, ah2_sampleBytes32C_size, ah2_sampleRandom64C_size, ah2_sampleDrKey96C_size,
      ah2_sampleIndexC_size, ah2_queryPrimC_size, ah2_queryChal_size,
      ah2_encEC_size, encEC, ah2_encKEM_size, encKEM, Expr.bytesCons, v,
      Comp.size, Expr.size, ah2_ops_sum_opSize_inl, ah2_ops_sum_opSize_inr,
      ah2_pqBytesOps_opSize, ah2_pqU32Ops_opSize, ah2_pqxdhOps_opSize,
      bits_0, bits_1, ↓reduceIte, Bool.false_eq_true]
    simp only [Comp.queryChal, Comp.size, Expr.size, ah2_ops_sum_opSize_inl,
      ah2_ops_sum_opSize_inr, ah2_pqBytesOps_opSize, ah2_pqU32Ops_opSize, ah2_pqxdhOps_opSize]
    dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
    omega
  change (sigInit2Dsl S K).size + (sigHandleDsl S K).size + (sigFinish2Dsl S).size ≤ _
  omega

end Ah2SizeHelpers

theorem sigReductionAuthDslProg2_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigReductionAuthDslProg2 S b).size ≤
      12000 + 85 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hP := sigReductionAuthProg2_size_le S b.q_total
  have hq : bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    ah2_bits_mono (by
      calc b.q_total ≤ (b.q_total + 1) * (b.q_total + 1) := by nlinarith
        _ ≤ 2 ^ 16 * ((b.q_total + 1) * (b.q_total + 1)) :=
          Nat.le_mul_of_pos_left _ (by decide)
        _ = 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := by rw [Nat.mul_assoc]
        _ ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
          unfold _root_.SignalPqxdh.Security.stepCostBudget; dsimp only; omega)
  dsimp only [sigReductionAuthDslProg2] at hP ⊢
  omega

theorem sigReductionAuthProg2_primQueries_le_budget (S : Setup) (b : QueryBudget) (K : Nat) :
    (sigReductionAuthProg2 S K).totalQueries sigPrimW sigWS b.q_total ≤ primQueryBudget S b := by
  have hI : (sigInit2Dsl S K).queries sigPrimW sigWS = 0 := by
    unfold sigInit2Dsl; split_ifs <;>
      simp [bindV, Comp.sampleIndexC, Comp.sampleBoolC, sigWS, Comp.queries]
  have hF : (sigFinish2Dsl S).queries sigPrimW sigWS = 0 := by
    unfold sigFinish2Dsl; split_ifs <;> simp [Comp.queries]
  have h : (sigReductionAuthProg2 S K).totalQueries sigPrimW sigWS b.q_total =
      (sigReductionAuthProg S K).totalQueries sigPrimW sigWS b.q_total := by
    simp [CostedReduction.totalQueries, sigReductionAuthProg2, sigReductionAuthProg,
      hI, hF, sigInitDsl_queries_prim, sigFinishDsl_queries_prim]
  rw [h]
  exact sigReductionAuthProg_primQueries_le_budget S b K

theorem sigReductionAuthDslProg2_totalPrimQueries_le (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (sigReductionAuthDslProg2 S b).totalQueries sigPrimW sigWS b.q_total ≤
      (sigReductionAuthDslAdv2 S b A).q_prim :=
  sigReductionAuthProg2_primQueries_le_budget S b b.q_total

theorem sigReductionAuthProg2_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) q)
    (pk : Bytes) :
    ((sigReductionAuthProg2 S K).eval A pk).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery q = true)
      ((sigReductionAuthProg2 S K).totalQueries sigPrimW sigWS q) :=
  CostedReduction.queryBound_eval (sigReductionAuthProg2 S K)
    (fun q => SignalPqxdh.isPrimQuery q = true) sigPrimW sigWS
    (fun g _ hg => by cases g with | inl _ => exact le_rfl | inr _ => cases hg)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec + eufCmaSignOracle.spec)
      (fun q => SignalPqxdh.isPrimQuery q = true) (Sum.inl (Sum.inl n)) 0).2
      (fun h => by cases h))
    A q hA pk

theorem sigInit2_potOK_pub (S : Setup) (K : Nat) (pk : (B 32).denote) :
    PotOK isSigChalQ (fun p : (Ty.prod .unit sigStTy).denote => sigPot p.2)
      ((sigInit2Dsl S K).eval (.cons pk .nil)) (2 * S.N_spk_tot) := by
  unfold sigInit2Dsl
  split_ifs with h0
  · refine potC_ret _ _ ?_
    simp [sigPot, Expr.eval]
  · unfold bindV
    refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
      (fun x => ?_) (by simp [Comp.sampleIndexC, Comp.queries, sigWS])
    refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
      (fun y => ?_) (by simp [Comp.sampleBoolC, Comp.queries, sigWS])
    refine potC_ret _ _ ?_
    simp only [sigPot, Expr.eval]
    have := Nat.min_le_right K S.N_spk_tot
    omega

theorem sigReductionAuthProg2_chalBounded_pub (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    ((sigReductionAuthProg2 S K).eval A pk).IsQueryBoundP isSigChalQ (2 * S.N_spk_tot) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot (sigInit2_potOK_pub S K pk) (fun as => ?_)
  refine PotOK.bindPot (B₁ := fun x : Bool × sigStTy.denote => sigPot x.2)
    (potOK_simulateQ_handlerImpl sigPot hUSigChal (sigReductionAuthProg2 S K).handle
      (fun q s => sigHandle_potOK S K s q) (A as.1) as.2)
    (fun bs => ?_)
  dsimp only [sigReductionAuthProg2, sigFinish2Dsl]
  split_ifs <;> exact potC_ret _ _ (Nat.zero_le _)

theorem sigReductionAuthDslAdv2_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (sigReductionAuthDslAdv2 S b A).Bounded := by
  have hA : ∀ u : Unit,
      A.1.run.IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro _
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;>
      simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  refine ⟨fun pk => ?_, fun pk => ?_⟩
  · exact sigReductionAuthProg2_chalBounded_pub S b.q_total (fun _ => A.1.run) pk
  · exact (sigReductionAuthProg2_primBounded S b.q_total b.q_total (fun _ => A.1.run) hA pk).mono
      (sigReductionAuthDslProg2_totalPrimQueries_le S b A)

end SignalPqxdh.Security.ReductionDsl.AuthHs
