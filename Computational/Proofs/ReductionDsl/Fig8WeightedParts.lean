/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.GameHop.ReductionDsl.CostUB

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction SM.Engine
  CKA AEADScheme MACScheme WireAEAD FSAEAD ReductionDsl
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.PureAuxMacroLift
open Computational.Proofs.ReductionDsl.Fig8SourceCosts
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts

namespace Computational.Proofs.ReductionDsl.Fig8WeightedParts

theorem compCostW_le_of_parts {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {opC : O.Op → ℕ} {sC : I.smp.Samp → ℕ} {qC : I.Tag → ℕ}
    {Γ : List (Ty S)} {t : Ty S} {c : Comp O I Γ t} {a b m : ℕ}
    (hC : c.cost ≤ a) (hE : compExcessUB opC sC qC c ≤ b) (hm : a + b ≤ m) :
    compCostW opC sC qC c ≤ m :=
  (compCostW_le_cost_add_excessUB opC sC qC c).trans ((Nat.add_le_add hC hE).trans hm)



def fig8AtomicStepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  100000 * L + L * (3 * ReductionDsl.bits qep + 60) + 120 * B +
    200 * ReductionDsl.bits qep + 25000000

lemma fig8Atomic_poly_le_ratchetCostBudget (q qep : ℕ) :
    (q + 1) * fig8AtomicStepBound q qep ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget fig8AtomicStepBound
  dsimp only
  have hbq : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  generalize ReductionDsl.bits qep = bq at hbq ⊢
  set M := maxForwardJumps + bq
  set L := q + 1
  set B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have hL_pos : 1 ≤ L := by omega
  have hM_lb : 25001 ≤ M := by omega
  have hm_le : maxForwardJumps + 1 ≤ M := by omega
  have hB_le : B ≤ L * M := Nat.mul_le_mul_left L hm_le
  have h100kL : 100000 * L ≤ 4 * (L * M) := by
    have h4M : 100000 ≤ 4 * M := by omega
    calc 100000 * L = L * 100000 := Nat.mul_comm _ _
      _ ≤ L * (4 * M) := Nat.mul_le_mul_left L h4M
      _ = 4 * (L * M) := by ring
  have h3b : 3 * bq + 60 ≤ 4 * M := by omega
  have hL3b : L * (3 * bq + 60) ≤ 4 * (L * M) :=
    (Nat.mul_le_mul_left L h3b).trans_eq (by ring)
  have hb_LM : bq ≤ L * M := by
    calc bq ≤ M := by omega
      _ = 1 * M := (Nat.one_mul M).symm
      _ ≤ L * M := Nat.mul_le_mul_right M hL_pos
  have h1_LM : 25001 ≤ L * M := by
    calc 25001 = 1 * 25001 := (Nat.one_mul _).symm
      _ ≤ L * M := Nat.mul_le_mul hL_pos hM_lb
  have hsum :
      100000 * L + L * (3 * bq + 60) + 120 * B +
        200 * bq + 25000000 ≤
        2 ^ 12 * (L * M) := by
    generalize L * M = LM at hB_le h100kL hL3b hb_LM h1_LM ⊢
    generalize L * (3 * bq + 60) = L3b at hL3b ⊢
    omega
  calc (q + 1) * (100000 * L + L * (3 * bq + 60) +
          120 * B + 200 * bq + 25000000)
      ≤ (q + 1) * (2 ^ 12 * (L * M)) := Nat.mul_le_mul_left (q + 1) hsum
    _ = 2 ^ 12 * (q + 1) ^ 2 * M := by
      change (q + 1) * (2 ^ 12 * ((q + 1) * M)) = 2 ^ 12 * (q + 1) ^ 2 * M
      ring

lemma bits_le_add_one (n : ℕ) : ReductionDsl.bits n ≤ n + 1 :=
  ReductionDsl.bits_le_succ n

lemma add_mul_le_ratchetCostBudget_atomic {q qep a b : ℕ}
    (ha : a ≤ fig8AtomicStepBound q qep) (hb : b ≤ fig8AtomicStepBound q qep) :
    a + q * b ≤ ratchetCostBudget q qep := by
  have hmul : q * b ≤ q * fig8AtomicStepBound q qep := Nat.mul_le_mul_left q hb
  have hring :
      (q + 1) * fig8AtomicStepBound q qep =
        q * fig8AtomicStepBound q qep + fig8AtomicStepBound q qep := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : a + q * b ≤ (q + 1) * fig8AtomicStepBound q qep := by omega
  exact h1.trans (fig8Atomic_poly_le_ratchetCostBudget q qep)

private lemma le_fig8AtomicStepBound_const {q qep c : ℕ} (hc : c ≤ 25000000) :
    c ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  generalize ReductionDsl.bits qep = bq
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize (q + 1) * (maxForwardJumps + 1) = B
  omega

lemma compiled_totalCost_le_ratchetCostBudget
    {q qep initW handleW finishW ovhI uC ovhH ovhF : ℕ}
    (hIF : initW + finishW + 100000 ≤ fig8AtomicStepBound q qep)
    (hH : handleW + 200000 ≤ fig8AtomicStepBound q qep)
    (hovhIF : ovhI + ovhF ≤ 100000)
    (huC : uC ≤ 200000)
    (hovhH : ovhH ≤ 200000) :
    (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) ≤
      ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep :=
    le_fig8AtomicStepBound_const (by decide)
  have hmax : max uC (handleW + ovhH) ≤ fig8AtomicStepBound q qep :=
    max_le (huC.trans h200k) (by omega)
  have h1 : (initW + ovhI) + (finishW + ovhF) ≤ fig8AtomicStepBound q qep := by omega
  have h2 :
      (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) =
        ((initW + ovhI) + (finishW + ovhF)) + q * max uC (handleW + ovhH) := by omega
  rw [h2]
  exact add_mul_le_ratchetCostBudget_atomic h1 hmax

private lemma linear_le_fig8AtomicStepBound {q qep k a b : ℕ}
    (hk : k ≤ 200) (ha : a ≤ 100000) (hb : b ≤ 25000000) :
    k * ReductionDsl.bits qep + a * (q + 1) + b ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  have hk' := Nat.mul_le_mul_right (ReductionDsl.bits qep) hk
  have ha' := Nat.mul_le_mul_right (q + 1) ha
  generalize ReductionDsl.bits qep = bq at hk' ⊢
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize (q + 1) * (maxForwardJumps + 1) = B
  generalize q + 1 = L at ha' ⊢
  omega

private lemma init_finish_le_step {q qep k1 k2 a1 a2 b1 b2 x y : ℕ}
    (hx : x ≤ k1 * ReductionDsl.bits qep + a1 * (q + 1) + b1)
    (hy : y ≤ k2 * ReductionDsl.bits qep + a2 * (q + 1) + b2)
    (hk : k1 + k2 ≤ 200) (ha : a1 + a2 ≤ 100000) (hb : b1 + b2 + 100000 ≤ 25000000) :
    x + y + 100000 ≤ fig8AtomicStepBound q qep := by
  refine (Nat.add_le_add (Nat.add_le_add hx hy) le_rfl).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound hk ha hb)
  ring

private lemma handle_le_step {q qep k a b h : ℕ}
    (hh : h ≤ k * ReductionDsl.bits qep + a * (q + 1) + b)
    (hk : k ≤ 200) (ha : a ≤ 100000) (hb : b + 200000 ≤ 25000000) :
    h + 200000 ≤ fig8AtomicStepBound q qep := by
  refine (Nat.add_le_add hh le_rfl).trans ?_
  refine (le_of_eq ?_).trans (linear_le_fig8AtomicStepBound hk ha hb)
  ring

private lemma simHandle_none_hm (bq L : ℕ) :
    (20 * bq + 5 * 1 + 1800 * L + 17025) + (65000 * L + 800000) ≤
      20 * bq + 66800 * L + 817030 := by omega

private lemma simHandle_some_hm {bq bi L : ℕ} (hbi : bi ≤ bq + 4) :
    (20 * bq + 5 * bi + 1800 * L + 17025) + (65000 * L + 800000) ≤
      25 * bq + 66800 * L + 817100 := by omega

private lemma implEC_step_arith {L B Lbq bq bB c e : ℕ}
    (hbB : bB ≤ B + 1)
    (hc : c + 12 ≤ 20000 * L + Lbq + 3 * B + 200 * bq + 350000)
    (he : e ≤ 5 * 0 + 0 + 7 * (300 * L + 250000) + 2 * 2000000 +
      2 * (500 * L + 40 * B + 6 * bB + 5700000) + 300 * L + 250000) :
    c + e + 200000 ≤ 100000 * L + Lbq + 120 * B + 200 * bq + 25000000 := by
  omega

private lemma hooksCKA_mono_arith {L B bq bt btH : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    3 * btH + bt + (B + 1) + 1010 ≤ 320 * L + 10 * bq + B + 2500 := by omega

private lemma hooksPRNG_mono_arith {L B bq bt btH : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    2 * bt + 3 * btH + (B + 1) + 910 ≤ 320 * L + 10 * bq + B + 2500 := by omega

private lemma hooksFS_mono_arith {L B j bq bt btH : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4) :
    300 * L + 20 * (j + 1) + 2 * bt + 2 * btH + (B + 1) + 2110 ≤
      320 * L + 10 * bq + B + 2500 := by omega

private lemma authOut_hm {L bq bt btL c : ℕ}
    (ht : bt ≤ bq + 4) (htL : btL ≤ bq + 4)
    (hc : c ≤ (btL + 3) + bt + 100 * L + 260) :
    c + 0 ≤ 2 * bq + 100 * L + 500 := by omega

private lemma privOut_hm {L bq bt btL c e : ℕ}
    (ht : bt ≤ bq + 4) (htL : btL ≤ bq + 4)
    (hc : c ≤ 2 * (btL + 3) + 2 * bt + 50 * L + 260)
    (he : e ≤ 250) :
    c + e ≤ 5 * bq + 100 * L + 1000 := by omega

private lemma initPRNG_hm {bq bt btH c e : ℕ}
    (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4)
    (hc : c ≤ 2 * bt + 3 * btH + 930) (he : e ≤ 3300) :
    c + e ≤ 5 * bq + 0 * 1 + 5000 := by omega

private lemma initFS_hm {L j bq bt btH c e : ℕ}
    (hj : j + 1 ≤ L) (ht : bt ≤ bq + 4) (htH : btH ≤ bq + 4)
    (hc : c ≤ 200 * L + 12 * (j + 1) + 2 * bt + 2 * btH + 2030)
    (he : e ≤ 200 * L + 5100) :
    c + e ≤ 4 * bq + 500 * L + 8000 := by omega

private lemma bind_ret_pair_unit_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {σ : Ty S'}
    {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : c.cost ≤ K) (hK : K + 5 ≤ M) :
    (Comp.bind c (Comp.ret (.pair .unit .v0))).cost ≤ M := by
  simp only [Comp.cost, Expr.cost, v0_cost]
  omega

private lemma bind_ret_pair_unit_excess_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} (opC : O'.Op → ℕ) (sampC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {Γ' : List (Ty S')} {σ : Ty S'} {c : Comp O' I' Γ' σ} {K M : ℕ}
    (hc : compExcessUB opC sampC qC c ≤ K) (hK : K ≤ M) :
    compExcessUB opC sampC qC (Comp.bind c (Comp.ret (.pair .unit .v0))) ≤ M := by
  simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
    exprExcessUB_v0]
  omega

private lemma samp_bind_ret_pair_unit_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {s : I'.smp.Samp}
    {u : Expr O' Γ' (I'.smp.sDom s)} {σ : Ty S'}
    (hs : I'.smp.sCost s = 1) (hu : u.cost = 1)
    {c : Comp O' I' ((I'.smp.sTy s) :: Γ') σ} {K M : ℕ}
    (hc : c.cost ≤ K) (hK : K + 9 ≤ M) :
    (Comp.bind (Comp.sample s u) (Comp.bind c (Comp.ret (.pair .unit .v0)))).cost ≤ M := by
  simp only [Comp.cost, Expr.cost, v0_cost, hs, hu]
  omega

private lemma samp_bind_ret_pair_unit_excess_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} (opC : O'.Op → ℕ) (sampC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {Γ' : List (Ty S')} {s : I'.smp.Samp}
    {u : Expr O' Γ' (I'.smp.sDom s)} {σ : Ty S'}
    (hu : exprExcessUB opC u = 0)
    {c : Comp O' I' ((I'.smp.sTy s) :: Γ') σ} {K M : ℕ}
    (hc : compExcessUB opC sampC qC c ≤ K) (hK : sampC s + K ≤ M) :
    compExcessUB opC sampC qC
      (Comp.bind (Comp.sample s u) (Comp.bind c (Comp.ret (.pair .unit .v0)))) ≤ M := by
  simp only [compExcessUB_bind, compExcessUB_sample, compExcessUB_ret,
    exprExcessUB_pair, exprExcessUB_unit, exprExcessUB_v0, hu]
  omega

private lemma comp_ret_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {τ : Ty S'}
    {e : Expr O' Γ' τ} {K M : ℕ}
    (he : e.cost ≤ K) (hM : K + 1 ≤ M) :
    (Comp.ret (I := I') e).cost ≤ M := by
  simp only [Comp.cost]
  omega

private lemma comp_ite_cost_le {S' : Sig} {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {O' : Ops S'} {I' : Iface S' TSpec} {Γ' : List (Ty S')} {τ : Ty S'}
    {cond : Expr O' Γ' .bool} {c1 c2 : Comp O' I' Γ' τ} {K1 K2 M : ℕ}
    (hcond : cond.cost ≤ K1) (hc : max c1.cost c2.cost ≤ K2) (hM : K1 + K2 + 1 ≤ M) :
    (Comp.ite cond c1 c2).cost ≤ M := by
  simp only [Comp.cost]
  omega

section ProgramWeightedBounds

section EngineWeightedBounds

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

set_option maxRecDepth 100000 in
lemma implEC_compCostW_le_fig8AtomicStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep : ℕ)
    (mo : SM.Construction.Mode)
    (htStar : mo.tStar < qep + 2)
    (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hhkC : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (300 * (q + 1) + 250000) 2000000
      (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
        6 * ReductionDsl.bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (SM.Engine.implEC
        (Γ' := [SM.Engine.esTy
          (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
          CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
        hk (q + 1) (2 + 1) qep maxForwardJumps
        (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qep := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  have hC := implEC_step_le_fig8StepBound hk q qep mo htStar htL hhkC
  have hE := implEC_excessUB_le hk
    (300 * (q + 1) + 250000) 2000000
    (500 * (q + 1) + 40 * ((q + 1) * (maxForwardJumps + 1)) +
      6 * ReductionDsl.bits ((q + 1) * (maxForwardJumps + 1)) + 5700000)
    (q + 1) qep maxForwardJumps mo hhkE
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  have hW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
    (SM.Engine.implEC
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) 3 qep maxForwardJumps (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1)
  have hbB := bits_le_add_one ((q + 1) * (maxForwardJumps + 1))
  simp only [exprExcessUB_v0, exprExcessUB_v1] at hE
  unfold fig8StepBound at hC
  unfold fig8AtomicStepBound
  dsimp only at hC ⊢
  generalize ReductionDsl.bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE hbB
  generalize (q + 1) * (maxForwardJumps + 1) = B at hE hbB hC hW ⊢
  omega

lemma redCKAAuthProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redCKAAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
        compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksCKA_mono_arith ht_bits htH_bits)
  have hhkE := (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * ReductionDsl.bits B + 5700000)
    (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤
        0 * ReductionDsl.bits qep + 0 * (q + 1) + 2100 := by
      dsimp only [P, SM.Construction.redCKAAuthProg]
      have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts (a := 520) (b := 1510) ?_ ?_ (by simp)
      · exact bind_ret_pair_unit_cost_le hiC0 (by simp only [Expr.cost]; decide)
      · exact bind_ret_pair_unit_excess_le _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤
        2 * ReductionDsl.bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, SM.Construction.redCKAAuthProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [SM.Construction.ckaEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [SM.Construction.ckaEsTy, .bool])
        (Expr.v0 (O := OO_cka) (t := SM.Construction.ckaEsTy))).1
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := (ReductionDsl.bits (tL.getD 0) + 3) + ReductionDsl.bits t + 100 * L + 260)
        (b := 0) ?_ ?_ (authOut_hm ht_bits htL_bits le_rfl)
      · exact comp_ret_cost_le hfC0 (by
          simp only [v0_cost]; dsimp only [mo, SM.Construction.Mode.policy]; omega)
      · simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redCKAAuthProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redCKAPrivProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redCKAPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC ckaQueryC P.init +
        compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨false, tL, t⟩
  let II := CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksCKA_mono_arith ht_bits htH_bits)
  have hhkE := (hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * ReductionDsl.bits B + 5700000)
    (by omega) (by decide) (by omega)
  have hsmp : II.smp.sCost CKA.CKASamp.bit = 1 := rfl
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC ckaQueryC P.init ≤
        0 * ReductionDsl.bits qep + 0 * (q + 1) + 2500 := by
      dsimp only [P, SM.Construction.redCKAPrivProg]
      have hiC0 := initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.bool, .unit]) .v0
      have hiE0 := initCKAEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.bool, .unit]) .v0
      refine compCostW_le_of_parts (a := 530) (b := 1710) ?_ ?_ (by simp)
      · exact samp_bind_ret_pair_unit_cost_le hsmp rfl hiC0 (by simp only [v0_cost]; decide)
      · exact samp_bind_ret_pair_unit_excess_le _ _ _ rfl hiE0
          (by simp only [exprExcessUB_v0, ckaSampC]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC ckaQueryC P.finish ≤
        5 * ReductionDsl.bits qep + 100 * (q + 1) + 1000 := by
      dsimp only [P, SM.Construction.redCKAPrivProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := privOutC_cost_le (O' := OO_cka) (I' := II)
        (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CKA.CKASamp.bit .unit)
        (Γ' := [SM.Construction.ckaEsTy, .bool])
        (SM.Engine.cGsB (SM.Engine.esG .v0)) .v1 .v0
      have hfE0 := privOutC_excessUB_le (O' := OO_cka) (I' := II) (ckaOpC B) ckaSampC ckaQueryC
        (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CKA.CKASamp.bit .unit)
        (Γ' := [SM.Construction.ckaEsTy, .bool])
        (SM.Engine.cGsB (SM.Engine.esG .v0)) .v1 .v0
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := 2 * (ReductionDsl.bits (tL.getD 0) + 3) + 2 * ReductionDsl.bits t + 50 * L + 260)
        (b := 250) ?_ ?_ (privOut_hm ht_bits htL_bits le_rfl le_rfl)
      · exact hfC0.trans (by
          simp only [cGsB_cost, esG_cost, v0_cost, v1_cost, Comp.cost, Expr.cost, hsmp]
          dsimp only [mo, SM.Construction.Mode.policy]
          omega)
      · exact hfE0.trans (by
          simp only [SM.Engine.cGsB, SM.Engine.esG, compExcessUB_sample, exprExcessUB_fst,
            exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, ckaSampC]
          decide)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redCKAPrivProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redPRNGAuthProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redPRNGAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC prngQueryC P.init +
        compCostW (ckaOpC B) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksPRNG_mono_arith ht_bits htH_bits)
  have hhkE := (hooksPRNGC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * ReductionDsl.bits B + 5700000)
    (by omega) (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC prngQueryC P.init ≤
        5 * ReductionDsl.bits qep + 0 * (q + 1) + 5000 := by
      dsimp only [P, SM.Construction.redPRNGAuthProg]
      have hiC0 := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
      have hiE0 := initPRNGEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 2 * ReductionDsl.bits t + 3 * ReductionDsl.bits (healEpoch tL) + 930)
        (b := 3300) ?_ ?_
        ((initPRNG_hm ht_bits htH_bits le_rfl le_rfl).trans (by simp))
      · exact bind_ret_pair_unit_cost_le hiC0 (by
          simp only [Expr.cost]; dsimp only [mo, SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le _ _ _ hiE0 (by simp only [exprExcessUB_bool]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC prngQueryC P.finish ≤
        2 * ReductionDsl.bits qep + 100 * (q + 1) + 500 := by
      dsimp only [P, SM.Construction.redPRNGAuthProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := authOutE_cost_le (O' := OO_cka)
        (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [SM.Construction.prngEsTy, .bool]) .v0
      have hfE0 := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [SM.Construction.prngEsTy, .bool])
        (Expr.v0 (O := OO_cka) (t := SM.Construction.prngEsTy))).1
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := (ReductionDsl.bits (tL.getD 0) + 3) + ReductionDsl.bits t + 100 * L + 260)
        (b := 0) ?_ ?_ (authOut_hm ht_bits htL_bits le_rfl)
      · exact comp_ret_cost_le hfC0 (by
          simp only [v0_cost]; dsimp only [mo, SM.Construction.Mode.policy]; omega)
      · simp only [compExcessUB_ret, hfE0, exprExcessUB_v0]; exact le_rfl
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redPRNGAuthProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redPRNGPrivProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redPRNGPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC prngQueryC P.init +
        compCostW (ckaOpC B) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨false, tL, t⟩
  let II := PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hhkC := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksPRNG_mono_arith ht_bits htH_bits)
  have hhkE := (hooksPRNGC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B B mo).mono
    (Ho' := 300 * L + 250000) (Hs' := 2000000)
    (Hr' := 500 * L + 40 * B + 6 * ReductionDsl.bits B + 5700000)
    (by omega) (by decide) (by omega)
  have hsmp : II.smp.sCost CKA.CKASamp.bit = 1 := rfl
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC prngQueryC P.init ≤
        5 * ReductionDsl.bits qep + 0 * (q + 1) + 5000 := by
      dsimp only [P, SM.Construction.redPRNGPrivProg]
      have hiC0 := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo (Γ' := [.bool, .unit]) .v0
      have hiE0 := initPRNGEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo (Γ' := [.bool, .unit]) .v0
      refine compCostW_le_of_parts
        (a := 2 * ReductionDsl.bits t + 3 * ReductionDsl.bits (healEpoch tL) + 930)
        (b := 3300) ?_ ?_
        ((initPRNG_hm ht_bits htH_bits le_rfl le_rfl).trans (by simp))
      · exact samp_bind_ret_pair_unit_cost_le hsmp rfl hiC0 (by
          simp only [v0_cost]; dsimp only [mo, SM.Construction.Mode.tH]; omega)
      · exact samp_bind_ret_pair_unit_excess_le _ _ _ rfl hiE0
          (by simp only [exprExcessUB_v0, ckaSampC]; decide)
    have hf : compCostW (ckaOpC B) ckaSampC prngQueryC P.finish ≤
        5 * ReductionDsl.bits qep + 100 * (q + 1) + 1000 := by
      dsimp only [P, SM.Construction.redPRNGPrivProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hfC0 := privOutC_cost_le (O' := OO_cka) (I' := II)
        (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CKA.CKASamp.bit .unit)
        (Γ' := [SM.Construction.prngEsTy, .bool])
        (SM.Engine.cGsB (SM.Engine.esG .v0)) .v1 .v0
      have hfE0 := privOutC_excessUB_le (O' := OO_cka) (I' := II) (ckaOpC B) ckaSampC prngQueryC
        (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (fun {Γ''} => @Comp.sample _ _ _ OO_cka II Γ'' CKA.CKASamp.bit .unit)
        (Γ' := [SM.Construction.prngEsTy, .bool])
        (SM.Engine.cGsB (SM.Engine.esG .v0)) .v1 .v0
      dsimp only [mo] at hfE0
      refine compCostW_le_of_parts
        (a := 2 * (ReductionDsl.bits (tL.getD 0) + 3) + 2 * ReductionDsl.bits t + 50 * L + 260)
        (b := 250) ?_ ?_ (privOut_hm ht_bits htL_bits le_rfl le_rfl)
      · exact hfC0.trans (by
          simp only [cGsB_cost, esG_cost, v0_cost, v1_cost, Comp.cost, Expr.cost, hsmp]
          dsimp only [mo, SM.Construction.Mode.policy]
          omega)
      · exact hfE0.trans (by
          simp only [SM.Engine.cGsB, SM.Engine.esG, compExcessUB_sample, exprExcessUB_fst,
            exprExcessUB_snd, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_unit, ckaSampC]
          decide)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redPRNGPrivProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redFSAuthProg_parts_le (q qep j t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) (hj : j < q) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redFSAuthProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps j tL t
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨true, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hjL : j + 1 ≤ L := by omega
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksFS_mono_arith hjL ht_bits htH_bits)
  have hhkE := hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo j
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤
        4 * ReductionDsl.bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, SM.Construction.redFSAuthProg]
      have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
      have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B L mo j (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 200 * L + 12 * (j + 1) + 2 * ReductionDsl.bits t + 2 * ReductionDsl.bits (healEpoch tL) + 2030)
        (b := 200 * L + 5100) ?_ ?_ (initFS_hm hjL ht_bits htH_bits le_rfl le_rfl)
      · exact bind_ret_pair_unit_cost_le hiC0 (by
          simp only [Expr.cost]; dsimp only [mo, SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le _ _ _ hiE0 (by
          simp only [exprExcessUB_bool]; omega)
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤
        0 * ReductionDsl.bits qep + 0 * (q + 1) + 300 := by
      dsimp only [P, SM.Construction.redFSAuthProg]
      exact compCostW_le_of_parts (a := 10) (b := 210)
        (by simp only [Comp.cost, Expr.cost]; decide)
        (by simp only [compExcessUB_sample, exprExcessUB_unit, ckaSampC]; decide)
        (by simp)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redFSAuthProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redFSPrivProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redFSPrivProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨false, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hj0 : 0 + 1 ≤ L := by omega
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo 0).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksFS_mono_arith hj0 ht_bits htH_bits)
  have hhkE := hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo 0
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤
        4 * ReductionDsl.bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, SM.Construction.redFSPrivProg]
      have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo 0 (Γ' := [.unit]) (.bool false)
      have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B L mo 0 (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 200 * L + 12 * (0 + 1) + 2 * ReductionDsl.bits t + 2 * ReductionDsl.bits (healEpoch tL) + 2030)
        (b := 200 * L + 5100) ?_ ?_ (initFS_hm hj0 ht_bits htH_bits le_rfl le_rfl)
      · exact bind_ret_pair_unit_cost_le hiC0 (by
          simp only [Expr.cost]; dsimp only [mo, SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le _ _ _ hiE0 (by
          simp only [exprExcessUB_bool]; omega)
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤
        5 * ReductionDsl.bits qep + 100 * (q + 1) + 1000 := by
      dsimp only [P, SM.Construction.redFSPrivProg]
      rw [show (2 : ℕ) + 1 = 3 from rfl]
      have hpvC := privValidE_cost_le (O' := OO_cka)
        (vpT := @SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E)
        (hsT := @SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E)
        L mo.policy (Γ' := [SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool]) .v0
      have hpvE := (pureEngineExprs_excessUB (ckaOpC B) L 3 0 mo.policy
        (Γ' := [SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool])
        (Expr.v0 (O := OO_cka) (t := SM.Construction.fsEsTy KC Γ CCoins T I KR RSt K SS RS M E))).2
      dsimp only [mo] at hpvE
      refine compCostW_le_of_parts
        (a := 2 * (ReductionDsl.bits (tL.getD 0) + 3) + 2 * ReductionDsl.bits t + 50 * L + 260)
        (b := 250) ?_ ?_ (privOut_hm ht_bits htL_bits le_rfl le_rfl)
      · refine comp_ite_cost_le hpvC (K2 := 3)
          (by simp only [Comp.cost, Expr.cost, v1_cost]; decide) ?_
        simp only [v0_cost]; dsimp only [mo, SM.Construction.Mode.policy]; omega
      · have h0 := hpvE
        simp only [exprExcessUB_v0] at h0
        simp only [compExcessUB_ite, compExcessUB_ret, compExcessUB_sample,
          exprExcessUB_v1, exprExcessUB_unit, ckaSampC]
        omega
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redFSPrivProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

lemma redFSPrivCoinProg_parts_le (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2) (htL : tL ∈ admissibleLastLeakGuesses (2 + 1) t) :
    let L := q + 1
    let B := (q + 1) * (maxForwardJumps + 1)
    let P := SM.Construction.redFSPrivCoinProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
      (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B) ckaSampC fsQueryC P.init +
        compCostW (ckaOpC B) ckaSampC fsQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B) ckaSampC fsQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  intro L B P
  obtain ⟨htL1, htL2⟩ := targetsL_bounds htL
  let mo : SM.Construction.Mode := ⟨false, tL, t⟩
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch tL) (qep := qep) (by omega)
  have hj0 : 0 + 1 ≤ L := by omega
  have hhkC := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo 0).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (hooksFS_mono_arith hj0 ht_bits htH_bits)
  have hhkE := hooksFSC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B L B mo 0
  refine ⟨?_, ?_⟩
  · have hi : compCostW (ckaOpC B) ckaSampC fsQueryC P.init ≤
        4 * ReductionDsl.bits qep + 500 * (q + 1) + 8000 := by
      dsimp only [P, SM.Construction.redFSPrivCoinProg]
      have hiC0 := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo 0 (Γ' := [.unit]) (.bool false)
      have hiE0 := initFSEStateC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B L mo 0 (Γ' := [.unit]) (.bool false)
      refine compCostW_le_of_parts
        (a := 200 * L + 12 * (0 + 1) + 2 * ReductionDsl.bits t + 2 * ReductionDsl.bits (healEpoch tL) + 2030)
        (b := 200 * L + 5100) ?_ ?_ (initFS_hm hj0 ht_bits htH_bits le_rfl le_rfl)
      · exact bind_ret_pair_unit_cost_le hiC0 (by
          simp only [Expr.cost]; dsimp only [mo, SM.Construction.Mode.tH]; omega)
      · exact bind_ret_pair_unit_excess_le _ _ _ hiE0 (by
          simp only [exprExcessUB_bool]; omega)
    have hf : compCostW (ckaOpC B) ckaSampC fsQueryC P.finish ≤
        0 * ReductionDsl.bits qep + 0 * (q + 1) + 300 := by
      dsimp only [P, SM.Construction.redFSPrivCoinProg]
      exact compCostW_le_of_parts (a := 10) (b := 210)
        (by simp only [Comp.cost, Expr.cost]; decide)
        (by simp only [compExcessUB_sample, exprExcessUB_unit, ckaSampC]; decide)
        (by simp)
    exact init_finish_le_step hi hf (by decide) (by decide) (by decide)
  · dsimp only [P, L, B, SM.Construction.redFSPrivCoinProg]
    exact implEC_compCostW_le_fig8AtomicStepBound _ q qep mo ht htL1 hhkC hhkE

end EngineWeightedBounds

end ProgramWeightedBounds

end Computational.Proofs.ReductionDsl.Fig8WeightedParts
