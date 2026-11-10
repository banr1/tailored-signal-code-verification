/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.GameHop.Swap
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.CryptoFoundations.SecExp.Measure
import VCVio.EvalDist.Monad.Basic

@[expose] public section

open scoped ENNReal
open MeasureTheory
open OracleComp OracleSpec
open SignalPqxdh Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

theorem simulateQ_run_query_inl_local {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (uq : unifSpec.Domain)
    (oa : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
    (liftM (unifSpec.query uq) >>= fun u =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa u)).run st) := by
  simp [simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]

theorem simulateQ_run_query_inr_local {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (gq : ι)
    (oa : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
    ((impl gq).run st >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa y.1)).run y.2) := by
  simp [simulateQ_bind, StateT.run_bind]

namespace AuthSubHops1to3

export Computational.Proofs.GameHop.Swap (SlotM)

namespace SlotM

export Computational.Proofs.GameHop.Swap.SlotM
  (fill1 fill1_some fill1_none bind_fill1_of_keep getSlot getSlot_run_some getSlot_run_none
   SlotComp)

namespace SlotComp
export Computational.Proofs.GameHop.Swap.SlotM.SlotComp
  (of_eq pure liftComp getSlot bind eager_eq_lazy_run' map)
end SlotComp

variable {κ : Type}

theorem SlotComp.run_some_eq_map_run' {samp : ProbComp κ} {α : Type}
    {mx : SlotM κ α} (h : SlotComp samp mx) (k : κ) :
    mx.run (some k) = (fun a => (a, some k)) <$> mx.run' (some k) := by
  simp only [StateT.run'_eq, Functor.map_map]
  conv_lhs => rw [← bind_pure (mx.run (some k))]
  rw [map_eq_bind_pure_comp]
  refine _root_.Proofs.SignalPqxdh.Security.bind_congr_of_support
    (mx.run (some k)) _ _ fun y hy => ?_
  rcases y with ⟨a, o⟩
  have ho : o = some k := h.keep k (a, o) hy
  subst ho
  rfl

@[simp] theorem run'_liftComp {α : Type} (c : ProbComp α) (o : Option κ) :
    (liftM c : SlotM κ α).run' o = c := by
  simp [StateT.run'_eq, StateT.run_monadLift, monadLift_self]

@[simp] theorem run'_pure {α : Type} (x : α) (o : Option κ) :
    (pure x : SlotM κ α).run' o = pure x := by
  simp [StateT.run'_eq]

theorem run'_bind_of_slotComp_some {samp : ProbComp κ} {α β : Type}
    {mx : SlotM κ α} {mf : α → SlotM κ β}
    (hx : SlotComp samp mx) (k : κ) :
    (mx >>= mf).run' (some k) = (mx.run' (some k) >>= fun a => (mf a).run' (some k)) := by
  rw [StateT.run'_eq, StateT.run_bind, SlotComp.run_some_eq_map_run' hx k]
  simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]

theorem run'_liftComp_bind {α β : Type} (c : ProbComp α) (mf : α → SlotM κ β) (o : Option κ) :
    ((liftM c : SlotM κ α) >>= mf).run' o = (c >>= fun a => (mf a).run' o) := by
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    map_eq_bind_pure_comp, bind_assoc]

theorem run'_getSlot_bind_some (samp : ProbComp κ) {β : Type} (mf : κ → SlotM κ β) (k : κ) :
    (getSlot samp >>= mf).run' (some k) = (mf k).run' (some k) := by
  simp [StateT.run'_eq, StateT.run_bind]

theorem run'_getSlot_bind_none (samp : ProbComp κ) {β : Type} (mf : κ → SlotM κ β) :
    (getSlot samp >>= mf).run' none = (samp >>= fun k => (mf k).run' (some k)) := by
  simp [StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

/-- Simulation bridge equating pre-sampled `simulateQ (fullPre k)` with lazy `simulateQ fullLazy`
    via a `SlotM` step. -/
theorem evalDist_preSample_eq_lazy_of_slotStep
    {ι α : Type} {QSpec : OracleSpec.{0, 0} ι} {St : Type}
    (samp : ProbComp κ) (hasFired : St → Bool)
    (implLazy : QueryImpl QSpec (StateT St ProbComp))
    (implPre : κ → QueryImpl QSpec (StateT St ProbComp))
    (stepSlot : (q : ι) → St → SlotM κ (QSpec.Range q × St))
    (hSlotComp : ∀ q st, SlotComp samp (stepSlot q st))
    (hSome : ∀ k q st, (stepSlot q st).run' (some k) = (implPre k q).run st)
    (hNone : ∀ q st (g : QSpec.Range q × St → ProbComp Bool),
      𝒟[(stepSlot q st).run' none >>= g] = 𝒟[(implLazy q).run st >>= g])
    (hAfter : ∀ k q st, hasFired st = true →
      (implPre k q).run st = (implLazy q).run st ∧
      ∀ x ∈ support ((implLazy q).run st), hasFired x.2 = true)
    (hFire : ∀ q st y, y ∈ support ((stepSlot q st).run none) →
      y.2.isSome = true → hasFired y.1.2 = true)
    (oa : OracleComp (unifSpec + QSpec) α) (st0 : St)
    (obs : α × St → ProbComp Bool) :
    let fullPre := fun k =>
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implPre k
    let fullLazy :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implLazy
    𝒟[samp >>= fun k => (simulateQ (fullPre k) oa).run st0 >>= obs] =
      𝒟[(simulateQ fullLazy oa).run st0 >>= obs] := by
  intro fullPre fullLazy
  let implSlot : QueryImpl QSpec (StateT St (SlotM κ)) := fun q => StateT.mk (stepSlot q)
  let fullSlot : QueryImpl (unifSpec + QSpec) (StateT St (SlotM κ)) :=
    (QueryImpl.ofLift unifSpec (SlotM κ)).liftTarget (StateT St (SlotM κ)) + implSlot
  have hInl : ∀ (uq : unifSpec.Domain)
      (mx : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) α) (st : St),
      (simulateQ fullSlot (liftM (OracleSpec.query (Sum.inl uq)) >>= mx)).run st =
        ((liftM (liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) : SlotM κ _) >>=
          fun u =>
          (simulateQ fullSlot (mx u)).run st) := by
    intro uq mx st; rfl
  have hInr : ∀ (gq : QSpec.Domain)
      (mx : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St),
      (simulateQ fullSlot (liftM (OracleSpec.query (Sum.inr gq)) >>= mx)).run st =
        (stepSlot gq st >>= fun x => (simulateQ fullSlot (mx x.1)).run x.2) := by
    intro gq mx st; rfl
  have hSimSlotComp : ∀ (oa' : OracleComp (unifSpec + QSpec) α) (st : St),
      SlotComp samp ((simulateQ fullSlot oa').run st) := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro st
      simp only [simulateQ_pure, StateT.run_pure]
      exact SlotComp.pure samp (a, st)
    | query_bind q mx ih =>
      intro st
      rcases q with uq | gq
      · exact SlotComp.of_eq (hInl uq mx st) ((SlotComp.liftComp samp _).bind fun u => ih u st)
      · exact SlotComp.of_eq (hInr gq mx st) ((hSlotComp gq st).bind fun x => ih x.1 x.2)
  have hSimSome : ∀ (k : κ) (oa' : OracleComp (unifSpec + QSpec) α) (st : St),
      ((simulateQ fullSlot oa').run st).run' (some k) = (simulateQ (fullPre k) oa').run st := by
    intro k oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro st
      simp [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      intro st
      rcases q with uq | gq
      · rw [hInl uq mx st, run'_liftComp_bind, simulateQ_run_query_inl_local]
        congr 1; ext u; exact ih u st
      · rw [hInr gq mx st, run'_bind_of_slotComp_some (hSlotComp gq st) k, hSome k gq st,
          simulateQ_run_query_inr_local]
        congr 1; ext ⟨r, st'⟩; exact ih r st'
  have hSimNone : ∀ (oa' : OracleComp (unifSpec + QSpec) α) (st : St) (o : Option κ),
      (o.isSome = true → hasFired st = true) →
      𝒟[((simulateQ fullSlot oa').run st).run' o >>= obs] =
        𝒟[(simulateQ fullLazy oa').run st >>= obs] := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro st o _
      simp [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      intro st o hInv
      rcases q with uq | gq
      · rw [hInl uq mx st, run'_liftComp_bind, simulateQ_run_query_inl_local, bind_assoc,
            bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
        exact ih u st o hInv
      · rw [hInr gq mx st, simulateQ_run_query_inr_local, bind_assoc]
        rcases o with _ | k
        · rw [← hNone gq st (fun x => (simulateQ fullLazy (mx x.1)).run x.2 >>= obs)]
          simp only [StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_apply, pure_bind]
          refine OracleComp.evalDist_bind_congr_of_support ((stepSlot gq st).run none) _ _
            fun ⟨⟨r, st'⟩, o'⟩ hy => ?_
          have hInv' : o'.isSome = true → hasFired st' = true := hFire gq st _ hy
          have hih := ih r st' o' hInv'
          simpa only [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
            pure_bind] using hih
        · have hFired : hasFired st = true := hInv rfl
          rw [run'_bind_of_slotComp_some (hSlotComp gq st) k, hSome k gq st,
            (hAfter k gq st hFired).1, bind_assoc]
          refine OracleComp.evalDist_bind_congr_of_support ((implLazy gq).run st) _ _
            fun ⟨r, st'⟩ hx => ?_
          have hFired' : hasFired st' = true := (hAfter k gq st hFired).2 (r, st') hx
          exact ih r st' (some k) (fun _ => hFired')
  have hEagerLazy := SlotComp.eager_eq_lazy_run' (hSimSlotComp oa st0) obs
  simp_rw [hSimSome _ oa st0] at hEagerLazy
  rw [hEagerLazy, hSimNone oa st0 none (fun h => by cases h)]

end SlotM

end AuthSubHops1to3

open AuthSubHops1to3

theorem abs_sub_toReal_eq_mul_sampleIndexRange_sub (N : ℕ)
    (H wTrue wFalse : ℕ → ProbComp Bool)
    (hT : ∀ k ∈ Finset.range N, (𝒟[wTrue k] {true}).toReal = (𝒟[H k] {true}).toReal)
    (hF : ∀ k ∈ Finset.range N, (𝒟[wFalse k] {true}).toReal = (𝒟[H (k + 1)] {true}).toReal) :
    |(𝒟[H 0] {true}).toReal - (𝒟[H N] {true}).toReal| =
      (N : ℝ) *
        |(𝒟[sampleIndexRange N >>= wTrue] {true}).toReal -
         (𝒟[sampleIndexRange N >>= wFalse] {true}).toReal| := by
  have hSumT :
      (N : ℝ) * (𝒟[sampleIndexRange N >>= wTrue] {true}).toReal =
        ∑ k ∈ Finset.range N, (𝒟[H k] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    exact Finset.sum_congr rfl hT
  have hSumF :
      (N : ℝ) * (𝒟[sampleIndexRange N >>= wFalse] {true}).toReal =
        ∑ k ∈ Finset.range N, (𝒟[H (k + 1)] {true}).toReal := by
    rw [mul_toReal_sampleIndexRange_bind_eq_sum]
    exact Finset.sum_congr rfl hF
  have hTel :
      ∑ k ∈ Finset.range N, (𝒟[H k] {true}).toReal -
        ∑ k ∈ Finset.range N, (𝒟[H (k + 1)] {true}).toReal =
      (𝒟[H 0] {true}).toReal - (𝒟[H N] {true}).toReal := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub' (fun k => (𝒟[H k] {true}).toReal) N
  have hDiff :
      (𝒟[H 0] {true}).toReal - (𝒟[H N] {true}).toReal =
        (N : ℝ) *
          ((𝒟[sampleIndexRange N >>= wTrue] {true}).toReal -
           (𝒟[sampleIndexRange N >>= wFalse] {true}).toReal) := by
    linarith
  rw [hDiff, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]

/-- Signed-telescoping `boolBias` hybrid bound under uniform index guessing over `N` steps. -/
theorem abs_sub_boolBias_le_two_mul_sampleIndexRange_coin_game (N : ℕ)
    (H wTrue wFalse : ℕ → ProbComp Bool)
    (hT : ∀ k ∈ Finset.range N, (𝒟[wTrue k] {true}).toReal = (𝒟[H k] {true}).toReal)
    (hF : ∀ k ∈ Finset.range N, (𝒟[wFalse k] {true}).toReal = (𝒟[H (k + 1)] {true}).toReal) :
    |(𝒟[H 0].boolBias).toReal - (𝒟[H N].boolBias).toReal| ≤
      2 * (N : ℝ) *
        (𝒟[do
          let b ← $ᵗ Bool
          let z ← if b then (sampleIndexRange N >>= wTrue)
                  else (sampleIndexRange N >>= wFalse)
          return (b == z)].boolBias).toReal := by
  have hBias := abs_sub_boolBias_toReal_le_two_mul_abs_sub (H 0) (H N)
  have hTel := abs_sub_toReal_eq_mul_sampleIndexRange_sub N H wTrue wFalse hT hF
  have hCoin :
      (𝒟[do
        let b ← $ᵗ Bool
        let z ← if b then (sampleIndexRange N >>= wTrue)
                else (sampleIndexRange N >>= wFalse)
        return (b == z)].boolBias).toReal =
      |(𝒟[sampleIndexRange N >>= wTrue] {true}).toReal -
       (𝒟[sampleIndexRange N >>= wFalse] {true}).toReal| := by
    rw [evalDist_boolBias_bind_uniformBool, MeasureTheory.Measure.toReal_boolDist]
  rw [hCoin, mul_assoc, ← hTel]
  exact hBias

/-! ## `PrfChainKey` (`G3.6 → G3.7`) cutoff hybrid -/

def sampCkPair (P : Primitives) (ideal : Bool) : ProbComp (Bytes × Bytes) := do
  let ck ← sampleBytes32
  if ideal then do
    let r1 ← sampleBytes32
    let r2 ← sampleBytes32
    pure (r1, r2)
  else
    pure (P.chainKdfSeed ck, P.chainKdfNext ck)

theorem prfCkExp_eq_sampCkPair
    (P : Primitives) (A : PrfCkAdv) :
    prfCkExp P A = (do
      let b ← $ᵗ Bool
      let p ← sampCkPair P (!b)
      let b' ← simulateQ (primBaseImpl P) (A.dist p.1 p.2)
      return (b' == b)) := by
  simp only [prfCkExp, sampCkPair, bind_assoc]
  congr 1; funext b
  cases b <;> rfl

def sendSlotIndex? {S : Setup} : SessionId S → Option Nat
  | .sendOPK u i     => some (sessionSlotIndex (S := S) (.sendOPK u i))
  | .sendNoOPK u i   => some (sessionSlotIndex (S := S) (.sendNoOPK u i))
  | .recvOPK _ _ _   => none
  | .recvNoOPK _ _ _ => none

theorem sendSlotIndex?_lt {S : Setup} {sid : SessionId S} {idx : Nat}
    (h : sendSlotIndex? sid = some idx) : idx < S.N_send_tot := by
  cases sid with
  | sendOPK u i =>
    simp only [sendSlotIndex?, Option.some.injEq] at h
    exact h ▸ sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
  | sendNoOPK u i =>
    simp only [sendSlotIndex?, Option.some.injEq] at h
    exact h ▸ sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
  | recvOPK _ _ _ => cases h
  | recvNoOPK _ _ _ => cases h

theorem sendSlotIndex?_inj {S : Setup} {sid1 sid2 : SessionId S} {idx : Nat}
    (h1 : sendSlotIndex? sid1 = some idx)
    (h2 : sendSlotIndex? sid2 = some idx) : sid1 = sid2 := by
  cases sid1 with
  | sendOPK u1 i1 =>
    cases sid2 with
    | sendOPK u2 i2 =>
      simp only [sendSlotIndex?, Option.some.injEq, sessionSlotIndex] at h1 h2
      have h : u1.val * S.N_send_opk + i1.val = u2.val * S.N_send_opk + i2.val := h1.trans h2.symm
      have hi1 : i1.val < S.N_send_opk := i1.isLt
      have hi2 : i2.val < S.N_send_opk := i2.isLt
      have hu : u1.val = u2.val := by
        have hd1 : (u1.val * S.N_send_opk + i1.val) / S.N_send_opk = u1.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi1), Nat.div_eq_of_lt hi1,
              Nat.add_zero]
        have hd2 : (u2.val * S.N_send_opk + i2.val) / S.N_send_opk = u2.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi2), Nat.div_eq_of_lt hi2,
              Nat.add_zero]
        rw [← hd1, ← hd2, h]
      have hi : i1.val = i2.val := by rw [hu] at h; omega
      rw [Fin.ext hu, Fin.ext hi]
    | sendNoOPK u2 i2 =>
      simp only [sendSlotIndex?, Option.some.injEq, sessionSlotIndex, Setup.N_send_opk_tot] at h1 h2
      have h : u1.val * S.N_send_opk + i1.val =
          S.N_id * S.N_send_opk + (u2.val * S.N_send_no_opk + i2.val) :=
        h1.trans h2.symm
      have hu1 : u1.val + 1 ≤ S.N_id := u1.isLt
      have hi1 : i1.val < S.N_send_opk := i1.isLt
      have hlt : u1.val * S.N_send_opk + i1.val < S.N_id * S.N_send_opk := by
        calc u1.val * S.N_send_opk + i1.val
            < u1.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left hi1 _
          _ = (u1.val + 1) * S.N_send_opk := by ring
          _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu1
      omega
    | recvOPK _ _ _ => cases h2
    | recvNoOPK _ _ _ => cases h2
  | sendNoOPK u1 i1 =>
    cases sid2 with
    | sendOPK u2 i2 =>
      simp only [sendSlotIndex?, Option.some.injEq, sessionSlotIndex, Setup.N_send_opk_tot] at h1 h2
      have h : S.N_id * S.N_send_opk + (u1.val * S.N_send_no_opk + i1.val) =
          u2.val * S.N_send_opk + i2.val :=
        h1.trans h2.symm
      have hu2 : u2.val + 1 ≤ S.N_id := u2.isLt
      have hi2 : i2.val < S.N_send_opk := i2.isLt
      have hlt : u2.val * S.N_send_opk + i2.val < S.N_id * S.N_send_opk := by
        calc u2.val * S.N_send_opk + i2.val
            < u2.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left hi2 _
          _ = (u2.val + 1) * S.N_send_opk := by ring
          _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu2
      omega
    | sendNoOPK u2 i2 =>
      simp only [sendSlotIndex?, Option.some.injEq, sessionSlotIndex] at h1 h2
      have h' : u1.val * S.N_send_no_opk + i1.val = u2.val * S.N_send_no_opk + i2.val := by omega
      have hi1 : i1.val < S.N_send_no_opk := i1.isLt
      have hi2 : i2.val < S.N_send_no_opk := i2.isLt
      have hu : u1.val = u2.val := by
        have hd1 : (u1.val * S.N_send_no_opk + i1.val) / S.N_send_no_opk = u1.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi1), Nat.div_eq_of_lt hi1,
              Nat.add_zero]
        have hd2 : (u2.val * S.N_send_no_opk + i2.val) / S.N_send_no_opk = u2.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi2), Nat.div_eq_of_lt hi2,
              Nat.add_zero]
        rw [← hd1, ← hd2, h']
      have hi : i1.val = i2.val := by rw [hu] at h'; omega
      rw [Fin.ext hu, Fin.ext hi]
    | recvOPK _ _ _ => cases h2
    | recvNoOPK _ _ _ => cases h2
  | recvOPK _ _ _ => cases h1
  | recvNoOPK _ _ _ => cases h1

/-- Whether slot `idx` (`< S.N_send_tot` initiator, `≥ S.N_send_tot` receiver) has fired in `hst`. -/
def authSlotFired (S : Setup) (idx : Nat) (hst : AuthHybridStateFixed S) : Bool :=
  if idx < S.N_send_tot then
    hst.toAuthHybridState.base.usedSendSessions.any (fun sid => sendSlotIndex? sid == some idx)
  else
    decide (idx < S.N_send_tot + hst.recvCount)

theorem contains_sid_of_authSlotFired {S : Setup} {idx : Nat} {sid : SessionId S}
    {hst : AuthHybridStateFixed S}
    (hFired : authSlotFired S idx hst = true)
    (hSlot : sendSlotIndex? sid = some idx) :
    hst.toAuthHybridState.base.usedSendSessions.contains sid = true := by
  have hlt : idx < S.N_send_tot := sendSlotIndex?_lt hSlot
  unfold authSlotFired at hFired
  simp only [hlt, ↓reduceIte, List.any_eq_true] at hFired
  rcases hFired with ⟨sid', hmem, hidx⟩
  rw [beq_iff_eq] at hidx
  have heq : sid' = sid := sendSlotIndex?_inj hidx hSlot
  subst heq
  exact List.contains_iff_mem.mpr hmem

theorem recvSlot_ne_of_authSlotFired {S : Setup} {idx : Nat}
    {hst : AuthHybridStateFixed S}
    (hFired : authSlotFired S idx hst = true) :
    S.N_send_tot + hst.recvCount ≠ idx := by
  intro heq
  have hge : ¬ (idx < S.N_send_tot) := by omega
  unfold authSlotFired at hFired
  simp only [hge, ↓reduceIte, decide_eq_true_eq] at hFired
  omega

def getCkAtSlot (idx : Nat) (samp : ProbComp (Bytes × Bytes)) (P : Primitives) (slotIdx : Nat) :
    SlotM (Bytes × Bytes) (Bytes × Bytes) :=
  if slotIdx == idx then
    SlotM.getSlot samp
  else
    liftM (sampCkPair P (slotIdx < idx))

theorem slotComp_getCkAtSlot (idx : Nat) (samp : ProbComp (Bytes × Bytes)) (P : Primitives)
    (slotIdx : Nat) :
    SlotM.SlotComp samp (getCkAtSlot idx samp P slotIdx) := by
  unfold getCkAtSlot
  split
  · exact SlotM.SlotComp.getSlot samp
  · exact SlotM.SlotComp.liftComp samp _

theorem run'_getCkAtSlot_bind_pure_some {α : Type}
    (idx : Nat) (samp : ProbComp (Bytes × Bytes)) (P : Primitives)
    (k : Bytes × Bytes) (slotIdx : Nat) (f : Bytes × Bytes → α) :
    (getCkAtSlot idx samp P slotIdx >>= fun x => pure (f x)).run' (some k) =
      ((if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx)) >>=
        fun x => pure (f x)) := by
  unfold getCkAtSlot
  split
  · rw [SlotM.run'_getSlot_bind_some, SlotM.run'_pure, pure_bind]
  · rw [SlotM.run'_liftComp_bind]
    simp only [SlotM.run'_pure]

theorem run'_getCkAtSlot_bind_pure_none {α : Type}
    (idx : Nat) (b : Bool) (P : Primitives)
    (slotIdx : Nat) (f : Bytes × Bytes → α) :
    (getCkAtSlot idx (sampCkPair P (!b)) P slotIdx >>= fun x => pure (f x)).run' none =
      (sampCkPair P (slotIdx < (if b then idx else idx + 1)) >>= fun x => pure (f x)) := by
  unfold getCkAtSlot
  by_cases h : slotIdx = idx
  · subst h
    simp only [beq_self_eq_true, ↓reduceIte, SlotM.run'_getSlot_bind_none, SlotM.run'_pure]
    cases b <;> simp
  · have hbeq : (slotIdx == idx) = false := beq_eq_false_iff_ne.mpr h
    have hlt : (slotIdx < idx) = (slotIdx < (if b then idx else idx + 1)) := by
      cases b
      · simp; omega
      · simp
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, SlotM.run'_liftComp_bind, SlotM.run'_pure, hlt]

def finishAuthSendCk {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes) :
    AuthResponse × AuthHybridStateFixed S :=
  let st := hst.toAuthHybridState.base
  let mkSeed := p.1
  let ck1_1 := p.2
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain st.roCache st.rootRoCache
    hst.toAuthHybridState
  (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def finishAuthRecvCk {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) :
    AuthResponse × AuthHybridStateFixed S :=
  let st := prep.hstDec.base
  let mkSeed := p.1
  let ck1_1 := p.2
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
    (drKey, rk1, ck1_1, pt, st.roCache, st.rootRoCache))
  let (resp, hst') := prep.finish res?
  (resp, { toAuthHybridState := hst', recvCount := recvCount' })

theorem authSlotFired_finishAuthSendCk_mono {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hFired : authSlotFired S idx hst = true) :
    authSlotFired S idx
      (finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
        hst p).2 = true := by
  unfold authSlotFired at hFired ⊢
  unfold finishAuthSendCk finishAuthHybridSend
  dsimp only
  split
  · rename_i hlt
    simp only [hlt, ↓reduceIte, List.any_cons, Bool.or_eq_true] at hFired ⊢
    exact Or.inr hFired
  · rename_i hge
    simp only [hge, ↓reduceIte] at hFired ⊢
    exact hFired

theorem authSlotFired_finishAuthSendCk_self {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hSlot : sendSlotIndex? sid = some idx) :
    authSlotFired S idx
      (finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
        hst p).2 = true := by
  have hlt : idx < S.N_send_tot := sendSlotIndex?_lt hSlot
  unfold authSlotFired finishAuthSendCk finishAuthHybridSend
  simp [hlt, hSlot]

theorem authSlotFired_finishAuthRecvCk_self {S : Setup} (P : Primitives) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hSlot : S.N_send_tot + hst.recvCount = idx) :
    authSlotFired S idx
      (finishAuthRecvCk P msg prep drKey rk1 spqrSalt? (hst.recvCount + 1) p).2 = true := by
  have hge : ¬ (idx < S.N_send_tot) := by omega
  unfold authSlotFired finishAuthRecvCk
  simp only [hge, ↓reduceIte, decide_eq_true_eq]
  omega

def authCkSendWith (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← sampleScalar32
          let kemCoins ← sampleCoins32
          let ephASk ← sampleScalar32
          let spqrCoins ← sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← sampleDRKey96
                let rk1 ← sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let p ← sampAt (sessionSlotIndex sid)
                  pure (finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain hst p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def authCkSendSlot (S : Setup) (P : Primitives) (idx : Nat) (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (i, _) => i == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← liftM sampleScalar32
          let kemCoins ← liftM sampleCoins32
          let ephASk ← liftM sampleScalar32
          let spqrCoins ← liftM sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← liftM sampleDRKey96
                let rk1 ← liftM sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let p ← getCkAtSlot idx samp P (sessionSlotIndex sid)
                  pure (finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain hst p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount })

def authCkRecvWith (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
          | some (_pqrStB, spqrSalt?) =>
            pure (finishAuthRecvCk P msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1))
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
          | some (_pqrStB, spqrSalt?) =>
            let p ← sampAt (S.N_send_tot + hst.recvCount)
            pure (finishAuthRecvCk P msg prep s.drKey rk1 spqrSalt? recvCount' p)
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
        | some (_pqrStB, spqrSalt?) =>
          let p ← sampAt (S.N_send_tot + hst.recvCount)
          pure (finishAuthRecvCk P msg prep drKey rk1 spqrSalt? recvCount' p)
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ←
        evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })

def authCkRecvSlot (S : Setup) (P : Primitives) (idx : Nat) (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
          | some (_pqrStB, spqrSalt?) =>
            pure (finishAuthRecvCk P msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1))
        else
          let rk1 ← liftM sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
          | some (_pqrStB, spqrSalt?) =>
            let p ← getCkAtSlot idx samp P (S.N_send_tot + hst.recvCount)
            pure (finishAuthRecvCk P msg prep s.drKey rk1 spqrSalt? recvCount' p)
      | none =>
        let drKey ← liftM sampleDRKey96
        let rk1 ← liftM sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
        | some (_pqrStB, spqrSalt?) =>
          let p ← getCkAtSlot idx samp P (S.N_send_tot + hst.recvCount)
          pure (finishAuthRecvCk P msg prep drKey rk1 spqrSalt? recvCount' p)
    else
      let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ←
        liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet)
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount' })

def authCkOtherStep (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  if hst.toAuthHybridState.base.hasWonAuth then
    pure (.noneResp, hst)
  else
    let (resp, base') ← (pqxdhAuthImpl true true S P q).run hst.toAuthHybridState.base
    pure (resp, { hst with toAuthHybridState := { hst.toAuthHybridState with base := base' } })

def authCkStepWith (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendWith S P sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendWith S P sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvWith S P sampAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvWith S P sampAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep S P qOther hst

def authCkStepSlot (S : Setup) (P : Primitives) (idx : Nat) (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSendSlot S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSendSlot S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvSlot S P idx samp msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvSlot S P idx samp msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep S P qOther hst)

/-! ## `SlotM` step equivalences -/

theorem AuthSubHops1to3.SlotM.SlotComp.liftComp_bind {κ α β : Type} (samp : ProbComp κ)
    (c : ProbComp α) {f : α → SlotM κ β}
    (hf : ∀ a, SlotM.SlotComp samp (f a)) :
    SlotM.SlotComp samp ((liftM c : SlotM κ α) >>= f) :=
  (SlotM.SlotComp.liftComp samp c).bind hf

theorem AuthSubHops1to3.SlotM.SlotComp.getCkAtSlot_bind {β : Type} (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (P : Primitives) (slotIdx : Nat)
    {f : Bytes × Bytes → SlotM (Bytes × Bytes) β}
    (hf : ∀ p, SlotM.SlotComp samp (f p)) :
    SlotM.SlotComp samp (getCkAtSlot idx samp P slotIdx >>= f) :=
  (slotComp_getCkAtSlot idx samp P slotIdx).bind hf

theorem authCkSendSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkSendSlot S P idx samp sid u bundle m0 m1 hst) := by
  unfold authCkSendSlot; dsimp only
  repeat (first
    | apply SlotM.SlotComp.pure
    | apply SlotM.SlotComp.liftComp
    | (apply SlotM.SlotComp.liftComp_bind; intro _)
    | (apply SlotM.SlotComp.getCkAtSlot_bind; intro _)
    | split)

theorem authCkRecvSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkRecvSlot S P idx samp msg prep? hst) := by
  unfold authCkRecvSlot; dsimp only
  repeat (first
    | apply SlotM.SlotComp.pure
    | apply SlotM.SlotComp.liftComp
    | (apply SlotM.SlotComp.liftComp_bind; intro _)
    | (apply SlotM.SlotComp.getCkAtSlot_bind; intro _)
    | split)

theorem authCkStepSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkStepSlot S P idx samp q hst) := by
  cases q <;> unfold authCkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure samp _
    · exact authCkSendSlot_slotComp S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure samp _
    · exact authCkSendSlot_slotComp S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authCkRecvSlot_slotComp S P idx samp msg _ hst
  case recvNoOPK k j l msg =>
    exact authCkRecvSlot_slotComp S P idx samp msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp samp _

theorem authCkSendSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authCkSendSlot S P idx samp sid u bundle m0 m1 hst).run' (some k) =
      authCkSendWith S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx))
        sid u bundle m0 m1 hst := by
  unfold authCkSendSlot authCkSendWith; dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getCkAtSlot_bind_pure_some]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authCkRecvSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authCkRecvSlot S P idx samp msg prep? hst).run' (some k) =
      authCkRecvWith S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx))
        msg prep? hst := by
  unfold authCkRecvSlot authCkRecvWith; dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getCkAtSlot_bind_pure_some]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authCkStepSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkStepSlot S P idx samp q hst).run' (some k) =
      authCkStepWith S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx))
        q hst := by
  cases q <;> unfold authCkStepSlot authCkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_some S P idx samp k (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_some S P idx samp k (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k' j o msg =>
    exact authCkRecvSlot_run'_some S P idx samp k msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkRecvSlot_run'_some S P idx samp k msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

theorem authCkSendSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authCkSendSlot S P idx (sampCkPair P (!b)) sid u bundle m0 m1 hst).run' none =
      authCkSendWith S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        sid u bundle m0 m1 hst := by
  unfold authCkSendSlot authCkSendWith; dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getCkAtSlot_bind_pure_none]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authCkRecvSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authCkRecvSlot S P idx (sampCkPair P (!b)) msg prep? hst).run' none =
      authCkRecvWith S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        msg prep? hst := by
  unfold authCkRecvSlot authCkRecvWith; dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [run'_getCkAtSlot_bind_pure_none]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)

theorem authCkStepSlot_run'_none_eq (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkStepSlot S P idx (sampCkPair P (!b)) q hst).run' none =
      authCkStepWith S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        q hst := by
  cases q <;> unfold authCkStepSlot authCkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_none S P idx b (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authCkSendSlot_run'_none S P idx b (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k' j o msg =>
    exact authCkRecvSlot_run'_none S P idx b msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkRecvSlot_run'_none S P idx b msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]

def SlotFireAtAuth (S : Setup) {κ : Type} (idx : Nat)
    (mx : SlotM κ (AuthResponse × AuthHybridStateFixed S)) : Prop :=
  ∀ y ∈ support (mx.run none), y.2.isSome = true → authSlotFired S idx y.1.2 = true

theorem SlotFireAtAuth.pure {S : Setup} {κ : Type} (idx : Nat)
    (x : AuthResponse × AuthHybridStateFixed S) :
    SlotFireAtAuth S (κ := κ) idx (pure x) := by
  intro y hy hSome
  simp [StateT.run_pure] at hy
  subst hy
  cases hSome

theorem SlotFireAtAuth.liftComp {S : Setup} {κ : Type} (idx : Nat)
    (c : ProbComp (AuthResponse × AuthHybridStateFixed S)) :
    SlotFireAtAuth S (κ := κ) idx (liftM c) := by
  intro y hy hSome
  simp only [StateT.run_monadLift, monadLift_self, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hy
  rcases hy with ⟨_, _, rfl⟩
  cases hSome

theorem SlotFireAtAuth.liftComp_bind {S : Setup} {κ α : Type} (idx : Nat)
    (c : ProbComp α) {f : α → SlotM κ (AuthResponse × AuthHybridStateFixed S)}
    (hf : ∀ a, SlotFireAtAuth S idx (f a)) :
    SlotFireAtAuth S idx ((liftM c : SlotM κ α) >>= f) := by
  intro y hy hSome
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩
  exact hf a y hy' hSome

theorem SlotFireAtAuth.getCkAtSlot_send {S : Setup} (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx
      (getCkAtSlot idx samp P (sessionSlotIndex sid) >>= fun p =>
        Pure.pure (finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p)) := by
  intro y hy hSome
  unfold getCkAtSlot at hy
  by_cases hEq : (sessionSlotIndex sid == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩
    rw [beq_iff_eq] at hEq
    exact authSlotFired_finishAuthSendCk_self P idx sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain
      hst p (hEq ▸ hSend)
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩
    cases hSome

theorem SlotFireAtAuth.getCkAtSlot_recv {S : Setup} (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx
      (getCkAtSlot idx samp P (S.N_send_tot + hst.recvCount) >>= fun p =>
        Pure.pure (finishAuthRecvCk P msg prep drKey rk1 spqrSalt? (hst.recvCount + 1) p)) := by
  intro y hy hSome
  unfold getCkAtSlot at hy
  by_cases hEq : (S.N_send_tot + hst.recvCount == idx) = true
  · simp only [hEq, ↓reduceIte, StateT.run_bind, SlotM.getSlot_run_none, bind_assoc, pure_bind,
      StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩
    rw [beq_iff_eq] at hEq
    exact authSlotFired_finishAuthRecvCk_self P idx msg prep drKey rk1 spqrSalt? hst p hEq
  · simp only [hEq, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind, StateT.run_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨p, _, rfl⟩
    cases hSome

theorem authCkSendSlot_fire (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx (authCkSendSlot S P idx samp sid u bundle m0 m1 hst) := by
  unfold authCkSendSlot; dsimp only
  repeat (first
    | with_reducible apply SlotFireAtAuth.pure
    | with_reducible apply SlotFireAtAuth.liftComp
    | (with_reducible apply SlotFireAtAuth.liftComp_bind; intro _)
    | (with_reducible apply SlotFireAtAuth.getCkAtSlot_send; exact hSend)
    | split)

theorem authCkRecvSlot_fire (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authCkRecvSlot S P idx samp msg prep? hst) := by
  unfold authCkRecvSlot; dsimp only
  repeat (first
    | with_reducible apply SlotFireAtAuth.pure
    | with_reducible apply SlotFireAtAuth.liftComp
    | (with_reducible apply SlotFireAtAuth.liftComp_bind; intro _)
    | with_reducible apply SlotFireAtAuth.getCkAtSlot_recv
    | split)

theorem authCkStepSlot_fire (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authCkStepSlot S P idx samp q hst) := by
  cases q <;> unfold authCkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authCkSendSlot_fire S P idx samp (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authCkSendSlot_fire S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authCkRecvSlot_fire S P idx samp msg _ hst
  case recvNoOPK k j l msg =>
    exact authCkRecvSlot_fire S P idx samp msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _

theorem authCkSendWith_congr_slot (S : Setup) (P : Primitives)
    (samp1 samp2 : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSlot : samp1 (sessionSlotIndex sid) = samp2 (sessionSlotIndex sid)) :
    authCkSendWith S P samp1 sid u bundle m0 m1 hst =
      authCkSendWith S P samp2 sid u bundle m0 m1 hst := by
  unfold authCkSendWith; dsimp only; rw [hSlot]

theorem authCkRecvWith_congr_slot (S : Setup) (P : Primitives)
    (samp1 samp2 : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hSlot : samp1 (S.N_send_tot + hst.recvCount) = samp2 (S.N_send_tot + hst.recvCount)) :
    authCkRecvWith S P samp1 msg prep? hst =
      authCkRecvWith S P samp2 msg prep? hst := by
  unfold authCkRecvWith; dsimp only; rw [hSlot]

def AuthSlotFiredAt (S : Setup) (idx : Nat)
    (mx : ProbComp (AuthResponse × AuthHybridStateFixed S)) : Prop :=
  ∀ y ∈ support mx, authSlotFired S idx y.2 = true

theorem AuthSlotFiredAt.pure {S : Setup} {idx : Nat} {x : AuthResponse × AuthHybridStateFixed S}
    (h : authSlotFired S idx x.2 = true) :
    AuthSlotFiredAt S idx (pure x) := by
  intro y hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  exact h

theorem AuthSlotFiredAt.bind {S : Setup} {α : Type} {idx : Nat}
    (mx : ProbComp α) {f : α → ProbComp (AuthResponse × AuthHybridStateFixed S)}
    (hf : ∀ a, AuthSlotFiredAt S idx (f a)) :
    AuthSlotFiredAt S idx (mx >>= f) := by
  intro y hy
  simp only [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨a, _, hy'⟩
  exact hf a y hy'

theorem authSlotFired_of_usedSendSessions_eq_and_recvCount_le {S : Setup} {idx : Nat}
    {hst hst' : AuthHybridStateFixed S}
    (hFired : authSlotFired S idx hst = true)
    (hUsed : hst'.toAuthHybridState.base.usedSendSessions =
      hst.toAuthHybridState.base.usedSendSessions)
    (hRecv : hst.recvCount ≤ hst'.recvCount) :
    authSlotFired S idx hst' = true := by
  unfold authSlotFired at hFired ⊢
  split
  · rename_i hlt
    simp only [hlt, ↓reduceIte] at hFired
    rw [hUsed]
    exact hFired
  · rename_i hge
    simp only [hge, ↓reduceIte, decide_eq_true_eq] at hFired ⊢
    omega

theorem authSlotFired_finishAuthHybridSend_mono {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authSlotFired S idx
      { toAuthHybridState :=
          (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
          spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
          hst.toAuthHybridState).2
        recvCount := hst.recvCount } = true := by
  unfold authSlotFired at hFired ⊢
  unfold finishAuthHybridSend
  dsimp only
  split
  · rename_i hlt
    simp only [hlt, ↓reduceIte, List.any_cons, Bool.or_eq_true] at hFired ⊢
    exact Or.inr hFired
  · rename_i hge
    simp only [hge, ↓reduceIte] at hFired ⊢
    exact hFired

theorem finishAuthHybridRecvOPK_usedSendSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples'
      msg hstDec res?).2.base.usedSendSessions =
      hstDec.base.usedSendSessions := by
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some res =>
    rcases res with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      split <;> rfl

theorem finishAuthHybridRecvNoOPK_usedSendSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples'
      msg hstDec res?).2.base.usedSendSessions =
      hstDec.base.usedSendSessions := by
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some res =>
    rcases res with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      split <;> rfl

theorem prepareAuthHybridRecvOPK_usedSendSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) {prep : PreparedAuthRecv S}
    (hPrep : prepareAuthHybridRecvOPK checkAuth P k j o msg hst = some prep) (res?) :
    (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions := by
  unfold prepareAuthHybridRecvOPK at hPrep
  dsimp only at hPrep
  repeat (split at hPrep <;> try cases hPrep)
  exact finishAuthHybridRecvOPK_usedSendSessions checkAuth P k j o _ _ _ _ msg _ res?

theorem prepareAuthHybridRecvNoOPK_usedSendSessions {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) {prep : PreparedAuthRecv S}
    (hPrep : prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst = some prep) (res?) :
    (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions := by
  unfold prepareAuthHybridRecvNoOPK at hPrep
  dsimp only at hPrep
  repeat (split at hPrep <;> try cases hPrep)
  exact finishAuthHybridRecvNoOPK_usedSendSessions checkAuth P k j l _ _ _ msg _ res?

theorem authCkSendWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkSendWith S P sampAt sid u bundle m0 m1 hst) := by
  unfold authCkSendWith; dsimp only
  repeat (first
    | (with_reducible apply AuthSlotFiredAt.pure;
       first
       | exact hFired
       | exact authSlotFired_finishAuthSendCk_mono P idx sid _ _ bundle m0 m1
           _ _ _ _ _ _ _ _ _ _ _ hst _ hFired
       | exact authSlotFired_finishAuthHybridSend_mono P idx sid _ _ _ bundle m0 m1
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst hFired)
    | (with_reducible apply AuthSlotFiredAt.bind; intro _)
    | split)

theorem authCkRecvWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hPrepUsed : ∀ prep, prep? = some prep → ∀ res?,
      (prep.finish res?).2.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkRecvWith S P sampAt msg prep? hst) := by
  cases hPrep : prep? with
  | none =>
    unfold authCkRecvWith; dsimp only
    exact AuthSlotFiredAt.pure
      (authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired rfl (Nat.le_succ _))
  | some prep =>
    have hUsed : ∀ res?, (prep.finish res?).2.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions := hPrepUsed prep hPrep
    have hFinish : ∀ res?,
        authSlotFired S idx
          { toAuthHybridState := (prep.finish res?).2, recvCount := hst.recvCount + 1 } = true :=
      fun res? =>
        authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired (hUsed res?) (Nat.le_succ _)
    unfold authCkRecvWith finishAuthRecvCk; dsimp only
    repeat (first
      | (with_reducible apply AuthSlotFiredAt.pure; exact hFinish _)
      | (with_reducible apply AuthSlotFiredAt.bind; intro _)
      | split)

theorem authCkOtherStep_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNotSend1 : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hNotSend2 : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (hNotRecv1 : ∀ k j o msg, q ≠ .recvOPK k j o msg)
    (hNotRecv2 : ∀ k j l msg, q ≠ .recvNoOPK k j l msg)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkOtherStep S P q hst) := by
  have hPres : PreservesAt AuthState.usedSendSessions hst.toAuthHybridState.base
      (pqxdhAuthImpl true true S P q) := by
    cases q with
    | sendOPK u i b m0 m1 => exact False.elim (hNotSend1 u i b m0 m1 rfl)
    | sendNoOPK u i b m0 m1 => exact False.elim (hNotSend2 u i b m0 m1 rfl)
    | recvOPK k j o msg => exact False.elim (hNotRecv1 k j o msg rfl)
    | recvNoOPK k j l msg => exact False.elim (hNotRecv2 k j l msg rfl)
    | _ =>
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
  unfold authCkOtherStep
  split
  · exact AuthSlotFiredAt.pure hFired
  · intro y hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨resp, base'⟩, hbase, rfl⟩
    exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired
      (hPres (resp, base') hbase) le_rfl

theorem authCkStepWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authCkStepWith S P sampAt q hst) := by
  cases q <;> unfold authCkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authCkSendWith_slotFired_mono S P idx sampAt (.sendOPK u i) u bundle m0 m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authCkSendWith_slotFired_mono S P idx sampAt (.sendNoOPK u i) u bundle m0 m1 hst hFired
  case recvOPK k j o msg =>
    exact authCkRecvWith_slotFired_mono S P idx sampAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authCkRecvWith_slotFired_mono S P idx sampAt msg _ hst
      (fun prep hPrep res? =>
        prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
          hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired

theorem lt_cutoff_bool_eq {s idx : Nat} (b : Bool) (hne : s ≠ idx) :
    (s < idx) = (s < (if b then idx else idx + 1)) := by
  cases b
  · simp; omega
  · simp

theorem authCkStepWith_after (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (k : Bytes × Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authCkStepWith S P (fun s => if s == idx then pure k else sampCkPair P (s < idx)) q hst =
      authCkStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst ∧
    ∀ x ∈ support
      (authCkStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authCkStepWith_slotFired_mono S P idx _ q hst hFired⟩
  have hSendEq :
      ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes),
      sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authCkSendWith S P (fun s => if s == idx then pure k else sampCkPair P (s < idx))
          sid u bundle m0 m1 hst =
        authCkSendWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1)))
          sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authCkSendWith
      simp only [hCont, ↓reduceIte]
    · have hne : sessionSlotIndex sid ≠ idx := by
        intro h; exact hEq (beq_iff_eq.mpr h)
      have hlt := lt_cutoff_bool_eq b hne
      apply authCkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte, hlt]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authCkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authCkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    have hlt := lt_cutoff_bool_eq b hne
    apply authCkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte, hlt]
  case recvNoOPK k' j l msg =>
    unfold authCkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    have hlt := lt_cutoff_bool_eq b hne
    apply authCkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte, hlt]
  all_goals rfl

noncomputable def finalizeAuthFixed {S : Setup} (P : Primitives) (secb b' : Bool)
    (finalSt : AuthHybridState S) : ProbComp Bool := do
  let allChallengedClean := finalSt.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.base.principals s)
  if hasEcPkCollisionAuth P finalSt ||
     hasBadSigAuth finalSt ||
     hasKemPkCollisionAuth finalSt ||
     hasBadKemShCrAuth P finalSt then
    $ᵗ Bool
  else if finalSt.base.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)

noncomputable def authCkPreSampleRun (S : Setup) (P : Primitives) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authCkCutoffExp (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => sampCkPair P (s < cutoff)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

/-- Pre-sampling `sampCkPair P (!b)` at slot `idx` matches `authCkCutoffExp` at `idx` or `idx + 1`. -/
theorem evalDist_preSample_authCk_eq_cutoff (S : Setup) (P : Primitives)
    (idx : Nat) (b : Bool) (A : AuthAdversary S) :
    𝒟[sampCkPair P (!b) >>= fun p => authCkPreSampleRun S P idx p A] =
      𝒟[authCkCutoffExp S P (if b then idx else idx + 1) A] := by
  unfold authCkPreSampleRun authCkCutoffExp
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    (sampCkPair P (!b))
    (authSlotFired S idx)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => sampCkPair P (s < (if b then idx else idx + 1))) q hst))
    (fun p q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst))
    (authCkStepSlot S P idx (sampCkPair P (!b)))
    (authCkStepSlot_slotComp S P idx (sampCkPair P (!b)))
    (authCkStepSlot_run'_some S P idx (sampCkPair P (!b)))
    (fun q hst g => by
      dsimp only [StateT.run_mk]
      rw [authCkStepSlot_run'_none_eq S P idx b q hst])
    (fun p q hst hFired => authCkStepWith_after S P idx b p q hst hFired)
    (authCkStepSlot_fire S P idx (sampCkPair P (!b)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

/-! ## Cutoff boundary helpers -/

theorem evalDist_sampleBytes32_bind_const (mx : ProbComp Bool) :
    𝒟[sampleBytes32 >>= fun _ => mx] = 𝒟[mx] :=
  OracleComp.evalDist_bind_const sampleBytes32 mx

theorem evalDist_simulateQ_proj_inv_bound {ι α St1 St2 : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (proj : St1 → St2)
    (Inv : St1 → Prop)
    (count : St1 → Nat)
    (isCounted : ℕ ⊕ ι → Bool)
    (hInl : ∀ n, isCounted (Sum.inl n) = false)
    (N : Nat)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ (gq : ι) (st : St1), Inv st → (isCounted (Sum.inr gq) = true → count st < N) →
      (∀ (k : QSpec.Range gq × St2 → ProbComp Bool),
        𝒟[(impl1 gq).run st >>= fun x => k (x.1, proj x.2)] =
          𝒟[(impl2 gq).run (proj st) >>= k]) ∧
      (∀ x ∈ support ((impl1 gq).run st),
        Inv x.2 ∧ count x.2 ≤ count st + (if isCounted (Sum.inr gq) then 1 else 0)))
    (oa : OracleComp (unifSpec + QSpec) α)
    (qBound : Nat)
    (hBound : IsQueryBoundP oa (fun q => isCounted q = true) qBound)
    (st : St1) (hInv : Inv st) (hCount : count st + qBound ≤ N)
    (obs : α × St2 → ProbComp Bool) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run st >>= fun x => obs (x.1, proj x.2)] =
      𝒟[(simulateQ full2 oa).run (proj st) >>= obs] := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing qBound st with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hBound
    rcases q with uq | gq
    · rcases hBound with ⟨_, hCont⟩
      simp only [hInl uq, Bool.false_eq_true, ↓reduceIte] at hCont
      rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local,
          bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
      exact ih u qBound (hCont u) st hInv hCount
    · rcases hBound with ⟨hFirst, hCont⟩
      have hLt : isCounted (Sum.inr gq) = true → count st < N := by
        intro hC
        rcases hFirst with hAbs | hPos
        · exfalso; exact hAbs hC
        · omega
      obtain ⟨hStepDist, hStepSupp⟩ := hStep gq st hInv hLt
      rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local,
          bind_assoc, bind_assoc]
      rw [← hStepDist (fun z => (simulateQ full2 (mx z.1)).run z.2 >>= obs)]
      refine OracleComp.evalDist_bind_congr_of_support ((impl1 gq).run st) _ _ (fun x hx => ?_)
      obtain ⟨hInv', hCount'⟩ := hStepSupp x hx
      by_cases hC : isCounted (Sum.inr gq) = true
      · rcases hFirst with hAbs | hPos
        · exfalso; exact hAbs hC
        · simp only [hC, ↓reduceIte] at hCont hCount'
          exact ih x.1 (qBound - 1) (hCont x.1) x.2 hInv' (by omega)
      · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hCont hCount'
        exact ih x.1 qBound (hCont x.1) x.2 hInv' (by omega)

theorem evalDist_simulateQ_proj_inv {ι α St1 St2 : Type}
    {QSpec : OracleSpec.{0, 0} ι}
    (proj : St1 → St2)
    (Inv : St1 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hStep : ∀ (gq : ι) (st : St1), Inv st →
      (∀ (k : QSpec.Range gq × St2 → ProbComp Bool),
        𝒟[(impl1 gq).run st >>= fun x => k (x.1, proj x.2)] =
          𝒟[(impl2 gq).run (proj st) >>= k]) ∧
      (∀ x ∈ support ((impl1 gq).run st), Inv x.2))
    (oa : OracleComp (unifSpec + QSpec) α)
    (st : St1) (hInv : Inv st)
    (obs : α × St2 → ProbComp Bool) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run st >>= fun x => obs (x.1, proj x.2)] =
      𝒟[(simulateQ full2 oa).run (proj st) >>= obs] :=
  evalDist_simulateQ_proj_inv_bound proj Inv (fun _ => 0) (fun _ => false) (fun _ => rfl) 1
    impl1 impl2
    (fun gq st hInv _ => ⟨(hStep gq st hInv).1, fun x hx => ⟨(hStep gq st hInv).2 x hx, Nat.le_refl 0⟩⟩)
    oa 0 (by simpa only [Bool.false_eq_true] using
      Computational.Proofs.GameHop.StateSim.isQueryBoundP_false oa 0) st hInv (Nat.zero_le 1) obs

def eraseIdealCk1_0 {S : Setup} (s : IdealAuthSession S) : IdealAuthSession S :=
  { s with ck1_0 := [] }

def eraseAuthCk1_0 {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with idealSessions := hst.idealSessions.map eraseIdealCk1_0 }

def eraseAuthFixedCk1_0 {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { toAuthHybridState := eraseAuthCk1_0 hst.toAuthHybridState
    recvCount := hst.recvCount }

@[simp] theorem eraseAuthCk1_0_base {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0 hst).base = hst.base := rfl

@[simp] theorem eraseAuthCk1_0_initKemRecs {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0 hst).initKemRecs = hst.initKemRecs := rfl

@[simp] theorem eraseAuthCk1_0_recvKemRecs {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0 hst).recvKemRecs = hst.recvKemRecs := rfl

@[simp] theorem eraseAuthCk1_0_empty (S : Setup) (secb : Bool) :
    eraseAuthCk1_0 (AuthHybridState.empty S secb) = AuthHybridState.empty S secb := rfl

@[simp] theorem eraseAuthFixedCk1_0_empty (S : Setup) (secb : Bool) :
    eraseAuthFixedCk1_0 (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S secb := rfl

@[simp] theorem finalizeAuthFixed_eraseAuthCk1_0 {S : Setup} (P : Primitives) (secb b' : Bool)
    (hst : AuthHybridState S) :
    finalizeAuthFixed P secb b' (eraseAuthCk1_0 hst) = finalizeAuthFixed P secb b' hst := rfl

@[simp] theorem matchIdealAuthHandshake_eraseIdealCk1_0 {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr (eraseIdealCk1_0 s) =
      matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s := rfl

theorem finishAuthHybridRecvOPK_eraseAuthCk1_0 {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry
      usedTriples' msg hstDec res?
    (x.1, eraseAuthCk1_0 x.2) =
      finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples'
        msg (eraseAuthCk1_0 hstDec) res? := by
  dsimp only [eraseAuthCk1_0]
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl

theorem finishAuthHybridRecvNoOPK_eraseAuthCk1_0 {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?
    (x.1, eraseAuthCk1_0 x.2) =
      finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples'
        msg (eraseAuthCk1_0 hstDec) res? := by
  dsimp only [eraseAuthCk1_0]
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl

theorem sampCkPair_bind_eq {α : Type} (P : Primitives) (ideal : Bool)
    (f : Bytes × Bytes → ProbComp α) :
    (sampleBytes32 >>= fun c =>
      (if ideal then do
        let ms ← sampleBytes32
        let cn ← sampleBytes32
        pure (ms, cn)
       else
        pure (P.chainKdfSeed c, P.chainKdfNext c)) >>= f) =
    (sampCkPair P ideal >>= f) := by
  simp only [sampCkPair, bind_assoc]

end SignalPqxdh.Security
