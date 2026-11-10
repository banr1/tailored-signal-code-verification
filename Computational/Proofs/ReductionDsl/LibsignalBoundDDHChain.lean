/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRF.CostedTables
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import Computational.Proofs.ReductionDsl.Soundness

/-!
# Costed PRF Operation Honesty and Lifted PRG Adversary Lemmas

Proves `OpsSizeHonest` for `prfConstantInputOps` and coin-forwarding simulation and zero-game-query
bounds (`simulateQ_liftPRGAdv_run`, `isQueryBoundP_liftPRGAdv`) for `ProbComp` PRG adversaries
lifted to `unifSpec + prgSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.Ratchet
  CryptoGames.PRF.Costed CryptoGames.PRG.Costed MACScheme

@[simp] private theorem env_get_cons_zero {S : Sig} {Γ : List (Ty S)} {t : Ty S}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get Var.zero = x := rfl

@[simp] private theorem env_get_cons_succ {S : Sig} {Γ : List (Ty S)} {t u : Ty S}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (Var.succ v) = ρ.get v := rfl

theorem prfOps_sizeHonest {Input Tag C : Type} (c : C → Input) :
    OpsSizeHonest (prfConstantInputOps (S := prfSig Input Tag) (.base .inp) c) := by
  intro o _ B _
  simp only [Ty.Fits]
  omega

theorem liftM_unif_query_bind {κ : Type} {G : OracleSpec κ} {α : Type}
    (t : unifSpec.Domain) (mx : unifSpec.Range t → ProbComp α) :
    (liftM (liftM (unifSpec.query t) >>= mx) : OracleComp (unifSpec + G) α) =
      (liftM ((unifSpec + G).query (.inl t)) >>=
        fun u => (liftM (mx u) : OracleComp (unifSpec + G) α)) := by
  rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query,
    liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  rfl

/-- Simulating a `CostedReduction` on a lifted `ProbComp` forwards all coin queries unchanged. -/
theorem simulateQ_liftPRGAdv_run {Input Tag : Type} {S : Sig} {O : Ops S}
    {I : Iface S (unifSpec + MACScheme.prfSpec Input Tag)}
    (hU : ∀ n, I.fwdU n = query (spec := unifSpec + MACScheme.prfSpec Input Tag) (.inl n))
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I prgSpec (prgCodec S) rIn aIn aOut out)
    (p : ProbComp aOut.denote) (s : R.σ.denote) :
    (simulateQ R.impl (liftM p : OracleComp (unifSpec + prgSpec) aOut.denote)).run s =
      (fun x => (x, s)) <$>
        (liftM p : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) aOut.denote) := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
    rw [liftM_unif_query_bind, liftM_unif_query_bind, simulateQ_query_bind, StateT.run_bind]
    have hstep : (R.impl (.inl t)).run s =
        (fun x => (x, s)) <$> liftM ((unifSpec + MACScheme.prfSpec Input Tag).query (.inl t)) := by
      simp [CostedReduction.impl, handlerImpl, hU, StateT.run_lift, map_eq_bind_pure_comp,
        OracleSpec.query]
    change ((R.impl (.inl t)).run s >>= fun z => (simulateQ R.impl (liftM (mx z.1))).run z.2) =
      (fun x => (x, s)) <$>
        (liftM ((unifSpec + MACScheme.prfSpec Input Tag).query (.inl t)) >>= fun u => liftM (mx u))
    rw [hstep, bind_map_left, map_bind]
    exact bind_congr fun u => ih u s

theorem isQueryBoundP_liftPRGAdv {R : Type} (B : PRGScheme.PRGAdversary R) (q : ℕ) (r : R) :
    (liftPRGAdv B r).IsQueryBoundP (isGameQuery (G := prgSpec)) q := by
  have h0 : ∀ p : ProbComp Bool,
      (liftM p : OracleComp (unifSpec + prgSpec) Bool).IsQueryBoundP
        (isGameQuery (G := prgSpec)) 0 := by
    intro p
    induction p using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx ih =>
      rw [liftM_unif_query_bind]
      refine isQueryBoundP_bind ?_ (fun u _ => ih u)
      simp [isQueryBoundP_query_iff, isGameQuery]
  exact (h0 (B r)).mono (Nat.zero_le q)

end CryptoVerification.LibsignalSession.Costed
