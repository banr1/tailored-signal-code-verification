/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhBounds
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhSigBound
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDhSessionSplit
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key `Auth` `GapDhWithSign` `ReductionDsl` Adversary Wiring

**Checked by Lean.** Packages `fgAuth1KeyGapDhProg S b.q_total` as `fgAuth1KeyGapDhDslAdv` and
proves `gapDhWithSignExp` equivalence with `fgAuth1KeyGapDhAdv4` together with
`GapDhWithSignAdv.Bounded` for both adversaries.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security Proofs.SignalPqxdh.Security.FgGapDh1Key
open SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open OracleSpec OracleComp

/-- One-key `Auth` `GapDhWithSign` reduction `fgAuth1KeyGapDhProg S b.q_total` packaged as a
    `GapDhWithSignAdv`. -/
def fgAuth1KeyGapDhDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapDhWithSignAdv where
  run U V := (fgAuth1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh  := authGdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

section Helpers
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

private theorem fgAuth1KeyGapDhDslAdv_run (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    (fgAuth1KeyGapDhDslAdv S b A).run U V =
      (fgAuth1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V) := rfl

private theorem primBaseImpl_eq (P : Primitives) :
    primBaseImpl P = QueryImpl.ofLift unifSpec ProbComp + primImpl P := rfl

private theorem isQueryBoundP_unifGdhSign_zero {α : Type} (mx : ProbComp α)
    (P : (PrimBaseSpec + sigAndDdhOracle.spec).Domain → Prop) [DecidablePred P]
    (hUnif : ∀ n : ℕ, ¬ P (Sum.inl (Sum.inl n))) :
    IsQueryBoundP (unifGdhSign mx) P 0 := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure P a 0
  | query_bind n r ih =>
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => unifGdhSign (r u)) P 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hUnif n), fun u => (ih u).mono (Nat.zero_le _)⟩

private theorem mem_support_unifGdhSign {α : Type} {mx : ProbComp α} {x : α}
    (hx : x ∈ support (unifGdhSign mx)) : x ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    change x ∈ support (pure a : OracleComp GdhSignSimSpec α) at hx
    simpa using hx
  | query_bind n r ih =>
    change x ∈ support
      (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => unifGdhSign (r u)) at hx
    rw [MonadAttach.mem_support_bind] at hx ⊢
    rcases hx with ⟨u, _, hru⟩
    exact ⟨u, mem_support_query _ _, ih u hru⟩

private theorem isQueryBoundP_fgAuth1KeyGapDhAdv4_of_runAt
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes)
    (P : (PrimBaseSpec + sigAndDdhOracle.spec).Domain → Prop) [DecidablePred P] (N : ℕ)
    (hUnif : ∀ n : ℕ, ¬ P (Sum.inl (Sum.inl n)))
    (hAt : ∀ useDh1 t sIdx, IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V) P N) :
    IsQueryBoundP ((fgAuth1KeyGapDhAdv4 S b A).run U V) P N := by
  dsimp only [fgAuth1KeyGapDhAdv4]
  refine (isQueryBoundP_bind (isQueryBoundP_unifGdhSign_zero _ P hUnif) fun p _ => ?_).mono
    (Nat.zero_add N).le
  rcases p with ⟨fl, bI⟩
  dsimp only
  split_ifs <;> exact hAt _ _ _

private theorem isQueryBoundP_fgAuth1KeyGapDhProg_of_runAt
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes)
    (P : (PrimBaseSpec + sigAndDdhOracle.spec).Domain → Prop) [DecidablePred P] (N : ℕ)
    (hUnif : ∀ n : ℕ, ¬ P (Sum.inl (Sum.inl n)))
    (hAt : ∀ useDh1 t sIdx, IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V) P N) :
    IsQueryBoundP ((fgAuth1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)) P N := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1
    funext q; cases q <;> rfl
  unfold CostedReduction.eval CostedReduction.impl
  dsimp only [fgAuth1KeyGapDhProg]
  rw [a1g2InitDsl_eval]
  simp only [bind_assoc, pure_bind]
  refine (isQueryBoundP_bind (isQueryBoundP_unifGdhSign_zero _ P hUnif) fun role hRole => ?_).mono
    (Nat.zero_add N).le
  obtain ⟨useDh1, t, rfl⟩ := sampleRole2Prob_mem_support S (mem_support_unifGdhSign hRole)
  refine (isQueryBoundP_bind (isQueryBoundP_unifGdhSign_zero _ P hUnif) fun spk hSpk => ?_).mono
    (Nat.zero_add N).le
  obtain ⟨sIdx, rfl⟩ := sampleSpkPair2Prob_mem_support S (mem_support_unifGdhSign hSpk)
  have hBody :
      (unifGdhSign ($ᵗ Bool) >>= fun secb =>
        ((simulateQ (handlerImpl (C := authCodec S) (a1g2HandleDsl S b.q_total)) A.1.run).run
            (a1g2StToVal S b.q_total (pa2Val S U V useDh1 t sIdx)
              (FgAuth1KeySimState.empty S secb)) >>=
          fun p => (a1g2FinishDsl S b.q_total).eval (.cons p.2 (.cons p.1 .nil)))) =
        fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V := by
    unfold fgAuth1KeyGapDhRunAt
    exact congrArg (unifGdhSign ($ᵗ Bool) >>= ·)
      (funext fun secb => a1g2Run_eq S b.q_total U V useDh1 t sIdx A.1.run hA secb)
  change IsQueryBoundP
    (unifGdhSign ($ᵗ Bool) >>= fun secb =>
      ((simulateQ (handlerImpl (C := authCodec S) (a1g2HandleDsl S b.q_total)) A.1.run).run
          (a1g2StToVal S b.q_total (pa2Val S U V useDh1 t sIdx)
            (FgAuth1KeySimState.empty S secb)) >>=
        fun p => (a1g2FinishDsl S b.q_total).eval (.cons p.2 (.cons p.1 .nil)))) P N
  rw [hBody]
  exact hAt useDh1 t sIdx

private def a1g2AtInitDsl (S : Setup) (K : Nat) : CS [a1gParams2Ty] (.prod .unit a1g2StTy) :=
  bindV (Comp.sampleBoolC (Γ := [a1gParams2Ty])) fun secb =>
  .ret (.pair .litUnit
    (.pair
      (.pair (.var (.vs .vz)) (emptySimE (v secb)))
      (.litNat (min K (min S.N_spk_tot S.N_recv)))))

private def a1g2AtProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (authSpec S) (authCodec S)
      a1gParams2Ty .unit .bool (B 32) where
  σ      := a1g2StTy
  init   := a1g2AtInitDsl S K
  handle := a1g2HandleDsl S K
  finish := a1g2FinishDsl S K

private theorem a1g2AtInitDsl_prim (S : Setup) (K : Nat) :
    (a1g2AtInitDsl S K).queries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := rfl

private theorem a1g2AtInitDsl_ddh (S : Setup) (K : Nat) :
    (a1g2AtInitDsl S K).queries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 := rfl

private theorem a1g2AtInitDsl_eval (S : Setup) (K : Nat) (pa : a1gParams2Ty.denote) :
    (a1g2AtInitDsl S K).eval (.cons pa .nil) =
      (unifGdhSign ($ᵗ Bool) >>= fun secb =>
        pure ((), a1g2StToVal S K pa (FgAuth1KeySimState.empty S secb))) := by
  simp only [a1g2AtInitDsl, bindV, Comp.eval, unifGdhSign,
    pqSigAndDdhIface, pqChalIface]
  refine congrArg (_ >>= ·) (funext fun secb => ?_)
  simp only [v, emptySimE, emptyAuthStE, fsMk, stMk, Expr.eval, Env.get_vz, Env.get_vs,
    Ext.refl_wk, a1g2StToVal, a1gClampedSigB, FgAuth1KeySimState.empty,
    Nat.sub_self, Nat.sub_zero]
  rfl

private theorem a1g_wire_split_arith (q k X F : ℕ) (hk : k ≤ q) (hX : 2 ≤ X) (hF : F ≤ 16 * X) :
    0 + (q * 32 + k * (16 * X - 32)) + F ≤ 32 * (q - k) + 16 * (k + 1) * X := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 16 * X = 32 + d := ⟨16 * X - 32, by omega⟩
  have h1 : 16 * X - 32 = d := by omega
  have h2 : k + r - k = r := by omega
  have h3 : 16 * (k + 1) * X = (k + 1) * (32 + d) := by rw [← hd]; ring
  rw [h1, h2, h3]
  nlinarith

private theorem isQueryBoundP_fgAuth1KeyGapDhRunAt_prim
    (useDh1 : Bool) (t sIdx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V)
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1
    funext q; cases q <;> rfl
  have hEvalEq : (a1g2AtProg S b.q_total).eval (fun _ => A.1.run) (pa2Val S U V useDh1 t sIdx) =
      fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V := by
    unfold CostedReduction.eval CostedReduction.impl fgAuth1KeyGapDhRunAt
    dsimp only [a1g2AtProg]
    rw [a1g2AtInitDsl_eval]
    simp only [bind_assoc, pure_bind]
    exact congrArg (unifGdhSign ($ᵗ Bool) >>= ·)
      (funext fun secb => a1g2Run_eq S b.q_total U V useDh1 t sIdx A.1.run hA secb)
  rw [← hEvalEq]
  refine (CostedReduction.queryBound_eval₂ (a1g2AtProg S b.q_total)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
    (fun t => isAuthSessionQ t = true) (kL := 32) (kH := 16 * (5 * S.N_dh + S.N_sess_tot + 12))
    (by omega)
    (fun q s _ => a1gHandle_primBound_heavy S b.q_total s q)
    (fun q s hq => a1gHandle_primBound_light S b.q_total s q (by simpa using hq))
    (fun _ => A.1.run) b.q_total (min b.q_on S.N_sess_tot)
    (authAdv_gameBound S b A) (fun _ => authAdv_sessionBound_on S b A)
    (pa2Val S U V useDh1 t sIdx)).mono ?_
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro k
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl k))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]
  · have h0 : (a1g2AtProg S b.q_total).init.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
      a1g2AtInitDsl_prim S b.q_total
    have hF : (a1g2AtProg S b.q_total).finish.queries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ S.N_dh * 4 + S.N_sess_tot * 2 := by
      change (fgAuth1KeyGapDhProg S b.q_total).finish.queries
        KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ _
      exact a1g_finish_prim_le S b.q_total
    rw [h0, ← a1g_split_prim_eq_gdhPrimQueryBudget S b]
    exact a1g_wire_split_arith b.q_total (min b.q_total (min b.q_on S.N_sess_tot)) _ _
      (min_le_left _ _) (by omega) (hF.trans (by omega))

section BilinearSignHelpers
open Proofs.SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl (isQueryBoundP_of_imp isQueryBoundP_or_add)

private abbrev a1g_isDdhSign (q : GdhSignSimSpec.Domain) : Prop := isDdhChalQuery q = true

private theorem ddhSign_pure {α : Type} (x : α) (n : ℕ) :
    IsQueryBoundP (pure x : OracleComp GdhSignSimSpec α) a1g_isDdhSign n :=
  isQueryBoundP_pure _ x n

private theorem ddhSign_bind0 {α β : Type} {n : ℕ}
    {mx : OracleComp GdhSignSimSpec α} {f : α → OracleComp GdhSignSimSpec β}
    (h1 : IsQueryBoundP mx a1g_isDdhSign 0)
    (h2 : ∀ x ∈ support mx, IsQueryBoundP (f x) a1g_isDdhSign n) :
    IsQueryBoundP (mx >>= f) a1g_isDdhSign n := by
  simpa using isQueryBoundP_bind h1 h2

private theorem ddhSign_lift {α : Type} {n : ℕ} {mx : OracleComp FgGapDh.GdhSimSpec α}
    (h : IsQueryBoundP mx a1g_isDdhGdh n) :
    IsQueryBoundP (liftGdhToSign mx) a1g_isDdhSign n := by
  induction mx using OracleComp.inductionOn generalizing n with
  | pure a => exact ddhSign_pure a n
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    cases t with
    | inl bq =>
      change IsQueryBoundP
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u))
        a1g_isDdhSign n
      rw [isQueryBoundP_query_bind_iff]
      have hb : a1g_isDdhSign (Sum.inl bq) = False := by simp [a1g_isDdhSign, isDdhChalQuery]
      have hg : a1g_isDdhGdh (Sum.inl bq) = False := by simp [a1g_isDdhGdh]
      refine ⟨Or.inl (fun hc => by cases hc), fun u => ?_⟩
      simpa [hb] using ih u (by simpa [hg] using h.2 u)
    | inr dq =>
      have hn : 0 < n := h.1.resolve_left (by simp [a1g_isDdhGdh])
      change IsQueryBoundP
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u))
        a1g_isDdhSign n
      rw [isQueryBoundP_query_bind_iff]
      have hb : a1g_isDdhSign (Sum.inr (Sum.inr dq)) = True := by simp [a1g_isDdhSign, isDdhChalQuery]
      have hg : a1g_isDdhGdh (Sum.inr dq) = True := by simp [a1g_isDdhGdh]
      refine ⟨Or.inr hn, fun u => ?_⟩
      simpa [hb] using ih u (by simpa [hg] using h.2 u)

private theorem mem_support_liftGdhToSign_iff {α : Type} (mx : OracleComp FgGapDh.GdhSimSpec α)
    (x : α) : x ∈ support (liftGdhToSign mx) ↔ x ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp [liftGdhToSign]
  | query_bind t r ih =>
    cases t with
    | inl bq =>
      change x ∈ support
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u)) ↔ _
      simp [ih]
    | inr dq =>
      change x ∈ support
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u)) ↔ _
      simp [ih]

private theorem ddhSign_unif {α : Type} (mx : OracleComp unifSpec α) :
    IsQueryBoundP (unifGdhSign mx) a1g_isDdhSign 0 :=
  ddhSign_lift (ddhGdh_unif mx)

private theorem ddhSign_primQ (t : PrimQuery) :
    IsQueryBoundP (primGdhSignQ t) a1g_isDdhSign 0 :=
  (isQueryBoundP_query_iff (spec := GdhSignSimSpec) a1g_isDdhSign
    (Sum.inl (Sum.inr t)) 0).2 (fun hc => by cases hc)

private theorem ddhSign_sigChalQ (m : Bytes) :
    IsQueryBoundP (sigChalQ m) a1g_isDdhSign 0 :=
  (isQueryBoundP_query_iff (spec := GdhSignSimSpec) a1g_isDdhSign
    (Sum.inr (Sum.inl (.sign m))) 0).2 (fun hc => by cases hc)

private theorem ddhGdh_fgRunRecvOPKAuthGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st st0 : FgAuthSimState S) (hFgEq : st.fgL = st0.fgL) (hRtEq : st.fgRootL = st0.fgRootL) :
    IsQueryBoundP (fgRunRecvOPKAuthGdh S maxLen k j o msg st) a1g_isDdhGdh
      (4 * (a1g_rDone st0 + a1g_sDone st0) + (a1g_rtRDone st0 + a1g_rtSDone st0)) ∧
    ∀ p ∈ support (fgRunRecvOPKAuthGdh S maxLen k j o msg st), a1g_SessStepPost st0 p.2 := by
  have hSt0 : a1g_SessStepPost st0 st := by
    unfold a1g_SessStepPost a1g_rDone a1g_sDone a1g_rtRDone a1g_rtSDone; rw [hFgEq, hRtEq]
    exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  unfold fgRunRecvOPKAuthGdh
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
      msg.hdr.pqspkId == UInt32.ofNat j.val &&
      msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
      msg.hdr.ikAPk.length == 32 &&
      msg.hdr.ekAPk.length == 32 &&
      msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : st.base.usedRecvOPK.contains (k.val, j.val, o.val) = true
  · simp only [h2, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun senderOk _ => ?_
  by_cases h3 : (!senderOk) = true
  · simp only [h3, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact ddhGdh_step_pure _ _ _ hSt0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact ddhGdh_step_pure _ _ _ hSt0
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact ddhGdh_step_pure _ _ _ hSt0
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only
        by_cases h4 : oEntry.consumed = true
        · simp only [h4, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
        simp only [h4, Bool.false_eq_true, ↓reduceIte]
        refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun canon _ => ?_
        refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun canonEph _ => ?_
        by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
            msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 || !canon || !canonEph) = true
        · simp only [h5, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
        simp only [h5, Bool.false_eq_true, ↓reduceIte]
        refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun ss? _ => ?_
        cases ss? with
        | none => exact ddhGdh_step_pure _ _ _ hSt0
        | some ss =>
          dsimp only
          refine ddhGdh_step_bind0 (ddhGdh_twoSide _ _ _ _) fun pos4 _ => ?_
          exact ddhGdh_fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss (some pos4) _ st st0 hFgEq hRtEq

private theorem ddhGdh_fgRunRecvNoOPKAuthGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st st0 : FgAuthSimState S) (hFgEq : st.fgL = st0.fgL) (hRtEq : st.fgRootL = st0.fgRootL) :
    IsQueryBoundP (fgRunRecvNoOPKAuthGdh S maxLen k j l msg st) a1g_isDdhGdh
      (4 * (a1g_rDone st0 + a1g_sDone st0) + (a1g_rtRDone st0 + a1g_rtSDone st0)) ∧
    ∀ p ∈ support (fgRunRecvNoOPKAuthGdh S maxLen k j l msg st), a1g_SessStepPost st0 p.2 := by
  have hSt0 : a1g_SessStepPost st0 st := by
    unfold a1g_SessStepPost a1g_rDone a1g_sDone a1g_rtRDone a1g_rtSDone; rw [hFgEq, hRtEq]
    exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  unfold fgRunRecvNoOPKAuthGdh
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
      msg.hdr.pqspkId == UInt32.ofNat j.val &&
      msg.hdr.opkId? == none &&
      msg.hdr.ikAPk.length == 32 &&
      msg.hdr.ekAPk.length == 32 &&
      msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
  · simp only [h2, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  refine ddhGdh_step_bind0 (ddhGdh_embedPrim _) fun senderOk _ => ?_
  by_cases h3 : (!senderOk) = true
  · simp only [h3, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact ddhGdh_step_pure _ _ _ hSt0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact ddhGdh_step_pure _ _ _ hSt0
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun canon _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun canonEph _ => ?_
      by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
          msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 || !canon || !canonEph) = true
      · simp only [h5, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ hSt0
      simp only [h5, Bool.false_eq_true, ↓reduceIte]
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun ss? _ => ?_
      cases ss? with
      | none => exact ddhGdh_step_pure _ _ _ hSt0
      | some ss =>
        dsimp only
        exact ddhGdh_fgFinishRecvAuthGdh S maxLen k j msg kEntry bEntry ss none _ st st0 hFgEq hRtEq

private theorem ddhSign_liftAuthSimStep1Key {S : Setup} {n : ℕ}
    {f : FgAuthSimState S → OracleComp FgGapDh.GdhSimSpec (AuthResponse × FgAuthSimState S)}
    {st : FgAuth1KeySimState S} {P : FgAuthSimState S → Prop}
    (hf : IsQueryBoundP (f st.sim) a1g_isDdhGdh n ∧ ∀ p ∈ support (f st.sim), P p.2) :
    IsQueryBoundP (liftAuthSimStep1Key f st) a1g_isDdhSign n ∧
    ∀ p ∈ support (liftAuthSimStep1Key f st), P p.2.sim := by
  unfold liftAuthSimStep1Key
  refine ⟨(isQueryBoundP_bind (n := n) (m := 0) (ddhSign_lift hf.1)
    fun _ _ => ddhSign_pure _ 0).mono (by omega), ?_⟩
  intro p hp
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  rcases hp with ⟨⟨r, sim'⟩, hsim, rfl⟩
  rw [mem_support_liftGdhToSign_iff] at hsim
  exact hf.2 (r, sim') hsim

private def a1g_FgEqPost {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  st'.fgL = st.fgL ∧ st'.fgRootL = st.fgRootL

private def a1g_RoRootStepPost {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  a1g_rtRDone st' ≤ a1g_rtRDone st + 1 ∧ a1g_rtSDone st' = a1g_rtSDone st ∧ st'.fgL = st.fgL

private theorem ddhSign_fgAuthInitPrin1KeyGdh {S : Setup} (prinFlag : Bool) (prinIdx : ℕ)
    (Up : Bytes) (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st) a1g_isDdhSign 0 ∧
    ∀ p ∈ support (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st),
      a1g_FgEqPost st.sim p.2.sim := by
  unfold fgAuthInitPrin1KeyGdh
  by_cases h : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
  · simp only [h, ↓reduceIte]
    refine ⟨ddhSign_pure _ 0, fun p hp => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨rfl, rfl⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ddhSign_bind0 (ddhSign_unif _) fun _ _ =>
      ddhSign_bind0 (ddhSign_primQ _) fun _ _ => ddhSign_pure _ 0, fun p hp => ?_⟩
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, _, _, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem ddhSign_fgAuthGenSPK1KeyGdh (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st)
      a1g_isDdhSign 0 ∧
    ∀ p ∈ support (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st),
      a1g_FgEqPost st.sim p.2.sim := by
  unfold fgAuthGenSPK1KeyGdh
  by_cases hT : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hT, ↓reduceIte]
    by_cases hA : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hA, ↓reduceIte]
      refine ⟨ddhSign_pure _ 0, fun p hp => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨rfl, rfl⟩
    simp only [hA, Bool.false_eq_true, ↓reduceIte]
    cases st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      refine ⟨ddhSign_pure _ 0, fun p hp => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨rfl, rfl⟩
    | some up =>
      rcases up with ⟨_, uEntry⟩; dsimp only
      by_cases hB : (st.sigBudget == 0) = true
      · simp only [hB, ↓reduceIte]
        refine ⟨ddhSign_pure _ 0, fun p hp => ?_⟩
        simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨rfl, rfl⟩
      simp only [hB, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ddhSign_bind0 (ddhSign_unif _) fun _ _ =>
        ddhSign_bind0 (ddhSign_primQ _) fun _ _ =>
        ddhSign_bind0 (ddhSign_sigChalQ _) fun _ _ =>
        ddhSign_bind0 (ddhSign_unif _) fun _ _ =>
        ddhSign_bind0 (ddhSign_primQ _) fun pqOut _ => ?_, ?_⟩
      · rcases pqOut with ⟨_, _⟩
        exact ddhSign_bind0 (ddhSign_sigChalQ _) fun _ _ => ddhSign_pure _ 0
      · intro p hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        rcases hp with ⟨_, _, _, _, _, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩
        exact ⟨rfl, rfl⟩
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    refine ddhSign_liftAuthSimStep1Key ?_
    dsimp only [fgAuthStep]
    by_cases hA : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hA, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    simp only [hA, Bool.false_eq_true, ↓reduceIte]
    cases st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    | some up =>
      rcases up with ⟨_, uEntry⟩; dsimp only
      refine ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun pqOut _ => ?_
      rcases pqOut with ⟨_, _⟩
      refine ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩

private def a1g_isAuthSessQ {S : Setup} : AuthQuery S → Bool
  | .sendOPK .. | .sendNoOPK .. | .recvOPK .. | .recvNoOPK .. => true
  | _ => false

private def a1g_isAuthRoQ {S : Setup} : AuthQuery S → Bool
  | .roQuery _ => true
  | _ => false

private def a1g_isAuthRootQ {S : Setup} : AuthQuery S → Bool
  | .roRootQuery _ _ => true
  | _ => false

private theorem ddhSign_fgAuth1KeyStepHalt_ro (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (secrets : Bytes) (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V (.roQuery secrets) st)
      a1g_isDdhSign (4 * a1g_sDone st.sim) ∧
    ∀ p ∈ support (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V (.roQuery secrets) st),
      a1g_RoStepPost st.sim p.2.sim := by
  unfold fgAuth1KeyStepHalt
  split_ifs
  · refine ⟨ddhSign_pure _ _, fun p hp => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨Nat.le_succ _, rfl, rfl⟩
  · dsimp only [fgAuth1KeyStep]
    refine ddhSign_liftAuthSimStep1Key ?_
    dsimp only [fgAuthStep]
    exact ddhGdh_fgRoQueryAuthGdh maxLen secrets st.sim

private theorem ddhSign_fgAuth1KeyStepHalt_root (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (rk dh : Bytes) (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V (.roRootQuery rk dh) st)
      a1g_isDdhSign (a1g_rtSDone st.sim) ∧
    ∀ p ∈ support (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V (.roRootQuery rk dh) st),
      a1g_RoRootStepPost st.sim p.2.sim := by
  unfold fgAuth1KeyStepHalt
  split_ifs
  · refine ⟨ddhSign_pure _ _, fun p hp => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨Nat.le_succ _, rfl, rfl⟩
  · dsimp only [fgAuth1KeyStep]
    refine ddhSign_liftAuthSimStep1Key ?_
    dsimp only [fgAuthStep]
    exact ddhGdh_fgRoRootQueryAuthGdh maxLen rk dh st.sim

private theorem ddhSign_fgAuth1KeyStepHalt_sess (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (gq : AuthQuery S) (hS : a1g_isAuthSessQ gq = true)
    (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V gq st)
      a1g_isDdhSign (4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim)) ∧
    ∀ p ∈ support (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V gq st),
      a1g_SessStepPost st.sim p.2.sim := by
  unfold fgAuth1KeyStepHalt
  split_ifs
  · refine ⟨ddhSign_pure _ _, fun p hp => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact a1g_sessStepPost_refl st.sim
  · cases gq with
    | sendOPK u i bundle m0 m1 =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      split_ifs
      · exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st.sim)
      · exact ddhGdh_fgRunSendAuthGdh useDh1 targetIdx S maxLen U (.sendOPK u i) u bundle m0 m1 st.sim
    | sendNoOPK u i bundle m0 m1 =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      split_ifs
      · exact ddhGdh_step_pure _ _ _ (a1g_sessStepPost_refl st.sim)
      · exact ddhGdh_fgRunSendAuthGdh useDh1 targetIdx S maxLen U (.sendNoOPK u i) u bundle m0 m1 st.sim
    | recvOPK k j o msg =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      exact ddhGdh_fgRunRecvOPKAuthGdh S maxLen k j o msg _ st.sim rfl rfl
    | recvNoOPK k j l msg =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      exact ddhGdh_fgRunRecvNoOPKAuthGdh S maxLen k j l msg _ st.sim rfl rfl
    | _ => cases hS

private theorem ddhSign_fgAuth1KeyStepHalt_other (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (gq : AuthQuery S)
    (hRo : a1g_isAuthRoQ gq = false) (hRt : a1g_isAuthRootQ gq = false) (hS : a1g_isAuthSessQ gq = false)
    (st : FgAuth1KeySimState S) :
    IsQueryBoundP (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V gq st)
      a1g_isDdhSign 0 ∧
    ∀ p ∈ support (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V gq st),
      a1g_FgEqPost st.sim p.2.sim := by
  unfold fgAuth1KeyStepHalt
  split_ifs
  · refine ⟨ddhSign_pure _ 0, fun p hp => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨rfl, rfl⟩
  · cases gq with
    | initPrin u => exact ddhSign_fgAuthInitPrin1KeyGdh useDh1 targetIdx U u st
    | genSPK u j =>
      exact ddhSign_fgAuthGenSPK1KeyGdh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st
    | corruptIK u =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      cases st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
      | some kp => rcases kp with ⟨_, _⟩; exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    | genOPK u j o =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      by_cases hA : (st.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
      · simp only [hA, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      refine ddhGdh_step_bind0 (ddhGdh_unif _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    | revealDhSecrets =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    | registerKey sk =>
      dsimp only [fgAuth1KeyStep]
      refine ddhSign_liftAuthSimStep1Key ?_
      dsimp only [fgAuthStep]
      by_cases hL : (sk.length != 32) = true
      · simp only [hL, ↓reduceIte]; exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
      simp only [hL, Bool.false_eq_true, ↓reduceIte]
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      refine ddhGdh_step_bind0 (ddhGdh_primQ _) fun _ _ => ?_
      exact ddhGdh_step_pure _ _ _ ⟨rfl, rfl⟩
    | roQuery _ => cases hRo
    | roRootQuery _ _ => cases hRt
    | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ => cases hS

private def a1g_onAuthGame {S : Setup} (pred : AuthQuery S → Bool) : (unifSpec + authSpec S).Domain → Prop
  | .inl _ => False
  | .inr q => pred q = true

private instance {S : Setup} (pred : AuthQuery S → Bool) : DecidablePred (a1g_onAuthGame pred)
  | .inl _ => isFalse False.elim
  | .inr q => inferInstanceAs (Decidable (pred q = true))

private theorem ddhSign_runWithGdhSignStep_phi (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (rR rtRR sR : ℕ) (st : FgAuth1KeySimState S),
      mx.IsQueryBoundP (a1g_onAuthGame a1g_isAuthRoQ) rR →
      mx.IsQueryBoundP (a1g_onAuthGame a1g_isAuthRootQ) rtRR →
      mx.IsQueryBoundP (a1g_onAuthGame a1g_isAuthSessQ) sR →
      IsQueryBoundP
        (runWithGdhSignStep (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V) mx st)
        a1g_isDdhSign (a1g_authPhi st.sim rR rtRR sR) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro rR rtRR sR st _ _ _
    rw [runWithGdhSignStep_pure]
    exact ddhSign_pure _ _
  | query_bind q k ih =>
    intro rR rtRR sR st hRo hRt hS
    rw [isQueryBoundP_query_bind_iff] at hRo hRt hS
    cases q with
    | inl n =>
      rw [runWithGdhSignStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun hc => by cases hc), fun u => ih u rR rtRR sR st
        (by simpa [a1g_onAuthGame] using hRo.2 u)
        (by simpa [a1g_onAuthGame] using hRt.2 u)
        (by simpa [a1g_onAuthGame] using hS.2 u)⟩
    | inr gq =>
      rw [runWithGdhSignStep_query_inr]
      cases gq with
      | roQuery secrets =>
        have hPos : 0 < rR := hRo.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthRoQ])
        obtain ⟨r', rfl⟩ : ∃ r', rR = r' + 1 := ⟨rR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_ro useDh1 targetIdx targetSpkIdx S maxLen U V secrets st
        refine (isQueryBoundP_bind (n := 4 * a1g_sDone st.sim)
          (m := a1g_phiMain (a1g_rDone st.sim + 1) (a1g_sDone st.sim) r' sR +
                a1g_phiRoot (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR sR)
          hs.1 fun p hp => ?_).mono ?_
        · have ⟨hrL, hsE, hrtE⟩ := hs.2 p hp
          have hCont := ih p.1 r' rtRR sR p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          refine hCont.mono ?_
          unfold a1g_authPhi a1g_rtRDone a1g_rtSDone
          rw [hsE, hrtE]
          have hm : a1g_phiMain (a1g_rDone p.2.sim) (a1g_sDone st.sim) r' sR ≤
              a1g_phiMain (a1g_rDone st.sim + 1) (a1g_sDone st.sim) r' sR := by
            unfold a1g_phiMain
            have := Nat.mul_le_mul_right sR (Nat.mul_le_mul_left 4 hrL)
            omega
          omega
        · unfold a1g_authPhi
          have := a1g_phiMain_ro (a1g_rDone st.sim) (a1g_sDone st.sim) r' sR (a1g_rDone st.sim + 1) le_rfl
          omega
      | roRootQuery rk dh =>
        have hPos : 0 < rtRR := hRt.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthRootQ])
        obtain ⟨rt', rfl⟩ : ∃ rt', rtRR = rt' + 1 := ⟨rtRR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_root useDh1 targetIdx targetSpkIdx S maxLen U V rk dh st
        refine (isQueryBoundP_bind (n := a1g_rtSDone st.sim)
          (m := a1g_phiMain (a1g_rDone st.sim) (a1g_sDone st.sim) rR sR +
                a1g_phiRoot (a1g_rtRDone st.sim + 1) (a1g_rtSDone st.sim) rt' sR)
          hs.1 fun p hp => ?_).mono ?_
        · have ⟨hrtL, hrtSE, hfgE⟩ := hs.2 p hp
          have hCont := ih p.1 rR rt' sR p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          refine hCont.mono ?_
          unfold a1g_authPhi a1g_rDone a1g_sDone
          rw [hrtSE, hfgE]
          have hr : a1g_phiRoot (a1g_rtRDone p.2.sim) (a1g_rtSDone st.sim) rt' sR ≤
              a1g_phiRoot (a1g_rtRDone st.sim + 1) (a1g_rtSDone st.sim) rt' sR := by
            unfold a1g_phiRoot
            have := Nat.mul_le_mul_right sR hrtL
            omega
          omega
        · unfold a1g_authPhi
          have := a1g_phiRoot_ro (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rt' sR (a1g_rtRDone st.sim + 1) le_rfl
          omega
      | sendOPK u i b0 m0 m1 =>
        have hPos : 0 < sR := hS.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthSessQ])
        obtain ⟨s', rfl⟩ : ∃ s', sR = s' + 1 := ⟨sR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_sess useDh1 targetIdx targetSpkIdx S maxLen U V
          (.sendOPK u i b0 m0 m1) rfl st
        refine (isQueryBoundP_bind
          (n := 4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim))
          (m := a1g_authPhi st.sim rR rtRR (s' + 1) -
                (4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim)))
          hs.1 fun p hp => ?_).mono ?_
        · have hPost := hs.2 p hp
          have hCont := ih p.1 rR rtRR s' p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone p.2.sim) (a1g_sDone p.2.sim) hPost.1
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone p.2.sim) (a1g_rtSDone p.2.sim) hPost.2
          exact hCont.mono (by unfold a1g_authPhi at *; omega)
        · have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone st.sim) (a1g_sDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          unfold a1g_authPhi; omega
      | sendNoOPK u i b0 m0 m1 =>
        have hPos : 0 < sR := hS.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthSessQ])
        obtain ⟨s', rfl⟩ : ∃ s', sR = s' + 1 := ⟨sR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_sess useDh1 targetIdx targetSpkIdx S maxLen U V
          (.sendNoOPK u i b0 m0 m1) rfl st
        refine (isQueryBoundP_bind
          (n := 4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim))
          (m := a1g_authPhi st.sim rR rtRR (s' + 1) -
                (4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim)))
          hs.1 fun p hp => ?_).mono ?_
        · have hPost := hs.2 p hp
          have hCont := ih p.1 rR rtRR s' p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone p.2.sim) (a1g_sDone p.2.sim) hPost.1
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone p.2.sim) (a1g_rtSDone p.2.sim) hPost.2
          exact hCont.mono (by unfold a1g_authPhi at *; omega)
        · have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone st.sim) (a1g_sDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          unfold a1g_authPhi; omega
      | recvOPK u j o msg =>
        have hPos : 0 < sR := hS.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthSessQ])
        obtain ⟨s', rfl⟩ : ∃ s', sR = s' + 1 := ⟨sR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_sess useDh1 targetIdx targetSpkIdx S maxLen U V
          (.recvOPK u j o msg) rfl st
        refine (isQueryBoundP_bind
          (n := 4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim))
          (m := a1g_authPhi st.sim rR rtRR (s' + 1) -
                (4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim)))
          hs.1 fun p hp => ?_).mono ?_
        · have hPost := hs.2 p hp
          have hCont := ih p.1 rR rtRR s' p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone p.2.sim) (a1g_sDone p.2.sim) hPost.1
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone p.2.sim) (a1g_rtSDone p.2.sim) hPost.2
          exact hCont.mono (by unfold a1g_authPhi at *; omega)
        · have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone st.sim) (a1g_sDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          unfold a1g_authPhi; omega
      | recvNoOPK u j l msg =>
        have hPos : 0 < sR := hS.1.resolve_left (by simp [a1g_onAuthGame, a1g_isAuthSessQ])
        obtain ⟨s', rfl⟩ : ∃ s', sR = s' + 1 := ⟨sR - 1, by omega⟩
        have hs := ddhSign_fgAuth1KeyStepHalt_sess useDh1 targetIdx targetSpkIdx S maxLen U V
          (.recvNoOPK u j l msg) rfl st
        refine (isQueryBoundP_bind
          (n := 4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim))
          (m := a1g_authPhi st.sim rR rtRR (s' + 1) -
                (4 * (a1g_rDone st.sim + a1g_sDone st.sim) + (a1g_rtRDone st.sim + a1g_rtSDone st.sim)))
          hs.1 fun p hp => ?_).mono ?_
        · have hPost := hs.2 p hp
          have hCont := ih p.1 rR rtRR s' p.2
            (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
            (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
          have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone p.2.sim) (a1g_sDone p.2.sim) hPost.1
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone p.2.sim) (a1g_rtSDone p.2.sim) hPost.2
          exact hCont.mono (by unfold a1g_authPhi at *; omega)
        · have h1 := a1g_phiMain_sess (a1g_rDone st.sim) (a1g_sDone st.sim) rR s' (a1g_rDone st.sim) (a1g_sDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          have h2 := a1g_phiRoot_sess (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) rtRR s' (a1g_rtRDone st.sim) (a1g_rtSDone st.sim) (Or.inl ⟨rfl, rfl⟩)
          unfold a1g_authPhi; omega
      | initPrin u =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V (.initPrin u) rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont
      | corruptIK u =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V (.corruptIK u) rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont
      | genSPK u j =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j) rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont
      | genOPK u j o =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V (.genOPK u j o) rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont
      | revealDhSecrets =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V .revealDhSecrets rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont
      | registerKey sk =>
        have hs := ddhSign_fgAuth1KeyStepHalt_other useDh1 targetIdx targetSpkIdx S maxLen U V (.registerKey sk) rfl rfl rfl st
        refine ddhSign_bind0 hs.1 fun p hp => ?_
        have ⟨hfg, hrt⟩ := hs.2 p hp
        have hCont := ih p.1 rR rtRR sR p.2
          (by simpa [a1g_onAuthGame, a1g_isAuthRoQ] using hRo.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthRootQ] using hRt.2 p.1)
          (by simpa [a1g_onAuthGame, a1g_isAuthSessQ] using hS.2 p.1)
        simpa [a1g_authPhi, a1g_rDone, a1g_sDone, a1g_rtRDone, a1g_rtSDone, hfg, hrt] using hCont

private theorem ddhGdh_extractCdhFromAuthSimState (S : Setup) (useDh1 : Bool) (maxLen : ℕ)
    (U V : Bytes) (st : FgAuthSimState S) :
    IsQueryBoundP (extractCdhFromAuthSimState S useDh1 maxLen U V st) a1g_isDdhGdh
      (maxLen + S.N_dh + S.N_sess_tot) := by
  unfold extractCdhFromAuthSimState
  have hLog : ∀ f : Bytes → Bytes,
      IsQueryBoundP (FgGapDh.findMGdh (fun z => FgGapDh.ddhGdhQ U V z)
        ((st.advRoLog.take maxLen).map f)) a1g_isDdhGdh maxLen := by
    intro f
    refine (ddhGdh_findM_weight _ (fun _ => 1) (fun z => ddhGdh_ddhQ U V z) _).mono ?_
    rw [a1g_sum_map_const_eq, Nat.one_mul, List.length_map]
    exact List.length_take_le maxLen st.advRoLog
  have hResp : ∀ cand : AuthRespRecord → OracleComp FgGapDh.GdhSimSpec Bytes,
      (∀ r, IsQueryBoundP (cand r) a1g_isDdhGdh 0) →
      IsQueryBoundP (FgGapDh.findMapMGdh cand U V (st.respRecs.take S.N_sess_tot))
        a1g_isDdhGdh S.N_sess_tot := fun cand hc =>
    (ddhGdh_findMapM_len cand hc U V _).mono (List.length_take_le S.N_sess_tot st.respRecs)
  split_ifs
  · refine (isQueryBoundP_bind (n := maxLen) (m := S.N_dh + S.N_sess_tot)
      (hLog _) fun m1 _ => ?_).mono (by omega)
    cases m1 with
    | some _ => exact ddhGdh_pure _ _
    | none =>
      refine ddhGdh_bind0 (ddhGdh_spkPows _) fun spkPows _ => ?_
      have hInit : IsQueryBoundP
          (FgGapDh.findMapMGdh (initAuthDh1CandWithPowsGdh st.base.principals spkPows st.advKeyPows)
            U V (st.base.sessions.take S.N_dh)) a1g_isDdhGdh S.N_dh := by
        refine (ddhGdh_findMapM_len _ (fun s => ?_) U V _).mono
          (List.length_take_le S.N_dh st.base.sessions)
        unfold initAuthDh1CandWithPowsGdh
        exact ddhGdh_bind0 (ddhGdh_primQ _) fun _ _ => ddhGdh_primQ _
      refine (isQueryBoundP_bind (n := S.N_dh) (m := S.N_sess_tot) hInit fun m2 _ => ?_).mono
        (by omega)
      cases m2 with
      | some _ => exact ddhGdh_pure _ _
      | none =>
        refine (isQueryBoundP_bind (n := S.N_sess_tot) (m := 0)
          (hResp _ fun r => ddhGdh_primQ _) fun m3 _ => ?_).mono (by omega)
        cases m3 <;> exact ddhGdh_pure _ 0
  · refine (isQueryBoundP_bind (n := maxLen) (m := S.N_dh + S.N_sess_tot)
      (hLog _) fun m1 _ => ?_).mono (by omega)
    cases m1 with
    | some _ => exact ddhGdh_pure _ _
    | none =>
      have hInit : IsQueryBoundP
          (FgGapDh.findMapMGdh initAuthDh3CandGdh U V (st.base.sessions.take S.N_dh))
          a1g_isDdhGdh S.N_dh := by
        refine (ddhGdh_findMapM_len _ (fun s => ?_) U V _).mono
          (List.length_take_le S.N_dh st.base.sessions)
        unfold initAuthDh3CandGdh
        split_ifs
        · exact ddhGdh_pure _ 0
        · exact ddhGdh_primQ _
      refine (isQueryBoundP_bind (n := S.N_dh) (m := S.N_sess_tot) hInit fun m2 _ => ?_).mono
        (by omega)
      cases m2 with
      | some _ => exact ddhGdh_pure _ _
      | none =>
        refine (isQueryBoundP_bind (n := S.N_sess_tot) (m := 0)
          (hResp _ fun r => ddhGdh_primQ _) fun m3 _ => ?_).mono (by omega)
        cases m3 <;> exact ddhGdh_pure _ 0

private theorem isQueryBoundP_fgAuth1KeyGapDhRunAt_ddh_bilinear (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    let M_ro := min b.q_ro b.q_total
    let M_root := min b.q_roRoot b.q_total
    let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
    IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V)
      (fun q => isDdhChalQuery q = true)
      ((4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1) +
        b.q_total + S.N_dh + S.N_sess_tot) := by
  intro M_ro M_root M_sess
  obtain ⟨hRoRaw, hSend, hRecv, hRootRaw, hTotRaw, hOnRaw⟩ := A.2
  have hRoM : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthRoQ) M_ro := by
    dsimp only [M_ro]
    by_cases h1 : b.q_ro ≤ b.q_total
    · rw [Nat.min_eq_left h1]
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRoRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [a1g_onAuthGame, a1g_isAuthRoQ, isAuthRoQuery]
    · rw [Nat.min_eq_right (Nat.le_of_not_le h1)]
      refine isQueryBoundP_of_imp (fun t ht => ?_) hTotRaw
      rcases t with _ | _
      · exact ht.elim
      · rfl
  have hRootM : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthRootQ) M_root := by
    dsimp only [M_root]
    by_cases h1 : b.q_roRoot ≤ b.q_total
    · rw [Nat.min_eq_left h1]
      refine isQueryBoundP_of_imp (fun t ht => ?_) hRootRaw
      rcases t with _ | gq
      · exact ht.elim
      · cases gq <;> simp_all [a1g_onAuthGame, a1g_isAuthRootQ, isAuthRoRootQuery]
    · rw [Nat.min_eq_right (Nat.le_of_not_le h1)]
      refine isQueryBoundP_of_imp (fun t ht => ?_) hTotRaw
      rcases t with _ | _
      · exact ht.elim
      · rfl
  have hSessAll : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthSessQ) S.N_sess_tot := by
    refine isQueryBoundP_or_add
      (p₁ := isAuthSendQuery) (p₂ := isAuthRecvQuery) ?_ hSend hRecv
    intro t ht
    rcases t with _ | gq
    · exact ht.elim
    · cases gq <;> simp_all [a1g_onAuthGame, a1g_isAuthSessQ, isAuthSendQuery, isAuthRecvQuery]
  have hSessQOn : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthSessQ) b.q_on := by
    refine isQueryBoundP_of_imp (fun t ht => ?_) hOnRaw
    rcases t with _ | gq
    · exact ht.elim
    · cases gq <;> simp_all [a1g_onAuthGame, a1g_isAuthSessQ, isAuthOnlineQuery]
  have hSessOnTot : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthSessQ) (min b.q_on b.q_total) := by
    by_cases hOnLe : b.q_on ≤ b.q_total
    · rw [Nat.min_eq_left hOnLe]; exact hSessQOn
    · rw [Nat.min_eq_right (Nat.le_of_not_le hOnLe)]
      refine isQueryBoundP_of_imp (fun t ht => ?_) hTotRaw
      rcases t with _ | _
      · exact ht.elim
      · rfl
  have hSessM : A.1.run.IsQueryBoundP (a1g_onAuthGame a1g_isAuthSessQ) M_sess := by
    dsimp only [M_sess]
    by_cases h2 : min b.q_on b.q_total ≤ S.N_sess_tot
    · rw [Nat.min_eq_left h2]
      exact hSessOnTot
    · rw [Nat.min_eq_right (Nat.le_of_not_le h2)]
      exact hSessAll
  unfold fgAuth1KeyGapDhRunAt
  refine ddhSign_bind0 (ddhSign_unif _) fun secb _ => ?_
  have hPhi := ddhSign_runWithGdhSignStep_phi useDh1 targetIdx targetSpkIdx S b.q_total U V
    A.1.run M_ro M_root M_sess (FgAuth1KeySimState.empty S secb) hRoM hRootM hSessM
  have hPhiEmpty : a1g_authPhi (FgAuth1KeySimState.empty S secb).sim M_ro M_root M_sess =
      (4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1) := by
    change a1g_phiMain 0 0 M_ro M_sess + a1g_phiRoot 0 0 M_root M_sess = _
    unfold a1g_phiMain a1g_phiRoot
    ring
  rw [hPhiEmpty] at hPhi
  refine (isQueryBoundP_bind (n := (4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1))
    (m := b.q_total + S.N_dh + S.N_sess_tot) hPhi fun p _ => ?_).mono (by omega)
  exact ddhSign_lift (ddhGdh_extractCdhFromAuthSimState S useDh1 b.q_total U V p.2.sim)

end BilinearSignHelpers

private theorem isQueryBoundP_fgAuth1KeyGapDhRunAt_ddh
    (useDh1 : Bool) (t sIdx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    IsQueryBoundP (fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V)
      (fun q => isDdhChalQuery q = true) (authGdhQueryBudget S b) := by
  let M_ro := min b.q_ro b.q_total
  let M_root := min b.q_roRoot b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  by_cases hLe : 5 * b.q_total ^ 2 ≤ (4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1)
  · have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
      have h := SignalPqxdh.QueryBounded.auth_total A.2
      convert h using 1
      funext q; cases q <;> rfl
    have hEvalEq : (a1g2AtProg S b.q_total).eval (fun _ => A.1.run) (pa2Val S U V useDh1 t sIdx) =
        fgAuth1KeyGapDhRunAt useDh1 t sIdx S b A U V := by
      unfold CostedReduction.eval CostedReduction.impl fgAuth1KeyGapDhRunAt
      dsimp only [a1g2AtProg]
      rw [a1g2AtInitDsl_eval]
      simp only [bind_assoc, pure_bind]
      exact congrArg (unifGdhSign ($ᵗ Bool) >>= ·)
        (funext fun secb => a1g2Run_eq S b.q_total U V useDh1 t sIdx A.1.run hA secb)
    rw [← hEvalEq]
    refine (CostedReduction.queryBound_eval (a1g2AtProg S b.q_total)
      (fun q => isDdhChalQuery q = true)
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_
      (fun _ => A.1.run) b.q_total (authAdv_gameBound S b A)
      (pa2Val S U V useDh1 t sIdx)).mono ?_
    · intro g x hx
      cases g with
      | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
      | inr t =>
        cases t with
        | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
        | inr u => rcases u with ⟨⟩; simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
    · intro n
      change IsQueryBoundP
        (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
        (fun q => isDdhChalQuery q = true) 0
      rw [isQueryBoundP_query_iff]
      simp [isDdhChalQuery]
    · dsimp only [CostedReduction.totalQueries]
      have h0 : (a1g2AtProg S b.q_total).init.queries
          SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
          SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = 0 :=
        a1g2AtInitDsl_ddh S b.q_total
      have hH : (a1g2AtProg S b.q_total).handle.queries
          SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
          SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ 5 * b.q_total := by
        change (fgAuth1KeyGapDhProg S b.q_total).handle.queries
          KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key ≤ _
        exact a1g_handle_ddh_le S b.q_total
      have hF : (a1g2AtProg S b.q_total).finish.queries
          SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
          SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ≤ b.q_total + S.N_dh + S.N_sess_tot := by
        change (fgAuth1KeyGapDhProg S b.q_total).finish.queries
          KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key ≤ _
        exact a1g_finish_ddh_le S b.q_total
      rw [h0, Nat.zero_add]
      unfold authGdhQueryBudget
      dsimp only
      change _ ≤ min (5 * b.q_total ^ 2) ((4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
      rw [Nat.min_eq_left hLe]
      generalize (a1g2AtProg S b.q_total).handle.queries
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = qH at hH ⊢
      generalize (a1g2AtProg S b.q_total).finish.queries
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = qF at hF ⊢
      have hMul : b.q_total * qH ≤ 5 * b.q_total ^ 2 := by
        calc b.q_total * qH ≤ b.q_total * (5 * b.q_total) := Nat.mul_le_mul_left _ hH
          _ = 5 * b.q_total ^ 2 := by ring
      omega
  ·
    refine (isQueryBoundP_fgAuth1KeyGapDhRunAt_ddh_bilinear useDh1 t sIdx S b A U V).mono ?_
    unfold authGdhQueryBudget
    dsimp only
    change (4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1) +
        b.q_total + S.N_dh + S.N_sess_tot ≤
      min (5 * b.q_total ^ 2) ((4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1)) +
        b.q_total + S.N_dh + S.N_sess_tot
    rw [Nat.min_eq_right (Nat.le_of_not_le hLe)]

end Helpers

set_option linter.style.haveILetI false in
/-- `fgAuth1KeyGapDhDslAdv` and `fgAuth1KeyGapDhAdv4` induce the same `gapDhWithSignExp`
    distribution. -/
theorem fgAuth1KeyGapDhDslAdv_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgAuth1KeyGapDhDslAdv S b A)] =
      𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgAuth1KeyGapDhAdv4 S b A)] := by
  letI : DiscreteMeasurableSpace (List UInt8) := ⟨fun _ => trivial⟩
  letI : DiscreteMeasurableSpace Bytes := ⟨fun _ => trivial⟩
  letI : DiscreteMeasurableSpace (B 32).denote := ⟨fun _ => trivial⟩
  unfold gapDhWithSignExp
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  refine congrArg (𝒟[sampleScalar32].bind ·) (funext fun u => ?_)
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  refine congrArg (𝒟[sampleScalar32].bind ·) (funext fun v => ?_)
  dsimp only
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, fgAuth1KeyGapDhDslAdv_run,
    primBaseImpl_eq]
  exact congrArg (fun μ : MeasureTheory.Measure Bytes => μ.bind _)
    (fgAuth1KeyGapDhProg_eval_eq S b A (P.x25519Base u) (P.x25519Base v) (primImpl P) _)

/-- `fgAuth1KeyGapDhDslAdv` satisfies `GapDhWithSignAdv.Bounded`. -/
theorem fgAuth1KeyGapDhDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (fgAuth1KeyGapDhDslAdv S b A).Bounded := by
  refine ⟨fun U V => ?_, fun U V => ?_, fun U V => ?_⟩
  · exact isQueryBoundP_fgAuth1KeyGapDhProg_of_runAt S b A U V
      (fun q => isDdhChalQuery q = true) (authGdhQueryBudget S b)
      (fun n => by simp [isDdhChalQuery])
      (fun useDh1 t sIdx => isQueryBoundP_fgAuth1KeyGapDhRunAt_ddh useDh1 t sIdx S b A U V)
  · exact isQueryBoundP_fgAuth1KeyGapDhProg_of_runAt S b A U V
      (fun q => isSigChalQuery q = true) (2 * min S.N_spk_tot S.N_recv)
      (fun n => by simp [isSigChalQuery])
      (fun useDh1 t sIdx => isQueryBoundP_fgAuth1KeyGapDhRunAt_sig useDh1 t sIdx S b A U V)
  · exact fgAuth1KeyGapDhProg_primBounded_gdhPrimQueryBudget S b.q_total b A U V

/-- `fgAuth1KeyGapDhAdv4` satisfies `GapDhWithSignAdv.Bounded`. -/
theorem fgAuth1KeyGapDhAdv4_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (fgAuth1KeyGapDhAdv4 S b A).Bounded := by
  refine ⟨fun U V => ?_, fun U V => ?_, fun U V => ?_⟩
  · exact isQueryBoundP_fgAuth1KeyGapDhAdv4_of_runAt S b A U V
      (fun q => isDdhChalQuery q = true) (authGdhQueryBudget S b)
      (fun n => by simp [isDdhChalQuery])
      (fun useDh1 t sIdx => isQueryBoundP_fgAuth1KeyGapDhRunAt_ddh useDh1 t sIdx S b A U V)
  · exact isQueryBoundP_fgAuth1KeyGapDhAdv4_sig S b A U V
  · exact isQueryBoundP_fgAuth1KeyGapDhAdv4_of_runAt S b A U V
      (fun q => isPrimQuery q = true) (gdhPrimQueryBudget S b)
      (fun n => by simp [isPrimQuery])
      (fun useDh1 t sIdx => isQueryBoundP_fgAuth1KeyGapDhRunAt_prim useDh1 t sIdx S b A U V)

/-- `fgAuth1KeyGapDhDslAdv` and `fgAuth1KeyGapDhAdv4` have equal `GapDhWithSign` advantage. -/
theorem fgAuth1KeyGapDhProg_gapDhWithSign_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    GapDhWithSign P isValidDhTriple pow8 (fgAuth1KeyGapDhDslAdv S b A) =
      GapDhWithSign P isValidDhTriple pow8 (fgAuth1KeyGapDhAdv4 S b A) := by
  simp only [GapDhWithSign, fgAuth1KeyGapDhDslAdv_eq]

end SignalPqxdh.Security.ReductionDsl.AuthHs
