/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyB
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC1
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC2
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyW
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-key `Auth` bad-signature hop: per-principal coupling induction

**Checked by Lean.** Proves the per-principal bad-signature bound `authSig1KeyPerKBound` from a
one-key FG step coupling `Auth1KeySigCoupling`, relating the pre-sampled real run
`pqxdhAuthSigPreImpl1Key` to the `GapSigEufCma` reduction `sigReductionAuth1KeyAt`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

noncomputable def sigAuth1KeyWinBool {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (res : (α × SigAuth1KeySimState S) × List Bytes) : Bool :=
  let (mStar, sigStar) := res.1.2.forgery.getD ([], [])
  P.sigVerify (P.sigPkGen sk) mStar sigStar && decide (mStar ∉ res.2)

def SigAuth1KeyWon {S : Setup} (P : Primitives) (sk : Bytes)
    (st : SigAuth1KeySimState S) (msgs : List Bytes) : Prop :=
  ∃ mStar sigStar,
    st.forgery = some (mStar, sigStar) ∧
    P.sigVerify (P.sigPkGen sk) mStar sigStar = true ∧
    mStar ∉ msgs

noncomputable def sigAuth1KeySimVal {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (maxLen : ℕ) (oa : OracleComp (unifSpec + authSpec S) α) (st : SigAuth1KeySimState S)
    (msgs : List Bytes) : ENNReal :=
  𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
      (runWithGdhSignStep (sigAuth1KeyStep S maxLen) oa st)).run msgs >>=
    fun res => pure (sigAuth1KeyWinBool P sk res)] {true}

private theorem evalDist_pure_true_mono {b1 b2 : Bool} (h : b1 = true → b2 = true) :
    𝒟[(pure b1 : ProbComp Bool)] {true} ≤ 𝒟[(pure b2 : ProbComp Bool)] {true} := by
  cases b1 with
  | false => simp
  | true => rw [h rfl]

theorem sigAuth1KeyStep_of_forgery {S : Setup} (maxLen : ℕ) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) (h : st.forgery.isSome = true) :
    sigAuth1KeyStep S maxLen q st = pure (.noneResp, st) := by
  unfold sigAuth1KeyStep; simp [h]

theorem one_le_sigAuth1KeySimVal_of_won {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (maxLen : ℕ) (oa : OracleComp (unifSpec + authSpec S) α) (st : SigAuth1KeySimState S)
    (msgs : List Bytes) (hWon : SigAuth1KeyWon P sk st msgs) :
    1 ≤ sigAuth1KeySimVal P sk maxLen oa st msgs := by
  unfold sigAuth1KeySimVal
  induction oa using OracleComp.inductionOn generalizing st msgs with
  | pure x =>
    rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
    simp [StateT.run_pure, sigAuth1KeyWinBool, hfg, hver, hnotmem]
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [runWithGdhSignStep_query_inl]
      have hq :
          (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
            (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithGdhSignStep (sigAuth1KeyStep S maxLen) (k u) st)).run msgs =
          (liftM (unifSpec.query n) >>= fun u =>
            (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
              (runWithGdhSignStep (sigAuth1KeyStep S maxLen) (k u) st)).run msgs) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      rw [hq, bind_assoc]
      calc (1 : ENNReal)
          = 𝒟[liftM (unifSpec.query n) >>= fun _ => pure true] {true} := by
              rw [OracleComp.evalDist_bind_const]; simp
        _ ≤ _ := evalDist_bind_true_mono_of_support _ _ _ (fun u _ => by
              simpa using ih u st msgs hWon)
    | inr gq =>
      rcases hWon with ⟨mStar, sigStar, hfg, hver, hnotmem⟩
      rw [runWithGdhSignStep_query_inr,
        sigAuth1KeyStep_of_forgery maxLen gq st (by simp [hfg]), pure_bind]
      exact ih .noneResp st msgs ⟨mStar, sigStar, hfg, hver, hnotmem⟩

theorem sigAuth1KeySimVal_anti {S : Setup} {α : Type} (P : Primitives) (sk : Bytes)
    (maxLen : ℕ) (oa : OracleComp (unifSpec + authSpec S) α) (st : SigAuth1KeySimState S)
    (l1 l2 : List Bytes) (hsub : ∀ m ∈ l1, m ∈ l2) :
    sigAuth1KeySimVal P sk maxLen oa st l2 ≤ sigAuth1KeySimVal P sk maxLen oa st l1 := by
  unfold sigAuth1KeySimVal
  rw [simulateQ_gapSigEufCmaFullImpl_run_append P _ sk _ l1,
    simulateQ_gapSigEufCmaFullImpl_run_append P _ sk _ l2, bind_map_left, bind_map_left]
  refine evalDist_bind_true_mono_of_support _ _ _ (fun x _ => evalDist_pure_true_mono ?_)
  unfold sigAuth1KeyWinBool
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_append, not_or]
  exact fun ⟨hv, hn, hl⟩ => ⟨hv, hn, fun h => hl (hsub _ h)⟩

theorem evalDist_authSigPre1Key_won_eq_zero (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (optSk : Option Bytes) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α)
    (st : AuthState S) (hWon : st.hasWonAuth = true) (hG : authSigGood1Key S P k sk st) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthState S) ProbComp) + pqxdhAuthSigPreImpl1Key k optSk S P) oa).run st >>=
      fun (_, s) => pure (hasBadSigAuthAt S P k s)] {true} = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp [StateT.run_pure, hasBadSigAuthAt_eq_false_of_good S P k sk st hG]
  | query_bind q kont ih =>
    cases q with
    | inl n =>
      simp only [FgGapDh.simulateQ_run_query_inl, bind_assoc]
      exact FgGapDh.evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u)
    | inr gq =>
      simp only [FgGapDh.simulateQ_run_query_inr, bind_assoc]
      refine FgGapDh.evalDist_bind_true_eq_zero_of_support _ _ (fun y hy => ?_)
      have hy' : y ∈ support ((pqxdhAuthSigPreImpl1Key k optSk S P gq).run st) := hy
      rw [pqxdhAuthSigPreImpl1Key_run_of_won k optSk S P gq st hWon] at hy'
      simp only [support_pure, Set.mem_singleton_iff] at hy'
      subst hy'
      exact ih _

theorem deadAuthDh1_eq_false_of_good (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (hst : AuthFgCutoffState S) (hG : authSigGood1Key S P k sk hst.base) :
    deadAuthDh1 k hst = false := by
  unfold deadAuthDh1
  cases hF : hst.base.principals.find? (fun (u, _) => u == k) with
  | none => rfl
  | some ue =>
    rcases ue with ⟨u, e⟩
    have hmem := List.mem_of_find?_eq_some hF
    have hu : u = k := by simpa using List.find?_some hF
    subst hu
    exact (hG.2.1 e hmem).2.2

/-- One-key FG step coupling relating `pqxdhAuthFgLatchedPreImpl1Key` to `fgAuth1KeySimImpl`. -/
structure Auth1KeySigCoupling (S : Setup) (P : Primitives) (b : QueryBudget) (k : ℕ) (sk : Bytes)
    where
  Inv : ℕ → AuthFgCutoffState S → FgAuth1KeySimState S → Prop
  inv_empty : ∀ secb, Inv b.q_total (AuthFgCutoffState.empty S secb)
    (FgAuth1KeySimState.empty S secb)
  inv_prinLen : ∀ rem hst st, Inv rem hst st → st.sim.base.principals.length ≤ S.N_dh
  inv_ext : ∀ rem hst st, Inv rem hst st → ∀ bundle,
    extractBundleForgery P k (P.sigPkGen sk) st.sim.base.principals st.sim.base.spkBundles
        bundle none =
      extractBundleForgery P k (P.sigPkGen sk) hst.base.principals hst.base.spkBundles bundle none
  inv_signed : ∀ rem hst st, Inv rem hst st →
    ∀ m ∈ bundleSignedMessages k st.sim.base.spkBundles, m ∈ bundleSignedMessages k hst.base.spkBundles
  step : ∀ (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuth1KeySimState S),
    hst.base.hasWonAuth = false → authSigGood1Key S P k sk hst.base → deadAuthDh1 k hst = false →
    Inv (rem + 1) hst st →
    ∀ (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool)
      (k2 : AuthResponse × FgAuth1KeySimState S → ProbComp Bool),
    (∀ r hst' st', deadAuthDh1 k hst' = false → Inv rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) →
    (∀ r hst', deadAuthDh1 k hst' = true → 𝒟[k1 (r, hst')] {true} = 0) →
    𝒟[(pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot (some sk) none S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgAuth1KeySimImpl P sk P.isValidDhTriple true k S.N_spk_tot S b.q_total
          (P.sigPkGen sk) (P.sigPkGen sk) q).run st >>= k2] {true}

noncomputable def authSigGuardK {S : Setup} (P : Primitives) (k : ℕ) (sk : Bytes) (l : List Bytes)
    (Kr : AuthResponse × AuthState S → ProbComp Bool) (x : AuthResponse × AuthState S) :
    ProbComp Bool :=
  @ite _ ((authSigGood1Key S P k sk x.2 ∨ (authSigLens S).Safe P k x.2) ∧
      x.2.hasWonAuth = false ∧ (∀ m ∈ l, m ∈ bundleSignedMessages k x.2.spkBundles))
    (Classical.propDecidable _) (Kr x) (pure false)

def SigAuth1KeyRel (S : Setup) (P : Primitives) (b : QueryBudget) (k : ℕ) (sk : Bytes)
    (C : Auth1KeySigCoupling S P b k sk) (rem : ℕ) (s : AuthState S) (st : SigAuth1KeySimState S)
    (l : List Bytes) : Prop :=
  (authSigLens S).Safe P k s ∨
  (st.forgery = none ∧ st.targetParty = k ∧ st.targetPk = P.sigPkGen sk ∧
    authSigGood1Key S P k sk s ∧ s.hasWonAuth = false ∧
    (∃ hst : AuthFgCutoffState S, hst.base = s ∧ C.Inv rem hst st.fg) ∧
    (∀ m ∈ l, m ∈ bundleSignedMessages k s.spkBundles))

theorem sigAuth1KeyDelegate_eq_map {S : Setup} (maxLen : ℕ) (q : AuthQuery S)
    (st : SigAuth1KeySimState S) :
    sigAuth1KeyDelegate S maxLen q st =
      (fun p => (p.1, { st with fg := p.2 })) <$>
        fgAuth1KeyStepHalt true st.targetParty S.N_spk_tot S maxLen st.targetPk st.targetPk q st.fg :=
  by
  unfold sigAuth1KeyDelegate
  rw [map_eq_bind_pure_comp]
  rfl

theorem sigAuth1Key_step_delegate (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : ℕ) (sk : Bytes) (C : Auth1KeySigCoupling S P b k sk)
    (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : SigAuth1KeySimState S)
    (l : List Bytes)
    (hFg : st.forgery = none) (hParty : st.targetParty = k) (hPk : st.targetPk = P.sigPkGen sk)
    (hG : authSigGood1Key S P k sk hst.base) (hWon : hst.base.hasWonAuth = false)
    (hInv : C.Inv (rem + 1) hst st.fg)
    (hl : ∀ m ∈ l, m ∈ bundleSignedMessages k hst.base.spkBundles)
    (hStep : ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base),
      authSigGood1Key S P k sk x.2 ∨ (authSigLens S).Safe P k x.2)
    (Kr : AuthResponse × AuthState S → ProbComp Bool)
    (K2 : (AuthResponse × SigAuth1KeySimState S) × List Bytes → ProbComp Bool)
    (hSafe : ∀ r s', (authSigLens S).Safe P k s' → 𝒟[Kr (r, s')] {true} = 0)
    (hWonC : ∀ r s', s'.hasWonAuth = true → authSigGood1Key S P k sk s' → 𝒟[Kr (r, s')] {true} = 0)
    (hAnti : ∀ y l1 l2, (∀ m ∈ l1, m ∈ l2) → 𝒟[K2 (y, l2)] {true} ≤ 𝒟[K2 (y, l1)] {true})
    (hCont : ∀ r s' st' l', SigAuth1KeyRel S P b k sk C rem s' st' l' →
      𝒟[Kr (r, s')] {true} ≤ 𝒟[K2 ((r, st'), l')] {true}) :
    𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true} ≤
      𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sigAuth1KeyDelegate S b.q_total q st)).run l >>= K2] {true} := by
  obtain ⟨fg0, tp, tpk, forg⟩ := st
  dsimp only at hFg hParty hPk hInv ⊢
  subst forg tp tpk
  have hA : 𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true} ≤
      𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>=
        fun x => authSigGuardK P k sk l Kr (x.1, clearAuthWon x.2)] {true} := by
    refine evalDist_bind_true_mono_of_support _ _ _ (fun x hx => ?_)
    rcases x with ⟨r, s'⟩
    cases hW : s'.hasWonAuth with
    | true =>
      rcases hStep (r, s') hx with hG' | hS'
      · rw [hWonC r s' hW hG']; exact zero_le
      · rw [hSafe r s' hS']; exact zero_le
    | false =>
      have hC : clearAuthWon s' = s' := clearAuthWon_of_hasWonAuth_false s' hW
      have hMono := bundleSignedMessages_mono_authSigPre1Key S P k (some sk) q hst.base (r, s') hx
      unfold authSigGuardK
      dsimp only
      rw [hC, ite_eq_left_of_eq_true _ _
        (eq_true ⟨hStep (r, s') hx, hW, fun m hm => hMono m (hl m hm)⟩)]
  refine le_trans hA ?_
  have hB : 𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>=
        fun x => authSigGuardK P k sk l Kr (x.1, clearAuthWon x.2)] {true} =
      𝒟[(pqxdhAuthFgLatchedPreImpl1Key true k S.N_spk_tot (some sk) none S P q).run hst >>=
        fun y => authSigGuardK P k sk l Kr (y.1, y.2.base)] {true} := by
    have h1 := map_clearAuthWon_authSigPre1Key_eq_fgPre_opt S P hP k (some sk) q hst hWon
    have h2 := congrArg (fun m => 𝒟[m >>= authSigGuardK P k sk l Kr] {true}) h1
    simp only [bind_map_left] at h2
    exact h2
  rw [hB]
  let K2' : AuthResponse × FgAuth1KeySimState S → ProbComp Bool := fun p =>
    K2 ((p.1, { fg := p.2, targetParty := k, targetPk := P.sigPkGen sk, forgery := none }),
      bundleSignedMessages k p.2.sim.base.spkBundles ++ l)
  have hR : 𝒟[(fgAuth1KeySimImpl P sk P.isValidDhTriple true k S.N_spk_tot S b.q_total
        (P.sigPkGen sk) (P.sigPkGen sk) q).run fg0 >>= K2'] {true} ≤
      𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sigAuth1KeyDelegate S b.q_total q { fg := fg0, targetParty := k, targetPk := P.sigPkGen sk, forgery := none })).run l >>= K2] {true} := by
    rw [sigAuth1KeyDelegate_eq_map, simulateQ_map, StateT.run_map,
      simulateQ_gapSigEufCmaFullImpl_run_append, bind_map_left, bind_map_left]
    have hE : (fgAuth1KeySimImpl P sk P.isValidDhTriple true k S.N_spk_tot S b.q_total
        (P.sigPkGen sk) (P.sigPkGen sk) q).run fg0 =
        Prod.fst <$> (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (fgAuth1KeyStepHalt true k S.N_spk_tot S b.q_total (P.sigPkGen sk) (P.sigPkGen sk) q
            fg0)).run [] := by
      rw [fst_simulateQ_gapSigEufCmaFullImpl_run, simulateQ_gapDhWithSignFullImpl_fgAuth1KeyStepHalt]
      rfl
    rw [hE, bind_map_left]
    refine evalDist_bind_true_mono_of_support _ _ _ (fun x hx => ?_)
    refine hAnti _ _ _ ?_
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_left _
        (log_subset_of_mem_support_fgAuth1KeyStepHalt P _ sk k S.N_spk_tot S b.q_total _ _ q
          fg0 x hx m h)
    · exact List.mem_append_right _ h
  refine le_trans ?_ hR
  refine C.step q rem hst fg0 hWon hG (deadAuthDh1_eq_false_of_good S P k sk hst hG) hInv
    (fun y => authSigGuardK P k sk l Kr (y.1, y.2.base)) K2' (fun r hst' st' _ hInv' => ?_)
    (fun r hst' hDead => ?_)
  · unfold authSigGuardK
    dsimp only
    split_ifs with hg
    · rcases hg with ⟨hGS, hW', hl'⟩
      rcases hGS with hG' | hS'
      · refine hCont r hst'.base { fg := st', targetParty := k, targetPk := P.sigPkGen sk, forgery := none } _ (Or.inr ⟨rfl, rfl, rfl, hG', hW',
          ⟨hst', rfl, hInv'⟩, fun m hm => ?_⟩)
        rcases List.mem_append.mp hm with h | h
        · exact C.inv_signed rem hst' st' hInv' m h
        · exact hl' m h
      · rw [hSafe r hst'.base hS']; exact zero_le
    · simp
  · unfold authSigGuardK
    dsimp only
    split_ifs with hg
    · rcases hg with ⟨hG' | hS', _, _⟩
      · rw [deadAuthDh1_eq_false_of_good S P k sk hst' hG'] at hDead; cases hDead
      · exact hSafe r hst'.base hS'
    · simp

theorem sigAuth1Key_step_send (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : ℕ) (sk : Bytes) (C : Auth1KeySigCoupling S P b k sk)
    (q : AuthQuery S) (bundle : PreKeyBundleInput) (rem : ℕ) (hst : AuthFgCutoffState S)
    (st : SigAuth1KeySimState S) (l : List Bytes)
    (hFg : st.forgery = none) (hParty : st.targetParty = k) (hPk : st.targetPk = P.sigPkGen sk)
    (hG : authSigGood1Key S P k sk hst.base) (hWon : hst.base.hasWonAuth = false)
    (hInv : C.Inv (rem + 1) hst st.fg)
    (hl : ∀ m ∈ l, m ∈ bundleSignedMessages k hst.base.spkBundles)
    (hq : sigAuth1KeyStep S b.q_total q st = sigAuth1KeySend S b.q_total q bundle st)
    (hGoodN : extractBundleForgery P k (P.sigPkGen sk) hst.base.principals hst.base.spkBundles
        bundle none = none →
      ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base),
        authSigGood1Key S P k sk x.2)
    (Kr : AuthResponse × AuthState S → ProbComp Bool)
    (K2 : (AuthResponse × SigAuth1KeySimState S) × List Bytes → ProbComp Bool)
    (hSafe : ∀ r s', (authSigLens S).Safe P k s' → 𝒟[Kr (r, s')] {true} = 0)
    (hWonC : ∀ r s', s'.hasWonAuth = true → authSigGood1Key S P k sk s' → 𝒟[Kr (r, s')] {true} = 0)
    (hAnti : ∀ y l1 l2, (∀ m ∈ l1, m ∈ l2) → 𝒟[K2 (y, l2)] {true} ≤ 𝒟[K2 (y, l1)] {true})
    (hCont : ∀ r s' st' l', SigAuth1KeyRel S P b k sk C rem s' st' l' →
      𝒟[Kr (r, s')] {true} ≤ 𝒟[K2 ((r, st'), l')] {true})
    (hWinCont : ∀ r st' l', SigAuth1KeyWon P sk st' l' → 1 ≤ 𝒟[K2 ((r, st'), l')] {true}) :
    𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true} ≤
      𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sigAuth1KeyStep S b.q_total q st)).run l >>= K2] {true} := by
  rw [hq]
  have hPrin := C.inv_prinLen _ _ _ hInv
  have hExt := C.inv_ext _ _ _ hInv bundle
  obtain ⟨fg0, tp, tpk, forg⟩ := st
  dsimp only at hFg hParty hPk hInv hPrin hExt ⊢
  subst forg tp tpk
  unfold sigAuth1KeySend
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_embedPrim_sigDdh_run,
    simulateQ_extractBundleForgeryPrim S P k (P.sigPkGen sk) _ _ bundle none hPrin, hExt,
    map_pure, pure_bind]
  cases hE : extractBundleForgery P k (P.sigPkGen sk) hst.base.principals hst.base.spkBundles
      bundle none with
  | some ms =>
    rcases ms with ⟨mStar, sigStar⟩
    simp only [Option.isSome_some, ↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind]
    have hValid := extractBundleForgery_valid_euf_cma P k (P.sigPkGen sk)
      hst.base.principals hst.base.spkBundles bundle hE
    calc 𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true}
        ≤ 1 := MeasureTheory.prob_le_one
      _ ≤ _ := hWinCont _ _ l ⟨mStar, sigStar, rfl, hValid.2.1,
          fun hm => hValid.2.2 (hl mStar hm)⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact sigAuth1Key_step_delegate S P hP b k sk C q rem hst
      { fg := fg0, targetParty := k, targetPk := P.sigPkGen sk, forgery := none } l rfl rfl rfl
      hG hWon hInv hl (fun x hx => Or.inl (hGoodN hE x hx)) Kr K2 hSafe hWonC hAnti hCont

theorem sigAuth1Key_step_nonsend (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : ℕ) (sk : Bytes) (C : Auth1KeySigCoupling S P b k sk)
    (q : AuthQuery S)
    (hS1 : ∀ u i bd m0 m1, q ≠ .sendOPK u i bd m0 m1)
    (hS2 : ∀ u i bd m0 m1, q ≠ .sendNoOPK u i bd m0 m1)
    (rem : ℕ) (hst : AuthFgCutoffState S) (st : SigAuth1KeySimState S) (l : List Bytes)
    (hFg : st.forgery = none) (hParty : st.targetParty = k) (hPk : st.targetPk = P.sigPkGen sk)
    (hG : authSigGood1Key S P k sk hst.base) (hWon : hst.base.hasWonAuth = false)
    (hInv : C.Inv (rem + 1) hst st.fg)
    (hl : ∀ m ∈ l, m ∈ bundleSignedMessages k hst.base.spkBundles)
    (Kr : AuthResponse × AuthState S → ProbComp Bool)
    (K2 : (AuthResponse × SigAuth1KeySimState S) × List Bytes → ProbComp Bool)
    (hSafe : ∀ r s', (authSigLens S).Safe P k s' → 𝒟[Kr (r, s')] {true} = 0)
    (hWonC : ∀ r s', s'.hasWonAuth = true → authSigGood1Key S P k sk s' → 𝒟[Kr (r, s')] {true} = 0)
    (hAnti : ∀ y l1 l2, (∀ m ∈ l1, m ∈ l2) → 𝒟[K2 (y, l2)] {true} ≤ 𝒟[K2 (y, l1)] {true})
    (hCont : ∀ r s' st' l', SigAuth1KeyRel S P b k sk C rem s' st' l' →
      𝒟[Kr (r, s')] {true} ≤ 𝒟[K2 ((r, st'), l')] {true}) :
    𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true} ≤
      𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sigAuth1KeyStep S b.q_total q st)).run l >>= K2] {true} := by
  have hEq : sigAuth1KeyStep S b.q_total q st = sigAuth1KeyDelegate S b.q_total q st := by
    unfold sigAuth1KeyStep
    simp only [hFg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [hEq]
  exact sigAuth1Key_step_delegate S P hP b k sk C q rem hst st l hFg hParty hPk hG hWon hInv hl
    (authSigGood1Key_step_of_not_send S P hP k sk q hS1 hS2 hst.base hG) Kr K2 hSafe hWonC hAnti
    hCont

theorem sigAuth1Key_step_le (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : ℕ) (sk : Bytes) (C : Auth1KeySigCoupling S P b k sk)
    (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : SigAuth1KeySimState S)
    (l : List Bytes)
    (hFg : st.forgery = none) (hParty : st.targetParty = k) (hPk : st.targetPk = P.sigPkGen sk)
    (hG : authSigGood1Key S P k sk hst.base) (hWon : hst.base.hasWonAuth = false)
    (hInv : C.Inv (rem + 1) hst st.fg)
    (hl : ∀ m ∈ l, m ∈ bundleSignedMessages k hst.base.spkBundles)
    (Kr : AuthResponse × AuthState S → ProbComp Bool)
    (K2 : (AuthResponse × SigAuth1KeySimState S) × List Bytes → ProbComp Bool)
    (hSafe : ∀ r s', (authSigLens S).Safe P k s' → 𝒟[Kr (r, s')] {true} = 0)
    (hWonC : ∀ r s', s'.hasWonAuth = true → authSigGood1Key S P k sk s' → 𝒟[Kr (r, s')] {true} = 0)
    (hAnti : ∀ y l1 l2, (∀ m ∈ l1, m ∈ l2) → 𝒟[K2 (y, l2)] {true} ≤ 𝒟[K2 (y, l1)] {true})
    (hCont : ∀ r s' st' l', SigAuth1KeyRel S P b k sk C rem s' st' l' →
      𝒟[Kr (r, s')] {true} ≤ 𝒟[K2 ((r, st'), l')] {true})
    (hWinCont : ∀ r st' l', SigAuth1KeyWon P sk st' l' → 1 ≤ 𝒟[K2 ((r, st'), l')] {true}) :
    𝒟[(pqxdhAuthSigPreImpl1Key k (some sk) S P q).run hst.base >>= Kr] {true} ≤
      𝒟[(simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
          (sigAuth1KeyStep S b.q_total q st)).run l >>= K2] {true} := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    exact sigAuth1Key_step_send S P hP b k sk C _ bundle rem hst st l hFg hParty hPk hG hWon hInv
      hl (by unfold sigAuth1KeyStep; simp [hFg])
      (fun hE => authSigGood1Key_step_sendOPK S P k sk u i bundle m0 m1 hst.base hG hE)
      Kr K2 hSafe hWonC hAnti hCont hWinCont
  | sendNoOPK u i bundle m0 m1 =>
    exact sigAuth1Key_step_send S P hP b k sk C _ bundle rem hst st l hFg hParty hPk hG hWon hInv
      hl (by unfold sigAuth1KeyStep; simp [hFg])
      (fun hE => authSigGood1Key_step_sendNoOPK S P k sk u i bundle m0 m1 hst.base hG hE)
      Kr K2 hSafe hWonC hAnti hCont hWinCont
  | _ =>
    exact sigAuth1Key_step_nonsend S P hP b k sk C _ (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rem hst st l hFg hParty hPk hG hWon hInv hl Kr K2 hSafe
      hWonC hAnti hCont

theorem evalDist_authSigPre1Key_le_sigAuth1KeySimVal (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (k : ℕ) (sk : Bytes)
    (C : Auth1KeySigCoupling S P b k sk) {α : Type}
    (oa : OracleComp (unifSpec + authSpec S) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ AuthQuery S => isGameQuery q = true) rem)
    (s : AuthState S) (st : SigAuth1KeySimState S) (l : List Bytes)
    (hRel : SigAuth1KeyRel S P b k sk C rem s st l) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthState S) ProbComp) + pqxdhAuthSigPreImpl1Key k (some sk) S P) oa).run s >>=
      fun (_, s') => pure (hasBadSigAuthAt S P k s')] {true} ≤
      sigAuth1KeySimVal P sk b.q_total oa st l := by
  unfold sigAuth1KeySimVal
  induction oa using OracleComp.inductionOn generalizing rem s st l with
  | pure x =>
    rcases hRel with hS | ⟨_, _, _, hG, _⟩
    · have hBadF : hasBadSigAuthAt S P k s = false :=
        (authSigLens S).safe_badAt_eq_false P k s hS
      simp [StateT.run_pure, hBadF]
    · simp [StateT.run_pure, hasBadSigAuthAt_eq_false_of_good S P k sk s hG]
  | query_bind q kont ih =>
    rw [isQueryBoundP_query_bind_iff] at hQb
    cases q with
    | inl n =>
      rcases hQb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      rw [runWithGdhSignStep_query_inl]
      have hqR :
          (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
            (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n))) >>=
              fun u => runWithGdhSignStep (sigAuth1KeyStep S b.q_total) (kont u) st)).run l =
          (liftM (unifSpec.query n) >>= fun u =>
            (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
              (runWithGdhSignStep (sigAuth1KeyStep S b.q_total) (kont u) st)).run l) := by
        simp [gapSigEufCmaFullImpl, primBaseImpl, QueryImpl.liftTarget,
          simulateQ_bind, StateT.run_bind, StateT.run_monadLift]
      simp only [FgGapDh.simulateQ_run_query_inl, hqR, bind_assoc]
      exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ =>
        ih u rem (h_cont u) s st l hRel)
    | inr gq =>
      rcases hRel with hS | ⟨hFg, hParty, hPk, hG, hWon, ⟨hst, hBase, hInv⟩, hl⟩
      · rw [evalDist_authSigPre1Key_safe_eq_zero S P k (some sk) _ s hS]; exact zero_le
      rcases hQb with ⟨h_abs | h_pos, h_cont⟩
      · exact absurd rfl h_abs
      cases rem with
      | zero => omega
      | succ rem' =>
        simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
        subst hBase
        rw [FgGapDh.simulateQ_run_query_inr, runWithGdhSignStep_query_inr]
        simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
        exact sigAuth1Key_step_le S P hP b k sk C gq rem' hst st l hFg hParty hPk hG hWon hInv hl
          (fun y => (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (AuthState S) ProbComp) + pqxdhAuthSigPreImpl1Key k (some sk) S P)
              (kont y.1)).run y.2 >>= fun (_, s') => pure (hasBadSigAuthAt S P k s'))
          (fun z => (simulateQ (gapSigEufCmaFullImpl P P.isValidDhTriple sk)
              (runWithGdhSignStep (sigAuth1KeyStep S b.q_total) (kont z.1.1) z.1.2)).run z.2 >>=
            fun res => pure (sigAuth1KeyWinBool P sk res))
          (fun r s' hS => evalDist_authSigPre1Key_safe_eq_zero S P k (some sk) (kont r) s' hS)
          (fun r s' hW hG' => evalDist_authSigPre1Key_won_eq_zero S P k sk (some sk) (kont r) s'
            hW hG')
          (fun y l1 l2 h => sigAuth1KeySimVal_anti P sk b.q_total (kont y.1) y.2 l1 l2 h)
          (fun r s' st' l' hR => ih r rem' (h_cont r) s' st' l' hR)
          (fun r st' l' hW => one_le_sigAuth1KeySimVal_of_won P sk b.q_total (kont r) st' l' hW)

/-- Per-principal one-key `Auth` bad-signature bound from `Auth1KeySigCoupling`. -/
theorem authSig1KeyPerKBound_of_coupling (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (k : ℕ) (hC : ∀ sk : Bytes, sk.length = 32 → Auth1KeySigCoupling S P b k sk) :
    authSig1KeyPerKBound S P b A k := by
  unfold authSig1KeyPerKBound
  rw [authSig1KeyPerK_lhs_noOpk_eq_exact,
    evalDist_authSigPerK_lhs_eq_preSample S P hP k A.1 (hasBadSigAuthAt S P k),
    gapSigEufCmaExp_eq_fullImpl]
  unfold sigReductionAuth1KeyAt sigReductionAuth1KeyRunAt
  dsimp only
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk hSk => ?_)
  have hvSk : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
  have C := hC sk hvSk
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_gapSigEufCmaFullImpl_unifGdhSign_run,
    simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_authSigPre1Key_le_sigAuth1KeySimVal S P hP b k sk C A.1.run b.q_total
    (QueryBounded.auth_total A.2) (AuthState.empty S secb)
    (SigAuth1KeySimState.empty S secb k (P.sigPkGen sk)) []
    (Or.inr ⟨rfl, rfl, rfl, authSigGood1Key_empty S P k sk secb, rfl,
      ⟨AuthFgCutoffState.empty S secb, rfl, C.inv_empty secb⟩,
      fun _ h => False.elim (List.not_mem_nil h)⟩)

end Proofs.SignalPqxdh.Security
