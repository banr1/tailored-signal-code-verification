/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSig
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Step Evaluation for `sigReductionAuthProg`

Proves that `extractC` evaluates to `extractBundleForgeryPrim` and that every non-signing branch of
`sigStepC` factors through `stepAuthForSigPrim`.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

def sigCoreToVal {S : Setup} (s : SigReductionState (AuthState S)) : sigCoreTy.denote :=
  (s.forgery, (s.targetParty, (s.targetPk, authStateToVal s.gameState)))

def doneVal {S : Setup} (p : AuthResponse × SigReductionState (AuthState S)) : sigStepTy.denote :=
  .inl (authRespToVal p.1, sigCoreToVal p.2)

set_option hygiene false in
macro "sig_unfold" : tactic => `(tactic| simp only [sigStepC, caseSumV, v, Comp.eval_caseSumC_elim,
  Expr.eval, hq, authQueryToVal, authQenc, Sum.elim_inl, Sum.elim_inr, wrapC, bindV, Comp.eval,
  Ext.step_wk, Ext.refl_wk, Env.get_vs, Env.get_vz])

set_option hygiene false in
macro "sig_close" : tactic => `(tactic| simp only [htp, htpk, hf, doneVal, sigCoreToVal,
  map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map])

set_option hygiene false in
macro "sig_subst" : tactic => `(tactic| (
  generalize Env.get env (Ext.wk st) = XS at hst ⊢; subst hst
  generalize Env.get env (Ext.wk tp) = XT at htp ⊢; subst htp
  generalize Env.get env (Ext.wk tpk) = XK at htpk ⊢; subst htpk))

set_option hygiene false in
macro "sig_pre" Q:term:max : tactic => `(tactic| (
  refine ⟨_, (pqxdhAuthSimImplPrim S $Q).run s.gameState,
    fun p => (p.1, {s with gameState := p.2}), ?_, ?_⟩
  rotate_left
  · simp [stepAuthForSigPrim, hf, map_eq_bind_pure_comp]
  sig_unfold))

@[simp] private theorem eval_bytesWiden_33_1536 {Γ : List (Ty pqSig)}
    (a : Expr pqxdhOps Γ (B 33)) (env : Env Γ) :
    Expr.eval (t := B 1569) (.bytesWiden 33 1536 a) env = a.eval env := rfl

theorem extractC_eval (S : Setup) (K : Nat) {Γa Γb Γc Γd Δ : List (Ty pqSig)}
    [ha : Ext Γa Δ] [hb : Ext Γb Δ] [hc : Ext Γc Δ] [hd : Ext Γd Δ] (env : Env Δ)
    (s : AuthState S) (tp : Var Γa .nat) (tpk : Var Γb (B 32)) (st : Var Γc authStateTy)
    (bu : Var Γd preKeyBundleTy) (tpv : Nat) (tpkv : Bytes) (b : PreKeyBundleInput)
    (htp : Env.get env (ha.wk tp) = tpv) (htpk : Env.get env (hb.wk tpk) = tpkv)
    (hst : Env.get env (hc.wk st) = authStateToVal s)
    (hbu : Env.get env (hd.wk bu) = preKeyBundleToVal b) (hK : s.spkBundles.length ≤ K)
    (hPrin : s.principals.length ≤ K) :
    (extractC S K tp tpk st bu).eval env =
      extractBundleForgeryPrim S tpv tpkv s.principals s.spkBundles b none := by
  simp only [extractC, bindV, honestPeerC, v, Comp.eval, Ext.step_wk, bind_assoc]
  rw [findHonestC_eval S env s st (h := hc) hst (hPrin := hPrin)]
  simp only [extractBundleForgeryPrim, isHonestUncorruptedPeerPrim, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def]
  refine bind_congr' (by simp [Expr.eval, hbu, preKeyBundleToVal, bundleV]) (fun f => ?_)
  simp only [Env.get_vs, Env.get_vz, htp, hst, hbu, buSpkB, buSpkSig, buPqspkB,
    buPqspkSig, encEC_eval, encKEM_eval, eval_queryPrim, PTag.dec_sigVerify, SignalPqxdh.LegacyCosted.PTag.enc,
    id_map, eval_bytesWiden_33_1536, Expr.eval_bytesBeq, preKeyBundleToVal,
    bundleV, Expr.eval, eCaseOpt, Expr.eval_caseOpt_elim, eval_natEq, eAny, stSpks, sbSpkPk,
    sbPqspkPk, peCorrupted, authStateToVal, Ext.refl_wk]
  rw [List.take_of_length_le (by simpa using hK)]
  generalize Env.get env (Ext.wk bu) = B at hbu ⊢
  subst hbu
  generalize Env.get env (Ext.wk tpk) = B at htpk ⊢
  subst htpk
  generalize Env.get env (Ext.wk tp) = B at htp ⊢
  subst htp
  simp only [preKeyBundleToVal, bundleV]
  rcases f with _ | ⟨k, e⟩
  · simp [SignalPqxdh.encodeEC, SignalPqxdh.encodeKEM]
  · have h1 : ∀ (k : Nat) (pk : Bytes),
        (List.map (Prod.map id spkBundleEntryToVal) s.spkBundles).any
          (fun x => x.1.1 == k && x.2.2.1 == pk) =
        s.spkBundles.any (fun x => x.1.1 == k && x.2.spkPk == pk) := by
      intro k pk; induction s.spkBundles <;> simp_all
    have h2 : ∀ (k : Nat) (pk : Bytes),
        (List.map (Prod.map id spkBundleEntryToVal) s.spkBundles).any
          (fun x => x.1.1 == k && x.2.2.2.2.2.1 == pk) =
        s.spkBundles.any (fun x => x.1.1 == k && x.2.pqspkPk == pk) := by
      intro k pk; induction s.spkBundles <;> simp_all
    cases hc : e.corrupted <;>
      simp [SignalPqxdh.encodeEC, SignalPqxdh.encodeKEM, List.any_map, Function.comp_def,
        principalEntryToVal, hc]
    all_goals erw [h1, h2]

def targetInitPrin {S : Setup} (s : SigReductionState (AuthState S)) (u : Nat)
    (p : Bytes × Bytes) :
    AuthResponse × SigReductionState (AuthState S) :=
  let e : PrincipalEntry :=
    { secIKA0 := p.1, ikAPk := p.2, secIKAsign := [], ikSignPk := s.targetPk, corrupted := false }
  (.initPrinResp p.2 s.targetPk,
    { s with gameState := { s.gameState with principals := (u, e) :: s.gameState.principals } })

section StepEval
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
  [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
  (s : SigReductionState (AuthState S))

/-- `sigStepC` on a non-`signTwo` query: a common computation `D` with a done-projection `g`. -/
def SigDoneFactor (qv : AuthQuery S) (lhs : OracleComp PrimBaseSpec sigStepTy.denote) : Prop :=
  ∃ (α : Type) (D : OracleComp PrimBaseSpec α)
    (g : α → AuthResponse × SigReductionState (AuthState S)),
    lhs = (doneVal ∘ g) <$> D ∧
    stepAuthForSigPrim S qv s = (fun a => SigStepResultPrim.done (g a).1 (g a).2) <$> D

set_option maxHeartbeats 1000000 in
theorem sigStepC_base (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (q : Var Γ₄ authQueryTy) (qv : AuthQuery S) (hf : s.forgery = none)
    (htp : Env.get env (h₁.wk tp) = s.targetParty)
    (htpk : Env.get env (h₂.wk tpk) = s.targetPk)
    (hst : Env.get env (h₃.wk st) = authStateToVal s.gameState)
    (hq : Env.get env (h₄.wk q) = authQueryToVal qv)
    (hK : AuthBaseListsBounded K s.gameState)
    (hb : ∀ u j, qv = .genSPK u j → u.val ≠ s.targetParty) :
    SigDoneFactor S s qv ((sigStepC S K tp tpk st q).eval env) := by
  cases qv
  case roQuery sec =>
    sig_pre (.roQuery sec)
    rw [roB_eval S K _ s.gameState st .vz sec ?_ rfl hK]
    · sig_close
    · simpa using hst
  case roRootQuery rk dh =>
    sig_pre (.roRootQuery rk dh)
    rw [roRootB_eval S K _ s.gameState st .vz rk dh ?_ rfl hK]
    · sig_close
    · simpa using hst
  case genOPK u j o =>
    sig_pre (.genOPK u j o)
    rw [genOpkB_eval S K _ s.gameState st .vz u j o ?_ rfl hK]
    · sig_close
    · simpa using hst
  case recvOPK k j o msg =>
    sig_pre (.recvOPK k j o msg)
    rw [recvB_eval_opk S K _ s.gameState st .vz k j o msg ?_ rfl hK]
    · sig_close
    · simpa using hst
  case recvNoOPK k j l msg =>
    sig_pre (.recvNoOPK k j l msg)
    rw [recvB_eval_noopk S K _ s.gameState st .vz k j l msg ?_ rfl hK]
    · sig_close
    · simpa using hst
  case registerKey sk =>
    sig_pre (.registerKey sk)
    rw [registerB_eval S _ s.gameState st .vz sk ?_ rfl]
    · sig_close
    · simpa using hst
  case revealDhSecrets =>
    refine ⟨_, (pqxdhAuthSimImplPrim S .revealDhSecrets).run s.gameState,
      fun p => (p.1, {s with gameState := p.2}), ?_, ?_⟩
    · sig_unfold
      simp [Expr.eval, htp, htpk, hst, hf, doneVal, sigCoreToVal, aNone, pqxdhAuthSimImplPrim]
    · simp [stepAuthForSigPrim, hf, map_eq_bind_pure_comp]
  case genSPK u j =>
    have hne := hb u j rfl
    refine ⟨_, (pqxdhAuthSimImplPrim S (.genSPK u j)).run s.gameState,
      fun p => (p.1, {s with gameState := p.2}), ?_, ?_⟩
    rotate_left
    · simp [stepAuthForSigPrim, hf, hne, map_eq_bind_pure_comp]
    sig_unfold
    split
    next h =>
      exfalso; simp [natEq, Expr.eval, htp] at h; exact hne h
    rw [genSpkB_eval S K _ s.gameState st .vz u j ?_ rfl hK]
    · sig_close
    · simpa using hst
  case initPrin u =>
    by_cases hex : s.gameState.principals.any (fun x => x.1 == u.val)
    · refine ⟨_, pure (AuthResponse.noneResp, s), id, ?_, ?_⟩
      · sig_unfold
        rw [ite_eq_left (by
          simp only [eAny, Expr.eval, eval_natEq, stPrin, Env.get_vs, Env.get_vz,
            hst, authStateToVal]
          rw [List.take_of_length_le (by simpa using hK.principals_le)]
          simpa [List.any_map, Function.comp_def] using hex)]
        simp only [Expr.eval, htp, htpk, hst, hf,
          doneVal, sigCoreToVal, aNone, map_pure, Function.comp_def, id]
        rfl
      · simp [stepAuthForSigPrim, hf, hex]
    by_cases ht : u.val = s.targetParty
    · refine ⟨_, (do
          let s0 ← embedUnif sampleScalar32
          let ik ← primQ (.x25519Base s0)
          pure (s0, ik)),
        targetInitPrin s u.val, ?_, ?_⟩
      rotate_left
      · simp [stepAuthForSigPrim, hf, ht, map_eq_bind_pure_comp, targetInitPrin]
        intro x hx; exact hex (List.any_eq_true.mpr ⟨_, hx, by simp [ht]⟩)
      sig_unfold
      rw [ite_eq_right (by
        simp only [eAny, Expr.eval, eval_natEq, stPrin, Env.get_vs, Env.get_vz,
          hst, authStateToVal]
        rw [List.take_of_length_le (by simpa using hK.principals_le)]
        simpa [List.any_map, Function.comp_def] using hex)]
      rw [ite_eq_left (by simp [natEq, Expr.eval, htp, ht])]
      simp only [hst, htp, htpk, aInitPrin, eval_sampleBytes32, eval_queryPrim,
        PTag.dec_x25519Base, SignalPqxdh.LegacyCosted.PTag.enc, id_map, Expr.eval_litBytes, Expr.eval,
        Env.get_vs, Env.get_vz]
      simp [authStateToVal, doneVal, sigCoreToVal, targetInitPrin, sampleScalar32, map_bind,
        principalEntryToVal, hf]
    · refine ⟨_, (pqxdhAuthSimImplPrim S (.initPrin u)).run s.gameState,
        fun p => (p.1, {s with gameState := p.2}), ?_, ?_⟩
      rotate_left
      · simp [stepAuthForSigPrim, hf, hex, ht, map_eq_bind_pure_comp]
      sig_unfold
      rw [ite_eq_right (by
        simp only [eAny, Expr.eval, eval_natEq, stPrin, Env.get_vs, Env.get_vz,
          hst, authStateToVal]
        rw [List.take_of_length_le (by simpa using hK.principals_le)]
        simpa [List.any_map, Function.comp_def] using hex)]
      rw [ite_eq_right (by simp [natEq, Expr.eval, htp, ht])]
      rw [initPrinB_eval S K _ s.gameState st .vz u ?_ rfl hK]
      · sig_close
      · simpa using hst
  case corruptIK u =>
    by_cases ht : u.val = s.targetParty
    · have hfind : ∀ (X : authStateTy.denote) (hX : X = authStateToVal s.gameState),
          List.find? (fun x => x.1 == (u : Nat)) X.2.2.1 =
            (s.gameState.principals.find? (fun x => x.1 == (u : Nat))).map
              (Prod.map id principalEntryToVal) := by
        intro X hX; subst hX; simp [authStateToVal, List.find?_map]
      rcases hfd : s.gameState.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
      · refine ⟨_, pure (AuthResponse.noneResp, s), id, ?_, ?_⟩
        rotate_left
        · have hfd' : s.gameState.principals.find? (fun x => x.1 == s.targetParty) = none :=
            ht ▸ hfd
          simp [stepAuthForSigPrim, hf, ht, hfd']
        sig_unfold
        rw [ite_eq_left (by simp [natEq, Expr.eval, htp, ht])]
        simp only [caseOptV, Comp.eval_caseOptC_elim, eFind, Expr.eval, stPrin, eval_natEq,
          Env.get_vs, Env.get_vz]
        rw [List.take_of_length_le (by simpa [hst, authStateToVal] using hK.principals_le)]
        rw [hfind _ hst, hfd]
        simp only [Option.elim, Comp.eval, Expr.eval, Env.get_vs, htp, htpk, hst, hf,
          doneVal, sigCoreToVal, aNone, map_pure, Function.comp_def, id]
        rfl
      · have hfd' : s.gameState.principals.find? (fun x => x.1 == s.targetParty) = some (i, e) :=
          ht ▸ hfd
        refine ⟨_, pure (), fun _ => (AuthResponse.noneResp, {s with gameState := {s.gameState with
          principals := s.gameState.principals.map (fun x =>
            if x.1 == u.val then (x.1, {x.2 with corrupted := true}) else x)}}), ?_, ?_⟩
        rotate_left
        · simp [stepAuthForSigPrim, hf, ht, hfd']
        sig_unfold
        rw [ite_eq_left (by simp [natEq, Expr.eval, htp, ht])]
        simp only [caseOptV, Comp.eval_caseOptC_elim, eFind, Expr.eval, stPrin, eval_natEq,
          Env.get_vs, Env.get_vz]
        rw [List.take_of_length_le (by simpa [hst, authStateToVal] using hK.principals_le)]
        rw [hfind _ hst, hfd]
        simp only [Option.map_some, Option.elim, Comp.eval, Expr.eval, eMap, Env.get_vs,
          Env.get_vz, htp, htpk, hst, peUpd, peSecIKA0, peIkAPk,
          peSecIKAsign, peIkSignPk, eval_natEq]
        rw [List.take_of_length_le (by simpa [authStateToVal] using hK.principals_le)]
        simp [Expr.eval, authStateToVal, doneVal, sigCoreToVal, aNone, hf, List.map_map,
          Function.comp_def, principalEntryToVal]
        intro a b _; split <;> rfl
    · refine ⟨_, (pqxdhAuthSimImplPrim S (.corruptIK u)).run s.gameState,
        fun p => (p.1, {s with gameState := p.2}), ?_, ?_⟩
      rotate_left
      · simp [stepAuthForSigPrim, hf, ht, map_eq_bind_pure_comp]
      sig_unfold
      rw [ite_eq_right (by simp [natEq, Expr.eval, htp, ht])]
      rw [corruptB_eval S K _ s.gameState st .vz u ?_ rfl hK]
      · sig_close
      · simpa using hst
  case sendOPK u i bu m0 m1 =>
    refine ⟨_, (do
        let fg ← extractBundleForgeryPrim S s.targetParty s.targetPk s.gameState.principals
          s.gameState.spkBundles bu none
        let p ← (pqxdhAuthSimImplPrim S (.sendOPK u i bu m0 m1)).run s.gameState
        pure (fg, p)),
      fun x => (x.2.1, {s with gameState := x.2.2, forgery := x.1}), ?_, ?_⟩
    rotate_left
    · simp [stepAuthForSigPrim, hf, map_eq_bind_pure_comp]
    sig_unfold
    simp only [letV, Comp.eval_letC, Comp.eval, Expr.eval, Env.get_vz]
    rw [extractC_eval S K _ s.gameState tp tpk st .vz s.targetParty s.targetPk bu
      ?_ ?_ ?_ rfl hK.spkBundles_le hK.principals_le]
    rotate_left
    · simpa using htp
    · simpa using htpk
    · simpa using hst
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr' rfl (fun fg => ?_)
    rw [sendB_eval_opk S K _ s.gameState st .vz u i bu m0 m1 ?_ rfl hK]
    · simp only [htp, htpk, Env.get_vs, Env.get_vz,
        doneVal, sigCoreToVal, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
        Prod.map]
    · simpa using hst
  case sendNoOPK u i bu m0 m1 =>
    refine ⟨_, (do
        let fg ← extractBundleForgeryPrim S s.targetParty s.targetPk s.gameState.principals
          s.gameState.spkBundles bu none
        let p ← (pqxdhAuthSimImplPrim S (.sendNoOPK u i bu m0 m1)).run s.gameState
        pure (fg, p)),
      fun x => (x.2.1, {s with gameState := x.2.2, forgery := x.1}), ?_, ?_⟩
    rotate_left
    · simp [stepAuthForSigPrim, hf, map_eq_bind_pure_comp]
    sig_unfold
    simp only [letV, Comp.eval_letC, Comp.eval, Expr.eval, Env.get_vz]
    rw [extractC_eval S K _ s.gameState tp tpk st .vz s.targetParty s.targetPk bu
      ?_ ?_ ?_ rfl hK.spkBundles_le hK.principals_le]
    rotate_left
    · simpa using htp
    · simpa using htpk
    · simpa using hst
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr' rfl (fun fg => ?_)
    rw [sendB_eval_noopk S K _ s.gameState st .vz u i bu m0 m1 ?_ rfl hK]
    · simp only [htp, htpk, Env.get_vs, Env.get_vz,
        doneVal, sigCoreToVal, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
        Prod.map]
    · simpa using hst

end StepEval
end SignalPqxdh.Security.ReductionDsl.AuthHs
