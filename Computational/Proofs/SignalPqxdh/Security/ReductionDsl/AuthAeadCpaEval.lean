/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaShallow
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaSend
import VCVio.EvalDist.Monad.Basic

/-!
# `aeadCpaRedProg` Step Evaluation

Step-evaluation equivalence for `cpaStepC`, the pre- and post-challenge handler of
`aeadCpaRedProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

/-! ## Generalized one-query step -/

def cpaSendCollapse {S : Setup} (ap : Bool) (hst : AuthHybridStateFixed S) :
    CpaSendRes S → (AuthResponse × AuthHybridStateFixed S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))
  | .inl x => .inl x
  | .inr (ad, m0, m1, p, h) => if ap then .inr ((ad, m0, m1), (p, h)) else .inl (.noneResp, hst)

def stepCpaGen (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((AuthResponse × AuthHybridStateFixed S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSendCollapse ap hst <$> cpaSendShOpk S ap idx u i b m0 m1 hst
  | .sendNoOPK u i b m0 m1 => cpaSendCollapse ap hst <$> cpaSendShNoOpk S ap idx u i b m0 m1 hst
  | q' => Sum.inl <$> stepAuthCpaNonSendPrim S q' hst

theorem stepCpaGen_true (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    stepCpaGen S true idx q hst = stepMidCpa S idx q hst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaGen, stepMidCpa]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaGen, stepMidCpa]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
  all_goals rfl

theorem stepCpaGen_false (S : Setup) (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    stepCpaGen S false idx q hst = Sum.inl <$> stepAuthCpaCutoffPrim idx S q hst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaGen, stepAuthCpaCutoffPrim, cpaSendShOpk, runAuthSendCpaCutoffPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> simp [cpaSendCollapse]
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaGen, stepAuthCpaCutoffPrim, cpaSendShNoOpk, runAuthSendCpaCutoffPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> simp [cpaSendCollapse]
  all_goals rfl

def cpaPreEnc {S : Setup} (idx : Nat) :
    (AuthResponse × AuthHybridStateFixed S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S)) →
    cpaPreTy.denote
  | .inl (r, h) => .inl (authRespToVal r, cpaStToVal idx h)
  | .inr (c, (p, h)) => .inr (c, (cpaPayloadToVal p, cpaStToVal idx h))

def cpaSendSlotCollapse {S : Setup} (ap : Bool) (shst : CpaSlotSt S) :
    CpaSlotSendRes S → (AuthResponse × CpaSlotSt S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))
  | .inl x => .inl x
  | .inr (ad, m0, m1, p, sh) =>
    if ap then .inr ((ad, m0, m1), (p, sh)) else .inl (.noneResp, shst)

def stepCpaSlotGen (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec ((AuthResponse × CpaSlotSt S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))) :=
  match q with
  | .sendOPK u i b m0 m1 =>
    cpaSendSlotCollapse ap shst <$> cpaSendSlotShOpk S ap idx u i b m0 m1 shst
  | .sendNoOPK u i b m0 m1 =>
    cpaSendSlotCollapse ap shst <$> cpaSendSlotShNoOpk S ap idx u i b m0 m1 shst
  | q' => (fun x => Sum.inl (x.1, (shst.1, x.2))) <$> stepAuthCpaNonSendPrim S q' shst.2

theorem stepCpaSlotGen_true (S : Setup) (idx : Nat) (q : AuthQuery S) (shst : CpaSlotSt S) :
    stepCpaSlotGen S true idx q shst = stepMidCpaSlot S idx q shst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen, stepMidCpaSlot]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen, stepMidCpaSlot]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
  all_goals rfl

theorem stepCpaSlotGen_false (S : Setup) (idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) :
    stepCpaSlotGen S false idx q shst = Sum.inl <$> cpaStepCutoffSlotPrim idx S q shst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen, cpaStepCutoffSlotPrim, cpaSendSlotShOpk, cpaRunSendCutoffSlotPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> simp [cpaSendSlotCollapse]
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen, cpaStepCutoffSlotPrim, cpaSendSlotShNoOpk, cpaRunSendCutoffSlotPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> simp [cpaSendSlotCollapse]
  all_goals
    simp only [stepCpaSlotGen, cpaStepCutoffSlotPrim, map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun ⟨_, _⟩ => ?_
    simp only [Function.comp_apply, pure_bind]

def cpaSlotPreEnc {S : Setup} (idx : Nat) :
    (AuthResponse × CpaSlotSt S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S)) →
    cpaPreTy.denote
  | .inl (r, sh) => .inl (authRespToVal r, cpaSlotStToVal idx sh)
  | .inr (c, (p, sh)) => .inr (c, (cpaPayloadToVal p, cpaSlotStToVal idx sh))

/-! ## Step evaluation -/

section StepEval

variable (S : Setup) (K : Nat)

theorem cpaInl_eval {Γ₁ Δ : List PT} (idxV : Var Γ₁ .nat) [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (idx : Nat) (hi : Env.get env (h₁.wk idxV) = idx) (m : Comp pqxdhOps pqPrimIface Δ RSF)
    (mx : OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S))
    (hm : m.eval env = Prod.map authRespToVal authHybridStateFixedToVal <$> mx) :
    (bindV (wrapCpa idxV m) fun r => .ret (.inl (v r)) :
      Comp pqxdhOps pqPrimIface Δ cpaPreTy).eval env =
      cpaPreEnc idx <$> (Sum.inl <$> mx :
        OracleComp PrimBaseSpec ((AuthResponse × AuthHybridStateFixed S) ⊕
          ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S)))) := by
  simp only [wrapCpa, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Env.get_succ, hm,
    hi, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h⟩
  rfl

theorem cpaSlotInl_eval {Γ₁ Γ₂ Δ : List PT} (idxV : Var Γ₁ .nat) (nsV : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (idx ns : Nat) (hi : Env.get env (h₁.wk idxV) = idx)
    (hns : Env.get env (h₂.wk nsV) = ns) (m : Comp pqxdhOps pqPrimIface Δ RSF)
    (mx : OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S))
    (hm : m.eval env = Prod.map authRespToVal authHybridStateFixedToVal <$> mx) :
    (bindV (wrapCpaSlot idxV nsV m) fun r => .ret (.inl (v r)) :
      Comp pqxdhOps pqPrimIface Δ cpaPreTy).eval env =
      cpaSlotPreEnc idx <$>
        ((fun x => Sum.inl (x.1, (ns, x.2))) <$> mx :
          OracleComp PrimBaseSpec ((AuthResponse × CpaSlotSt S) ⊕
            ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S)))) := by
  simp only [wrapCpaSlot, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Env.get_succ, hm,
    hi, hns, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h⟩
  rfl

set_option maxHeartbeats 4000000 in
theorem cpaStepC_slot_eval (ap : Bool) (idx n : Nat) (q : AuthQuery S) (shst : CpaSlotSt S)
    (hI : CpaSlotInv n shst) (hn : n + 1 ≤ K) :
    (cpaStepC S K ap).eval (.cons (cpaSlotStToVal idx shst) (.cons (authQueryToVal q) .nil)) =
      cpaSlotPreEnc idx <$> stepCpaSlotGen S ap idx q shst := by
  rcases shst with ⟨ns, hst⟩
  have hB : AuthListsBounded K hst := hI.inv.bnd.mono (by omega)
  have hIdeal : hst.toAuthHybridState.idealSessions.length ≤ K :=
    Nat.le_trans hI.ideal_le (by omega)
  cases q <;>
    simp only [cpaStepC, cpaNonSendSlotC, letV, eval_letC, caseSumV, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authQueryToVal, authQenc]
  case initPrin u =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (initPrinFixedB_eval S K _ _ _ hst u ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.initPrin u) hst hI.inv.won rfl]; rfl)
      | rfl
  case corruptIK u =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (corruptFixedB_eval S K _ _ _ hst u ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.corruptIK u) hst hI.inv.won rfl]; rfl)
      | rfl
  case genSPK u j =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (genSpkFixedB_eval S K _ _ _ hst u j ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.genSPK u j) hst hI.inv.won rfl]; rfl)
      | rfl
  case genOPK u j o =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (genOpkFixedB_eval S K _ _ _ hst u j o ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.genOPK u j o) hst hI.inv.won rfl]; rfl)
      | rfl
  case roQuery sec =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (roFixedB_eval S K _ _ _ hst sec ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.roQuery sec) hst hI.inv.won rfl]; rfl)
      | rfl
  case roRootQuery rk dh =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (roRootFixedB_eval S K _ _ _ hst rk dh ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.roRootQuery rk dh) hst hI.inv.won rfl]; rfl)
      | rfl
  case registerKey sk =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (registerFixedB_eval S _ _ _ hst sk ?_ ?_)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim_cpa_eq S (.registerKey sk) hst hI.inv.won rfl]; rfl)
      | rfl
  case revealDhSecrets =>
    simp only [bindV, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero, pure_bind]
    simp [stepCpaSlotGen, stepAuthCpaNonSendPrim, stepAuthOtherPrim, cpaSlotPreEnc, aNone,
      cpaSlotStToVal, Expr.eval, authRenc]
  case recvOPK k j o msg =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (cpaRecvC_slot_eval_opk S K _ _ _ hst k j o msg ?_ ?_ hB hIdeal)).trans ?_
    all_goals rfl
  case recvNoOPK k j l msg =>
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (cpaRecvC_slot_eval_noopk S K _ _ _ hst k j l msg ?_ ?_ hB hIdeal)).trans ?_
    all_goals rfl
  case sendOPK u i b m0 m1 =>
    rw [bindV_eval]
    refine (congrArg (fun m => m >>= _)
      (cpaSendSlotB_eval_opk S K ap _ _ _ _ _ idx ns hst u i b m0 m1 ?_ ?_ ?_ ?_ hB)).trans ?_
    all_goals first
      | rfl
      | (simp only [stepCpaSlotGen, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
           pure_bind]
         refine bind_congr fun x => ?_
         rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> cases ap <;> rfl)
  case sendNoOPK u i b m0 m1 =>
    rw [bindV_eval]
    refine (congrArg (fun m => m >>= _)
      (cpaSendSlotB_eval_noopk S K ap _ _ _ _ _ idx ns hst u i b m0 m1 ?_ ?_ ?_ ?_ hB)).trans ?_
    all_goals first
      | rfl
      | (simp only [stepCpaSlotGen, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
           pure_bind]
         refine bind_congr fun x => ?_
         rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> cases ap <;> rfl)

end StepEval

end SignalPqxdh.Security.ReductionDsl.AuthAead
