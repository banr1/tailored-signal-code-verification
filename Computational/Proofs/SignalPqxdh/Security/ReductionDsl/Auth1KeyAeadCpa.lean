/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaMid
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaSend
public import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `AeadIndCpa` `ReductionDsl` Program

Defines `aeadCpaRedProg1Key`, obtained from `aeadCpaRedProg` by replacing `.initPrin` with
`initPrin1KeyFixedB`, and proves experiment equivalence with `aeadCpaReductionAuthFixed1Key`
along with static cost, query-count, and `.Bounded` bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp RoKem

section Cpa1KeyBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

def cpaNonSend1KeyC (idx : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (q : Var Γ₃ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ]
    (send : (opk : Bool) → {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] →
      Var Δ' sendQTy → Comp pqxdhOps pqPrimIface Δ' cpaPreTy)
    (inl : {Δ' : List PT} → [Ext Γ₁ Δ'] → Comp pqxdhOps pqPrimIface Δ' (.prod authRespTy cpaStTy) →
      Comp pqxdhOps pqPrimIface Δ' cpaPreTy) : Comp pqxdhOps pqPrimIface Δ cpaPreTy :=
  caseSumV (v q) (fun u => inl (wrapCpa idx (initPrin1KeyFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun u => inl (wrapCpa idx (corruptFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (genSpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (genOpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => send true x) fun q =>
  caseSumV (v q) (fun x => send false x) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (cpaRecvC S K true fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (cpaRecvC S K false fhst x))) fun q =>
  caseSumV (v q) (fun sec => inl (wrapCpa idx (roFixedB K fhst sec))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (roRootFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun _ => inl (.ret (.pair aNone (.pair (v idx) (.pair (.nat 0) (v fhst)))))) fun sk =>
  inl (wrapCpa idx (registerFixedB fhst sk))

def cpaNonSendSlot1KeyC {Γ₄ : List PT} (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (send : (opk : Bool) → {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] → [Ext Γ₃ Δ'] →
      Var Δ' sendQTy → Comp pqxdhOps pqPrimIface Δ' cpaPreTy)
    (inl : {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] →
      Comp pqxdhOps pqPrimIface Δ' (.prod authRespTy cpaStTy) →
      Comp pqxdhOps pqPrimIface Δ' cpaPreTy) : Comp pqxdhOps pqPrimIface Δ cpaPreTy :=
  caseSumV (v q) (fun u => inl (wrapCpaSlot idx ns (initPrin1KeyFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun u => inl (wrapCpaSlot idx ns (corruptFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (genSpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (genOpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => send true x) fun q =>
  caseSumV (v q) (fun x => send false x) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (cpaRecvC S K true fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (cpaRecvC S K false fhst x))) fun q =>
  caseSumV (v q) (fun sec => inl (wrapCpaSlot idx ns (roFixedB K fhst sec))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (roRootFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun _ => inl (.ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst)))))) fun sk =>
  inl (wrapCpaSlot idx ns (registerFixedB fhst sk))

end Cpa1KeyBranches

section Prog1Key

variable (S : Setup) (K : Nat)

def cpaStep1KeyC (allowPause : Bool) : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] cpaPreTy :=
  letV (.fst (.var .zero) : Expr pqxdhOps [cpaStTy, authQueryTy] .nat) fun idx =>
  letV (.fst (.snd (.var (.succ .zero))) :
      Expr pqxdhOps [.nat, cpaStTy, authQueryTy] .nat) fun ns =>
  letV (.snd (.snd (.var (.succ (.succ .zero)))) :
      Expr pqxdhOps [.nat, .nat, cpaStTy, authQueryTy] authHybridStateFixedTy) fun fhst =>
  cpaNonSendSlot1KeyC S K idx ns fhst
    (.succ (.succ (.succ (.succ .zero))) :
      Var [authHybridStateFixedTy, .nat, .nat, cpaStTy, authQueryTy] authQueryTy)
    (fun opk => fun x =>
      bindV (cpaSendSlotB S K opk allowPause idx ns fhst x) fun r =>
      caseSumV (v r)
        (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
        (fun p => if allowPause then
            .ret (.inr (.pair (.fst (v p)) (.pair (.fst (.snd (v p)))
              (.pair (v idx) (.snd (.snd (v p)))))))
          else .ret (.inl (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst)))))))
    (fun m => bindV m fun r => .ret (.inl (v r)))

def cpaPre1KeyC : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] cpaPreTy := cpaStep1KeyC S K true

def cpaPost1KeyC : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] (.prod authRespTy cpaStTy) :=
  bindV (cpaStep1KeyC S K false) fun r =>
  caseSumV (v r) (fun d => .ret (v d)) fun _ =>
    .ret (.pair aNone (.var (.succ (.succ .zero)) : Expr pqxdhOps _ cpaStTy))

/-- `ReductionDsl` program for `aeadCpaReductionAuthFixed1Key S b` at list bound `K`. -/
def aeadCpaRedProg1Key :
    TwoStageCostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool cpaChOutTy (.opt (B 32)) .bool where
  σ          := cpaStTy
  π          := cpaPayloadTy
  init       := cpaInitC S K
  handlePre  := cpaPre1KeyC S K
  chDone     := cpaDefaultChC
  resume     := cpaResumeC
  handlePost := cpaPost1KeyC S K
  finish     := cpaFinishC S K

end Prog1Key

theorem stepAuthOtherPrim1Key_true_eq_of_ne {S : Setup} (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    SignalPqxdh.Security.stepAuthOtherPrim1Key true S q hst =
      SignalPqxdh.Security.stepAuthOtherPrim true S q hst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem stepAuthCpaNonSendPrim1Key_eq_of_ne {S : Setup} (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    stepAuthCpaNonSendPrim1Key S q hst = stepAuthCpaNonSendPrim S q hst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem stepAuthCpaCutoffPrim1Key_eq_of_ne {S : Setup} (cut : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    stepAuthCpaCutoffPrim1Key cut S q hst = stepAuthCpaCutoffPrim cut S q hst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem stepAuthOtherPrim1Key_cpa_initPrin {S : Setup} (u : Fin S.N_id)
    (hst : AuthHybridStateFixed S) (hw : hst.toAuthHybridState.base.hasWonAuth = false) :
    SignalPqxdh.Security.stepAuthOtherPrim1Key true S (.initPrin u) hst =
      AuthSubHops1to3.stepAuthOtherPrim1Key S (.initPrin u) hst := by
  simp only [SignalPqxdh.Security.stepAuthOtherPrim1Key, AuthSubHops1to3.stepAuthOtherPrim1Key, hw,
    Bool.false_eq_true, ite_false]

def stepCpaGen1Key (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec ((AuthResponse × AuthHybridStateFixed S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSendCollapse ap hst <$> cpaSendShOpk S ap idx u i b m0 m1 hst
  | .sendNoOPK u i b m0 m1 => cpaSendCollapse ap hst <$> cpaSendShNoOpk S ap idx u i b m0 m1 hst
  | q' => Sum.inl <$> stepAuthCpaNonSendPrim1Key S q' hst

theorem stepCpaGen1Key_eq_of_ne (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) :
    stepCpaGen1Key S ap idx q hst = stepCpaGen S ap idx q hst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

def stepMidCpa1Key (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec
      (((authSpec S).Range q × AuthHybridStateFixed S) ⊕
        ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSendResToStep <$> cpaSendShOpk S true idx u i b m0 m1 hst
  | .sendNoOPK u i b m0 m1 => cpaSendResToStep <$> cpaSendShNoOpk S true idx u i b m0 m1 hst
  | q' => Sum.inl <$> stepAuthCpaNonSendPrim1Key S q' hst

theorem stepCpaGen1Key_true (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    stepCpaGen1Key S true idx q hst = stepMidCpa1Key S idx q hst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaGen1Key, stepMidCpa1Key]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaGen1Key, stepMidCpa1Key]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
  all_goals rfl

theorem stepCpaGen1Key_false (S : Setup) (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    stepCpaGen1Key S false idx q hst = Sum.inl <$> stepAuthCpaCutoffPrim1Key idx S q hst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaGen1Key, stepAuthCpaCutoffPrim1Key, cpaSendShOpk, runAuthSendCpaCutoffPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> simp [cpaSendCollapse]
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaGen1Key, stepAuthCpaCutoffPrim1Key, cpaSendShNoOpk, runAuthSendCpaCutoffPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> simp [cpaSendCollapse]
  all_goals rfl

theorem cpaStep1KeyC_eval_inr (S : Setup) (K : Nat) (ap : Bool) (sv : cpaStTy.denote) (y : _)
    (qv : authQueryTy.denote) (hq : qv = Sum.inr y) :
    (cpaStep1KeyC S K ap).eval (.cons sv (.cons qv .nil)) =
      (cpaStepC S K ap).eval (.cons sv (.cons qv .nil)) := by
  subst hq
  simp only [cpaStep1KeyC, cpaStepC, cpaNonSendSlot1KeyC, cpaNonSendSlotC, letV, eval_letC,
    caseSumV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]

theorem stepAuthCpaCutoffSlotPrim1Key_eq_of_ne {S : Setup} (cut : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (shst : CpaSlotSt S) :
    stepAuthCpaCutoffSlotPrim1Key cut S q shst = cpaStepCutoffSlotPrim cut S q shst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

def stepCpaSlotGen1Key (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec ((AuthResponse × CpaSlotSt S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))) :=
  match q with
  | .sendOPK u i b m0 m1 =>
    cpaSendSlotCollapse ap shst <$> cpaSendSlotShOpk S ap idx u i b m0 m1 shst
  | .sendNoOPK u i b m0 m1 =>
    cpaSendSlotCollapse ap shst <$> cpaSendSlotShNoOpk S ap idx u i b m0 m1 shst
  | q' => (fun x => Sum.inl (x.1, (shst.1, x.2))) <$> stepAuthCpaNonSendPrim1Key S q' shst.2

theorem stepCpaSlotGen1Key_eq_of_ne (S : Setup) (ap : Bool) (idx : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (shst : CpaSlotSt S) :
    stepCpaSlotGen1Key S ap idx q shst = stepCpaSlotGen S ap idx q shst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

def stepMidCpaSlot1Key (S : Setup) (idx : Nat) (q : AuthQuery S) (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec
      (((authSpec S).Range q × CpaSlotSt S) ⊕
        ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSlotSendResToStep <$> cpaSendSlotShOpk S true idx u i b m0 m1 shst
  | .sendNoOPK u i b m0 m1 =>
    cpaSlotSendResToStep <$> cpaSendSlotShNoOpk S true idx u i b m0 m1 shst
  | q' => (fun x => Sum.inl (x.1, (shst.1, x.2))) <$> stepAuthCpaNonSendPrim1Key S q' shst.2

theorem stepCpaSlotGen1Key_true (S : Setup) (idx : Nat) (q : AuthQuery S) (shst : CpaSlotSt S) :
    stepCpaSlotGen1Key S true idx q shst = stepMidCpaSlot1Key S idx q shst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen1Key, stepMidCpaSlot1Key]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen1Key, stepMidCpaSlot1Key]
    refine congrArg (· <$> _) (funext fun x => ?_)
    rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
  all_goals rfl

theorem stepCpaSlotGen1Key_false (S : Setup) (idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) :
    stepCpaSlotGen1Key S false idx q shst =
      Sum.inl <$> stepAuthCpaCutoffSlotPrim1Key idx S q shst := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen1Key, stepAuthCpaCutoffSlotPrim1Key, cpaSendSlotShOpk,
      runAuthSendCpaCutoffSlotPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      change (cpaTryPauseSendSlotPrim false idx S (.sendOPK u i) u b m0 m1 shst >>= _) =
        (cpaTryPauseSendSlotPrim false idx S (.sendOPK u i) u b m0 m1 shst >>= _)
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> simp [cpaSendSlotCollapse]
  case sendNoOPK u i b m0 m1 =>
    simp only [stepCpaSlotGen1Key, stepAuthCpaCutoffSlotPrim1Key, cpaSendSlotShNoOpk,
      runAuthSendCpaCutoffSlotPrim]
    split
    · simp only [map_pure]; rfl
    · simp only [map_eq_bind_pure_comp, bind_assoc]
      change (cpaTryPauseSendSlotPrim false idx S (.sendNoOPK u i) u b m0 m1 shst >>= _) =
        (cpaTryPauseSendSlotPrim false idx S (.sendNoOPK u i) u b m0 m1 shst >>= _)
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> simp [cpaSendSlotCollapse]
  all_goals
    simp only [stepCpaSlotGen1Key, stepAuthCpaCutoffSlotPrim1Key, map_eq_bind_pure_comp,
      bind_assoc]
    refine bind_congr fun ⟨_, _⟩ => ?_
    simp only [Function.comp_apply, pure_bind]

theorem cpaStep1KeyC_slot_eval (S : Setup) (K : Nat) (ap : Bool) (idx n : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) (hn : n + 1 ≤ K) :
    (cpaStep1KeyC S K ap).eval (.cons (cpaSlotStToVal idx shst) (.cons (authQueryToVal q) .nil)) =
      cpaSlotPreEnc idx <$> stepCpaSlotGen1Key S ap idx q shst := by
  by_cases hq : AuthQuery.NotInitPrin q
  · have hInr : ∃ y, authQueryToVal q = Sum.inr y := by
      cases q <;> first | exact absurd rfl (hq _) | exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := hInr
    rw [cpaStep1KeyC_eval_inr S K ap (cpaSlotStToVal idx shst) y (authQueryToVal q) hy,
      cpaStepC_slot_eval S K ap idx n q shst hI hn,
      stepCpaSlotGen1Key_eq_of_ne S ap idx q hq shst]
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      cases q <;> first | exact ⟨_, rfl⟩ | exact absurd (fun _ h => by cases h) hq
    rcases shst with ⟨ns, hst⟩
    have hB : AuthListsBounded K hst := hI.inv.bnd.mono (by omega)
    simp only [cpaStep1KeyC, cpaNonSendSlot1KeyC, letV, eval_letC, caseSumV, v, Comp.eval,
      Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authQueryToVal, authQenc]
    refine (cpaSlotInl_eval S _ _ _ idx ns ?_ ?_ _ _
      (initPrin1KeyFixedB_eval S K _ _ _ hst u ?_ ?_ hB)).trans ?_
    all_goals first
      | (rw [← stepAuthOtherPrim1Key_cpa_initPrin u hst hI.inv.won]; rfl)
      | rfl

theorem stepAuthCpaNonSendPrim1Key_leaves (S : Setup) (n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst) :
    AllLeaves (fun x => CpaInv (n + 1) x.2) (stepAuthCpaNonSendPrim1Key S q hst) := by
  by_cases hq : AuthQuery.NotInitPrin q
  · rw [stepAuthCpaNonSendPrim1Key_eq_of_ne q hq hst]
    exact stepAuthCpaNonSendPrim_leaves S n q hst hI
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      cases q <;> first | exact ⟨_, rfl⟩ | exact absurd (fun _ h => by cases h) hq
    simp only [stepAuthCpaNonSendPrim1Key, stepAuthOtherPrim1Key_cpa_initPrin u hst hI.won]
    have hI' : CpaInv (n + 1) hst := hI.mono (Nat.le_succ n)
    unfold AuthSubHops1to3.stepAuthOtherPrim1Key; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hI') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hI') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    have hB' : AuthListsBounded (n + 1) hst := hI.bnd.mono (Nat.le_succ n)
    rcases hB' with ⟨hHB', hSalt'⟩
    cases hHB'
    refine AllLeaves.pure ⟨⟨?_, hSalt'⟩, hI.won⟩
    constructor <;> first
      | (simp only [List.length_cons]; exact Nat.succ_le_succ hI.bnd.principals_le)
      | assumption

theorem stepAuthCpaNonSendPrim1Key_ideal_leaves (S : Setup) (n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ n) :
    AllLeaves (fun x => CpaInv (n + 1) x.2 ∧
        x.2.toAuthHybridState.idealSessions.length ≤ n + 1)
      (stepAuthCpaNonSendPrim1Key S q hst) := by
  by_cases hq : AuthQuery.NotInitPrin q
  · rw [stepAuthCpaNonSendPrim1Key_eq_of_ne q hq hst]
    exact stepAuthCpaNonSendPrim_ideal_leaves S n q hst hI hIdeal
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      cases q <;> first | exact ⟨_, rfl⟩ | exact absurd (fun _ h => by cases h) hq
    simp only [stepAuthCpaNonSendPrim1Key, stepAuthOtherPrim1Key_cpa_initPrin u hst hI.won]
    have hLeaf0 : CpaInv (n + 1) hst ∧ hst.toAuthHybridState.idealSessions.length ≤ n + 1 :=
      ⟨hI.mono (Nat.le_succ n), Nat.le_trans hIdeal (Nat.le_succ n)⟩
    unfold AuthSubHops1to3.stepAuthOtherPrim1Key; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hLeaf0) (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hLeaf0) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    have hB' : AuthListsBounded (n + 1) hst := hI.bnd.mono (Nat.le_succ n)
    rcases hB' with ⟨hHB', hSalt'⟩
    cases hHB'
    refine AllLeaves.pure ⟨⟨⟨?_, hSalt'⟩, hI.won⟩, Nat.le_trans hIdeal (Nat.le_succ n)⟩
    constructor <;> first
      | (simp only [List.length_cons]; exact Nat.succ_le_succ hI.bnd.principals_le)
      | assumption

theorem stepAuthCpaCutoffSlotPrim1Key_leaves (S : Setup) (cut n : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) :
    AllLeaves (fun x => CpaSlotInv (n + 1) x.2) (stepAuthCpaCutoffSlotPrim1Key cut S q shst) := by
  by_cases hI' : AuthQuery.NotInitPrin q
  · rw [stepAuthCpaCutoffSlotPrim1Key_eq_of_ne cut q hI' shst]
    exact cpaStepCutoffSlotPrim_leaves S cut n q shst hI
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      cases q <;> first | exact ⟨_, rfl⟩ | exact absurd (fun _ h => by cases h) hI'
    simp only [stepAuthCpaCutoffSlotPrim1Key]
    exact AllLeaves.bind
      (stepAuthCpaNonSendPrim1Key_ideal_leaves S n (.initPrin u) shst.2 hI.inv hI.ideal_le)
      fun ⟨_, _⟩ ⟨hinv, hideal⟩ =>
        AllLeaves.pure ⟨hinv, hideal, Nat.le_trans hI.slot_le (Nat.le_succ n)⟩

theorem stepMidCpaSlot1Key_leaves (S : Setup) (idx n : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) :
    HoldsOnLeaves (PreStepInvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) n)
      (stepMidCpaSlot1Key S idx q shst) := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepMidCpaSlot1Key, cpaSendSlotShOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (cpaTryPauseSendSlotPrim_leaves S true idx n _ u b m0 m1 shst hI).toHoldsOnLeaves
        (fun x hx => cpaSlotSendResToStep_leaf S idx n x hx)
  case sendNoOPK u i b m0 m1 =>
    simp only [stepMidCpaSlot1Key, cpaSendSlotShNoOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (cpaTryPauseSendSlotPrim_leaves S true idx n _ u b m0 m1 shst hI).toHoldsOnLeaves
        (fun x hx => cpaSlotSendResToStep_leaf S idx n x hx)
  all_goals
    exact HoldsOnLeaves.map _
      (stepAuthCpaNonSendPrim1Key_ideal_leaves S n _ shst.2 hI.inv hI.ideal_le).toHoldsOnLeaves
      (fun x ⟨hinv, hideal⟩ => ⟨hinv, hideal, Nat.le_trans hI.slot_le (Nat.le_succ n)⟩)

theorem stepAuthCpaCutoffPrim1Key_leaves (S : Setup) (cut n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst) :
    AllLeaves (fun x => CpaInv (n + 1) x.2) (stepAuthCpaCutoffPrim1Key cut S q hst) := by
  by_cases hI' : AuthQuery.NotInitPrin q
  · rw [stepAuthCpaCutoffPrim1Key_eq_of_ne cut q hI' hst]
    exact stepAuthCpaCutoffPrim_leaves S cut n q hst hI
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI' hne
    exact stepAuthCpaNonSendPrim1Key_leaves S n _ hst hI

theorem stepMidCpa1Key_leaves (S : Setup) (idx n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst) :
    HoldsOnLeaves (PreStepInvP (fun n h => CpaInv n h) (CpaPI S) n) (stepMidCpa1Key S idx q hst) := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepMidCpa1Key, cpaSendShOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (tryPauseAuthCpaSendFixedPrim_leaves S true idx n _ u b m0 m1 hst hI).toHoldsOnLeaves
        (fun x hx => cpaSendResToStep_leaf S n x hx)
  case sendNoOPK u i b m0 m1 =>
    simp only [stepMidCpa1Key, cpaSendShNoOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (tryPauseAuthCpaSendFixedPrim_leaves S true idx n _ u b m0 m1 hst hI).toHoldsOnLeaves
        (fun x hx => cpaSendResToStep_leaf S n x hx)
  all_goals
    exact HoldsOnLeaves.map _ (stepAuthCpaNonSendPrim1Key_leaves S n _ hst hI).toHoldsOnLeaves
      (fun x hx => hx)

theorem stepUntilCpa1Key_eq (S : Setup) (idx : Nat) (mx : OracleComp (unifSpec + authSpec S) Bool)
    (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim1Key idx S false mx fuel hst =
      Gcpa <$> stepUntilPauseFuel false (stepMidCpa1Key S idx) mx fuel hst := by
  refine stepUntilPauseFuel_char false (stepMidCpa1Key S idx) Gcpa
    (fun mx fuel h => stepUntilAuthCpaChallengeFixedPrim1Key idx S false mx fuel h) ?_ ?_ ?_ ?_
    mx fuel hst
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilAuthCpaChallengeFixedPrim1Key]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k s
    simp only [stepUntilAuthCpaChallengeFixedPrim1Key]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilAuthCpaChallengeFixedPrim1Key]
    rw [OracleComp.construct_query_bind]
    cases gq
    case sendOPK u i b m0 m1 =>
      simp only [stepMidCpa1Key, cpaSendShOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
    case sendNoOPK u i b m0 m1 =>
      simp only [stepMidCpa1Key, cpaSendShNoOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
    all_goals
      simp only [stepMidCpa1Key]
      rw [bind_map_left]

theorem runWithPrimStepFuel1Key_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    runWithPrimStepFuel false (stepAuthCpaCutoffPrim1Key idx S) mx fuel hst =
      runWithFuelPrim false (stepAuthCpaCutoffPrim1Key idx S) mx fuel hst := by
  have := runWithFuelPrim_char false (stepAuthCpaCutoffPrim1Key idx S) id
    (fun mx fuel h => runWithPrimStepFuel false (stepAuthCpaCutoffPrim1Key idx S) mx fuel h)
    (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]
      rfl)
    (fun gq k s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind])
    mx fuel hst
  rw [this, id_map]

def GcpaSlot1Key {S : Setup} :
    Option (Bytes × Bytes × Bytes) ×
      RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (CpaSlotSt S) →
    AuthCpaSlotPauseResult S Bool
  | (_, .done a sh) => .done a sh
  | (some c, .paused _ p sh k) => .paused c.1 c.2.1 c.2.2 p sh k
  | (none, .paused _ p sh k) => .paused p.ad p.m0 p.m1 p sh k

theorem stepUntilCpaSlot1Key_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (shst : CpaSlotSt S) :
    stepUntilAuthCpaChallengeSlotPrim1Key idx S false mx fuel shst =
      GcpaSlot1Key <$> stepUntilPauseFuel false (stepMidCpaSlot1Key S idx) mx fuel shst := by
  refine stepUntilPauseFuel_char false (stepMidCpaSlot1Key S idx) GcpaSlot1Key
    (fun mx fuel sh => stepUntilAuthCpaChallengeSlotPrim1Key idx S false mx fuel sh) ?_ ?_ ?_ ?_
    mx fuel shst
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilAuthCpaChallengeSlotPrim1Key]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k s
    simp only [stepUntilAuthCpaChallengeSlotPrim1Key]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilAuthCpaChallengeSlotPrim1Key]
    rw [OracleComp.construct_query_bind]
    cases gq
    case sendOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot1Key, cpaSendSlotShOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        change (tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u b m0 m1 s >>= _) =
          (tryPauseAuthCpaSendSlotPrim true idx S (.sendOPK u i) u b m0 m1 s >>= _)
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    case sendNoOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot1Key, cpaSendSlotShNoOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        change (tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u b m0 m1 s >>= _) =
          (tryPauseAuthCpaSendSlotPrim true idx S (.sendNoOPK u i) u b m0 m1 s >>= _)
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    all_goals
      simp only [stepMidCpaSlot1Key]
      rw [bind_map_left]

theorem runWithPrimStepFuelSlot1Key_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (shst : CpaSlotSt S) :
    runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim1Key idx S) mx fuel shst =
      runWithFuelPrim false (stepAuthCpaCutoffSlotPrim1Key idx S) mx fuel shst := by
  have := runWithFuelPrim_char false (stepAuthCpaCutoffSlotPrim1Key idx S) id
    (fun mx fuel sh => runWithPrimStepFuel false (stepAuthCpaCutoffSlotPrim1Key idx S) mx fuel sh)
    (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]
      rfl)
    (fun gq k s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind])
    mx fuel shst
  rw [this, id_map]

theorem cpaFinish1Key_eval (S : Setup) (K idx : Nat) (c? : Option Bytes) (b' : Bool)
    (hst : AuthHybridStateFixed S) (hB : AuthListsBounded K hst) :
    (aeadCpaRedProg1Key S K).finish.eval (.cons (cpaStToVal idx hst) (.cons b' (.cons c? .nil))) =
      AuthSubHops1to3.finalizeAuthFixedPrim S true b' hst.toAuthHybridState :=
  cpaFinish_eval S K idx c? b' hst hB

theorem cpaInit_slot1Key_eval (S : Setup) (K : Nat) :
    (aeadCpaRedProg1Key S K).init.eval (.cons () .nil) =
      (do
        let idx ← embedUnif (sampleIndexRange (min K S.N_send_tot))
        pure ((), cpaSlotStToVal idx (0, AuthHybridStateFixed.empty S true))) :=
  cpaInit_slot_eval S K

theorem cpaPostStep_slot1Key_eq (S : Setup) (K n idx : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) (hn : n + 1 ≤ K) :
    (do
      let p ← (aeadCpaRedProg1Key S K).handlePost.eval
          (.cons (cpaSlotStToVal idx shst) (.cons ((authCodec S).qenc q) .nil))
      return ((authCodec S).rdec q p.1, p.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × cpaStTy.denote)) =
      Prod.map id (cpaSlotStToVal idx) <$> stepAuthCpaCutoffSlotPrim1Key idx S q shst := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  dsimp only [aeadCpaRedProg1Key, authCodec, cpaPost1KeyC]
  rw [bindV_eval]
  erw [cpaStep1KeyC_slot_eval S K false idx n q shst hI hn, stepCpaSlotGen1Key_false]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun x => ?_
  show (pure (valToAuthResp (authRespToVal x.1), cpaSlotStToVal idx x.2) :
      OracleComp PrimBaseSpec ((authSpec S).Range q × cpaStTy.denote)) =
    pure (x.1, cpaSlotStToVal idx x.2)
  rw [hr]

theorem cpaResume_slot1Key_eval (S : Setup) (K idx : Nat) (c? : Option Bytes)
    (p : AuthCpaPausePayload S) (shst : CpaSlotSt S) :
    (aeadCpaRedProg1Key S K).resume.eval
        (.cons (cpaSlotStToVal idx shst) (.cons (cpaPayloadToVal p) (.cons c? .nil))) =
      pure (authRespToVal (finishAuthCpaSendFixedPure true true p (c?.getD []) shst.2).1,
        cpaSlotStToVal idx
          (idx + 1, (finishAuthCpaSendFixedPure true true p (c?.getD []) shst.2).2)) :=
  cpaResume_slot_eval S K idx c? p shst

theorem cpaFinish_slot1Key_eval (S : Setup) (K idx : Nat) (c? : Option Bytes) (b' : Bool)
    (shst : CpaSlotSt S) (hB : AuthListsBounded K shst.2) :
    (aeadCpaRedProg1Key S K).finish.eval
        (.cons (cpaSlotStToVal idx shst) (.cons b' (.cons c? .nil))) =
      AuthSubHops1to3.finalizeAuthFixedPrim S true b' shst.2.toAuthHybridState :=
  cpaFinish_slot_eval S K idx c? b' shst hB

/-- `AeadIndCpa` adversary obtained by running `aeadCpaRedProg1Key` at capacity and fuel `b.q_total`. -/
def aeadCpaDsl1KeyAdv (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : AeadIndCpaAdv where
  State := Mid (authSpec S) Bool (aeadCpaRedProg1Key S b.q_total).π.denote
    (aeadCpaRedProg1Key S b.q_total).σ.denote cpaChOutTy.denote
  choose := do
    let r ← (aeadCpaRedProg1Key S b.q_total).eval1 (fun _ => A.run) () b.q_total false
    pure (r.1.1, r.1.2.1, r.1.2.2, r.2)
  dist st c? := (aeadCpaRedProg1Key S b.q_total).eval2 st c? b.q_total false
  q_prim := primQueryBudget S b

def FcpaB1Key (S : Setup) (b : QueryBudget) (A : AuthAdversary S) (x : CpaMid S) :
    Bytes × Bytes × Bytes × (aeadCpaDsl1KeyAdv S b A).State :=
  ((x.2.1.getD ([], [0], [0])).1, (x.2.1.getD ([], [0], [0])).2.1,
    (x.2.1.getD ([], [0], [0])).2.2,
    midOfStepUntilPause ([], ([0], [0]))
      (x.2.1, x.2.2.mapSt cpaPayloadToVal (cpaStToVal x.1)))

def cpaSlotOutA1Key {S : Setup} : AuthCpaSlotPauseResult S Bool → Bytes × Bytes × Bytes
  | .paused ad m0 m1 _ _ _ => if m0.length == m1.length then (ad, m0, m1) else ([], [0], [0])
  | .done _ _ => ([], [0], [0])

def FcpaSlotA1Key {S : Setup} (x : CpaSlotMid S) :
    Bytes × Bytes × Bytes × (Nat × AuthCpaSlotPauseResult S Bool) :=
  ((cpaSlotOutA1Key (GcpaSlot1Key x.2)).1, (cpaSlotOutA1Key (GcpaSlot1Key x.2)).2.1,
    (cpaSlotOutA1Key (GcpaSlot1Key x.2)).2.2, (x.1, GcpaSlot1Key x.2))

def FcpaSlotB1Key (S : Setup) (b : QueryBudget) (A : AuthAdversary S) (x : CpaSlotMid S) :
    Bytes × Bytes × Bytes × (aeadCpaDsl1KeyAdv S b A).State :=
  ((x.2.1.getD ([], [0], [0])).1, (x.2.1.getD ([], [0], [0])).2.1,
    (x.2.1.getD ([], [0], [0])).2.2,
    midOfStepUntilPause ([], ([0], [0]))
      (x.2.1, x.2.2.mapSt cpaPayloadToVal (cpaSlotStToVal x.1)))

theorem aeadCpaDsl1KeyAdv_aeadIndCpaExp_slot_eq_core (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total) :
    aeadIndCpaExp P (aeadCpaDsl1KeyAdv S b A) =
      aeadIndCpaExp P
        { State := Nat × AuthCpaSlotPauseResult S Bool
          choose := aeadCpaReductionAuthSlotChoose1Key S b.q_total A
          dist := aeadCpaReductionAuthSlotDist1Key S b.q_total
          q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5 } := by
  have hr : ∀ x, valToAuthResp (authRespToVal x) = x := valToAuthResp_authRespToVal
  have hMono : ∀ {n m : Nat} {st : CpaSlotSt S}, n ≤ m → CpaSlotInv n st → CpaSlotInv m st :=
    fun hnm hI => hI.mono hnm
  have hL : ∀ idx : Nat,
      HoldsOnLeaves (Stage1InvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) b.q_total)
        (stepUntilPauseFuel false (stepMidCpaSlot1Key S idx) A.run b.q_total
          (0, AuthHybridStateFixed.empty S true)) :=
    fun idx =>
      (stepUntilPauseFuel_map_boundedP false id id (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx)
        hMono (stepMidCpaSlot1Key S idx) (stepMidCpaSlot1Key S idx) b.q_total
        (fun _ _ _ _ _ => by simp)
        (fun n q st hI => stepMidCpaSlot1Key_leaves S idx n q st hI) A.run b.q_total hA b.q_total 0
        (0, AuthHybridStateFixed.empty S true) (cpaSlotInv_empty S) (by omega)).1
  let m : OracleComp PrimBaseSpec (CpaSlotMid S) := do
    let idx ← embedUnif (sampleIndexRange (min b.q_total S.N_send_tot))
    let r ← stepUntilPauseFuel false (stepMidCpaSlot1Key S idx) A.run b.q_total
      (0, AuthHybridStateFixed.empty S true)
    pure (idx, r)
  let shallowAdv1Key : AeadIndCpaAdv :=
    { State := Nat × AuthCpaSlotPauseResult S Bool
      choose := aeadCpaReductionAuthSlotChoose1Key S b.q_total A
      dist := aeadCpaReductionAuthSlotDist1Key S b.q_total
      q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5 }
  refine aeadIndCpaExp_congr P shallowAdv1Key (aeadCpaDsl1KeyAdv S b A) m
    (fun x => Stage1InvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S x.1) b.q_total x.2) ?_
    FcpaSlotA1Key (FcpaSlotB1Key S b A) ?_ ?_ ?_ ?_
  · refine HoldsOnLeaves.bind_const _ fun idx => ?_
    exact HoldsOnLeaves.bind (hL idx) fun x hx => HoldsOnLeaves.pure hx
  · show aeadCpaReductionAuthSlotChoose1Key S b.q_total A = _
    simp only [aeadCpaReductionAuthSlotChoose1Key, aeadCpaReductionAuthSlotAtChoose1Key, m,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun idx => ?_
    rw [stepUntilCpaSlot1Key_eq]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨_ | c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩ <;>
      simp only [GcpaSlot1Key, FcpaSlotA1Key, cpaSlotOutA1Key] <;> (try split) <;> rfl
  · show (do
        let r ← (aeadCpaRedProg1Key S b.q_total).eval1 (fun _ => A.run) () b.q_total false
        pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) = _
    simp only [TwoStageCostedReduction.eval1, m]
    erw [cpaInit_slot1Key_eval]
    simp only [bind_assoc, pure_bind, map_bind]
    refine bind_congr fun idx => ?_
    erw [GRed2_run1_eq_stepUntilPauseFuel (aeadCpaRedProg1Key S b.q_total) false ([], ([0], [0]))]
    simp only [bind_map_left]
    refine (congrArg (fun x => x >>= _)
      (stepUntilPauseFuel_map_boundedP false cpaPayloadToVal (cpaSlotStToVal idx)
        (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) hMono (stepMidCpaSlot1Key S idx) _ b.q_total
        ?hstep (fun n q st hI => stepMidCpaSlot1Key_leaves S idx n q st hI) A.run b.q_total hA
        b.q_total 0 (0, AuthHybridStateFixed.empty S true) (cpaSlotInv_empty S)
        (by omega)).2).trans ?_
    case hstep =>
      intro n q st hn hI
      dsimp only [aeadCpaRedProg1Key, authCodec, cpaPre1KeyC]
      erw [cpaStep1KeyC_slot_eval S _ true idx n q st hI hn, stepCpaSlotGen1Key_true]
      refine (bind_map_left _ _ _).trans ?_
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun x => ?_
      rcases x with ⟨r, sh'⟩ | ⟨c, p, sh'⟩
      · show (pure (Sum.inl (valToAuthResp (authRespToVal r), cpaSlotStToVal idx sh')) :
            OracleComp PrimBaseSpec (((authSpec S).Range q × cpaStTy.denote) ⊕
              ((Bytes × Bytes × Bytes) × (cpaPayloadTy.denote × cpaStTy.denote)))) =
          pure (Sum.inl (r, cpaSlotStToVal idx sh'))
        rw [hr]
      · rfl
    · refine (bind_map_left _ _ _).trans ?_
      refine (hL idx).bind_congr _ _ fun x hx => ?_
      rcases x with ⟨c, ⟨a, sh⟩ | ⟨q, p, sh, k⟩⟩
      · obtain ⟨rfl, -⟩ := hx
        rfl
      · obtain ⟨c', n, rr, rfl, -⟩ := hx
        rfl
  · rintro ⟨idx, c, r⟩ hx
    rcases r with ⟨a, sh⟩ | ⟨q, p, sh, k⟩
    · obtain ⟨rfl, -⟩ := hx
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨⟨c1, c2, c3⟩, n, rr, rfl, hP, -, -⟩ := hx
      have h1 : c1 = p.ad := hP.pause.ad_eq
      have h2 : c2 = p.m0 := hP.pause.m0_eq
      have h3 : c3 = p.m1 := hP.pause.m1_eq
      have hl : (c2.length == c3.length) = true := by
        rw [h2, h3, hP.pause.len_eq]; exact beq_self_eq_true _
      simp only [FcpaSlotB1Key, FcpaSlotA1Key, GcpaSlot1Key, cpaSlotOutA1Key, hl, ite_true,
        Option.getD_some]
      exact ⟨trivial, trivial, trivial⟩
  · rintro ⟨idx, c, r⟩ hx c?
    rcases r with ⟨a, sh⟩ | ⟨q, p, sh, k⟩
    · obtain ⟨rfl, hI⟩ := hx
      simp only [aeadCpaDsl1KeyAdv, shallowAdv1Key, FcpaSlotA1Key, FcpaSlotB1Key, GcpaSlot1Key,
        aeadCpaReductionAuthSlotDist1Key]
      simp only [TwoStageCostedReduction.eval2, midOfStepUntilPause, RedProg2State.mapSt,
        resumeAuthCpaAfterChallengeSlotPrim1Key, pure_bind]
      erw [cpaFinish_slot1Key_eval S _ idx c? a sh hI.inv.bnd,
        finalizeAuthFixedPrim_true_eq S a _ hI.inv.won]
    · obtain ⟨⟨c1, c2, c3⟩, n, rr, rfl, hP, hb, hc⟩ := hx
      simp only [aeadCpaDsl1KeyAdv, shallowAdv1Key, FcpaSlotA1Key, FcpaSlotB1Key, GcpaSlot1Key,
        aeadCpaReductionAuthSlotDist1Key]
      simp only [TwoStageCostedReduction.eval2, midOfStepUntilPause, RedProg2State.mapSt,
        resumeAuthCpaAfterChallengeSlotPrim1Key]
      erw [cpaResume_slot1Key_eval]
      have hSlotEq : sh.1 = idx := hP.slot_eq
      have hSlotLe : sh.1 ≤ n := hP.slot_le
      have hIdxLe : idx + 1 ≤ n + 1 := by omega
      have hI' := finishAuthCpaSendFixedPure_slot_inv S n (idx + 1) true true p (c?.getD []) sh.2
        hP.pause.inv hP.ideal_le hIdxLe hP.pause.ro_le hP.pause.root_le
      rcases hfin : finishAuthCpaSendFixedPure true true p (c?.getD []) sh.2 with ⟨resp, h'⟩
      rw [hfin] at hI'
      refine (pure_bind _ _).trans ?_
      erw [runFuel_pqPrimIface_eq_runWithFuelPrim,
        show (authCodec S).rdec q (authRespToVal resp) = resp from hr resp]
      rw [runWithPrimStepFuelSlot1Key_eq]
      refine (congrArg (fun x => x >>= _)
        (runWithFuelPrim_map_boundedP false (cpaSlotStToVal idx) (fun n sh => CpaSlotInv n sh)
          hMono (stepAuthCpaCutoffSlotPrim1Key idx S) _ b.q_total ?hstep
          (fun n q st hI => (stepAuthCpaCutoffSlotPrim1Key_leaves S idx n q st hI).toHoldsOnLeaves)
          (k resp) rr (hc resp) b.q_total (n + 1) (idx + 1, h') hI' (by omega)).2).trans ?_
      case hstep =>
        intro n q st hn hI
        exact cpaPostStep_slot1Key_eq S b.q_total n idx q st hI hn
      · refine (bind_map_left _ _ _).trans ?_
        refine (runWithFuelPrim_map_boundedP false id (fun n sh => CpaSlotInv n sh) hMono
          (stepAuthCpaCutoffSlotPrim1Key idx S) (stepAuthCpaCutoffSlotPrim1Key idx S) b.q_total
          (fun _ _ _ _ _ => by simp)
          (fun n q st hI => (stepAuthCpaCutoffSlotPrim1Key_leaves S idx n q st hI).toHoldsOnLeaves)
          (k resp) rr (hc resp) b.q_total (n + 1) (idx + 1, h') hI' (by omega)).1.bind_congr _ _
          fun y hy => ?_
        obtain ⟨b', fs⟩ := y
        erw [cpaFinish_slot1Key_eval S _ idx c? b' fs hy.inv.bnd,
          finalizeAuthFixedPrim_true_eq S b' _ hy.inv.won]

/-- `aeadCpaDsl1KeyAdv` and `aeadCpaReductionAuthFixed1Key` induce the same `AeadIndCpa` experiment. -/
theorem aeadCpaDsl1KeyAdv_aeadIndCpaExp_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    aeadIndCpaExp P (aeadCpaDsl1KeyAdv S b A.1) =
      aeadIndCpaExp P (aeadCpaReductionAuthFixed1Key S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => q.isRight = true) b.q_total := by
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;> rfl
  exact aeadCpaDsl1KeyAdv_aeadIndCpaExp_slot_eq_core P S b A.1 hA

theorem aeadCpaDsl1KeyAdv_aeadIndCpa_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa P (aeadCpaDsl1KeyAdv S b A.1) = AeadIndCpa P (aeadCpaReductionAuthFixed1Key S b A) := by
  unfold AeadIndCpa; rw [aeadCpaDsl1KeyAdv_aeadIndCpaExp_eq]

section Cpa1KeyCost

variable (S : Setup) (K : Nat)

theorem cpaStep1KeyC_cost_le (ap : Bool) : (cpaStep1KeyC S K ap).cost ≤ (cpaStepC S K ap).cost := by
  simp only [cpaStep1KeyC, cpaStepC, cpaNonSendSlot1KeyC, cpaNonSendSlotC, letV, Comp.letC,
    caseSumV, wrapCpaSlot, bindV, Comp.cost]
  gcongr
  exact initPrin1KeyFixedB_cost_le K _ _

theorem cpaStep1KeyC_queries_le (ap : Bool) (w : pqPrimIface.Tag → ℕ)
    (ws : pqPrimIface.smp.Samp → ℕ) :
    (cpaStep1KeyC S K ap).queries w ws ≤ (cpaStepC S K ap).queries w ws := by
  simp only [cpaStep1KeyC, cpaStepC, cpaNonSendSlot1KeyC, cpaNonSendSlotC, letV, Comp.letC,
    caseSumV, wrapCpaSlot, bindV, Comp.queries]
  gcongr
  exact initPrin1KeyFixedB_queries_le K _ _ w ws

theorem cpaPost1KeyC_cost_le : (cpaPost1KeyC S K).cost ≤ (cpaPostC S K).cost := by
  have h := cpaStep1KeyC_cost_le S K false
  simp only [cpaPost1KeyC, cpaPostC, bindV, Comp.cost]
  gcongr

theorem cpaPost1KeyC_queries_le (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (cpaPost1KeyC S K).queries w ws ≤ (cpaPostC S K).queries w ws := by
  have h := cpaStep1KeyC_queries_le S K false w ws
  simp only [cpaPost1KeyC, cpaPostC, bindV, Comp.queries]
  gcongr

theorem aeadCpaRedProg1Key_totalCost_le (q : Nat) :
    (aeadCpaRedProg1Key S K).totalCost q ≤ (aeadCpaRedProg S K).totalCost q := by
  have h1 : (cpaPre1KeyC S K).cost ≤ (cpaPreC S K).cost := cpaStep1KeyC_cost_le S K true
  have h2 := cpaPost1KeyC_cost_le S K
  simp only [TwoStageCostedReduction.totalCost, aeadCpaRedProg1Key, aeadCpaRedProg]
  gcongr
  exacts [h1, h2]

theorem aeadCpaRedProg1Key_totalQueries_le (w : pqPrimIface.Tag → ℕ)
    (ws : pqPrimIface.smp.Samp → ℕ) (q : Nat) :
    (aeadCpaRedProg1Key S K).totalQueries w ws q ≤ (aeadCpaRedProg S K).totalQueries w ws q := by
  have h1 : (cpaPre1KeyC S K).queries w ws ≤ (cpaPreC S K).queries w ws :=
    cpaStep1KeyC_queries_le S K true w ws
  have h2 := cpaPost1KeyC_queries_le S K w ws
  simp only [TwoStageCostedReduction.totalQueries, aeadCpaRedProg1Key, aeadCpaRedProg]
  gcongr
  exacts [h1, h2]

end Cpa1KeyCost

/-- Step-cost budget for `aeadCpaRedProg1Key`. -/
theorem aeadCpaRedProg1Key_totalCost_budget (S : Setup) (b : QueryBudget) :
    (aeadCpaRedProg1Key S b.q_total).totalCost b.q_total ≤
      SignalPqxdh.Security.stepCostBudget S b :=
  (aeadCpaRedProg1Key_totalCost_le S b.q_total b.q_total).trans
    (aeadCpaRedProg_totalCost_le_security S b)

/-- Primitive-query budget for `aeadCpaRedProg1Key`. -/
theorem aeadCpaRedProg1Key_totalQueries_budget (S : Setup) (b : QueryBudget) :
    (aeadCpaRedProg1Key S b.q_total).totalQueries primW primWS b.q_total ≤ primQueryBudget S b :=
  (aeadCpaRedProg1Key_totalQueries_le S b.q_total primW primWS b.q_total).trans
    (aeadCpaRedProg_totalQueries_le S b)

/-- `aeadCpaDsl1KeyAdv` satisfies `AeadIndCpaAdv.Bounded`. -/
theorem aeadCpaDsl1KeyAdv_bounded (S : Setup) (b : QueryBudget) (A : AuthAdversary S) :
    (aeadCpaDsl1KeyAdv S b A).Bounded := by
  refine ⟨?_, fun st c? => ?_⟩
  · dsimp only [aeadCpaDsl1KeyAdv]
    have h1 := queryBound_eval1 (aeadCpaRedProg1Key S b.q_total)
      (fun q => isPrimQuery₀ q = true) primW primWS pqPrimIface_hw pqPrimIface_hU
      (fun _ => A.run) () b.q_total false
    exact (isQueryBoundP_bind h1 (fun r _ => isQueryBoundP_pure (spec := PrimBaseSpec) _ _ 0)).mono
      (by have := aeadCpaRedProg1Key_totalQueries_budget S b; omega)
  · dsimp only [aeadCpaDsl1KeyAdv]
    exact (queryBound_eval2 (aeadCpaRedProg1Key S b.q_total)
      (fun q => isPrimQuery₀ q = true) primW primWS pqPrimIface_hw pqPrimIface_hU
      st c? b.q_total false).mono (aeadCpaRedProg1Key_totalQueries_budget S b)

end SignalPqxdh.Security.ReductionDsl.AuthAead
