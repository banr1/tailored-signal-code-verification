/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.RedProg2Sim
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrComp
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrStep
import VCVio.EvalDist.Monad.Basic

/-!
# Loop Layer for `shcrReductionAuthProg`

Invariant preservation and evaluation lemmas for the pause check, pre-pause step, and
init/resume/finish components of `shcrReductionAuthProg`, relating the shallow runners to
`RedProg2`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] authCodec

/-! ## Invariant preservation -/

/-- Reduction-state invariant: bounded game lists and fixed target key pair. -/
structure ShInv {S : Setup} (pk sk : Bytes) (n : Nat) (h : AuthShCrState S) : Prop where
  bnd : AuthBaseListsBounded n h.base
  tpk : h.targetPk = pk
  tsk : h.targetSk = sk

theorem ShInv.mono {S : Setup} {pk sk : Bytes} {n m : Nat} {h : AuthShCrState S} (hnm : n ≤ m)
    (hI : ShInv pk sk n h) : ShInv pk sk m h :=
  ⟨hI.bnd.mono hnm, hI.tpk, hI.tsk⟩

theorem liftShCrBasePrim_inv (S : Setup) (pk sk : Bytes) (n : Nat) (h : AuthShCrState S)
    (hI : ShInv pk sk n h) (q : AuthQuery S) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      ((liftShCrBasePrim (S := S) (pqxdhAuthSimImplPrim S q)).run h) := by
  simp only [liftShCrBasePrim, StateT.run]
  exact HoldsOnLeaves.bind (pqxdhAuthSimImplPrim_hol S n q h.base hI.bnd)
    fun p hp => HoldsOnLeaves.pure ⟨hp, hI.tpk, hI.tsk⟩

set_option maxHeartbeats 1000000 in
theorem finishAuthSimBasePrim_bnd (S : Setup) (n : Nat) (sid : SessionId S)
    (b : PreKeyBundleInput) (m0 m1 : Bytes) (ui : UInfo) (ek eph spc ss ct : Bytes)
    (s : AuthState S) (hB : AuthBaseListsBounded n s) :
    HoldsOnLeaves (fun p : AuthResponse × Option (AuthState S) =>
        ∀ b', p.2 = some b' → AuthBaseListsBounded (n + 1) b')
      (finishAuthSimBasePrim S sid b m0 m1 ui ek eph spc ss ct s) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hB
  unfold finishAuthSimBasePrim
  repeat (first
    | (refine HoldsOnLeaves.pure ?_; intro b' hb; cases hb <;> hol_leaf)
    | (refine HoldsOnLeaves.bind (evalHkdfOrRoPrim_hol _ _ _) fun _ _ => ?_)
    | (refine HoldsOnLeaves.bind (evalRootKdfOrRoPrim_hol _ _ _ _) fun _ _ => ?_)
    | (refine HoldsOnLeaves.bind_const _ fun _ => ?_)
    | split
    | (dsimp only))

theorem runAuthShCrSendPrim_inv (S : Setup) (pk sk : Bytes) (n : Nat) (h : AuthShCrState S)
    (hI : ShInv pk sk n h) (sid : SessionId S) (u : Fin S.N_id) (bu : PreKeyBundleInput)
    (m0 m1 : Bytes) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      ((runAuthShCrSendPrim S sid u bu m0 m1).run h) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  simp only [runAuthShCrSendPrim, StateT.run]
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | ui
  · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun ok => ?_
  split
  · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  refine HoldsOnLeaves.bind_const _ fun enc => ?_
  rcases enc with _ | ⟨ss, ct⟩
  · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
      ShInv pk sk (n + 1) x.2) ⟨hI1.bnd, hI.tpk, hI.tsk⟩
  refine HoldsOnLeaves.bind (finishAuthSimBasePrim_bnd S n _ _ _ _ _ _ _ _ _ _ _ hI.bnd)
    fun p hp => HoldsOnLeaves.pure ?_
  obtain ⟨r, _ | b'⟩ := p
  · exact ⟨hI1.bnd, hI.tpk, hI.tsk⟩
  · exact ⟨hp b' rfl, hI.tpk, hI.tsk⟩

theorem runAuthShCrAcceptPrim_inv (S : Setup) (pk sk : Bytes) (n : Nat) (h : AuthShCrState S)
    (hI : ShInv pk sk n h) (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (q : AuthQuery S) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      ((runAuthShCrAcceptPrim S k j hdr q).run h) := by
  simp only [runAuthShCrAcceptPrim, StateT.run, stApply_bind]
  refine HoldsOnLeaves.bind (liftShCrBasePrim_inv S pk sk n h hI q) fun p hp => ?_
  obtain ⟨r, h'⟩ := p
  simp only [recordAcceptKemGenericPrim]
  split
  · exact HoldsOnLeaves.pure hp
  split
  · exact HoldsOnLeaves.pure hp
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | ss
  · exact HoldsOnLeaves.pure hp
  · exact HoldsOnLeaves.pure ⟨hp.bnd, hp.tpk, hp.tsk⟩

set_option maxHeartbeats 1000000 in
theorem pqxdhAuthShCrPrimImpl_inv (S : Setup) (pk sk : Bytes) (n : Nat) (q : AuthQuery S)
    (h : AuthShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhAuthShCrPrimImpl true S q).run h) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  have hL := liftShCrBasePrim_inv S pk sk n h hI
  have hI0 := hI
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, htp, hts⟩ := hI
  cases q
  case genSPK u j =>
    simp only [pqxdhAuthShCrPrimImpl, runAuthShCrGenSPKPrim, StateT.run, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    split
    · exact hL _
    · split
      · simp only [genSpkTargetAuthPrim]
        split
        · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
            ShInv pk sk (n + 1) x.2) hI1
        split
        swap
        · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
            ShInv pk sk (n + 1) x.2) hI1
        refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.pure ⟨?_, htp, hts⟩
        hol_leaf
      · exact hL _
  case sendOPK u i bu m0 m1 =>
    simp only [pqxdhAuthShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
        ShInv pk sk (n + 1) x.2) hI1
    · exact runAuthShCrSendPrim_inv S pk sk n h hI0 _ u bu m0 m1
  case sendNoOPK u i bu m0 m1 =>
    simp only [pqxdhAuthShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure (P := fun x : AuthResponse × AuthShCrState S =>
        ShInv pk sk (n + 1) x.2) hI1
    · exact runAuthShCrSendPrim_inv S pk sk n h hI0 _ u bu m0 m1
  case recvOPK k j o msg => exact runAuthShCrAcceptPrim_inv S pk sk n h hI0 k j msg.hdr _
  case recvNoOPK k j l msg => exact runAuthShCrAcceptPrim_inv S pk sk n h hI0 k j msg.hdr _
  all_goals exact hL _

/-! ## Pause check -/

def tryPauseMidAux (S : Setup) (sIdx : Nat) (sid : SessionId S) (u : Fin S.N_id)
    (bu : PreKeyBundleInput) (m0 m1 : Bytes) (h : AuthShCrState S) :
    OracleComp PrimBaseSpec (Option (PauseMid S)) := do
  match ← preCheckAuthSimPrim S sid u bu m0 m1 h.base with
  | none => pure none
  | some ui =>
    let ok ← checkBundleSigsPrim S h.base.principals bu
    pure (if !ok then none else if h.sendCount == sIdx then some (sid, bu, m0, m1, ui) else none)

def tryPauseMid (S : Setup) (sIdx : Nat) (q : AuthQuery S) (h : AuthShCrState S) :
    OracleComp PrimBaseSpec (Option (PauseMid S)) :=
  match q with
  | .sendOPK u i bu m0 m1 =>
    if bu.opkB?.isNone then pure none else tryPauseMidAux S sIdx (.sendOPK u i) u bu m0 m1 h
  | .sendNoOPK u i bu m0 m1 =>
    if bu.opkB?.isSome then pure none else tryPauseMidAux S sIdx (.sendNoOPK u i) u bu m0 m1 h
  | _ => pure none

def toPaused {S : Setup} (h : AuthShCrState S)
    (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool) (d : PauseMid S) :
    PausedShCrAuthData S :=
  { sid := d.1, bundle := d.2.1, m0 := d.2.2.1, m1 := d.2.2.2.1, uInfo := d.2.2.2.2, hst := h,
    cont := cont }

theorem tryPauseMidAux_shallow (S : Setup) (sIdx : Nat) (sid : SessionId S) (u : Fin S.N_id)
    (bu : PreKeyBundleInput) (m0 m1 : Bytes) (h : AuthShCrState S)
    (cont : AuthResponse → OracleComp (unifSpec + authSpec S) Bool) :
    Option.map (toPaused h cont) <$> tryPauseMidAux S sIdx sid u bu m0 m1 h =
      (do
        match ← preCheckAuthSimPrim S sid u bu m0 m1 h.base with
        | none => pure none
        | some uInfo =>
          let sigOk ← checkBundleSigsPrim S h.base.principals bu
          if !sigOk then pure none
          else if h.sendCount == sIdx then pure (some ⟨sid, bu, m0, m1, uInfo, h, cont⟩)
          else pure none) := by
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ui
  · simp
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  cases ok
  · simp
  · by_cases hc : (h.sendCount == sIdx) = true <;> simp [hc, toPaused]

theorem tryPauseMid_shallow (S : Setup) (sIdx : Nat) (q : AuthQuery S)
    (cont : (authSpec S).Range q → OracleComp (unifSpec + authSpec S) Bool)
    (h : AuthShCrState S) :
    tryPauseAuthQueryPrim S sIdx q cont h =
      Option.map (toPaused h cont) <$> tryPauseMid S sIdx q h := by
  cases q <;> simp only [tryPauseAuthQueryPrim, tryPauseMid, map_pure, Option.map_none]
  case sendOPK u i bu m0 m1 =>
    split
    · simp
    · rw [tryPauseMidAux_shallow]; rfl
  case sendNoOPK u i bu m0 m1 =>
    split
    · simp
    · rw [tryPauseMidAux_shallow]; rfl

section PauseEval
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ) (sV : Var Γ₁ shcrStTy) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
  (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h) (hB : AuthBaseListsBounded K h.base)
include hs hB

theorem tryPauseOpk_eval (xV : Var Γ₂ sendQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : env.get (h₂.wk xV) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1))))) :
    (tryPauseC S K true sV xV).eval env =
      Option.map pauseToVal <$> tryPauseMid S sIdx (.sendOPK u i b m0 m1) h := by
  unfold tryPauseC
  simp only [letV, bindV, caseOptV, Comp.eval_letC, Comp.eval, Expr.eval, v, hx, hs, Env.get_vs,
    Env.get_vz, Ext.step_wk, Ext.refl_wk, sendGuardE, scBase, shcrStToVal, buOpkB, isSomeE,
    ite_true]
  simp only [tryPauseMid]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  · simp [preKeyBundleToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isNone_some, Bool.not_true, Bool.false_eq_true,
    ite_false]
  set b : PreKeyBundleInput :=
    ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ with hbdef
  erw [preCheckC_eval S K (Env.cons (authStateToVal h.base) env) true Var.vz h.base rfl hB xV
    (.sendOPK u i) u i.val b m0 m1 (by simpa using hx) rfl]
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ui
  · simp []
  simp only [Option.map_some]
  erw [checkSigsC_eval S K _ Var.vz h.base (by simp) Var.vz b rfl hB.principals_le]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  simp only [eval_natEq, scCnt, scSIdx, Expr.eval,
    Env.get_vs]
  erw [hs]
  cases ok
  · simp
  · by_cases hc : h.sendCount = sIdx
    · simp [hc, shcrStToVal]
    · simp [hc, shcrStToVal]

theorem tryPauseNoOpk_eval (xV : Var Γ₂ sendQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hx : env.get (h₂.wk xV) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1))))) :
    (tryPauseC S K false sV xV).eval env =
      Option.map pauseToVal <$> tryPauseMid S sIdx (.sendNoOPK u i b m0 m1) h := by
  unfold tryPauseC
  simp only [letV, bindV, caseOptV, Comp.eval_letC, Comp.eval, Expr.eval, v, hx, hs, Env.get_vs,
    Env.get_vz, Ext.step_wk, Ext.refl_wk, sendGuardE, scBase, shcrStToVal, buOpkB, isSomeE,
    Bool.false_eq_true, ↓reduceIte]
  simp only [tryPauseMid]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  case some => simp [preKeyBundleToVal]
  simp only [preKeyBundleToVal, bundleV, Option.isSome_none, Bool.false_eq_true, ite_false]
  set b : PreKeyBundleInput := ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩
    with hbdef
  erw [preCheckC_eval S K (Env.cons (authStateToVal h.base) env) false Var.vz h.base rfl hB xV
    (.sendNoOPK u i) u i.val b m0 m1 (by simpa using hx) rfl]
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ui
  · simp []
  simp only [Option.map_some]
  erw [checkSigsC_eval S K _ Var.vz h.base (by simp) Var.vz b rfl hB.principals_le]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  simp only [eval_natEq, scCnt, scSIdx, Expr.eval,
    Env.get_vs]
  erw [hs]
  cases ok
  · simp
  · by_cases hc : h.sendCount = sIdx
    · simp [hc, shcrStToVal]
    · simp [hc, shcrStToVal]

end PauseEval

theorem pauseCheckC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ]
    [h₂ : Ext Γ₂ Δ] (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : AuthShCrState S) (sIdx : Nat)
    (chosen : Bytes) (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h)
    (hB : AuthBaseListsBounded K h.base) (qV : Var Γ₂ authQueryTy) (q : AuthQuery S)
    (hq : env.get (h₂.wk qV) = authQueryToVal q) :
    (pauseCheckC S K sV qV).eval env = Option.map pauseToVal <$> tryPauseMid S sIdx q h := by
  unfold pauseCheckC
  cases q <;> simp only [caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq,
    authQueryToVal]
  case sendOPK u i bu m0 m1 =>
    exact tryPauseOpk_eval S K _ _ h sIdx chosen (by simpa using hs) hB _ u i bu m0 m1 (by simp)
  case sendNoOPK u i bu m0 m1 =>
    exact tryPauseNoOpk_eval S K _ _ h sIdx chosen (by simpa using hs) hB _ u i bu m0 m1 (by simp)
  all_goals simp [Comp.eval, Expr.eval, tryPauseMid]

/-! ## Pre-pause step -/

/-- One pre-pause step: pause (outputting `bundle.pqspkB`) or run the simulator handler. -/
def stepMid (S : Setup) (sIdx : Nat) (q : AuthQuery S) (h : AuthShCrState S) :
    OracleComp PrimBaseSpec
      ((AuthResponse × AuthShCrState S) ⊕ (Bytes × (PauseMid S × AuthShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhAuthShCrPrimImpl true S q).run h

theorem shcrPreC_eval (S : Setup) (Q K n : Nat) (q : AuthQuery S) (h : AuthShCrState S)
    (sIdx : Nat) (chosen : Bytes) (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (shcrReductionAuthProg S Q K).handlePre.eval
        (.cons (shcrStToVal sIdx chosen h) (.cons (authQueryToVal q) .nil)) =
      Sum.map (encSCS sIdx chosen) (Prod.map id (Prod.map pauseToVal (shcrStToVal sIdx chosen))) <$>
        stepMid S sIdx q h := by
  have hK : AuthBaseListsBounded K h.base := hB.mono (by omega)
  dsimp only [shcrReductionAuthProg, authCodec]
  simp only [shcrPreC, bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ h sIdx chosen rfl hK _ q rfl]
  simp only [stepMid, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcrPostC_eval S K n _ _ _ q h sIdx chosen (by simp) (by simp) hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, m0, m1, ui⟩ := d
    simp [Expr.eval, v, pauseToVal, shcrStToVal, preKeyBundleToVal]

def Gsh (S : Setup) :
    Option Bytes × RedProg2State (authSpec S) Bool (PauseMid S) (AuthShCrState S) →
      (Bool × AuthShCrState S) ⊕ PausedShCrAuthData S
  | (_, .done a h) => .inl (a, h)
  | (_, .paused _ d h c) => .inr (toPaused h c d)

theorem stepUntilShCr_eq (S : Setup) (sIdx : Nat) (mx : OracleComp (unifSpec + authSpec S) Bool)
    (h : AuthShCrState S) (fuel : Nat) :
    stepUntilShCrFuelAuthPrim S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelAuthPrim S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelAuthPrim]
    rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelAuthPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelAuthPrim]
    rw [OracleComp.construct_query_bind]
    dsimp only
    rw [tryPauseMid_shallow, bind_map_left]
    simp only [stepMid, bind_assoc]
    refine bind_congr fun o => ?_
    rcases o with _ | d
    · simp only [Option.map_none, map_eq_bind_pure_comp, bind_assoc]
      rfl
    · simp only [Option.map_some, pure_bind]
      rfl

theorem runWithFuelShCr_eq (S : Setup) (mx : OracleComp (unifSpec + authSpec S) Bool)
    (h : AuthShCrState S) (fuel : Nat) :
    runWithFuelAuthShCrPrim S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhAuthShCrPrimImpl true S q).run s) mx fuel h := by
  have := runWithFuelPrim_char false (fun q s => (pqxdhAuthShCrPrimImpl true S q).run s) id
    (fun mx fuel h => runWithFuelAuthShCrPrim S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelAuthShCrPrim]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelAuthShCrPrim]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelAuthShCrPrim]; rw [OracleComp.construct_query_bind]) mx fuel h
  rw [this, id_map]

/-! ## Init, resume, and finish evaluation -/

theorem shcrResume_eval (S : Setup) (Q K : Nat) (d : PauseMid S) (h : AuthShCrState S)
    (sIdx : Nat) (chosen ss ct : Bytes) (hB : AuthBaseListsBounded K h.base) :
    (shcrReductionAuthProg S Q K).resume.eval
        (.cons (shcrStToVal sIdx chosen h) (.cons (pauseToVal d) (.cons (ss, ct) .nil))) =
      encSCS sIdx d.2.1.pqspkB <$>
        postKemAuthPrim S d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 h ss ct := by
  obtain ⟨sid, bu, m0, m1, ui⟩ := d
  dsimp only [shcrReductionAuthProg, authCodec]
  simp only [shcrResumeC, letV, bindV, Comp.eval_letC, Comp.eval,
    Expr.eval, v, Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, scBase, shcrStToVal,
    postKemAuthPrim, eval_sampleBytes32,
    sampleScalar32, sampleCoins32, SignalPqxdh.Security.embedUnif, map_eq_bind_pure_comp,
    bind_assoc]
  refine bind_congr fun ek => bind_congr fun eph => bind_congr fun spc => ?_
  erw [finishC_eval S K _ Var.vz h.base rfl hB Var.vz sid bu m0 m1 ui rfl Var.vz ek eph spc rfl
    Var.vz ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun o => ?_
  simp only [Function.comp_apply, pure_bind]
  erw [shcrFinC_eval S _ Var.vz h sIdx chosen rfl _ sid rfl _ bu.pqspkB rfl Var.vz ss ct rfl
    Var.vz o rfl]
  simp only [pure_bind]
  rcases o with ⟨r, _ | b'⟩ <;>
    simp [applyShCrFinish, encSCS, shcrStToVal, pauseToVal, preKeyBundleToVal]

theorem shcrFinish_eval (S : Setup) (Q K : Nat) (a : Bool) (h : AuthShCrState S) (sIdx : Nat)
    (chosen ss ct : Bytes) :
    (shcrReductionAuthProg S Q K).finish.eval
        (.cons (shcrStToVal sIdx chosen h) (.cons a (.cons (ss, ct) .nil))) =
      extractCollidingKemCtPrim Q h.targetPk h.targetSk chosen ct ss h.recvKemRecs := by
  dsimp only [shcrReductionAuthProg, authCodec]
  exact shcrExtractC_eval S _ Q Var.vz Var.vz h sIdx chosen ss ct rfl rfl

def initSh (S : Setup) (secb : Bool) (bIdx : Nat) (pk sk : Bytes) : AuthShCrState S where
  base := AuthState.empty S secb
  targetBIdx? := some bIdx
  targetPk := pk
  targetSk := sk

private theorem embedUnif_sampleIndexRange_congr {α : Type} {N : Nat} (hN : 0 < N)
    (f g : Nat → OracleComp PrimBaseSpec α) (hfg : ∀ j < N, f j = g j) :
    (embedUnif (sampleIndexRange N) >>= f) = (embedUnif (sampleIndexRange N) >>= g) := by
  simp only [SignalPqxdh.Security.embedUnif, sampleIndexRange, hN, ↓reduceDIte,
    liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  exact bind_congr fun j => hfg j.val j.isLt

theorem shcrInit_eval (S : Setup) (Q K : Nat) (pk sk : Bytes) :
    (shcrReductionAuthProg S Q K).init.eval (.cons (pk, sk) .nil) =
      if S.N_spk_tot * S.N_send_tot = 0 then (do
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal 0 pk (initSh S secb 0 pk sk)))
      else (do
        let uIdx ← embedUnif (sampleIndexRange S.N_id)
        let jIdx ← embedUnif (sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (sampleIndexRange S.N_send_tot)
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal sIdx pk
          (initSh S secb (uIdx * S.N_recv + jIdx) pk sk))) := by
  dsimp only [shcrReductionAuthProg, authCodec]
  split_ifs with h0
  · simp only [bindV, eval_sampleBool, Comp.eval, Expr.eval, v, emptyAuthStE,
      shcrStToVal, initSh, authStateToVal, AuthState.empty, Option.map, Nat.zero_div, Nat.zero_mod,
      List.map_nil]
    rfl
  · have hPos : 0 < S.N_recv :=
      Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (Nat.pos_of_ne_zero h0))
    simp only [bindV, eval_sampleIndex, eval_sampleBool, Comp.eval]
    refine bind_congr fun uIdx => ?_
    refine embedUnif_sampleIndexRange_congr hPos _ _ fun jIdx hj => ?_
    refine bind_congr fun sIdx => bind_congr fun secb => ?_
    have hDiv : (uIdx * S.N_recv + jIdx) / S.N_recv = uIdx := by
      rw [Nat.add_comm, Nat.add_mul_div_right jIdx uIdx hPos,
        Nat.div_eq_of_lt hj, Nat.zero_add]
    have hMod : (uIdx * S.N_recv + jIdx) % S.N_recv = jIdx := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [Expr.eval, v, emptyAuthStE, shcrStToVal, initSh, authStateToVal,
      AuthState.empty, Option.map, hDiv, hMod, List.map_nil]
    rfl

end SignalPqxdh.Security.ReductionDsl.AuthHs
