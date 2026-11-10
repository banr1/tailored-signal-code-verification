/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrBranch
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.RedProg2Sim
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrEval
import VCVio.EvalDist.Monad.Basic

/-!
# `shcrKeyIndProg` Loop Layer

The two runners of `shcrKeyIndProg` (`TwoStageCostedReduction.eval1` / `TwoStageCostedReduction.eval2`) simulate the
shallow `KemShCr` reduction `shcrReductionKeyIndCore`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp RoKem

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

/-! ## Invariant preservation -/

/-- Reduction-state invariant: bounded game lists and fixed target key pair. -/
structure ShInv {S : Setup} (pk sk : Bytes) (n : ℕ) (h : KeyIndShCrState S) : Prop where
  bnd : KeyIndListsBounded h.base n
  tpk : h.targetPk = pk
  tsk : h.targetSk = sk

theorem ShInv.mono {S : Setup} {pk sk : Bytes} {n m : ℕ} {h : KeyIndShCrState S} (hnm : n ≤ m)
    (hI : ShInv pk sk n h) : ShInv pk sk m h :=
  ⟨hI.bnd.mono hnm, hI.tpk, hI.tsk⟩

theorem liftShCrBasePrim_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (h : KeyIndShCrState S)
    (hI : ShInv pk sk n h) (q : KeyIndQuery S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((liftShCrBasePrim (S := S) (pqxdhKeyIndImplPrim true S q)).run h) := by
  simp only [liftShCrBasePrim, StateT.run]
  exact HoldsOnLeaves.bind (pqxdhKeyIndImplPrim_hol true S n q h.base hI.bnd)
    fun p hp => HoldsOnLeaves.pure ⟨hp, hI.tpk, hI.tsk⟩

theorem finishKeyIndBasePrim_bnd (S : Setup) (n : ℕ) (sid : SessionId S) (b : PreKeyBundleInput)
    (e : PrincipalEntry) (ek ss ct : Bytes) (s : KeyIndState S) (hB : KeyIndListsBounded s n) :
    HoldsOnLeaves (fun p : KeyIndResponse × Option (KeyIndState S) =>
        ∀ b', p.2 = some b' → KeyIndListsBounded b' (n + 1))
      (finishKeyIndBasePrim S sid b e ek ss ct s) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hB
  unfold finishKeyIndBasePrim
  repeat (first
    | (refine HoldsOnLeaves.pure ?_; rintro b' ⟨⟩; khol_leaf)
    | (refine HoldsOnLeaves.bind (evalHkdfOrRoPrim_hol' _ _ _) fun _ _ => ?_)
    | (refine HoldsOnLeaves.bind_const _ fun _ => ?_)
    | split
    | (dsimp only))

theorem runKeyIndShCrInitiatePrim_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (h : KeyIndShCrState S)
    (hI : ShInv pk sk n h) (sid : SessionId S) (u : Fin S.N_id) (bu : PreKeyBundleInput) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((runKeyIndShCrInitiatePrim S sid u bu).run h) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  simp only [runKeyIndShCrInitiatePrim, StateT.run]
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | uE
  · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
    HoldsOnLeaves.bind_const _ fun ok => ?_
  split
  · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
      ShInv pk sk (n + 1) x.2) hI1
  refine HoldsOnLeaves.bind_const _ fun enc => ?_
  rcases enc with _ | ⟨ss, ct⟩
  · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
      ShInv pk sk (n + 1) x.2) ⟨hI1.bnd, hI.tpk, hI.tsk⟩
  refine HoldsOnLeaves.bind (finishKeyIndBasePrim_bnd S n _ _ _ _ _ _ _ hI.bnd) fun p hp => ?_
  refine HoldsOnLeaves.pure ?_
  obtain ⟨r, _ | b'⟩ := p
  · exact ⟨hI1.bnd, hI.tpk, hI.tsk⟩
  · exact ⟨hp b' rfl, hI.tpk, hI.tsk⟩

theorem runKeyIndShCrAcceptPrim_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (h : KeyIndShCrState S)
    (hI : ShInv pk sk n h) (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (q : KeyIndQuery S) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((runKeyIndShCrAcceptPrim S k j hdr q).run h) := by
  simp only [runKeyIndShCrAcceptPrim, StateT.run, kstApply_bind]
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
theorem pqxdhKeyIndShCrPrimImpl_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhKeyIndShCrPrimImpl true S q).run h) := by
  have hI1 : ShInv pk sk (n + 1) h := hI.mono (Nat.le_succ n)
  have hL := liftShCrBasePrim_inv S pk sk n h hI
  have hI0 := hI
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, htp, hts⟩ := hI
  cases q
  case genSPK u j =>
    simp only [pqxdhKeyIndShCrPrimImpl, runKeyIndShCrGenSPKPrim, StateT.run, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    split
    · exact hL _
    · split
      · simp only [genSpkTargetKeyIndPrim]
        split
        · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
            ShInv pk sk (n + 1) x.2) hI1
        split
        swap
        · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
            ShInv pk sk (n + 1) x.2) hI1
        refine HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.bind_const _ fun _ => HoldsOnLeaves.bind_const _ fun _ =>
          HoldsOnLeaves.pure ⟨?_, htp, hts⟩
        khol_leaf
      · exact hL _
  case initiateOPK u i bu =>
    simp only [pqxdhKeyIndShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
        ShInv pk sk (n + 1) x.2) hI1
    · exact runKeyIndShCrInitiatePrim_inv S pk sk n h hI0 _ u bu
  case initiateNoOPK u i bu =>
    simp only [pqxdhKeyIndShCrPrimImpl]
    split
    · exact HoldsOnLeaves.pure (P := fun x : KeyIndResponse × KeyIndShCrState S =>
        ShInv pk sk (n + 1) x.2) hI1
    · exact runKeyIndShCrInitiatePrim_inv S pk sk n h hI0 _ u bu
  case acceptOPK k j o hdr => exact runKeyIndShCrAcceptPrim_inv S pk sk n h hI0 k j hdr _
  case acceptNoOPK k j l hdr => exact runKeyIndShCrAcceptPrim_inv S pk sk n h hI0 k j hdr _
  all_goals exact hL _

/-! ## Pause check -/

abbrev PauseMid (S : Setup) := SessionId S × PreKeyBundleInput × (ℕ × PrincipalEntry)

def encPause {S : Setup} (d : PauseMid S) : pauseTy.denote :=
  (sessionIdToVal d.1, (preKeyBundleToVal d.2.1, (d.2.2.1, principalEntryToVal d.2.2.2)))

def tryPauseMidAux (S : Setup) (sIdx : ℕ) (sid : SessionId S) (u : ℕ) (bu : PreKeyBundleInput)
    (h : KeyIndShCrState S) : OracleComp PrimBaseSpec (Option (PauseMid S)) := do
  match ← preCheckFullPrim S sid u bu h.base with
  | none => pure none
  | some uE =>
    let ok ← checkBundleSigsPrim S h.base.principals bu
    pure (if !ok then none else if h.sendCount == sIdx then some (sid, bu, uE) else none)

def tryPauseMid (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    OracleComp PrimBaseSpec (Option (PauseMid S)) :=
  match q with
  | .initiateOPK u i bu =>
    if bu.opkB?.isNone then pure none else tryPauseMidAux S sIdx (.sendOPK u i) u.val bu h
  | .initiateNoOPK u i bu =>
    if bu.opkB?.isSome then pure none else tryPauseMidAux S sIdx (.sendNoOPK u i) u.val bu h
  | _ => pure none

def toPaused {S : Setup} (h : KeyIndShCrState S)
    (cont : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool) (d : PauseMid S) :
    PausedShCrData S :=
  { sid := d.1, bundle := d.2.1, uEntry := d.2.2.2, hst := h, cont := cont }

theorem tryPauseMidAux_shallow (S : Setup) (sIdx : ℕ) (sid : SessionId S) (u : Fin S.N_id)
    (bu : PreKeyBundleInput) (h : KeyIndShCrState S)
    (cont : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool) :
    Option.map (toPaused h cont) <$> tryPauseMidAux S sIdx sid u.val bu h =
      (do
        match ← preCheckKeyIndPrim S sid u bu h.base with
        | none => pure none
        | some uEntry =>
          let sigOk ← checkBundleSigsPrim S h.base.principals bu
          if !sigOk then pure none
          else if h.sendCount == sIdx then
            pure (some { sid := sid, bundle := bu, uEntry := uEntry, hst := h, cont := cont })
          else pure none) := by
  rw [← preCheckFullPrim_snd]
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨k, e⟩
  · simp
  simp only [Option.map_some, bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  cases ok
  · simp
  · by_cases hc : (h.sendCount == sIdx) = true <;> simp [hc, toPaused]

theorem tryPauseMid_shallow (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S)
    (cont : (keyIndSpec S).Range q → OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) :
    tryPauseKeyIndQueryPrim S sIdx q cont h =
      Option.map (toPaused h cont) <$> tryPauseMid S sIdx q h := by
  cases q <;> simp only [tryPauseKeyIndQueryPrim, tryPauseMid, map_pure, Option.map_none]
  case initiateOPK u i bu =>
    split
    · simp
    · rw [tryPauseMidAux_shallow]; rfl
  case initiateNoOPK u i bu =>
    split
    · simp
    · rw [tryPauseMidAux_shallow]; rfl

section PauseEval
variable (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
  (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : KeyIndShCrState S) (sIdx : ℕ) (chosen : Bytes)
  (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen) (hB : KeyIndListsBounded h.base K)
include hs hB

theorem tryPauseOpk_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (tryPauseC S K true sV xV).eval env =
      Option.map encPause <$> tryPauseMid S sIdx (.initiateOPK u i b) h := by
  unfold tryPauseC
  simp only [letV_eval, bindV, caseOptV, Comp.eval, Expr.eval, v, hx, hs, Env.get_succ',
    Env.get_zero', Ext.step_wk', Ext.refl_wk', initSidE, initGuardE, scBase, shcrStToVal, buOpkB,
    isSomeE, ite_true]
  simp only [tryPauseMid]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  · simp []
  simp only [preKeyBundleToVal, bundleV, Option.isNone_some, Bool.not_true, Bool.false_eq_true,
    ite_false]
  erw [preCheckC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendOPK u i) rfl Var.zero u.val rfl
    Var.zero ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ rfl]
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨k, e⟩
  · simp []
  simp only [Option.map_some, Prod.map, id]
  erw [checkSigsC_eval S K _ Var.zero h.base rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, some (oid, opk), pqspkId, pqspkB, pqspkSig⟩ rfl hB.principals_le]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  simp only [natEq, scCnt, scSIdx, Expr.eval, Env.get_succ', hs, shcrStToVal]
  cases ok
  · simp
  · by_cases hc : (h.sendCount == sIdx) = true
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp at hc; simp [hc, encPause, sessionIdToVal]
    · simp at hc; simp [hc]

theorem tryPauseNoOpk_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (tryPauseC S K false sV xV).eval env =
      Option.map encPause <$> tryPauseMid S sIdx (.initiateNoOPK u i b) h := by
  unfold tryPauseC
  simp only [letV_eval, bindV, caseOptV, Comp.eval, Expr.eval, v, hx, hs, Env.get_succ',
    Env.get_zero', Ext.step_wk', Ext.refl_wk', initSidE, initGuardE, scBase, shcrStToVal, buOpkB,
    isSomeE, ite_false, Bool.false_eq_true]
  simp only [tryPauseMid]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩
  swap
  · simp []
  simp only [preKeyBundleToVal, bundleV, Option.isSome_none, Bool.false_eq_true, ite_false]
  erw [preCheckC_eval S K _ Var.zero h.base rfl hB Var.zero (.sendNoOPK u i) rfl Var.zero u.val rfl
    Var.zero ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩ rfl]
  simp only [tryPauseMidAux, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨k, e⟩
  · simp []
  simp only [Option.map_some, Prod.map, id]
  erw [checkSigsC_eval S K _ Var.zero h.base rfl Var.zero
    ⟨ikB, spkId, spkB, spkSig, none, pqspkId, pqspkB, pqspkSig⟩ rfl hB.principals_le]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ok => ?_
  simp only [natEq, scCnt, scSIdx, Expr.eval, Env.get_succ', hs, shcrStToVal]
  cases ok
  · simp
  · by_cases hc : (h.sendCount == sIdx) = true
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp at hc; simp [hc, encPause, sessionIdToVal]
    · simp at hc; simp [hc]

end PauseEval

theorem pauseCheckC_eval (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ shcrStTy) (env : Env Δ) (h : KeyIndShCrState S) (sIdx : ℕ) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen) (hB : KeyIndListsBounded h.base K)
    (qV : Var Γ₂ keyIndQueryTy) (q : KeyIndQuery S)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q) :
    (pauseCheckC S K sV qV).eval env = Option.map encPause <$> tryPauseMid S sIdx q h := by
  unfold pauseCheckC
  cases q <;> simp only [caseSumV, Comp.eval, Expr.eval, v, hq, keyIndQueryToVal, keyIndQenc,
    Env.get_zero', Ext.refl_wk', tryPauseMid, map_pure, Option.map_none]
  case initiateOPK u i bu =>
    exact tryPauseOpk_eval S K _ _ h sIdx chosen (by exact hs) hB _ u i bu rfl
  case initiateNoOPK u i bu =>
    exact tryPauseNoOpk_eval S K _ _ h sIdx chosen (by exact hs) hB _ u i bu rfl

/-! ## Pre-pause step -/

def stepMid (S : Setup) (sIdx : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S) :
    OracleComp PrimBaseSpec
      ((KeyIndResponse × KeyIndShCrState S) ⊕ (Bytes × (PauseMid S × KeyIndShCrState S))) := do
  match ← tryPauseMid S sIdx q h with
  | some d => pure (.inr (d.2.1.pqspkB, (d, h)))
  | none => Sum.inl <$> (pqxdhKeyIndShCrPrimImpl true S q).run h

theorem shcrPreC_eval (S : Setup) (K n : ℕ) (q : KeyIndQuery S) (h : KeyIndShCrState S)
    (sIdx : ℕ) (chosen : Bytes) (hB : KeyIndListsBounded h.base n) (hn : n + 1 ≤ K) :
    (shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).eval
        (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      Sum.map (encSCS sIdx chosen) (Prod.map id (Prod.map encPause (shcrStToVal · sIdx chosen))) <$>
        stepMid S sIdx q h := by
  have hK : KeyIndListsBounded h.base K := hB.mono (by omega)
  unfold shcrPreC
  simp only [bindV, caseOptV, Comp.eval]
  rw [pauseCheckC_eval S K _ _ h sIdx chosen rfl hK _ q rfl]
  simp only [stepMid, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun o => ?_
  rcases o with _ | d
  · simp only [Option.map_none, Expr.eval]
    rw [shcrPostC_eval S K n _ _ _ q h sIdx chosen rfl rfl hB hn]
    simp [map_eq_bind_pure_comp, Expr.eval, v]
  · obtain ⟨sid, bu, k, e⟩ := d
    simp [Expr.eval, v, encPause, shcrStToVal, preKeyBundleToVal]

def Gsh (S : Setup) :
    Option Bytes × RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S) →
      (Bool × KeyIndShCrState S) ⊕ PausedShCrData S
  | (_, .done a h) => .inl (a, h)
  | (_, .paused _ d h c) => .inr (toPaused h c d)

theorem stepUntilShCr_eq (S : Setup) (sIdx : ℕ) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    stepUntilShCrFuelKeyIndPrim S sIdx mx h fuel =
      Gsh S <$> stepUntilPauseFuel false (stepMid S sIdx) mx fuel h := by
  refine stepUntilPauseFuel_char false (stepMid S sIdx) (Gsh S)
    (fun mx fuel h => stepUntilShCrFuelKeyIndPrim S sIdx mx h fuel) ?_ ?_ ?_ ?_ mx fuel h
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilShCrFuelKeyIndPrim]
    rw [OracleComp.construct_query_bind]
  · intro gq k s
    simp only [stepUntilShCrFuelKeyIndPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilShCrFuelKeyIndPrim]
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

theorem runWithFuelShCr_eq (S : Setup) (mx : OracleComp (unifSpec + keyIndSpec S) Bool)
    (h : KeyIndShCrState S) (fuel : ℕ) :
    runWithFuelKeyIndShCrPrim S mx h fuel =
      runWithFuelPrim false (fun q s => (pqxdhKeyIndShCrPrimImpl true S q).run s) mx fuel h := by
  have := runWithFuelPrim_char false (fun q s => (pqxdhKeyIndShCrPrimImpl true S q).run s) id
    (fun mx fuel h => runWithFuelKeyIndShCrPrim S mx h fuel) (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithFuelKeyIndShCrPrim]; rw [OracleComp.construct_query_bind])
    (fun gq k s => by
      simp only [runWithFuelKeyIndShCrPrim]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithFuelKeyIndShCrPrim]; rw [OracleComp.construct_query_bind]) mx fuel h
  rw [this, id_map]

/-! ## Init, resume, and finish evaluation -/

theorem shcrResumeC_eval (S : Setup) (K : ℕ) (d : PauseMid S) (h : KeyIndShCrState S)
    (sIdx : ℕ) (chosen ss ct : Bytes) (hB : KeyIndListsBounded h.base K) :
    (shcrResumeC S K (Γ₁ := [.prod (B 32) (B 1568)])
      (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
      (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
      (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero).eval
        (.cons (shcrStToVal h sIdx chosen) (.cons (encPause d) (.cons (ss, ct) .nil))) =
      encSCS sIdx d.2.1.pqspkB <$> postKemKeyIndPrim S d.1 d.2.1 d.2.2.2 h ss ct := by
  obtain ⟨sid, bu, k, e⟩ := d
  unfold shcrResumeC
  simp only [letV_eval, bindV, Comp.eval, Expr.eval, v, Env.get_succ', Env.get_zero',
    Ext.step_wk', Ext.refl_wk', scBase, shcrStToVal, encPause, postKemKeyIndPrim,
    sBytes32_eval, sampleScalar32, SignalPqxdh.Security.embedUnif, map_eq_bind_pure_comp,
    bind_assoc]
  refine bind_congr fun ek => ?_
  erw [initFinishC_eval S K _ Var.zero h.base rfl hB Var.zero sid rfl Var.zero bu rfl
    Var.zero k e rfl Var.zero ek rfl Var.zero ss ct rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine (finishKeyIndBasePrim_isSome S _ _ e ek ss ct h.base).bind_congr _ _ fun p hp => ?_
  rcases p with ⟨r, _ | base'⟩
  · simp at hp
  simp [encFin, shcrFinE, applyShCrFinish, encSCS, shcrStToVal, initRecToVal, Expr.eval]

theorem shcrResume_eval (S : Setup) (Q K : ℕ) (d : PauseMid S) (h : KeyIndShCrState S)
    (sIdx : ℕ) (chosen ss ct : Bytes) (hB : KeyIndListsBounded h.base K) :
    (shcrKeyIndProg S Q K).resume.eval
        (.cons (shcrStToVal h sIdx chosen) (.cons (encPause d) (.cons (ss, ct) .nil))) =
      encSCS sIdx d.2.1.pqspkB <$> postKemKeyIndPrim S d.1 d.2.1 d.2.2.2 h ss ct :=
  shcrResumeC_eval S K d h sIdx chosen ss ct hB

theorem shcrExtractC_eval (S : Setup) (Q : ℕ) (a : Bool) (h : KeyIndShCrState S) (sIdx : ℕ)
    (chosen ss ct : Bytes) :
    (shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
      (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
      (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .zero .zero).eval
        (.cons (shcrStToVal h sIdx chosen) (.cons a (.cons (ss, ct) .nil))) =
      extractCollidingKemCtPrim Q h.targetPk h.targetSk chosen ct ss h.recvKemRecs := by
  unfold shcrExtractC
  simp only [bindV, findMV, Comp.eval, Expr.eval, v, Env.get_zero', Ext.step_wk',
    Ext.refl_wk', scRR, scTSk, scTPk, scChosen, shcrStToVal, findML_prim,
    findMPrim_take_map, extractCollidingKemCtPrim, isWinningKemShCrCtPrim, map_eq_bind_pure_comp,
    bind_assoc, Function.comp_def, pure_bind]
  refine bind_congr2 (congrArg (fun p => findMPrim p _) (funext fun r => ?_)) fun o => ?_
  · simp only [qKemDecaps_eval, Expr.eval, recvRecToVal, optBytesEq, eqB_eval, orE_eval, eLet2,
      eCaseOpt, v, Env.get_succ', Env.get_zero', Ext.step_wk', Ext.refl_wk']
    refine bind_congr fun dec => ?_
    rcases dec with _ | d <;> simp [Expr.eval, eLet]
    by_cases h1 : d = ss <;> by_cases h2 : r.kemCt = ct <;> by_cases h3 : chosen = h.targetPk <;>
      simp [h1, h2, h3]
  · rcases o with _ | r <;> simp [eCaseOpt, rrCt, Expr.eval, recvRecToVal]

theorem shcrFinish_eval (S : Setup) (Q K : ℕ) (a : Bool) (h : KeyIndShCrState S) (sIdx : ℕ)
    (chosen ss ct : Bytes) :
    (shcrKeyIndProg S Q K).finish.eval
        (.cons (shcrStToVal h sIdx chosen) (.cons a (.cons (ss, ct) .nil))) =
      extractCollidingKemCtPrim Q h.targetPk h.targetSk chosen ct ss h.recvKemRecs :=
  shcrExtractC_eval S Q a h sIdx chosen ss ct

def initSh (S : Setup) (secb : Bool) (bIdx : ℕ) (pk sk : Bytes) : KeyIndShCrState S where
  base := KeyIndState.empty S secb
  targetBIdx? := some bIdx
  targetPk := pk
  targetSk := sk

private theorem embedUnif_sampleIndexRange_congr {α : Type} {N : ℕ} (hN : 0 < N)
    (f g : ℕ → OracleComp PrimBaseSpec α) (hfg : ∀ j < N, f j = g j) :
    (embedUnif (RoKem.sampleIndexRange N) >>= f) =
      (embedUnif (RoKem.sampleIndexRange N) >>= g) := by
  simp only [SignalPqxdh.Security.embedUnif, RoKem.sampleIndexRange, hN, ↓reduceDIte,
    liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  exact bind_congr fun j => hfg j.val j.isLt

theorem shcrInit_eval (S : Setup) (Q K : ℕ) (pk sk : Bytes) :
    (shcrKeyIndProg S Q K).init.eval (.cons (pk, sk) .nil) =
      if S.N_spk_tot * S.N_send_tot = 0 then (do
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb 0 pk sk) 0 pk))
      else (do
        let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
        let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
        let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
        let secb ← embedUnif ($ᵗ Bool)
        pure ((), shcrStToVal (initSh S secb (uIdx * S.N_recv + jIdx) pk sk) sIdx pk)) := by
  dsimp only [shcrKeyIndProg]
  split_ifs with h0
  · simp only [bindV, Comp.eval, sBool_eval]
    refine bind_congr fun secb => ?_
    simp only [Expr.eval, v, Env.get_zero', Env.get_succ', Ext.refl_wk',
      emptyStE, stMk, shcrStToVal, initSh, keyIndStateToVal, KeyIndState.empty,
      Option.map, Nat.zero_div, Nat.zero_mod, List.map_nil]
  · have hPos : 0 < S.N_recv :=
      Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right (Nat.pos_of_ne_zero h0))
    have hsr : ∀ n, FgGapDh.sampleIndexRange n = RoKem.sampleIndexRange n := fun _ => rfl
    simp only [bindV, Comp.eval, sIndex_eval, sBool_eval, hsr]
    refine bind_congr fun uIdx => ?_
    refine embedUnif_sampleIndexRange_congr hPos _ _ fun jIdx hj => ?_
    refine bind_congr fun sIdx => bind_congr fun secb => ?_
    have hDiv : (uIdx * S.N_recv + jIdx) / S.N_recv = uIdx := by
      rw [Nat.add_comm, Nat.add_mul_div_right jIdx uIdx hPos,
        Nat.div_eq_of_lt hj, Nat.zero_add]
    have hMod : (uIdx * S.N_recv + jIdx) % S.N_recv = jIdx := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [Expr.eval, v, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      emptyStE, stMk, shcrStToVal, initSh, keyIndStateToVal, KeyIndState.empty,
      Option.map, hDiv, hMod, List.map_nil]

/-! ## Stage invariants and intermediate adversary -/

theorem stepMid_inv (S : Setup) (sIdx : ℕ) (pk sk : Bytes) (n : ℕ) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (PreStepInvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) n)
      (stepMid S sIdx q h) := by
  unfold stepMid
  refine HoldsOnLeaves.bind_const _ fun o => ?_
  rcases o with _ | d
  · exact HoldsOnLeaves.map _ (pqxdhKeyIndShCrPrimImpl_inv S pk sk n q h hI) fun _ hx => hx
  · exact HoldsOnLeaves.pure ⟨rfl, hI⟩

theorem postKem_inv (S : Setup) (pk sk : Bytes) (n : ℕ) (d : PauseMid S) (h : KeyIndShCrState S)
    (hI : ShInv pk sk n h) (ss ct : Bytes) :
    HoldsOnLeaves (fun x : KeyIndResponse × KeyIndShCrState S => ShInv pk sk (n + 1) x.2)
      (postKemKeyIndPrim S d.1 d.2.1 d.2.2.2 h ss ct) := by
  unfold postKemKeyIndPrim
  refine HoldsOnLeaves.bind_const _ fun ek => ?_
  refine HoldsOnLeaves.bind (finishKeyIndBasePrim_bnd S n _ _ _ _ _ _ _ hI.bnd) fun p hp => ?_
  refine HoldsOnLeaves.pure ?_
  obtain ⟨r, _ | b'⟩ := p
  · exact ⟨hI.bnd.mono (Nat.le_succ n), hI.tpk, hI.tsk⟩
  · exact ⟨hp b' rfl, hI.tpk, hI.tsk⟩

def chosenOf {S : Setup} (pk : Bytes) :
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S) → Bytes
  | .done _ _ => pk
  | .paused _ d _ _ => d.2.1.pqspkB

def midRun (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (ℕ × (Option Bytes ×
      RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :=
  if S.N_spk_tot * S.N_send_tot = 0 then do
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid S 0) A.run b.q_total
      (initSh S secb 0 pk sk)
    pure (0, r)
  else do
    let uIdx ← embedUnif (RoKem.sampleIndexRange S.N_id)
    let jIdx ← embedUnif (RoKem.sampleIndexRange S.N_recv)
    let sIdx ← embedUnif (RoKem.sampleIndexRange S.N_send_tot)
    let secb ← embedUnif ($ᵗ Bool)
    let r ← stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
    pure (sIdx, r)

def toShallow {S : Setup} (st : Bytes × Bytes × ℕ × (Option Bytes ×
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) : ShCrFinishState S :=
  (st.1, st.2.1, chosenOf st.1 st.2.2.2.2, Gsh S st.2.2.2)

def midAdv (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) : KemShCrAdv where
  State := Bytes × Bytes × ℕ × (Option Bytes ×
    RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))
  choosePk := fun pk sk => (fun x => (chosenOf pk x.2.2, (pk, sk, x))) <$> midRun S b A pk sk
  findCollision := fun st => findCollisionKeyIndPrim S b (toShallow st)
  q_prim := primQueryBudget S b

theorem kemShCrExp_mid_core (P : Primitives) (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) :
    KemShCr P (shcrReductionKeyIndCore S b A) = KemShCr P (midAdv S b A) := by
  refine SignalPqxdh.Security.ReductionDsl.AuthHs.kemShCr_eq_of_choosePk_spk_send
    P S (shcrReductionKeyIndCore S b A) (midAdv S b A) toShallow
    (fun bIdx sIdx pk sk => do
      let secb ← embedUnif ($ᵗ Bool)
      let r ← stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk)
      pure (chosenOf pk r.2, (pk, sk, sIdx, r))) ?_ ?_ (fun _ _ _ => rfl)
  · intro pk sk
    simp only [shcrReductionKeyIndCore, choosePkKeyIndPrimAt, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun idx => bind_congr fun secb => ?_
    rw [stepUntilShCr_eq, bind_map_left]
    refine bind_congr fun r => ?_
    obtain ⟨c, st⟩ := r
    rcases st with ⟨a, h⟩ | ⟨q, d, h, k⟩ <;> rfl
  · intro pk sk
    simp only [midAdv, midRun]
    split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

/-! ## DSL adversary and experiment equality -/

def stepPreD (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec ((KeyIndResponse × shcrStTy.denote) ⊕
      (Bytes × (pauseTy.denote × shcrStTy.denote))) :=
  (shcrKeyIndProg S Q K).handlePre.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote ⊕ (Bytes × (pauseTy.denote × shcrStTy.denote))) => match x with
    | .inl (rVal, st') => pure (.inl (valToKeyIndResp rVal, st'))
    | .inr (ch1Val, (pVal, st')) => pure (.inr (ch1Val, (pVal, st')))

theorem stepPreD_eq (S : Setup) (Q K K' : ℕ) (sIdx : ℕ) (pk sk : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk K' h) (hK : K' + 1 ≤ K) :
    stepPreD S Q K q (shcrStToVal h sIdx pk) =
      Sum.map (Prod.map id (shcrStToVal · sIdx pk))
        (Prod.map id (Prod.map encPause (shcrStToVal · sIdx pk))) <$> stepMid S sIdx q h := by
  unfold stepPreD
  have hpre : (shcrKeyIndProg S Q K).handlePre.eval
      (.cons (shcrStToVal h sIdx pk) (.cons (keyIndQueryToVal q) .nil)) = _ :=
    shcrPreC_eval S K K' q h sIdx pk hI.bnd hK
  rw [hpre, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨r, h'⟩ | ⟨c, d, h'⟩
  · have hr : valToKeyIndResp (keyIndRespToVal r) = r := keyIndRdec_keyIndRenc r
    simp only [Function.comp_apply, Sum.map_inl, encSCS, Prod.map, id]
    erw [pure_bind]
    simp only [hr]
  · rfl

theorem eval1_unfold (S : Setup) (Q K : ℕ) (A : KeyIndAdversary S) (pk sk : Bytes)
    (fuel : ℕ) :
    (shcrKeyIndProg S Q K).eval1 (fun _ => A.run) (pk, sk) fuel false =
    (do
      let (_, st0) ← (shcrKeyIndProg S Q K).init.eval (.cons (pk, sk) .nil)
      let r : Option Bytes × RedProg2State (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote ←
          stepUntilPauseFuel false (stepPreD S Q K) A.run fuel st0
      match r with
      | (_, .done aOut stFinal) => do
        let v ← (shcrKeyIndProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
        pure (v, .done aOut stFinal)
      | (c?, .paused gq p stPaused c) =>
        let ch1 := c?.getD pk
        pure (ch1, .paused gq ch1 p stPaused c) :
      OracleComp PrimBaseSpec (Bytes × Mid (keyIndSpec S) Bool pauseTy.denote
        shcrStTy.denote Bytes)) := by
  unfold TwoStageCostedReduction.eval1
  refine bind_congr (m := OracleComp PrimBaseSpec) fun ast0 => ?_
  rcases ast0 with ⟨a, st0⟩
  dsimp only
  rw [GRed2_run1_eq_stepUntilPauseFuel (shcrKeyIndProg S Q K) false pk A.run fuel st0,
    bind_map_left]
  refine bind_congr2 ?_ fun r => ?_
  · congr 1; funext q st; unfold stepPreD
    refine bind_congr fun x => ?_
    rcases x with ⟨_, _⟩ | ⟨_, _, _⟩ <;> rfl
  rcases r with ⟨c?, ⟨aOut, stFinal⟩ | ⟨gq, p, stPaused, c⟩⟩ <;> rfl

theorem initSh_inv (S : Setup) (secb : Bool) (bIdx : ℕ) (pk sk : Bytes) :
    ShInv pk sk 0 (initSh S secb bIdx pk sk) :=
  ⟨by constructor <;> simp [initSh, KeyIndState.empty], rfl, rfl⟩

theorem stepRun_bounded (S : Setup) (Q K Ks sIdx : ℕ) (pk sk : Bytes) (A : KeyIndAdversary S)
    (h0 : KeyIndShCrState S) (hI0 : ShInv pk sk 0 h0)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) Ks)
    (hK : Ks + 1 ≤ K) :
    HoldsOnLeaves (Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) Ks)
        (stepUntilPauseFuel false (stepMid S sIdx) A.run Ks h0) ∧
      stepUntilPauseFuel false (stepPreD S Q K) A.run Ks (shcrStToVal h0 sIdx pk) =
        Prod.map id (RedProg2State.mapSt encPause (shcrStToVal · sIdx pk)) <$>
          stepUntilPauseFuel false (stepMid S sIdx) A.run Ks h0 :=
  stepUntilPauseFuel_map_boundedC false encPause (shcrStToVal · sIdx pk)
    (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) (fun hnm hI => ShInv.mono hnm hI)
    (stepMid S sIdx) (stepPreD S Q K) Ks
    (fun _ q st hn hI => stepPreD_eq S Q K _ sIdx pk sk q st hI (by omega))
    (fun n q st hI => stepMid_inv S sIdx pk sk n q st hI) A.run Ks hA Ks 0 h0 hI0 (by omega)

def encMid {S : Setup} (pk : Bytes)
    (x : ℕ × (Option Bytes × RedProg2State (keyIndSpec S) Bool (PauseMid S) (KeyIndShCrState S))) :
    Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes :=
  match x.2.2 with
  | .done a h => .done a (shcrStToVal h x.1 pk)
  | .paused q d h c => .paused q d.2.1.pqspkB (encPause d) (shcrStToVal h x.1 pk) c

theorem midRun_inv (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total) :
    HoldsOnLeaves
      (fun x => Stage1InvC (ShInv pk sk) (fun d : PauseMid S => d.2.1.pqspkB) b.q_total x.2)
      (midRun S b A pk sk) := by
  unfold midRun
  split_ifs
  · refine HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun_bounded S b.q_total (b.q_total + 1) b.q_total 0 pk sk A
      (initSh S secb 0 pk sk) (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr
  · refine HoldsOnLeaves.bind_const _ fun uIdx => HoldsOnLeaves.bind_const _ fun jIdx =>
      HoldsOnLeaves.bind_const _ fun sIdx => HoldsOnLeaves.bind_const _ fun secb => ?_
    exact HoldsOnLeaves.bind (stepRun_bounded S b.q_total (b.q_total + 1) b.q_total sIdx pk sk A
      (initSh S secb (uIdx * S.N_recv + jIdx) pk sk)
      (initSh_inv _ _ _ _ _) hA le_rfl).1 fun _ hr => HoldsOnLeaves.pure hr

theorem eval1_eq (S : Setup) (Q K : ℕ) (b : QueryBudget) (A : KeyIndAdversary S)
    (pk sk : Bytes)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    (shcrKeyIndProg S Q K).eval1 (fun _ => A.run) (pk, sk) b.q_total false =
    (fun x => (chosenOf pk x.2.2, encMid pk x)) <$> midRun S b A pk sk := by
  have hBody : ∀ bIdx sIdx secb,
      (stepUntilPauseFuel false (stepPreD S Q K) A.run b.q_total
        (shcrStToVal (initSh S secb bIdx pk sk) sIdx pk) >>= fun r =>
        match r with
        | (_, .done aOut stFinal) => do
          let v ← (shcrKeyIndProg S Q K).chDone.eval (.cons stFinal (.cons aOut .nil))
          pure (v, .done aOut stFinal)
        | (c?, .paused gq p stPaused c) =>
          let ch1 := c?.getD pk
          pure (ch1, .paused gq ch1 p stPaused c)) =
      (stepUntilPauseFuel false (stepMid S sIdx) A.run b.q_total
        (initSh S secb bIdx pk sk) >>= fun r =>
        pure (chosenOf pk r.2, encMid pk (sIdx, r))) := by
    intro bIdx sIdx secb
    obtain ⟨hInv, hEq⟩ := stepRun_bounded S Q K b.q_total sIdx pk sk A
      (initSh S secb bIdx pk sk) (initSh_inv _ _ _ _ _) hA hK
    erw [hEq, bind_map_left]
    refine hInv.bind_congr _ _ fun r hr => ?_
    obtain ⟨c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ := r
    · obtain ⟨rfl, hI⟩ := hr
      simp [shcrKeyIndProg, Comp.eval, Expr.eval, shcrStToVal, chosenOf, encMid,
        RedProg2State.mapSt, hI.tpk]
    · obtain ⟨rfl, -⟩ := hr
      rfl
  rw [eval1_unfold, shcrInit_eval]
  unfold midRun
  split_ifs <;> simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · refine bind_congr fun secb => hBody 0 0 secb
  · refine bind_congr fun uIdx => bind_congr fun jIdx => bind_congr fun sIdx =>
      bind_congr fun secb => hBody (uIdx * S.N_recv + jIdx) sIdx secb

def shcrKeyIndDslAdvK (S : Setup) (b : QueryBudget) (K : ℕ) (A : KeyIndAdversary S) :
    KemShCrAdv where
  State := Mid (keyIndSpec S) Bool pauseTy.denote shcrStTy.denote Bytes
  choosePk := fun pk sk =>
    (shcrKeyIndProg S b.q_total K).eval1 (fun _ => A.run) (pk, sk) b.q_total false
  findCollision := fun st ss ct =>
    (shcrKeyIndProg S b.q_total K).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

def stepPostD (S : Setup) (Q K : ℕ) (q : KeyIndQuery S) (st : shcrStTy.denote) :
    OracleComp PrimBaseSpec (KeyIndResponse × shcrStTy.denote) :=
  (shcrKeyIndProg S Q K).handlePost.eval (.cons st (.cons (keyIndQueryToVal q) .nil)) >>=
    fun (x : SCS.denote) => pure (valToKeyIndResp x.1, x.2)

theorem stepPostD_eq (S : Setup) (Q K Ks sIdx : ℕ) (pk sk chosen : Bytes) (q : KeyIndQuery S)
    (h : KeyIndShCrState S) (hI : ShInv pk sk Ks h) (hK : Ks + 1 ≤ K) :
    stepPostD S Q K q (shcrStToVal h sIdx chosen) =
      Prod.map id (shcrStToVal · sIdx chosen) <$> (pqxdhKeyIndShCrPrimImpl true S q).run h := by
  unfold stepPostD
  have hpost : (shcrKeyIndProg S Q K).handlePost.eval
      (.cons (shcrStToVal h sIdx chosen) (.cons (keyIndQueryToVal q) .nil)) =
      encSCS sIdx chosen <$> (pqxdhKeyIndShCrPrimImpl true S q).run h :=
    shcrPostC_eval S K Ks (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero _ q h sIdx chosen rfl rfl hI.bnd hK
  rw [hpost, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  erw [bind_assoc]
  refine bind_congr fun x => ?_
  have hr : valToKeyIndResp (keyIndRespToVal x.1) = x.1 := keyIndRdec_keyIndRenc x.1
  simp only [Function.comp_apply, encSCS, Prod.map, id]
  erw [pure_bind]
  simp only [hr]

theorem eval2_done (S : Setup) (Q K fuel : ℕ) (a : Bool) (st : shcrStTy.denote)
    (ss ct : Bytes) :
    (shcrKeyIndProg S Q K).eval2 (.done a st) (ss, ct) fuel false =
    (shcrKeyIndProg S Q K).finish.eval (.cons st (.cons a (.cons (ss, ct) .nil))) := by
  simp only [TwoStageCostedReduction.eval2, pure_bind]

theorem eval2_paused (S : Setup) (Q K fuel : ℕ) (q : KeyIndQuery S) (ch : Bytes)
    (p : pauseTy.denote) (st : shcrStTy.denote)
    (k : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool)
    (ss ct : Bytes) :
    (shcrKeyIndProg S Q K).eval2 (.paused q ch p st k) (ss, ct) fuel false =
    ((shcrKeyIndProg S Q K).resume.eval (.cons st (.cons p (.cons (ss, ct) .nil))) >>=
      fun (x : SCS.denote) => runWithFuelPrim false (stepPostD S Q K)
        (k (valToKeyIndResp x.1)) fuel x.2 >>= fun (y : Bool × shcrStTy.denote) =>
      (shcrKeyIndProg S Q K).finish.eval (.cons y.2 (.cons y.1 (.cons (ss, ct) .nil)))) := by
  simp only [TwoStageCostedReduction.eval2]
  refine bind_congr fun x => ?_
  rw [runFuel_pqPrimIface_eq_runWithFuelPrim]
  rfl

theorem kemShCrExp_dsl_mid (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    kemShCrExp P (shcrKeyIndDslAdvK S b K A) = kemShCrExp P (midAdv S b A) := by
  refine kemShCrExp_congr P (midAdv S b A) (shcrKeyIndDslAdvK S b K A)
    (fun st => Stage1InvC (ShInv st.1 st.2.1) (fun d : PauseMid S => d.2.1.pqspkB)
      b.q_total st.2.2.2)
    (fun st => encMid st.1 st.2.2) ?_ ?_ ?_
  · intro pk sk
    simp only [shcrKeyIndDslAdvK, midAdv]
    rw [eval1_eq S b.q_total K b A pk sk hA hK, Functor.map_map]
  · intro pk sk
    simp only [midAdv]
    exact HoldsOnLeaves.map _ (midRun_inv S b A pk sk hA) fun _ hx => hx
  · rintro ⟨pk, sk, sIdx, c, ⟨a, h⟩ | ⟨q, d, h, k⟩⟩ ⟨_, hI⟩ ss ct
    · have hI' : ShInv pk sk b.q_total h := hI
      show (shcrKeyIndProg S b.q_total K).eval2
          (.done a (shcrStToVal h sIdx pk)) (ss, ct) b.q_total false =
        findCollisionKeyIndPrim S b (pk, sk, pk, .inl (a, h)) ss ct
      erw [eval2_done, shcrFinish_eval]
      simp only [findCollisionKeyIndPrim, pure_bind, hI'.tpk, hI'.tsk]
    · obtain ⟨n, r, hIn, hnr, hk⟩ := hI
      show (shcrKeyIndProg S b.q_total K).eval2
          (.paused q d.2.1.pqspkB (encPause d) (shcrStToVal h sIdx pk) k) (ss, ct) b.q_total
          false =
        findCollisionKeyIndPrim S b (pk, sk, d.2.1.pqspkB, .inr (toPaused h k d)) ss ct
      erw [eval2_paused, shcrResume_eval S _ K d h sIdx pk ss ct (hIn.bnd.mono (by omega))]
      erw [bind_map_left]
      simp only [findCollisionKeyIndPrim, resumePausedKeyIndPrim, toPaused, bind_assoc]
      refine (postKem_inv S pk sk n d h hIn ss ct).bind_congr _ _ fun p hp => ?_
      obtain ⟨resp, h'⟩ := p
      have hr : valToKeyIndResp (keyIndRespToVal resp) = resp := keyIndRdec_keyIndRenc resp
      dsimp only [encSCS]
      rw [hr]
      obtain ⟨hInvR, hEqR⟩ := runWithFuelPrim_map_bounded false (shcrStToVal · sIdx d.2.1.pqspkB)
        (fun n h => ShInv pk sk n h) (fun hnm hI => ShInv.mono hnm hI)
        (fun q s => (pqxdhKeyIndShCrPrimImpl true S q).run s) (stepPostD S b.q_total K) b.q_total
        (fun q st hI => stepPostD_eq S b.q_total K b.q_total sIdx pk sk _ q st hI hK)
        (fun n q st hI => pqxdhKeyIndShCrPrimImpl_inv S pk sk n q st hI) (k resp) r (hk resp)
        b.q_total (n + 1) h' hp (by omega)
      rw [hEqR, bind_map_left, runWithFuelShCr_eq]
      refine hInvR.bind_congr _ _ fun y hy => ?_
      obtain ⟨a, hf⟩ := y
      dsimp only [Prod.map, id]
      erw [shcrFinish_eval]
      rw [hy.tpk, hy.tsk]

theorem kemShCrExp_shcrKeyIndDslAdvK_of_queryBound (P : Primitives) (S : Setup) (b : QueryBudget)
    (K : ℕ) (A : KeyIndAdversary S)
    (hA : IsQueryBoundP A.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total)
    (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyIndDslAdvK S b K A) = KemShCr P (shcrReductionKeyIndCore S b A) := by
  have hDslMid : KemShCr P (shcrKeyIndDslAdvK S b K A) = KemShCr P (midAdv S b A) := by
    unfold KemShCr
    rw [kemShCrExp_dsl_mid P S b K A hA hK]
  rw [hDslMid, ← kemShCrExp_mid_core]

/-- `KemShCr` adversary built from `shcrKeyIndProg` at handler bound `keyIndLoopBound b`. -/
def shcrKeyIndDslAdv (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrAdv :=
  shcrKeyIndDslAdvK S b (2 * b.q_total + 1) A.1

theorem kemShCrExp_shcrKeyIndDslAdvK (P : Primitives) (S : Setup) (b : QueryBudget) (K : ℕ)
    (A : BoundedAdv (KeyIndAdversary S) b) (hK : b.q_total + 1 ≤ K) :
    KemShCr P (shcrKeyIndDslAdvK S b K A.1) = KemShCr P (shcrReductionKeyInd S b A) := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    have h := A.2.2.2.2.1
    convert h using 1; funext q; cases q <;> rfl
  exact kemShCrExp_shcrKeyIndDslAdvK_of_queryBound P S b K A.1 hA hK

theorem kemShCrExp_shcrKeyIndDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyIndDslAdv S b A) = KemShCr P (shcrReductionKeyInd S b A) :=
  kemShCrExp_shcrKeyIndDslAdvK P S b _ A (by omega)

/-- The DSL `KemShCr` reduction has exactly the advantage of the shallow one. -/
theorem KemShCr_shcrKeyIndDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyIndDslAdv S b A) = KemShCr P (shcrReductionKeyInd S b A) :=
  kemShCrExp_shcrKeyIndDslAdv P S b A

theorem KemShCrReal_shcrKeyIndDslAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCrReal P (shcrKeyIndDslAdv S b A) = KemShCrReal P (shcrReductionKeyInd S b A) :=
  congrArg ENNReal.toReal (KemShCr_shcrKeyIndDslAdv P S b A)

end SignalPqxdh.Security.ReductionDsl.KeyInd
