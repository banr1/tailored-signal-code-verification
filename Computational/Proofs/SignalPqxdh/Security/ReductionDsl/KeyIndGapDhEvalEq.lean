/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhGrow
import VCVio.EvalDist.Monad.Basic

/-!
# End-to-End Evaluation Equivalence for `fgKeyIndGapDhProg`

Proves that `(fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)` equals the shallow
`GapDH` reduction `(fgKeyIndGapDhAdv4 S b A).run U V` for every bounded `KeyInd` adversary `A`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.FgGapDh.Ik SignalPqxdh.Security.FgGapDh.Opk
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

/-- With `k` game queries still allowed, every non-truncated state list has at most `K - k` entries. -/
def Inv {S : Setup} (K k : Nat) (st : FgKeyIndSimState S) : Prop :=
  k + st.base.principals.length ≤ K ∧
  k + st.base.spkBundles.length ≤ K ∧
  k + st.base.opkEntries.length ≤ K ∧
  k + st.base.sessions.length ≤ K ∧
  k + st.base.respSessions.length ≤ K ∧
  k + st.base.usedRecvOPK.length ≤ K ∧
  k + st.base.usedRecvNoOPK.length ≤ K ∧
  k + st.base.seenKyberBaseKeys.length ≤ K ∧
  k + st.base.roCache.length ≤ K ∧
  k + st.base.advKeys.length ≤ K ∧
  k + st.rawRoCache.length ≤ K ∧
  k + st.advKeyPows.length ≤ K

theorem Inv.mono {S : Setup} (K k : Nat) (st : FgKeyIndSimState S) (h : Inv K (k + 1) st) :
    Inv K k st := by
  simp only [Inv] at h ⊢; omega

theorem Inv.of_grow {S : Setup} (K k : Nat) (st st' : FgKeyIndSimState S) (h : Inv K (k + 1) st)
    (hg : Grow st st') : Inv K k st' := by
  simp only [Inv, Grow] at h hg ⊢; omega

theorem Inv.empty (S : Setup) (K : Nat) (secb : Bool) :
    Inv K K (_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb) := by
  simp only [Inv, _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty,
    KeyIndState.empty, List.length_nil, Nat.add_zero, Nat.le_refl, and_self]

theorem Inv.bnd {S : Setup} (K k : Nat) (st : FgKeyIndSimState S) (h : Inv K k st) :
    FgSimListsBounded st K := by
  simp only [Inv] at h
  exact ⟨⟨by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩, by omega, by omega⟩

/-- Runner bridge between `simulateQ (handlerImpl h)` and `runWithGdhStep` under a countdown invariant `Inv`. -/
theorem simulateQ_handlerImpl_bind_eq_runWithGdhStep_bind {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {C : GameCodec pqSig GSpec}
    {σ : PT} {σS α β : Type}
    (h : Comp pqxdhOps pqGapDhIface [σ, C.Q] (.prod C.R σ))
    (stepS : (q : ιI) → σS → OracleComp GdhSimSpec (GSpec.Range q × σS))
    (enc : σS → σ.denote) (Inv : Nat → σS → Prop)
    (hMono : ∀ k s, Inv (k + 1) s → Inv k s)
    (hStep : ∀ k q s, Inv (k + 1) s →
      (do let p ← h.eval (.cons (enc s) (.cons (C.qenc q) .nil))
          pure (C.rdec q p.1, p.2)) =
        (fun x => (x.1, enc x.2)) <$> stepS q s)
    (hPres : ∀ k q s, Inv (k + 1) s → ∀ x ∈ support (stepS q s), Inv k x.2)
    (f : α × σ.denote → OracleComp GdhSimSpec β)
    (g : α × σS → OracleComp GdhSimSpec β)
    (hfg : ∀ a s, Inv 0 s → f (a, enc s) = g (a, s))
    (mx : OracleComp (unifSpec + GSpec) α) (qTotal : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) qTotal)
    (s : σS) (hs : Inv qTotal s) :
    ((simulateQ (handlerImpl (C := C) h) mx).run (enc s) >>= f) =
      (runWithGdhStep stepS mx s >>= g) := by
  induction mx using OracleComp.inductionOn generalizing qTotal s with
  | pure a =>
    have h0 : Inv 0 s := by
      clear hMx
      induction qTotal with
      | zero => exact hs
      | succ n ih => exact ih (hMono n s hs)
    simp only [simulateQ_pure, StateT.run_pure, runWithGdhStep, OracleComp.construct_pure,
      pure_bind]
    exact hfg a s h0
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · rcases hMx with ⟨_, hCont⟩
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hCont
      rw [simulateQ_query_bind, StateT.run_bind]
      change (((pqGapDhIface.fwdU uq >>= fun u => pure (u, enc s)) >>= fun x =>
          (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) >>= f) =
        ((liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl uq))) >>= fun u =>
          runWithGdhStep stepS (k u) s) >>= g)
      simp only [pqGapDhIface, pqChalIface, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qTotal (hCont u) s hs
    · rcases hMx with ⟨hFirst, hCont⟩
      have hPos : 0 < qTotal := by
        rcases hFirst with hAbs | hPos
        · exact absurd rfl hAbs
        · exact hPos
      simp only [Sum.isRight_inr, ↓reduceIte] at hCont
      obtain ⟨n, rfl⟩ : ∃ n, qTotal = n + 1 := ⟨qTotal - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hCont
      rw [simulateQ_query_bind, StateT.run_bind]
      change (((do let p ← h.eval (.cons (enc s) (.cons (C.qenc gq) .nil))
                   pure (C.rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) >>= f) =
        ((stepS gq s >>= fun p => runWithGdhStep stepS (k p.1) p.2) >>= g)
      rw [hStep n gq s hs]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      refine bind_congr_of_forall_mem_support _ (fun x hx => ?_)
      exact ih x.1 n (hCont x.1) x.2 (hPres n gq s hs x hx)

def runFrom (S : Setup) (K : Nat) (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdhStateTy.denote) : OracleComp GdhSimSpec Bytes := do
  let (b, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdhHandle S K)) A).run x0
  (gdhFinish S K).eval (.cons s' (.cons b .nil))

theorem runFrom_eq (S : Setup) (K : Nat) (pa : paramsTy.denote)
    (stepS : (q : KeyIndQuery S) → FgKeyIndSimState S →
      OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (hStep : ∀ q st, FgSimListsBounded st K →
      (gdhHandle S K).eval (.cons (pa, simStateToVal st) (.cons (keyIndQueryToVal q) .nil)) =
        encGdhRS pa <$> stepS q st)
    (hGrow : ∀ q st, ∀ x ∈ support (stepS q st), Grow st x.2)
    (ext : FgKeyIndSimState S → OracleComp GdhSimSpec Bytes)
    (hFin : ∀ (a : Bool) st, FgSimListsBounded st K →
      (gdhFinish S K).eval (.cons (pa, simStateToVal st) (.cons a .nil)) = ext st)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K) (secb : Bool) :
    runFrom S K A
      (pa, simStateToVal (_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb)) =
      (do
        let (_, stF) ← runWithGdhStep stepS A
          (_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb)
        ext stF) := by
  unfold runFrom
  refine simulateQ_handlerImpl_bind_eq_runWithGdhStep_bind
    (C := keyIndCodec S) (σ := gdhStateTy) (gdhHandle S K) stepS
    (fun st => (pa, simStateToVal st)) (Inv K) (Inv.mono K)
    (fun k q st h => ?_)
    (fun k q st h x hx => Inv.of_grow K k st x.2 h (hGrow q st x hx))
    (fun p => (gdhFinish S K).eval (.cons p.2 (.cons p.1 .nil)))
    (fun p => ext p.2)
    (fun a st h => hFin a st (Inv.bnd K 0 st h)) A K hA _ (Inv.empty S K secb)
  dsimp only [keyIndCodec, keyIndQueryToVal]
  rw [hStep q st (Inv.bnd K (k + 1) st h)]
  simp only [encGdhRS, keyIndRespToVal, keyIndRdec_keyIndRenc,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

def paramsFlatVal (S : Setup) (U V : Bytes) (idx : Nat) : paramsTy.denote :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then
    paramsDhVal S true (idx / S.N_spk_tot) (idx % S.N_spk_tot) U V
  else if idx < nA + nC then
    let r := idx - nA
    paramsDhVal S false (r / S.N_spk_tot) (r % S.N_spk_tot) U V
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    paramsIkVal S (r / S.N_id) (r % S.N_id) U V
  else
    let r := idx - (nA + nC + nB)
    paramsOpkVal S (r / S.N_opk_tot) (r % S.N_opk_tot) U V

@[simp] theorem initParamsFlat_eval (S : Setup) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (initParamsFlat S U V idx).eval env =
      paramsFlatVal S (U.eval env) (V.eval env) (idx.eval env) := by
  simp only [initParamsFlat, paramsFlatVal, initParamsDh_eval, initParamsIk_eval,
    initParamsOpk_eval, Expr.eval]
  split_ifs <;> simp_all

@[simp] theorem emptySimE_eval {S : Setup} {Γ : List PT} (secb : Expr pqxdhOps Γ .bool) (env : Env Γ) :
    (emptySimE secb).eval env =
      simStateToVal (_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S
        (secb.eval env)) := by
  simp [emptySimE, emptyStE, smMk, stMk, Expr.eval, simStateToVal,
    _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty,
    keyIndStateToVal, KeyIndState.empty]

theorem fgKeyIndGapDhProg_eval_runFrom (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyIndGapDhProg S K).eval (fun _ => A) (U, V) =
      (do
        let idx ← unifGdh (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
        let secb ← unifGdh ($ᵗ Bool)
        runFrom S K A
          (paramsFlatVal S U V idx,
            simStateToVal (FgGapDh.FgKeyIndSimState.empty S secb))) := by
  simp only [CostedReduction.eval, fgKeyIndGapDhProg, initAdv4, bindV, letV_eval, Comp.eval, gPrim_eval,
    sIndex_eval, sBool_eval, initParamsFlat_eval, emptySimE_eval (S := S),
    v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    unifGdh, FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq,
    bind_assoc, pure_bind]
  rfl

def fgKeyIndGapDhRunAtFlatComp (S : Setup) (K idx : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) : OracleComp GdhSimSpec Bytes :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then do
    let secb ← unifGdh ($ᵗ Bool)
    let initSt := _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb
    let (_, finalSt) ← runWithGdhStep
      (fgKeyIndStep true (idx / S.N_spk_tot) (idx % S.N_spk_tot) S K U V) A initSt
    extractCdhFromSimState S true K U V finalSt
  else if idx < nA + nC then do
    let r := idx - nA
    let secb ← unifGdh ($ᵗ Bool)
    let initSt := _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb
    let (_, finalSt) ← runWithGdhStep
      (fgKeyIndStep false (r / S.N_spk_tot) (r % S.N_spk_tot) S K U V) A initSt
    extractCdhFromSimState S false K U V finalSt
  else if idx < nA + nC + nB then do
    let r := idx - (nA + nC)
    let secb ← unifGdh ($ᵗ Bool)
    let initSt := _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb
    let (_, finalSt) ← runWithGdhStep
      (fgKeyIndStepIk (r / S.N_id) (r % S.N_id) S K U V) A initSt
    extractCdh2FromAdvRoLog K U V finalSt.advRoLog
  else do
    let r := idx - (nA + nC + nB)
    let secb ← unifGdh ($ᵗ Bool)
    let initSt := _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb
    let (_, finalSt) ← runWithGdhStep
      (fgKeyIndStepOpk (r / S.N_opk_tot) (r % S.N_opk_tot) S K U V) A initSt
    extractCdh4FromAdvRoLog K U V finalSt.advRoLog

theorem fgKeyIndGapDhProg_eval_eq_of_queryBound (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP (A ()) (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (U V : Bytes) :
    (fgKeyIndGapDhProg S K).eval A (U, V) =
      (do
        let idx ← unifGdh (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
        fgKeyIndGapDhRunAtFlatComp S K idx (A ()) U V) := by
  have hfun : A = (fun _ => A ()) := funext fun ⟨⟩ => rfl
  rw [hfun, fgKeyIndGapDhProg_eval_runFrom]
  refine bind_congr fun idx => ?_
  unfold fgKeyIndGapDhRunAtFlatComp paramsFlatVal
  by_cases h1 : idx < S.N_id * S.N_spk_tot
  · simp only [h1, ↓reduceIte]
    refine bind_congr fun secb => ?_
    exact runFrom_eq S K _ _
      (fun q st hB => gdhHandle_eval_dh S K true _ _ U V q st hB)
      (fun q st => fgKeyIndStep_grow true _ _ K U V q st) _
      (fun a st hB => gdhFinish_eval_mode0 S K a _ st rfl hB.advKeyPows_le
        hB.base_le)
      (A ()) hA secb
  by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
  · simp only [h1, h2, ↓reduceIte]
    refine bind_congr fun secb => ?_
    exact runFrom_eq S K _ _
      (fun q st hB => gdhHandle_eval_dh S K false _ _ U V q st hB)
      (fun q st => fgKeyIndStep_grow false _ _ K U V q st) _
      (fun a st _ => gdhFinish_eval_mode1 S K a _ st rfl)
      (A ()) hA secb
  by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
  · simp only [h1, h2, h3, ↓reduceIte]
    refine bind_congr fun secb => ?_
    exact runFrom_eq S K _ _
      (fun q st hB => gdhHandle_eval_ik S K _ _ U V q st hB)
      (fun q st => fgKeyIndStepIk_grow _ _ K U V q st) _
      (fun a st _ => gdhFinish_eval_mode2 S K a _ st rfl)
      (A ()) hA secb
  · simp only [h1, h2, h3, ↓reduceIte]
    refine bind_congr fun secb => ?_
    exact runFrom_eq S K _ _
      (fun q st hB => gdhHandle_eval_opk S K _ _ U V q st hB)
      (fun q st => fgKeyIndStepOpk_grow _ _ K U V q st) _
      (fun a st _ => gdhFinish_eval_mode3 S K a _ st rfl)
      (A ()) hA secb

/-- Evaluation equivalence between `fgKeyIndGapDhProg S b.q_total` and `fgKeyIndGapDhAdv4 S b A`. -/
theorem fgKeyIndGapDhProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    (fgKeyIndGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V) =
      (fgKeyIndGapDhAdv4 S b A).run U V := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q; cases q <;> rfl
  rw [fgKeyIndGapDhProg_eval_eq_of_queryBound S b.q_total (fun _ => A.1.run) hA U V]
  rfl

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
