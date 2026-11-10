/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
public import Computational.Proofs.SignalPqxdh.Security.SigHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ProbabilityTheory ENNReal
open scoped BigOperators
open SignalPqxdh SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

theorem runShCrAcceptGeneric_clearFalse {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      clearShCrTarget x.2 = x.2 := by
  intro x hx
  unfold runShCrAcceptGeneric at hx
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  have hCleary := liftShCrBase_clearFalse baseAccept hst hClear y hy
  exact recordAcceptKemGeneric_clearFalse P getBundles isNoneResp k j hdr y.1 y.2 hCleary x hx

theorem runShCrAcceptGeneric_setShCrTarget {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run (setShCrTarget hst bIdx pk
      sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst := by
  unfold runShCrAcceptGeneric
  simp only [StateT.run_bind, liftShCrBase_setShCrTarget, bind_map_left, map_bind]
  congr 1; ext y
  exact recordAcceptKemGeneric_setShCrTarget P getBundles isNoneResp k j hdr y.1 y.2 bIdx pk sk

theorem runShCrAcceptGeneric_preserves_bundles {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (baseAccept.run hst.base), getBundles y.2 = getBundles hst.base) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      getBundles x.2.base = getBundles hst.base := by
  intro x hx
  unfold runShCrAcceptGeneric at hx
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  have hy_b := liftShCrBase_preserves_bundles getBundles baseAccept hst hm y hy
  have hx_b :=
    (recordAcceptKemGeneric_preserves_base_and_send P getBundles isNoneResp k j hdr y.1 y.2 x hx).1
  rw [hx_b, hy_b]

theorem runShCrAcceptGeneric_validStep {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (baseAccept.run hst.base), getBundles y.2 = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  unfold runShCrAcceptGeneric at hx
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  have hVy := liftShCrBase_validStep getBundles baseAccept bIdx pk sk hst hm hV y hy
  exact recordAcceptKemGeneric_validStep P getBundles isNoneResp k j hdr y.1 bIdx pk sk y.2 hVy x hx

theorem runShCrAcceptGeneric_sendStep {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      x.2.sendCount = hst.sendCount ∧ x.2.initKemRecs = hst.initKemRecs := by
  intro x hx
  unfold runShCrAcceptGeneric at hx
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hx
  rcases hx with ⟨y, hy, hx⟩
  have hx_s :=
    recordAcceptKemGeneric_preserves_base_and_send P getBundles isNoneResp k j hdr y.1 y.2 x hx
  simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨_, _, hy⟩
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  exact ⟨hx_s.2.1, hx_s.2.2⟩

@[simp] theorem applyShCrFinish_setShCrTarget {S : Setup} {Base Resp : Type}
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S Base)
    (bIdx : Nat) (pk sk : Bytes) (out : Resp × Option Base) :
    applyShCrFinish sid pqspkPk ss kemCt (setShCrTarget hst bIdx pk sk) out =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk)
        (applyShCrFinish sid pqspkPk ss kemCt hst out) := by
  rcases out with ⟨resp, none | base'⟩ <;> rfl

theorem applyShCrFinish_clearFalse {S : Setup} {Base Resp : Type}
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S Base)
    (out : Resp × Option Base) (hClear : clearShCrTarget hst = hst) :
    clearShCrTarget (applyShCrFinish sid pqspkPk ss kemCt hst out).2 =
      (applyShCrFinish sid pqspkPk ss kemCt hst out).2 := by
  rw [clearShCrTarget_eq_iff] at hClear ⊢
  rcases out with ⟨resp, none | base'⟩ <;> exact hClear

theorem applyShCrFinish_bundles {S : Setup} {Base Resp : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S Base)
    (out : Resp × Option Base)
    (hb : ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base) :
    getBundles (applyShCrFinish sid pqspkPk ss kemCt hst out).2.base = getBundles hst.base := by
  rcases out with ⟨resp, none | base'⟩
  · rfl
  · exact hb base' rfl

theorem applyShCrFinish_valid {S : Setup} {Base Resp : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (bIdx : Nat) (pk sk : Bytes)
    (hst : ShCrState S Base) (out : Resp × Option Base)
    (hb : ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ValidTargetRecv getBundles bIdx pk sk (applyShCrFinish sid pqspkPk ss kemCt hst out).2 := by
  rcases out with ⟨resp, none | base'⟩
  · exact hV
  · refine ⟨hV.1, hV.2.1, hV.2.2.1, ?_, hV.2.2.2.2⟩
    intro p hp
    dsimp only [applyShCrFinish] at hp
    rw [hb base' rfl] at hp
    exact hV.2.2.2.1 p hp

theorem applyShCrFinish_send {S : Setup} {Base Resp : Type}
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : ShCrState S Base)
    (out : Resp × Option Base) :
    (applyShCrFinish sid pqspkPk ss kemCt hst out).2.sendCount = hst.sendCount + 1 ∧
    ∀ i ∈ (applyShCrFinish sid pqspkPk ss kemCt hst out).2.initKemRecs,
      i ∈ hst.initKemRecs ∨
      (i.sendIdx = hst.sendCount ∧ i.pqspkPk = pqspkPk ∧ i.kemCt = kemCt ∧ i.kemSs = ss) := by
  rcases out with ⟨resp, none | base'⟩
  · exact ⟨rfl, fun i hi => Or.inl hi⟩
  · refine ⟨rfl, fun i hi => ?_⟩
    simp only [applyShCrFinish, List.mem_cons] at hi
    rcases hi with rfl | hi_old
    · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl hi_old

def checkBundleSigs (P : Primitives) (principals : List (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) : Bool :=
  let sigPkB := resolveSigPk P principals bundle.ikB
  P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
  P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig

def runShCrInitiate2 {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base)) :
    StateT (ShCrState S Base) ProbComp Resp := fun hst => do
  let st := hst.base
  let some uInfo := preCheck st
    | return (noneResp, hst)
  let ekASk ← sampleScalar32
  let kemCoins ← sampleCoins32
  if !checkBundleSigs P (getPrincipals st) bundle then
    return (noneResp, hst)
  match P.kemEncaps bundle.pqspkB kemCoins with
  | none => return (noneResp, { hst with sendCount := hst.sendCount + 1 })
  | some (ss, kemCt) =>
    applyShCrFinish sid bundle.pqspkB ss kemCt hst <$> finishBase uInfo ekASk ss kemCt st

def postKem2 {S : Setup} {Base Resp U : Type}
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uInfo : U)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (ss kemCt : Bytes) :
    ProbComp (Resp × ShCrState S Base) := do
  let ekASk ← sampleScalar32
  applyShCrFinish sid bundle.pqspkB ss kemCt hst <$> finishBase uInfo ekASk ss kemCt hst.base

noncomputable def tryPause2 {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (targetSendIdx : Nat)
    (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) : Option (PausedShCrKem S Base) :=
  match preCheck hst.base with
  | none => none
  | some uInfo =>
    if !checkBundleSigs P (getPrincipals hst.base) bundle then
      none
    else if hst.sendCount == targetSendIdx then
      let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (ShCrState S Base) ProbComp) + implTrue
      some {
        bundle := bundle
        resume := fun ss kemCt =>
          postKem2 sid bundle uInfo finishBase hst ss kemCt >>= fun y =>
            (simulateQ fullImpl (cont y.1)).run y.2
      }
    else
      none

theorem mem_support_runShCrInitiate2 {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (x : Resp × ShCrState S Base)
    (hx : x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle
      finishBase).run hst)) :
    (x = (noneResp, hst) ∧ (preCheck hst.base = none ∨
      checkBundleSigs P (getPrincipals hst.base) bundle = false)) ∨
    (∃ uInfo, preCheck hst.base = some uInfo ∧
      checkBundleSigs P (getPrincipals hst.base) bundle = true ∧
      (x = (noneResp, { hst with sendCount := hst.sendCount + 1 }) ∨
       ∃ ekASk ss kemCt out,
         out ∈ support (finishBase uInfo ekASk ss kemCt hst.base) ∧
         x = applyShCrFinish sid bundle.pqspkB ss kemCt hst out)) := by
  unfold runShCrInitiate2 StateT.run at hx
  dsimp only at hx
  revert hx
  cases hpre : preCheck hst.base
  · simp only [support_pure, Set.mem_singleton_iff]
    intro hx; exact Or.inl ⟨hx, Or.inl trivial⟩
  · rename_i uInfo
    dsimp only
    simp only [MonadAttach.mem_support_bind]
    intro hx
    rcases hx with ⟨ekASk, _, kemCoins, _, hx⟩
    revert hx
    cases hsig : checkBundleSigs P (getPrincipals hst.base) bundle
    · simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff]
      intro hx; exact Or.inl ⟨hx, Or.inr trivial⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hkem : P.kemEncaps bundle.pqspkB kemCoins
      · simp only [support_pure, Set.mem_singleton_iff]
        intro hx; exact Or.inr ⟨uInfo, rfl, trivial, Or.inl hx⟩
      · rename_i kemPair
        rcases kemPair with ⟨ss, kemCt⟩
        dsimp only
        simp only [support_map, Set.mem_image]
        intro hx
        rcases hx with ⟨out, hout, hx⟩
        exact Or.inr ⟨uInfo, rfl, trivial, Or.inr ⟨ekASk, ss, kemCt, out, hout, hx.symm⟩⟩

theorem runShCrInitiate2_setShCrTarget {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      (setShCrTarget hst bIdx pk sk) =
    Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
      (runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run hst := by
  unfold runShCrInitiate2 StateT.run
  dsimp only [setShCrTarget]
  cases preCheck hst.base
  · simp [Prod.map]
  · rename_i uInfo
    dsimp only
    simp only [map_bind]
    congr 1; ext ekASk
    congr 1; ext kemCoins
    cases checkBundleSigs P (getPrincipals hst.base) bundle
    · simp [Prod.map]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [Prod.map]
      | some kemPair =>
        rcases kemPair with ⟨ss, kemCt⟩
        dsimp only
        simp only [Functor.map_map]
        congr 1; funext out
        exact applyShCrFinish_setShCrTarget sid bundle.pqspkB ss kemCt hst bIdx pk sk out

theorem runShCrInitiate2_clearFalse {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      clearShCrTarget x.2 = x.2 := by
  intro x hx
  rcases mem_support_runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨_, _, _, rfl | ⟨_, ss, kemCt, out, _, rfl⟩⟩
  · exact hClear
  · rw [clearShCrTarget_eq_iff] at hClear ⊢; exact hClear
  · exact applyShCrFinish_clearFalse sid bundle.pqspkB ss kemCt hst out hClear

theorem runShCrInitiate2_preserves_bundles {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base) :
    ∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      getBundles x.2.base = getBundles hst.base := by
  intro x hx
  rcases mem_support_runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ss, kemCt, out, hout, rfl⟩⟩
  · rfl
  · rfl
  · exact applyShCrFinish_bundles getBundles sid bundle.pqspkB ss kemCt hst out
      (hFinishB uInfo ekASk ss kemCt out hout)

theorem runShCrInitiate2_validStep {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  rcases mem_support_runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ss, kemCt, out, hout, rfl⟩⟩
  · exact hV
  · exact hV
  · exact applyShCrFinish_valid getBundles sid bundle.pqspkB ss kemCt bIdx pk sk hst out
      (hFinishB uInfo ekASk ss kemCt out hout) hV

theorem runShCrInitiate2_sendStep {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  intro x hx
  rcases mem_support_runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨_, _, _, rfl | ⟨_, ss, kemCt, out, _, rfl⟩⟩
  · exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  · exact ⟨Nat.le_succ _, fun i hi => Or.inl hi⟩
  · rcases applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out with ⟨hcnt, hinit⟩
    refine ⟨by omega, fun i hi => ?_⟩
    rcases hinit i hi with hi_old | ⟨hi_idx, _⟩
    · exact Or.inl hi_old
    · exact Or.inr ⟨hi_idx, by omega⟩

theorem runShCrInitiate2_pauseNone {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (sIdx : Nat) (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPause2 P getPrincipals implTrue preCheck sid bundle finishBase sIdx cont hst =
      none) :
    ∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      x.2.sendCount ≤ sIdx := by
  intro x hx
  rcases mem_support_runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, hpre, hsig, hrest⟩
  · exact hLe
  · unfold tryPause2 at hNone
    rw [hpre, hsig] at hNone
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_eq_right_iff,
      reduceCtorEq, imp_false, Bool.not_eq_true, beq_eq_false_iff_ne] at hNone
    rcases hrest with rfl | ⟨_, ss, kemCt, out, _, rfl⟩
    · dsimp only; omega
    · have hcnt := (applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out).1
      omega

theorem runShCrInitiate2_pauseSome {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx sIdx : Nat) (pk sk : Bytes)
    (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) (paused : PausedShCrKem S Base)
    (hFinishB : ∀ uInfo ekASk ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst)
    (hSome : tryPause2 P getPrincipals implTrue preCheck sid bundle finishBase sIdx cont hst =
      some paused) :
    ∃ (noneOut : Resp)
      (postKem : Bytes → Bytes → ProbComp (Resp × ShCrState S Base)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
      (∀ obs : Resp × ShCrState S Base → ProbComp Bool,
        𝒟[(runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run hst >>=
          obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv getBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  unfold tryPause2 at hSome
  cases hpre : preCheck hst.base with
  | none => rw [hpre] at hSome; cases hSome
  | some uInfo =>
    rw [hpre] at hSome
    dsimp only at hSome
    cases hsig : checkBundleSigs P (getPrincipals hst.base) bundle
    · rw [hsig] at hSome; simp at hSome
    · rw [hsig] at hSome
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSome
      cases hcnt : (hst.sendCount == sIdx)
      · rw [hcnt] at hSome; simp at hSome
      · rw [hcnt] at hSome
        simp only [↓reduceIte, Option.some.injEq] at hSome
        subst hSome
        have hsIdx : hst.sendCount = sIdx := beq_iff_eq.mp hcnt
        refine ⟨noneResp, postKem2 sid bundle uInfo finishBase hst, ?_, ?_, ?_⟩
        · intro ss ct; rfl
        · intro obs
          unfold runShCrInitiate2 StateT.run postKem2
          dsimp only
          rw [hpre]
          dsimp only
          simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
          rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleCoins32]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
          cases P.kemEncaps bundle.pqspkB r with
          | none =>
            simp only [pure_bind, hsIdx]
            exact OracleComp.evalDist_bind_const _ _
          | some kemPair =>
            rcases kemPair with ⟨ss, ct⟩
            simp only [bind_map_left]
        · intro ss ct y hy
          unfold postKem2 at hy
          simp only [MonadAttach.mem_support_bind, support_map, Set.mem_image] at hy
          rcases hy with ⟨ekASk, _, out, hout, rfl⟩
          have hVy := applyShCrFinish_valid getBundles sid bundle.pqspkB ss ct bIdx pk sk hst out
            (hFinishB uInfo ekASk ss ct out hout) hV
          rcases applyShCrFinish_send sid bundle.pqspkB ss ct hst out with ⟨hSend, hInit⟩
          refine ⟨hVy, by omega, fun i hi => ?_⟩
          rcases hInit i hi with hi_old | ⟨hi_idx, hi_pk, hi_ct, hi_ss⟩
          · exact Or.inl hi_old
          · exact Or.inr ⟨hi_idx.trans hsIdx, hi_pk, hi_ct, hi_ss⟩


def runShCrInitiate4 {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base →
      ProbComp (Resp × Option Base)) :
    StateT (ShCrState S Base) ProbComp Resp := fun hst => do
  let st := hst.base
  let some uInfo := preCheck st
    | return (noneResp, hst)
  let ekASk ← sampleScalar32
  let kemCoins ← sampleCoins32
  let ephASk ← sampleScalar32
  let spqrCoins ← sampleCoins32
  if !checkBundleSigs P (getPrincipals st) bundle then
    return (noneResp, hst)
  match P.kemEncaps bundle.pqspkB kemCoins with
  | none => return (noneResp, { hst with sendCount := hst.sendCount + 1 })
  | some (ss, kemCt) =>
    applyShCrFinish sid bundle.pqspkB ss kemCt hst <$>
      finishBase uInfo ekASk ephASk spqrCoins ss kemCt st

def postKem4 {S : Setup} {Base Resp U : Type}
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uInfo : U)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (ss kemCt : Bytes) :
    ProbComp (Resp × ShCrState S Base) := do
  let ekASk ← sampleScalar32
  let ephASk ← sampleScalar32
  let spqrCoins ← sampleCoins32
  applyShCrFinish sid bundle.pqspkB ss kemCt hst <$>
    finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base

noncomputable def tryPause4 {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (targetSendIdx : Nat)
    (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) : Option (PausedShCrKem S Base) :=
  match preCheck hst.base with
  | none => none
  | some uInfo =>
    if !checkBundleSigs P (getPrincipals hst.base) bundle then
      none
    else if hst.sendCount == targetSendIdx then
      let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (ShCrState S Base) ProbComp) + implTrue
      some {
        bundle := bundle
        resume := fun ss kemCt =>
          postKem4 sid bundle uInfo finishBase hst ss kemCt >>= fun y =>
            (simulateQ fullImpl (cont y.1)).run y.2
      }
    else
      none

theorem mem_support_runShCrInitiate4 {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (x : Resp × ShCrState S Base)
    (hx : x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle
      finishBase).run hst)) :
    (x = (noneResp, hst) ∧ (preCheck hst.base = none ∨
      checkBundleSigs P (getPrincipals hst.base) bundle = false)) ∨
    (∃ uInfo, preCheck hst.base = some uInfo ∧
      checkBundleSigs P (getPrincipals hst.base) bundle = true ∧
      (x = (noneResp, { hst with sendCount := hst.sendCount + 1 }) ∨
       ∃ ekASk ephASk spqrCoins ss kemCt out,
         out ∈ support (finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base) ∧
         x = applyShCrFinish sid bundle.pqspkB ss kemCt hst out)) := by
  unfold runShCrInitiate4 StateT.run at hx
  dsimp only at hx
  revert hx
  cases hpre : preCheck hst.base
  · simp only [support_pure, Set.mem_singleton_iff]
    intro hx; exact Or.inl ⟨hx, Or.inl trivial⟩
  · rename_i uInfo
    dsimp only
    simp only [MonadAttach.mem_support_bind]
    intro hx
    rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩
    revert hx
    cases hsig : checkBundleSigs P (getPrincipals hst.base) bundle
    · simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff]
      intro hx; exact Or.inl ⟨hx, Or.inr trivial⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hkem : P.kemEncaps bundle.pqspkB kemCoins
      · simp only [support_pure, Set.mem_singleton_iff]
        intro hx; exact Or.inr ⟨uInfo, rfl, trivial, Or.inl hx⟩
      · rename_i kemPair
        rcases kemPair with ⟨ss, kemCt⟩
        dsimp only
        simp only [support_map, Set.mem_image]
        intro hx
        rcases hx with ⟨out, hout, hx⟩
        exact Or.inr ⟨uInfo, rfl, trivial, Or.inr ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout,
          hx.symm⟩⟩

theorem runShCrInitiate4_setShCrTarget {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (bIdx : Nat) (pk sk : Bytes) :
    (runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      (setShCrTarget hst bIdx pk sk) =
    Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
      (runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run hst := by
  unfold runShCrInitiate4 StateT.run
  dsimp only [setShCrTarget]
  cases preCheck hst.base
  · simp [Prod.map]
  · rename_i uInfo
    dsimp only
    simp only [map_bind]
    congr 1; ext ekASk
    congr 1; ext kemCoins
    congr 1; ext ephASk
    congr 1; ext spqrCoins
    cases checkBundleSigs P (getPrincipals hst.base) bundle
    · simp [Prod.map]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [Prod.map]
      | some kemPair =>
        rcases kemPair with ⟨ss, kemCt⟩
        simp only [Functor.map_map]
        congr 1; funext out
        exact applyShCrFinish_setShCrTarget sid bundle.pqspkB ss kemCt hst bIdx pk sk out

theorem runShCrInitiate4_clearFalse {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      clearShCrTarget x.2 = x.2 := by
  intro x hx
  rcases mem_support_runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨_, _, _, rfl | ⟨_, _, _, ss, kemCt, out, _, rfl⟩⟩
  · exact hClear
  · rw [clearShCrTarget_eq_iff] at hClear ⊢; exact hClear
  · exact applyShCrFinish_clearFalse sid bundle.pqspkB ss kemCt hst out hClear

theorem runShCrInitiate4_preserves_bundles {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ephASk spqrCoins ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base) :
    ∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      getBundles x.2.base = getBundles hst.base := by
  intro x hx
  rcases mem_support_runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout, rfl⟩⟩
  · rfl
  · rfl
  · exact applyShCrFinish_bundles getBundles sid bundle.pqspkB ss kemCt hst out
      (hFinishB uInfo ekASk ephASk spqrCoins ss kemCt out hout)

theorem runShCrInitiate4_validStep {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx : Nat) (pk sk : Bytes) (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ephASk spqrCoins ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst) :
    ∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      ValidTargetRecv getBundles bIdx pk sk x.2 := by
  intro x hx
  rcases mem_support_runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, _, _, rfl | ⟨ekASk, ephASk, spqrCoins, ss, kemCt, out, hout, rfl⟩⟩
  · exact hV
  · exact hV
  · exact applyShCrFinish_valid getBundles sid bundle.pqspkB ss kemCt bIdx pk sk hst out
      (hFinishB uInfo ekASk ephASk spqrCoins ss kemCt out hout) hV

theorem runShCrInitiate4_sendStep {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  intro x hx
  rcases mem_support_runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨_, _, _, rfl | ⟨_, _, _, ss, kemCt, out, _, rfl⟩⟩
  · exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  · exact ⟨Nat.le_succ _, fun i hi => Or.inl hi⟩
  · rcases applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out with ⟨hcnt, hinit⟩
    refine ⟨by omega, fun i hi => ?_⟩
    rcases hinit i hi with hi_old | ⟨hi_idx, _⟩
    · exact Or.inl hi_old
    · exact Or.inr ⟨hi_idx, by omega⟩

theorem runShCrInitiate4_pauseNone {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (sIdx : Nat) (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPause4 P getPrincipals implTrue preCheck sid bundle finishBase sIdx cont hst =
      none) :
    ∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      x.2.sendCount ≤ sIdx := by
  intro x hx
  rcases mem_support_runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase hst x
    hx with
    ⟨rfl, _⟩ | ⟨uInfo, hpre, hsig, hrest⟩
  · exact hLe
  · unfold tryPause4 at hNone
    rw [hpre, hsig] at hNone
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ite_eq_right_iff,
      reduceCtorEq, imp_false, Bool.not_eq_true, beq_eq_false_iff_ne] at hNone
    rcases hrest with rfl | ⟨_, _, _, ss, kemCt, out, _, rfl⟩
    · dsimp only; omega
    · have hcnt := (applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out).1
      omega

theorem runShCrInitiate4_pauseSome {S : Setup} {Base Resp U ι : Type}
    {QSpec : OracleSpec.{0, 0} ι} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (implTrue : QueryImpl QSpec (StateT (ShCrState S Base) ProbComp))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx sIdx : Nat) (pk sk : Bytes)
    (cont : Resp → OracleComp (unifSpec + QSpec) Bool)
    (hst : ShCrState S Base) (paused : PausedShCrKem S Base)
    (hFinishB : ∀ uInfo ekASk ephASk spqrCoins ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hV : ValidTargetRecv getBundles bIdx pk sk hst)
    (hSome : tryPause4 P getPrincipals implTrue preCheck sid bundle finishBase sIdx cont hst =
      some paused) :
    ∃ (noneOut : Resp)
      (postKem : Bytes → Bytes → ProbComp (Resp × ShCrState S Base)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (ShCrState S Base) ProbComp) + implTrue) (cont y.1)).run y.2)) ∧
      (∀ obs : Resp × ShCrState S Base → ProbComp Bool,
        𝒟[(runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run hst >>=
          obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv getBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  unfold tryPause4 at hSome
  cases hpre : preCheck hst.base with
  | none => rw [hpre] at hSome; cases hSome
  | some uInfo =>
    rw [hpre] at hSome
    dsimp only at hSome
    cases hsig : checkBundleSigs P (getPrincipals hst.base) bundle
    · rw [hsig] at hSome; simp at hSome
    · rw [hsig] at hSome
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSome
      cases hcnt : (hst.sendCount == sIdx)
      · rw [hcnt] at hSome; simp at hSome
      · rw [hcnt] at hSome
        simp only [↓reduceIte, Option.some.injEq] at hSome
        subst hSome
        have hsIdx : hst.sendCount = sIdx := beq_iff_eq.mp hcnt
        refine ⟨noneResp, postKem4 sid bundle uInfo finishBase hst, ?_, ?_, ?_⟩
        · intro ss ct; rfl
        · intro obs
          unfold runShCrInitiate4 StateT.run postKem4
          dsimp only
          rw [hpre]
          dsimp only
          simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
          rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleCoins32]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
          cases P.kemEncaps bundle.pqspkB r with
          | none =>
            simp only [pure_bind, hsIdx]
            rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const,
                OracleComp.evalDist_bind_const]
          | some kemPair =>
            rcases kemPair with ⟨ss, ct⟩
            simp only [bind_map_left]
        · intro ss ct y hy
          unfold postKem4 at hy
          simp only [MonadAttach.mem_support_bind, support_map, Set.mem_image] at hy
          rcases hy with ⟨ekASk, _, ephASk, _, spqrCoins, _, out, hout, rfl⟩
          have hVy := applyShCrFinish_valid getBundles sid bundle.pqspkB ss ct bIdx pk sk hst out
            (hFinishB uInfo ekASk ephASk spqrCoins ss ct out hout) hV
          rcases applyShCrFinish_send sid bundle.pqspkB ss ct hst out with ⟨hSend, hInit⟩
          refine ⟨hVy, by omega, fun i hi => ?_⟩
          rcases hInit i hi with hi_old | ⟨hi_idx, hi_pk, hi_ct, hi_ss⟩
          · exact Or.inl hi_old
          · exact Or.inr ⟨hi_idx.trans hsIdx, hi_pk, hi_ct, hi_ss⟩


theorem liftShCrBase_afterGen {S : Setup} {Base α : Type}
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (m : StateT Base ProbComp α) (bIdx : Nat) (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (m.run hst.base), getBundles y.2 = getBundles hst.base)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk, (liftShCrBase m).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$> (liftShCrBase m).run hst) ∧
    (∀ x ∈ support ((liftShCrBase m).run hst),
      hasGeneratedTargetBundle S bIdx (getBundles x.2.base)) := by
  refine ⟨liftShCrBase_setShCrTarget m hst bIdx, fun x hx => ?_⟩
  rw [liftShCrBase_preserves_bundles getBundles m hst hm x hx]
  exact hGen

theorem runShCrAcceptGeneric_afterGen {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (bIdx : Nat) (hst : ShCrState S Base)
    (hm : ∀ y ∈ support (baseAccept.run hst.base), getBundles y.2 = getBundles hst.base)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk,
      (runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run (setShCrTarget hst bIdx
      pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst) ∧
    (∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      hasGeneratedTargetBundle S bIdx (getBundles x.2.base)) := by
  refine ⟨runShCrAcceptGeneric_setShCrTarget P getBundles isNoneResp baseAccept k j hdr hst bIdx,
    fun x hx => ?_⟩
  rw [runShCrAcceptGeneric_preserves_bundles P getBundles isNoneResp baseAccept k j hdr hst hm x hx]
  exact hGen

theorem runShCrAcceptGeneric_sendStep' {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  intro x hx
  rcases runShCrAcceptGeneric_sendStep P getBundles isNoneResp baseAccept k j hdr hst x hx with ⟨h1,
    h2⟩
  exact ⟨by omega, fun i hi => Or.inl (h2 ▸ hi)⟩

theorem runShCrAcceptGeneric_pauseNone {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (sIdx : Nat) (hst : ShCrState S Base) (hLe : hst.sendCount ≤ sIdx) :
    ∀ x ∈ support ((runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst),
      x.2.sendCount ≤ sIdx := by
  intro x hx
  have h1 := (runShCrAcceptGeneric_sendStep P getBundles isNoneResp baseAccept k j hdr hst x hx).1
  omega

theorem runShCrGenSPKGeneric_sendStep' {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : ShCrState S Base) :
    ∀ x ∈ support ((runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  intro x hx
  rcases runShCrGenSPKGeneric_sendStep P getPrincipals getBundles setBundles noneResp bundleResp u j
    hst x hx with ⟨h1, h2⟩
  exact ⟨by omega, fun i hi => Or.inl (h2 ▸ hi)⟩

theorem runShCrGenSPKGeneric_pauseNone {S : Setup} {Base Resp : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (setBundles : Base → List ((Nat × Nat) × SpkBundleEntry) → Base)
    (noneResp : Resp) (bundleResp : PreKeyBundleInput → Resp)
    (u : Fin S.N_id) (j : Fin S.N_recv) (sIdx : Nat) (hst : ShCrState S Base)
    (hLe : hst.sendCount ≤ sIdx) :
    ∀ x ∈ support ((runShCrGenSPKGeneric true P getPrincipals getBundles setBundles noneResp
      bundleResp u j).run hst),
      x.2.sendCount ≤ sIdx := by
  intro x hx
  have h1 :=
    (runShCrGenSPKGeneric_sendStep P getPrincipals getBundles setBundles noneResp bundleResp u j hst
    x hx).1
  omega

theorem runShCrInitiate2_afterGen {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx : Nat) (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk, (runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run hst) ∧
    (∀ x ∈ support ((runShCrInitiate2 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      hasGeneratedTargetBundle S bIdx (getBundles x.2.base)) := by
  refine ⟨runShCrInitiate2_setShCrTarget P getPrincipals noneResp preCheck sid bundle finishBase hst
    bIdx, fun x hx => ?_⟩
  rw [runShCrInitiate2_preserves_bundles P getPrincipals getBundles noneResp preCheck sid bundle
    finishBase hst hFinishB x hx]
  exact hGen

theorem runShCrInitiate4_afterGen {S : Setup} {Base Resp U : Type} (P : Primitives)
    (getPrincipals : Base → List (Nat × PrincipalEntry))
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (noneResp : Resp)
    (preCheck : Base → Option U)
    (sid : SessionId S) (bundle : PreKeyBundleInput)
    (finishBase : U → Bytes → Bytes → Bytes → Bytes → Bytes → Base → ProbComp (Resp × Option Base))
    (bIdx : Nat) (hst : ShCrState S Base)
    (hFinishB : ∀ uInfo ekASk ephASk spqrCoins ss kemCt out,
      out ∈ support (finishBase uInfo ekASk ephASk spqrCoins ss kemCt hst.base) →
      ∀ base', out.2 = some base' → getBundles base' = getBundles hst.base)
    (hGen : hasGeneratedTargetBundle S bIdx (getBundles hst.base)) :
    (∀ pk sk, (runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run hst) ∧
    (∀ x ∈ support ((runShCrInitiate4 P getPrincipals noneResp preCheck sid bundle finishBase).run
      hst),
      hasGeneratedTargetBundle S bIdx (getBundles x.2.base)) := by
  refine ⟨runShCrInitiate4_setShCrTarget P getPrincipals noneResp preCheck sid bundle finishBase hst
    bIdx, fun x hx => ?_⟩
  rw [runShCrInitiate4_preserves_bundles P getPrincipals getBundles noneResp preCheck sid bundle
    finishBase hst hFinishB x hx]
  exact hGen

/-! ### `PreservesAt` for `spkBundles` on Base Queries -/

macro "prove_preserves_at_rokem" : tactic =>
  `(tactic| repeat (first
    | with_reducible apply PreservesAt.pure
    | (rw [pure_bind])
    | with_reducible apply PreservesAt.get_bind
    | (with_reducible apply PreservesAt.liftM_bind; intro _)
    | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
    | (with_reducible apply PreservesAt.set_bind; rfl)
    | (with_reducible apply PreservesAt.set_eq; rfl)
    | (split; try dsimp only)))

theorem map_base_liftShCrBase {S : Setup} {Base α : Type}
    (m : StateT Base ProbComp α) (hst : ShCrState S Base) :
    (Prod.map id ShCrState.base <$> (liftShCrBase m).run hst) = m.run hst.base := by
  simp [liftShCrBase, StateT.run, Prod.map]

theorem map_base_recordAcceptKemGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) :
    (Prod.map id ShCrState.base <$>
      (recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst) =
      pure (out, hst.base) := by
  unfold recordAcceptKemGeneric StateT.run
  dsimp only
  cases isNoneResp out
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp [Prod.map]
    | some pair =>
      rcases pair with ⟨_, bEntry⟩
      dsimp only
      cases P.kemDecaps bEntry.pqspkSk hdr.kemCt <;> simp [Prod.map]
  · simp [Prod.map]

theorem map_base_runShCrAcceptGeneric {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (baseAccept : StateT Base ProbComp Resp)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (hst : ShCrState S Base) :
    (Prod.map id ShCrState.base <$>
      (runShCrAcceptGeneric P getBundles isNoneResp baseAccept k j hdr).run hst) =
      baseAccept.run hst.base := by
  unfold runShCrAcceptGeneric
  simp only [StateT.run_bind, map_bind, map_base_recordAcceptKemGeneric]
  simp [liftShCrBase, StateT.run]

/-! ### `KeyInd` Instantiation -/

abbrev liftKeyIndShCrBase {S : Setup} {α : Type}
    (m : StateT (KeyIndState S) ProbComp α) : StateT (KeyIndShCrState S) ProbComp α :=
  liftShCrBase m

def preCheckKeyInd (S : Setup) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    Option PrincipalEntry :=
  if st.sessions.any (fun e => e.sid == sid) then none
  else match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => none
    | some (_, uEntry) =>
      if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then none
      else some uEntry

def finishKeyIndBase (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S) :
    ProbComp (KeyIndResponse × Option (KeyIndState S)) := do
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← evalHkdfOrRo true P st.roCache secrets
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S := {
    sid         := sid
    honestPeer  := honestPeer
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    fresh       := honestPeer.isSome
    drKeyReal   := drKeyReal
    drKeyRand   := drKeyReal
    hdr         := hdr
    tested      := false
  }
  let drKeyRand ←
    match keyIndPartnerRandKey? P st.respSessions sessEntry with
    | some k => pure k
    | none   => sampleDRKey96
  let base' : KeyIndState S :=
    { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions, roCache :=
      roCache' }
  let resp : KeyIndResponse :=
    match findHonestPrincipal P st.principals bundle.ikB with
    | some _ => .hdrResp hdr
    | none   => .initUnfreshResp drKeyReal hdr
  return (resp, some base')

theorem finishKeyIndBase_spkBundles (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S)
    (out : KeyIndResponse × Option (KeyIndState S))
    (hout : out ∈ support (finishKeyIndBase S P sid bundle uEntry ekASk ss kemCt st)) :
    ∀ base', out.2 = some base' → base'.spkBundles = st.spkBundles := by
  intro base' hbase
  unfold finishKeyIndBase at hout
  dsimp only at hout
  simp only [MonadAttach.mem_support_bind] at hout
  rcases hout with ⟨⟨drKeyReal, roCache'⟩, _, hout⟩
  dsimp only at hout
  split at hout
  · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hout
    subst hout; injection hbase with h; subst h; rfl
  · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨drKeyRand, _, rfl⟩
    injection hbase with h; subst h; rfl

abbrev runKeyIndShCrInitiate (_checkG2 : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndShCrState S) ProbComp KeyIndResponse :=
  runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
    (preCheckKeyInd S P sid u bundle) sid bundle (finishKeyIndBase S P sid bundle)

abbrev runKeyIndShCrGenSPK (embedTarget : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndShCrState S) ProbComp KeyIndResponse :=
  runShCrGenSPKGeneric embedTarget P KeyIndState.principals KeyIndState.spkBundles
    (fun st bs => { st with spkBundles :=
      bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j

def pqxdhKeyIndShCrImpl (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .genSPK u j => runKeyIndShCrGenSPK checkG2 S P u j
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure .noneResp
    else runKeyIndShCrInitiate checkG2 S P (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure .noneResp
    else runKeyIndShCrInitiate checkG2 S P (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndImpl true S P (.acceptOPK k j o hdr)) k j hdr
  | .acceptNoOPK k j l hdr =>
    runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndImpl true S P (.acceptNoOPK k j l hdr)) k j hdr
  | q_other => liftKeyIndShCrBase (pqxdhKeyIndImpl true S P q_other)

def pqxdhKeyIndShCrCachedImpl (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .genSPK u j => runKeyIndShCrGenSPK checkG2 S P u j
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure .noneResp
    else runKeyIndShCrInitiate checkG2 S P (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure .noneResp
    else runKeyIndShCrInitiate checkG2 S P (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr
  | .acceptNoOPK k j l hdr =>
    runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr
  | q_other => liftKeyIndShCrBase (pqxdhKeyIndCachedImpl true S P q_other)

def cacheShCrAdvKeys (S : Setup) (P : Primitives) (hst : KeyIndShCrState S) : KeyIndShCrState S :=
  { hst with base := cacheKeyIndAdvKeys S P hst.base }

theorem CommutesRel.liftKeyIndShCrBase_cache (S : Setup) (P : Primitives)
    (hst : KeyIndShCrState S)
    (m1 m2 : StateT (KeyIndState S) ProbComp KeyIndResponse)
    (hm : CommutesRel (cacheKeyIndAdvKeys S P) hst.base m1 m2) :
    CommutesRel (cacheShCrAdvKeys S P) hst (liftKeyIndShCrBase m1) (liftKeyIndShCrBase m2) := by
  unfold CommutesRel at hm ⊢
  unfold liftKeyIndShCrBase liftShCrBase StateT.run
  dsimp only [cacheShCrAdvKeys]
  rw [hm, bind_map_left, map_bind]
  refine bind_congr (fun x => ?_)
  simp [Prod.map, cacheShCrAdvKeys]

theorem preCheckKeyInd_cacheKeyIndAdvKeys (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    preCheckKeyInd S P sid u bundle (cacheKeyIndAdvKeys S P st) =
      preCheckKeyInd S P sid u bundle st := by
  unfold preCheckKeyInd cacheKeyIndAdvKeys
  dsimp only
  cases st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      rw [koskBundleOk_map_cache]
  · rfl

theorem runKeyIndShCrInitiate_false_commutes_cache (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (hst : KeyIndShCrState S) :
    CommutesRel (cacheShCrAdvKeys S P) hst
      (runKeyIndShCrInitiate false S P sid u bundle)
      (runKeyIndShCrInitiate false S P sid u bundle) := by
  unfold CommutesRel runKeyIndShCrInitiate runShCrInitiate2 StateT.run
  dsimp only [cacheShCrAdvKeys]
  rw [preCheckKeyInd_cacheKeyIndAdvKeys]
  cases preCheckKeyInd S P sid u bundle hst.base with
  | none => simp [Prod.map, cacheShCrAdvKeys]
  | some uEntry =>
    dsimp only
    simp only [map_bind]
    refine bind_congr (fun ekASk => bind_congr (fun kemCoins => ?_))
    change (if !checkBundleSigs P hst.base.principals bundle then _ else _) =
      Prod.map id (cacheShCrAdvKeys S P) <$> (if !checkBundleSigs P hst.base.principals bundle then
        _ else _)
    split_ifs
    · simp [Prod.map, cacheShCrAdvKeys]
    · cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [Prod.map, cacheShCrAdvKeys]
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩
        dsimp only
        unfold finishKeyIndBase
        dsimp only [cacheKeyIndAdvKeys]
        simp only [map_bind, Functor.map_map]
        refine bind_congr (fun roOut => ?_)
        rcases roOut with ⟨drKeyReal, roCache'⟩
        dsimp only
        cases keyIndPartnerRandKey? P hst.base.respSessions _ with
        | some k =>
          dsimp only
          simp only [pure_bind, map_pure]
          cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
            simp [applyShCrFinish, Prod.map, cacheShCrAdvKeys, cacheKeyIndAdvKeys]
        | none =>
          dsimp only
          simp only [map_bind]
          refine bind_congr (fun drKeyRand => ?_)
          cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
            simp [applyShCrFinish, Prod.map, cacheShCrAdvKeys, cacheKeyIndAdvKeys]

theorem runKeyIndShCrAccept_commutes_cache (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    CommutesRel (cacheShCrAdvKeys S P) hst
      (runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp (pqxdhKeyIndCachedImpl true S
        P q) k j hdr)
      (runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp (pqxdhKeyIndImpl true S P q) k
        j hdr) := by
  have hBase := CommutesRel.liftKeyIndShCrBase_cache S P hst
    (pqxdhKeyIndCachedImpl true S P q) (pqxdhKeyIndImpl true S P q)
    (pqxdhKeyIndCachedImpl_commutes_cache true S P q hst.base)
  unfold CommutesRel at hBase ⊢
  unfold runShCrAcceptGeneric
  simp only [StateT.run_bind, hBase, bind_map_left, map_bind]
  refine bind_congr (fun x => ?_)
  rcases x with ⟨out, hst'⟩
  dsimp only [Prod.map, id]
  unfold recordAcceptKemGeneric StateT.run
  dsimp only [cacheShCrAdvKeys, cacheKeyIndAdvKeys]
  split_ifs
  · simp [Prod.map, cacheShCrAdvKeys, cacheKeyIndAdvKeys]
  · cases hst'.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp [Prod.map, cacheShCrAdvKeys, cacheKeyIndAdvKeys]
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      cases P.kemDecaps bEntry.pqspkSk hdr.kemCt <;>
        simp [Prod.map, cacheShCrAdvKeys, cacheKeyIndAdvKeys]

theorem pqxdhKeyIndShCrCachedImpl_false_commutes_cache (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    CommutesRel (cacheShCrAdvKeys S P) hst
      (pqxdhKeyIndShCrCachedImpl false S P q)
      (pqxdhKeyIndShCrImpl false S P q) := by
  cases q with
  | genSPK u j =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst
      (pqxdhKeyIndCachedImpl true S P (.genSPK u j))
      (pqxdhKeyIndImpl true S P (.genSPK u j))
      (pqxdhKeyIndCachedImpl_commutes_cache true S P (.genSPK u j) hst.base)
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, pqxdhKeyIndShCrImpl]
    split_ifs
    · exact CommutesRel.pure (cacheShCrAdvKeys S P) hst KeyIndResponse.noneResp
    · exact runKeyIndShCrInitiate_false_commutes_cache S P (.sendOPK u i) u bundle hst
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl, pqxdhKeyIndShCrImpl]
    split_ifs
    · exact CommutesRel.pure (cacheShCrAdvKeys S P) hst KeyIndResponse.noneResp
    · exact runKeyIndShCrInitiate_false_commutes_cache S P (.sendNoOPK u i) u bundle hst
  | acceptOPK k j o hdr =>
    exact runKeyIndShCrAccept_commutes_cache S P k j hdr (.acceptOPK k j o hdr) hst
  | acceptNoOPK k j l hdr =>
    exact runKeyIndShCrAccept_commutes_cache S P k j hdr (.acceptNoOPK k j l hdr) hst
  | initPrin u =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.initPrin u) hst.base)
  | corruptIK u =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.corruptIK u) hst.base)
  | genOPK u j o =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.genOPK u j o) hst.base)
  | testSession sid =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.testSession sid) hst.base)
  | revealSessionKey sid =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.revealSessionKey sid) hst.base)
  | roQuery secrets =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.roQuery secrets) hst.base)
  | revealDhSecrets =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P .revealDhSecrets hst.base)
  | registerKey sk =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.registerKey sk) hst.base)
  | revealSpkSk u j =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _ (pqxdhKeyIndCachedImpl_commutes_cache
      true S P (.revealSpkSk u j) hst.base)

noncomputable def tryPauseKeyIndQuery (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : Option (PausedShCrKem S (KeyIndState S)) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyIndShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
      (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyIndShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
      (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst
  | _, _ => none

noncomputable def shcrChoosePkKeyIndAt (S : Setup) (P : Primitives)
    (bIdx sIdx : Nat) (A : KeyIndAdversary S) :
    Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) :=
  shcrChoosePkGenericAt P ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    (pqxdhKeyIndShCrCachedImpl true S P) (tryPauseKeyIndQuery S P) bIdx sIdx A.run

noncomputable def runKeyIndShCrSim (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndShCrState S) := do
  let secb ← $ᵗ Bool
  let initSt : KeyIndShCrState S := { base := KeyIndState.empty S secb }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl false S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

noncomputable def badKemShCrProbKeyIndAt (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal

theorem pqxdhKeyIndCachedImpl_preserves_spkBundles (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S)
    (hNotGen : ∀ u j, q ≠ .genSPK u j)
    (hNotRev : ∀ u j, q ≠ .revealSpkSk u j) :
    ∀ y ∈ support ((pqxdhKeyIndCachedImpl true S P q).run st),
      y.2.spkBundles = st.spkBundles := by
  change PreservesAt KeyIndState.spkBundles st (pqxdhKeyIndCachedImpl true S P q)
  cases q with
  | genSPK u j => exact False.elim (hNotGen u j rfl)
  | revealSpkSk u j => exact False.elim (hNotRev u j rfl)
  | _ =>
    unfold pqxdhKeyIndCachedImpl
    try unfold pqxdhKeyIndImpl
    try unfold runKeyIndInitiate
    dsimp only
    prove_preserves_at_rokem

theorem revealSpkSk_afterGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S)
    (hGen : hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk,
      (liftShCrBase (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j))).run (setShCrTarget hst bIdx
      pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (liftShCrBase (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j))).run hst) ∧
    (∀ x ∈ support ((liftShCrBase (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j))).run hst),
      hasGeneratedTargetBundle S bIdx x.2.base.spkBundles) := by
  refine ⟨liftShCrBase_setShCrTarget _ hst bIdx, fun x hx => ?_⟩
  change x ∈ support (do
    let (a, base') ← (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)).run hst.base
    return (a, { hst with base := base' })) at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨y, hy, rfl⟩
  unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
  | none =>
    intro hy
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hGen
  | some bp =>
    rcases bp with ⟨_, bEntry⟩
    intro hy
    dsimp only at hy
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rcases hGen with ⟨u₀, j₀, hidx₀, hany₀⟩
    refine ⟨u₀, j₀, hidx₀, ?_⟩
    rw [List.any_map, List.any_congr rfl]
    · exact hany₀
    · intro ⟨idx, b⟩
      dsimp only [Function.comp_def]
      split_ifs <;> rfl

theorem revealSpkSk_validStep (S : Setup) (P : Primitives) (bIdx : Nat) (pk sk : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst) :
    ∀ x ∈ support ((liftShCrBase (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j))).run hst),
      ValidTargetRecv KeyIndState.spkBundles bIdx pk sk x.2 := by
  intro x hx
  change x ∈ support (do
    let (a, base') ← (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)).run hst.base
    return (a, { hst with base := base' })) at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨y, hy, rfl⟩
  unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
  | none =>
    intro hy
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact hV
  | some bp =>
    rcases bp with ⟨_, bEntry⟩
    intro hy
    dsimp only at hy
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨hV.1, hV.2.1, hV.2.2.1, ?_, hV.2.2.2.2⟩
    intro p hp hidx
    rw [List.mem_map] at hp
    rcases hp with ⟨⟨idx, b⟩, hmem, hp_eq⟩
    cases h_eq : (idx == (u.val, j.val)) <;>
      simp only [h_eq, ↓reduceIte, Bool.false_eq_true] at hp_eq <;>
      (subst hp_eq; exact hV.2.2.2.1 (idx, b) hmem hidx)

theorem pqxdhKeyIndShCrCachedImpl_clearFalse (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl false S P q).run hst), clearShCrTarget x.2 = x.2 := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_clearFalse P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles :=
        bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j hst hClear
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_clearFalse P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) hst hClear
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hClear
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_clearFalse P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst hClear
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hClear
  | acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_clearFalse P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr hst hClear
  | acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_clearFalse P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst hClear
  | initPrin u =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.initPrin u)) hst hClear
  | corruptIK u =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.corruptIK u)) hst hClear
  | genOPK u j o =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.genOPK u j o)) hst hClear
  | testSession sid =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.testSession sid)) hst hClear
  | roQuery secrets =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.roQuery secrets)) hst hClear
  | revealDhSecrets =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P .revealDhSecrets) hst hClear
  | revealSessionKey sid =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.revealSessionKey sid)) hst
      hClear
  | registerKey sk =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.registerKey sk)) hst hClear
  | revealSpkSk u j =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)) hst hClear

theorem pqxdhKeyIndShCrCachedImpl_afterGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyIndShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' =>
        setShCrTarget s' bIdx pk sk) <$> (pqxdhKeyIndShCrCachedImpl false S P q).run hst) ∧
    (∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl false S P q).run hst),
      hasGeneratedTargetBundle S bIdx x.2.base.spkBundles) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_afterGen P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ =>
        rfl) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j bIdx hst hClear hGen
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_afterGen P KeyIndState.principals KeyIndState.spkBundles
        KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) bIdx hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout) hGen
    · simp only [↓reduceIte]
      refine ⟨fun _ _ => by simp [StateT.run_pure, Prod.map], fun x hx => ?_⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hGen
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_afterGen P KeyIndState.principals KeyIndState.spkBundles
        KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) bIdx hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout) hGen
    · simp only [↓reduceIte]
      refine ⟨fun _ _ => by simp [StateT.run_pure, Prod.map], fun x hx => ?_⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hGen
  | acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_afterGen P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptOPK k j o hdr) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_afterGen P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptNoOPK k j l hdr) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | initPrin u =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.initPrin
      u)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.initPrin u) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | corruptIK u =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.corruptIK
      u)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.corruptIK u) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | genOPK u j o =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.genOPK u j
      o)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.genOPK u j o) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | testSession sid =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.testSession
      sid)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.testSession sid) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | roQuery secrets =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.roQuery
      secrets)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.roQuery secrets) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | revealDhSecrets =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      .revealDhSecrets) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P .revealDhSecrets hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | revealSessionKey sid =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      (.revealSessionKey sid)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.revealSessionKey sid) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | registerKey sk =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.registerKey
      sk)) bIdx hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.registerKey sk) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hGen
  | revealSpkSk u j =>
    exact revealSpkSk_afterGen S P bIdx u j hst hGen

theorem pqxdhKeyIndShCrCachedImpl_beforeGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hNotGen : ¬ hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyIndShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' =>
        setShCrTarget s' bIdx pk sk) <$> (pqxdhKeyIndShCrCachedImpl false S P q).run hst) ∨
    ((∀ obs : (keyIndSpec S).Range q × KeyIndShCrState S → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (pqxdhKeyIndShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pair.1 pair.2) >>= fun x
          =>
        obs (x.1, clearShCrTarget x.2)] =
      𝒟[(pqxdhKeyIndShCrCachedImpl false S P q).run hst >>= obs]) ∧
     (∀ pk sk,
       ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk)),
      x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
      hasGeneratedTargetBundle S bIdx (clearShCrTarget x.2).base.spkBundles)) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_beforeGen P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ =>
        rfl) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j bIdx hst hClear hNotGen
  | initiateOPK u i bundle =>
    left; intro pk sk; dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_setShCrTarget P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) hst bIdx pk sk
    · simp [StateT.run_pure, Prod.map]
  | initiateNoOPK u i bundle =>
    left; intro pk sk; dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_setShCrTarget P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst bIdx pk sk
    · simp [StateT.run_pure, Prod.map]
  | acceptOPK k j o hdr =>
    left; exact runShCrAcceptGeneric_setShCrTarget P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr hst bIdx
  | acceptNoOPK k j l hdr =>
    left; exact runShCrAcceptGeneric_setShCrTarget P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst bIdx
  | initPrin u =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.initPrin u)) hst bIdx
  | corruptIK u =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.corruptIK u)) hst bIdx
  | genOPK u j o =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.genOPK u j o)) hst bIdx
  | testSession sid =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.testSession sid)) hst
      bIdx
  | roQuery secrets =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.roQuery secrets)) hst
      bIdx
  | revealDhSecrets =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P .revealDhSecrets) hst
      bIdx
  | revealSessionKey sid =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.revealSessionKey sid))
      hst bIdx
  | registerKey skAdv =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.registerKey skAdv)) hst
      bIdx
  | revealSpkSk u j =>
    left; exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)) hst
      bIdx

theorem pqxdhKeyIndShCrCachedImpl_validStep (S : Setup) (P : Primitives) (bIdx : Nat) (pk sk :
  Bytes)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl true S P q).run hst),
      ValidTargetRecv KeyIndState.spkBundles bIdx pk sk x.2 := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_validStep P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs }) (fun _ _ =>
        rfl) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j bIdx pk sk hst hV
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_validStep P KeyIndState.principals KeyIndState.spkBundles
        KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) bIdx pk sk hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout) hV
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hV
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_validStep P KeyIndState.principals KeyIndState.spkBundles
        KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) bIdx pk sk hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out
          hout) hV
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hV
  | acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_validStep P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptOPK k j o hdr) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_validStep P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptNoOPK k j l hdr) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | initPrin u =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.initPrin
      u)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.initPrin u) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | corruptIK u =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.corruptIK
      u)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.corruptIK u) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | genOPK u j o =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.genOPK u j
      o)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.genOPK u j o) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | testSession sid =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      (.testSession sid)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.testSession sid) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | roQuery secrets =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P (.roQuery
      secrets)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.roQuery secrets) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | revealDhSecrets =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      .revealDhSecrets) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P .revealDhSecrets hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | revealSessionKey sid =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      (.revealSessionKey sid)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.revealSessionKey sid) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | registerKey skAdv =>
    exact liftShCrBase_validStep KeyIndState.spkBundles (pqxdhKeyIndCachedImpl true S P
      (.registerKey skAdv)) bIdx pk sk hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.registerKey skAdv) hst.base
        (by intro _ _ h; cases h) (by intro _ _ h; cases h)) hV
  | revealSpkSk u j =>
    exact revealSpkSk_validStep S P bIdx pk sk u j hst hV

theorem pqxdhKeyIndShCrCachedImpl_sendStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl true S P q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  cases q with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_sendStep' P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles :=
        bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j hst
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_sendStep P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) hst
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runShCrInitiate2_sendStep P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact ⟨le_rfl, fun i hi => Or.inl hi⟩
  | acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_sendStep' P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr hst
  | acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_sendStep' P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst
  | initPrin u => exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.initPrin u)) hst
  | corruptIK u => exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.corruptIK u)) hst
  | genOPK u j o => exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.genOPK u j o)) hst
  | testSession sid =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.testSession sid)) hst
  | roQuery secrets =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.roQuery secrets)) hst
  | revealDhSecrets =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P .revealDhSecrets) hst
  | revealSessionKey sid =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.revealSessionKey sid)) hst
  | registerKey sk =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.registerKey sk)) hst
  | revealSpkSk u j =>
    exact liftShCrBase_sendStep (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)) hst

theorem pqxdhKeyIndShCrCachedImpl_pauseNone (S : Setup) (P : Primitives) (sIdx : Nat)
    (gq : KeyIndQuery S) (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec +
      keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPauseKeyIndQuery S P sIdx gq cont hst = none) :
    ∀ x ∈ support ((pqxdhKeyIndShCrCachedImpl true S P gq).run hst), x.2.sendCount ≤ sIdx := by
  cases gq with
  | genSPK u j =>
    exact runShCrGenSPKGeneric_pauseNone P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles :=
        bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp u j sIdx hst hLe
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery] at hNone
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyIndShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQuery] at hNone
    dsimp only [pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyIndShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_pauseNone P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr sIdx hst hLe
  | acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_pauseNone P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr sIdx hst hLe
  | initPrin u =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.initPrin u)) sIdx hst hLe
  | corruptIK u =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.corruptIK u)) sIdx hst hLe
  | genOPK u j o =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.genOPK u j o)) sIdx hst hLe
  | testSession sid =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.testSession sid)) sIdx hst hLe
  | roQuery secrets =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.roQuery secrets)) sIdx hst hLe
  | revealDhSecrets =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P .revealDhSecrets) sIdx hst hLe
  | revealSessionKey sid =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.revealSessionKey sid)) sIdx hst
      hLe
  | registerKey sk =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.registerKey sk)) sIdx hst hLe
  | revealSpkSk u j =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndCachedImpl true S P (.revealSpkSk u j)) sIdx hst hLe


end Proofs.SignalPqxdh.Security
