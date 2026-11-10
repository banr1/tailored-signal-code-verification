/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3
import Computational.Proofs.SignalPqxdh.Security.FgGapDh
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingE
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hop `G3 → G3.5`: cutoff wrapper, handshake matching, and send/recv case analysis

Defines the stage-indexed cutoff wrapper `pqxdhAuthAdvStageImpl`, proves `isAuthG3Abort`
monotonicity and `buildSecrets` ↔ `matchIdealAuthHandshake` equivalence, and discharges the
matched non-ideal receive subcases.
-/

@[expose] public section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Stage-indexed cutoff wrapper -/

/-- `AuthHybridState S` augmented with the adversary RO log and responder handshake log. -/
structure AuthAdvCutoffState (S : Setup) where
  hyb       : AuthHybridState S
  advRoLog  : List Bytes := []
  respRecs  : List AuthRespRecord := []

def AuthAdvCutoffState.empty (S : Setup) (secb : Bool) : AuthAdvCutoffState S :=
  { hyb := AuthHybridState.empty S secb
    advRoLog := []
    respRecs := [] }

@[simp]
theorem AuthAdvCutoffState.hyb_empty (S : Setup) (secb : Bool) :
    (AuthAdvCutoffState.empty S secb).hyb = AuthHybridState.empty S secb := rfl

/-- Executes `pqxdhAuthHybridKoskImpl` while logging `.roQuery` inputs and responder handshakes. -/
def pqxdhAuthAdvStageImpl (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthAdvCutoffState S) ProbComp) := fun q =>
  match q with
  | .roQuery secrets => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl stage true true S P (.roQuery secrets)).run hst.hyb
    return (resp, { hst with hyb := h', advRoLog := secrets :: hst.advRoLog }))
  | .recvOPK k j o msg => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl stage true true S P (.recvOPK k j o msg)).run hst.hyb
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
    return (resp, { hst with hyb := h', respRecs := rRec :: hst.respRecs }))
  | .recvNoOPK k j l msg => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl stage true true S P (.recvNoOPK k j l msg)).run
      hst.hyb
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
    return (resp, { hst with hyb := h', respRecs := rRec :: hst.respRecs }))
  | q => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl stage true true S P q).run hst.hyb
    return (resp, { hst with hyb := h' }))

theorem map_hyb_pqxdhAuthAdvStageImpl (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthAdvCutoffState S) :
    Prod.map id AuthAdvCutoffState.hyb <$> ((pqxdhAuthAdvStageImpl stage S P q).run hst) =
      (pqxdhAuthHybridKoskImpl stage true true S P q).run hst.hyb := by
  cases q <;> simp [pqxdhAuthAdvStageImpl, StateT.run_mk, Prod.map]

theorem map_hyb_fullAuthAdvStageImpl (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthAdvCutoffState S) :
    Prod.map id AuthAdvCutoffState.hyb <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthAdvCutoffState S) ProbComp) +
        pqxdhAuthAdvStageImpl stage S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl stage true true S P) q).run hst.hyb := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_hyb_pqxdhAuthAdvStageImpl stage S P gq hst

theorem simulateQ_map_hyb_fullAuthAdvStageImpl (stage : AuthHybridStage) (S : Setup) (P :
    Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl stage S P
    let fullHyb := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthHybridState S) ProbComp) + pqxdhAuthHybridKoskImpl stage true true S P
    Prod.map id AuthAdvCutoffState.hyb <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullHyb oa).run hst.hyb :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthAdvCutoffState.hyb
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl stage S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridState S) ProbComp) + pqxdhAuthHybridKoskImpl stage true true S P)
    (map_hyb_fullAuthAdvStageImpl stage S P)
    oa hst

/-- Combined Hop 1–3 abort predicate on `AuthHybridState S`. -/
def isAuthG3Abort {S : Setup} (P : Primitives) (hst : AuthHybridState S) : Bool :=
  hasEcPkCollisionAuth P hst || hasBadSigAuth hst ||
  hasKemPkCollisionAuth hst || hasBadKemShCrAuth P hst

noncomputable def finalizeAuthKosk (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalSt : AuthHybridState S) : ProbComp Bool :=
  let allChallengedClean := finalSt.base.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.base.principals s)
  if isAuthG3Abort P finalSt then
    $ᵗ Bool
  else if finalSt.base.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)

@[simp]
theorem finalizeAuthKosk_of_isAuthG3Abort {S : Setup} (P : Primitives)
    (secb b' : Bool) (finalSt : AuthHybridState S)
    (hAbort : isAuthG3Abort P finalSt = true) :
    finalizeAuthKosk S P secb b' finalSt = $ᵗ Bool := by
  unfold finalizeAuthKosk
  simp [hAbort]

theorem authKoskExpAtStage_eq_bind_finalizeAuthKosk (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage stage S P A = (do
      let secb ← $ᵗ Bool
      let initSt := AuthHybridState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S)
        ProbComp) +
        pqxdhAuthHybridKoskImpl stage true true S P
      let (b', finalSt) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalSt) := rfl

theorem authKoskExpAtStage_eq_advStage (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage stage S P A = (do
      let secb ← $ᵗ Bool
      let initSt := AuthAdvCutoffState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthAdvCutoffState S)
        ProbComp) +
        pqxdhAuthAdvStageImpl stage S P
      let (b', finalHst) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalHst.hyb) := by
  rw [authKoskExpAtStage_eq_bind_finalizeAuthKosk]
  apply bind_congr; intro secb
  have hsim := simulateQ_map_hyb_fullAuthAdvStageImpl stage S P A.run
    (AuthAdvCutoffState.empty S secb)
  dsimp only [AuthAdvCutoffState.hyb_empty] at hsim ⊢
  rw [← hsim, bind_map_left]
  rfl

theorem authFixedAdvG3_sub_G3_5_le_two_mul_abs_sub
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    |authFixedAdvG3 S P A - authFixedAdvG3_5 S P A| ≤
      2 * |(𝒟[authKoskExpAtStage .g3_5 S P A] {true}).toReal -
           (𝒟[authKoskExpAtStage .g3 S P A] {true}).toReal| := by
  have hG3 : authFixedAdvG3 S P A = (𝒟[authKoskExpAtStage .g3 S P A].boolBias).toReal := by
    change authFixedAdvAtStage .g3 S P A = _
    rw [authFixedAdvAtStage_eq_authKoskAdvAtStage .g3 S P A]
    rfl
  have hG35 : authFixedAdvG3_5 S P A = (𝒟[authKoskExpAtStage .g3_5 S P A].boolBias).toReal := by
    change authFixedAdvAtStage .g3_5 S P A = _
    rw [authFixedAdvAtStage_eq_authKoskAdvAtStage .g3_5 S P A]
    rfl
  rw [hG3, hG35, abs_sub_comm (𝒟[authKoskExpAtStage .g3_5 S P A] {true}).toReal]
  exact abs_sub_boolBias_toReal_le_two_mul_abs_sub
    (authKoskExpAtStage .g3 S P A) (authKoskExpAtStage .g3_5 S P A)

/-! ## `isAuthG3Abort` monotonicity -/

theorem hasDuplicateBytes_eq_false_of_nodup :
    ∀ {L : List Bytes}, L.Nodup → hasDuplicateBytes L = false
  | [], _ => rfl
  | x :: xs, h => by
    rcases List.nodup_cons.mp h with ⟨hx, hxs⟩
    simp only [hasDuplicateBytes, Bool.or_eq_false_iff, hasDuplicateBytes_eq_false_of_nodup hxs,
      and_true]
    exact Bool.eq_false_iff.mpr (fun hmem => hx (List.contains_iff_mem.mp hmem))

theorem hasDuplicateBytes_mono_sublist {L1 L2 : List Bytes}
    (hSub : L1.Sublist L2) (hDup : hasDuplicateBytes L1 = true) :
    hasDuplicateBytes L2 = true := by
  by_contra hNot
  have hF2 : hasDuplicateBytes L2 = false := Bool.eq_false_iff.mpr hNot
  have hNodup2 : L2.Nodup := nodup_of_hasDuplicateBytes_eq_false L2 hF2
  have hNodup1 : L1.Nodup := hNodup2.sublist hSub
  have hF1 : hasDuplicateBytes L1 = false := hasDuplicateBytes_eq_false_of_nodup hNodup1
  rw [hDup] at hF1; cases hF1

/-- Monotone state-extension relation preserved by `pqxdhAuthHybridKoskImpl` queries. -/
structure AuthHybridExtends {S : Setup} (P : Primitives)
    (hst1 hst2 : AuthHybridState S) : Prop where
  prin_pks_sub  :
    (hst1.base.principals.map (fun (_, e) => P.pow8 e.ikAPk)).Sublist
      (hst2.base.principals.map (fun (_, e) => P.pow8 e.ikAPk))
  spk_pks_sub   :
    (hst1.base.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)).Sublist
      (hst2.base.spkBundles.map (fun (_, b) => P.pow8 b.spkPk))
  opk_pks_sub   :
    (hst1.base.opkEntries.map (fun (_, o) => P.pow8 o.opkPk)).Sublist
      (hst2.base.opkEntries.map (fun (_, o) => P.pow8 o.opkPk))
  kem_pks_sub   :
    (hst1.base.spkBundles.map (fun (_, b) => b.pqspkPk)).Sublist
      (hst2.base.spkBundles.map (fun (_, b) => b.pqspkPk))
  sessions_sub  : hst1.base.sessions.Sublist hst2.base.sessions
  initRecs_sub  : hst1.initKemRecs.Sublist hst2.initKemRecs
  recvRecs_sub  : hst1.recvKemRecs.Sublist hst2.recvKemRecs

theorem AuthHybridExtends.refl {S : Setup} (P : Primitives) (hst : AuthHybridState S) :
    AuthHybridExtends P hst hst :=
  ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
   List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩

theorem AuthHybridExtends.trans {S : Setup} {P : Primitives}
    {hst1 hst2 hst3 : AuthHybridState S}
    (h12 : AuthHybridExtends P hst1 hst2) (h23 : AuthHybridExtends P hst2 hst3) :
    AuthHybridExtends P hst1 hst3 :=
  ⟨h12.prin_pks_sub.trans h23.prin_pks_sub,
   h12.spk_pks_sub.trans h23.spk_pks_sub,
   h12.opk_pks_sub.trans h23.opk_pks_sub,
   h12.kem_pks_sub.trans h23.kem_pks_sub,
   h12.sessions_sub.trans h23.sessions_sub,
   h12.initRecs_sub.trans h23.initRecs_sub,
   h12.recvRecs_sub.trans h23.recvRecs_sub⟩

theorem isAuthG3Abort_mono_of_extends {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S}
    (hExt : AuthHybridExtends P hst1 hst2)
    (hAb : isAuthG3Abort P hst1 = true) :
    isAuthG3Abort P hst2 = true := by
  unfold isAuthG3Abort at hAb ⊢
  simp only [Bool.or_eq_true] at hAb ⊢
  rcases hAb with ((hEc | hSig) | hKem) | hShCr
  · left; left; left
    unfold hasEcPkCollisionAuth allHonestEcPksAuth HasAuthState.toAuthState
      instHasAuthStateAuthHybridState at hEc ⊢
    dsimp only at hEc ⊢
    have hSub4 :
        (hst1.base.sessions.map (fun s => P.pow8 (P.x25519Base s.ekASk))).Sublist
          (hst2.base.sessions.map (fun s => P.pow8 (P.x25519Base s.ekASk))) :=
      hExt.sessions_sub.map _
    have hSubAll :=
      ((hExt.prin_pks_sub.append hExt.spk_pks_sub).append hExt.opk_pks_sub).append hSub4
    exact hasDuplicateBytes_mono_sublist hSubAll hEc
  · left; left; right
    unfold hasBadSigAuth HasAuthState.toAuthState instHasAuthStateAuthHybridState at hSig ⊢
    dsimp only at hSig ⊢
    rw [List.any_eq_true] at hSig ⊢
    rcases hSig with ⟨s, hs, hBadS⟩
    exact ⟨s, hExt.sessions_sub.subset hs, hBadS⟩
  · left; right
    unfold hasKemPkCollisionAuth allHonestKemPksAuth HasAuthState.toAuthState
      instHasAuthStateAuthHybridState at hKem ⊢
    dsimp only at hKem ⊢
    exact hasDuplicateBytes_mono_sublist hExt.kem_pks_sub hKem
  · right
    unfold hasBadKemShCrAuth _root_.SignalPqxdh.Security.hasBadKemShCrRecords
      HasAuthState.toInitKemRecs HasAuthState.toRecvKemRecs
      instHasAuthStateAuthHybridState at hShCr ⊢
    dsimp only at hShCr ⊢
    rw [List.any_eq_true] at hShCr ⊢
    rcases hShCr with ⟨i, hi, hAnyR⟩
    rw [List.any_eq_true] at hAnyR
    rcases hAnyR with ⟨r, hr, hPair⟩
    refine ⟨i, hExt.initRecs_sub.subset hi, ?_⟩
    rw [List.any_eq_true]
    exact ⟨r, hExt.recvRecs_sub.subset hr, hPair⟩

private theorem map_prin_ikAPk_corrupt {P : Primitives} (u : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))).map
        (fun (_, e) => P.pow8 e.ikAPk) =
    principals.map (fun (_, e) => P.pow8 e.ikAPk) := by
  rw [List.map_map]
  congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

private theorem map_opk_opkPk_consume {P : Primitives} (key : Nat × Nat × Nat)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) :
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (_, o) => P.pow8 o.opkPk) =
    opkEntries.map (fun (_, o) => P.pow8 o.opkPk) := by
  rw [List.map_map]
  congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

private theorem state_eq_of_liftM {σ α : Type} (mx : ProbComp α) (s : σ) :
    ∀ p ∈ support ((liftM mx : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp
  simp only [StateT.run_monadLift, monadLift_self, support_bind, Set.mem_iUnion,
    mem_support_pure_iff] at hp
  rcases hp with ⟨_, _, rfl⟩; rfl

private theorem state_eq_of_pure {σ α : Type} (a : α) (s : σ) :
    ∀ p ∈ support ((pure a : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp
  simp only [StateT.run_pure, mem_support_pure_iff] at hp
  rcases hp with ⟨_, rfl⟩; rfl

private theorem authHybridExtends_bind_state_eq {S : Setup} {α β : Type} (P : Primitives)
    {m1 : StateT (AuthHybridState S) ProbComp α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S)
    {y : β × AuthHybridState S}
    (hy : y ∈ support ((m1 >>= f).run hst))
    (h1 : ∀ p ∈ support (m1.run hst), p.2 = hst)
    (h2 : ∀ a, ∀ y ∈ support ((f a).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hy
  rcases hy with ⟨⟨a, hst'⟩, hp, hy'⟩
  rw [h1 (a, hst') hp] at hy'
  exact h2 a y hy'

private theorem authHybridExtends_pure_noneResp {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pure AuthResponse.noneResp : StateT (AuthHybridState S) ProbComp
      AuthResponse).run hst)) :
    AuthHybridExtends P hst y.2 := by
  rw [StateT.run_pure, mem_support_pure_iff] at hy
  rcases hy with ⟨_, rfl⟩
  exact AuthHybridExtends.refl P hst

private theorem authHybridExtends_if_noneResp {S : Setup} (P : Primitives) (c : Prop) [Decidable c]
    (m : StateT (AuthHybridState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (h : y ∈ support (m.run hst) → AuthHybridExtends P hst y.2)
    (hy : y ∈ support ((if c then pure AuthResponse.noneResp else m).run hst)) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · exact authHybridExtends_pure_noneResp P hst hy
  · exact h hy

private theorem authHybridExtends_ite_bind1 {S : Setup} {α1 α β : Type} (P : Primitives)
    {c : Prop} [Decidable c]
    {d1 : ProbComp α1} {g : α1 → α} {d2 : ProbComp α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S) {y : β × AuthHybridState S}
    (hy : y ∈ support ((if c then (do let dk ← liftM d1; let x ← pure (g dk); f x)
                        else (do let x ← liftM d2; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun dk y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_pure _ hst) (fun x y hy => hk x y
      hy)
  · exact authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun x y hy => hk x y
      hy)

private theorem authHybridExtends_ite_bind2 {S : Setup} {α1 α2 α β : Type} (P : Primitives)
    {c : Prop} [Decidable c]
    {d1 : ProbComp α1} {d2 : ProbComp α2} {g : α1 → α2 → α} {d3 : ProbComp α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S) {y : β × AuthHybridState S}
    (hy : y ∈ support ((if c then (do let r ← liftM d1; let c ← liftM d2; let x ← pure (g r c); f x)
                        else (do let x ← liftM d3; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun r y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun c y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_pure _ hst) (fun x y hy => hk x y
      hy)
  · exact authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun x y hy => hk x y
      hy)

private theorem authHybridExtends_ite_bind3 {S : Setup} {α1 α2 α β : Type} (P : Primitives)
    {c : Prop} [Decidable c]
    {d1 : ProbComp α1} {d2 : ProbComp α2} {g : α1 → α2 → α} {v : α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S) {y : β × AuthHybridState S}
    (hy : y ∈ support ((if c then
        (do let ms ← liftM d1; let cn ← liftM d2; let x ← pure (g ms cn); f x)
                        else (do let x ← pure v; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun ms y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun cn y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy (state_eq_of_pure _ hst) (fun x y hy => hk x y
      hy)
  · exact authHybridExtends_bind_state_eq P hst hy (state_eq_of_pure _ hst) (fun x y hy => hk x y
      hy)

private theorem authHybridExtends_ite_bind4 {S : Setup} {α β : Type} (P : Primitives)
    {c : Prop} [Decidable c]
    {d1 : ProbComp α} {v : α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S) {y : β × AuthHybridState S}
    (hy : y ∈ support ((if c then (do let x ← liftM d1; f x)
                        else (do let x ← pure v; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · exact authHybridExtends_bind_state_eq P hst hy (state_eq_of_liftM _ hst) (fun x y hy => hk x y
      hy)
  · exact authHybridExtends_bind_state_eq P hst hy (state_eq_of_pure _ hst) (fun x y hy => hk x y
      hy)

private theorem authHybridExtends_of_liftAuthBase {S : Setup} (P : Primitives)
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base),
      AuthHybridExtends P hst { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((liftAuthBase m).run hst)) :
    AuthHybridExtends P hst y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩
  exact h (resp, base') hp

theorem authHybridExtends_runAuthHybridSendKosk {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst)) :
    AuthHybridExtends P hst y.2 := by
  unfold runAuthHybridSendKosk at hy
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
  refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    rw [hF] at hy; exact authHybridExtends_pure_noneResp P hst hy
  | some ue =>
    rcases ue with ⟨_, uEntry⟩; rw [hF] at hy; dsimp only at hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_bind_state_eq P hst hy
      (state_eq_of_liftM _ hst) (fun ekASk y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy
      (state_eq_of_liftM _ hst) (fun kemCoins y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy
      (state_eq_of_liftM _ hst) (fun ephASk y hy => ?_)
    refine authHybridExtends_bind_state_eq P hst hy
      (state_eq_of_liftM _ hst) (fun spqrCoins y hy => ?_)
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
    | none =>
      rw [hKem] at hy; exact authHybridExtends_pure_noneResp P hst hy
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; rw [hKem] at hy; dsimp only at hy
      refine authHybridExtends_ite_bind1 P hst hy (fun drRo y hy => ?_)
      rcases drRo with ⟨drKey, roCache'⟩
      refine authHybridExtends_ite_bind2 P hst hy (fun rkRo y hy => ?_)
      rcases rkRo with ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      refine authHybridExtends_ite_bind3 P hst hy (fun mkCk y hy => ?_)
      rcases mkCk with ⟨mkSeed, ck1_1⟩
      cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
      | none =>
        rw [hSpqr] at hy; exact authHybridExtends_pure_noneResp P hst hy
      | some spqrOut =>
        rcases spqrOut with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [hSpqr] at hy; dsimp only at hy
        refine authHybridExtends_ite_bind4 P hst hy (fun deriveMessageKeys y hy => ?_)
        rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
        have hInitSub :
            hst.initKemRecs.Sublist
              ({ sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs :=
                ss } :: hst.initKemRecs) :=
          List.sublist_cons_self _ _
        split_ifs at hy <;>
          (rw [StateT.run_pure, mem_support_pure_iff] at hy;
           rcases hy with ⟨_, rfl⟩;
           exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
             List.Sublist.refl _, List.sublist_cons_self _ _,
             hInitSub, List.Sublist.refl _⟩)

theorem authHybridExtends_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    AuthHybridExtends P hst y.2 := by
  unfold pqxdhAuthHybridKoskImpl at hy
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy
    split_ifs at hy
    · exact authHybridExtends_pure_noneResp P hst hy
    · exact authHybridExtends_runAuthHybridSendKosk stage useRo P (.sendOPK u i) u bundle m0 m1 hst
        hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy
    split_ifs at hy
    · exact authHybridExtends_pure_noneResp P hst hy
    · exact authHybridExtends_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) u bundle m0 m1
        hst hy
  | recvOPK k j o msg =>
    dsimp only at hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            rw [hFk] at hy; exact authHybridExtends_pure_noneResp P hst hy
          | some ke =>
            rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
            cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              rw [hFb] at hy; exact authHybridExtends_pure_noneResp P hst hy
            | some kb =>
              rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
              cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
                o.val)) with
              | none =>
                rw [hFo] at hy; exact authHybridExtends_pure_noneResp P hst hy
              | some oo =>
                rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
                refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
                refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
                cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                    | none =>
                      rw [hDec] at hy; exact authHybridExtends_pure_noneResp P hst hy
                    | some ss =>
                      rw [hDec] at hy; dsimp only at hy
                      rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
                      refine AuthHybridExtends.trans ?_
                        (authHybridExtends_bind_state_eq P _ hy
                          (state_eq_of_liftM _ _) (fun schedRes y hy => ?_))
                      · exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.sublist_cons_self _ _⟩
                      · cases schedRes with
                      | none =>
                        exact authHybridExtends_pure_noneResp P _ hy
                      | some out =>
                        rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                        dsimp only at hy
                        cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                        | none =>
                          rw [hFS] at hy; dsimp only at hy
                          rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                            mem_support_pure_iff] at hy
                          rcases hy with ⟨_, rfl⟩
                          refine ⟨List.Sublist.refl _, List.Sublist.refl _, ?_,
                            List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                              List.Sublist.refl _⟩
                          dsimp only; rw [map_opk_opkPk_consume]
                        | some se =>
                          rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                          split_ifs at hy <;>
                            (rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                              mem_support_pure_iff] at hy;
                             rcases hy with ⟨_, rfl⟩;
                             refine ⟨List.Sublist.refl _, List.Sublist.refl _, ?_,
                               List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                                 List.Sublist.refl _⟩;
                             dsimp only; rw [map_opk_opkPk_consume])
  | recvNoOPK k j l msg =>
    dsimp only at hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            rw [hFk] at hy; exact authHybridExtends_pure_noneResp P hst hy
          | some ke =>
            rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
            cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              rw [hFb] at hy; exact authHybridExtends_pure_noneResp P hst hy
            | some kb =>
              rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
              refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
              cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                | none =>
                  rw [hDec] at hy; exact authHybridExtends_pure_noneResp P hst hy
                | some ss =>
                  rw [hDec] at hy; dsimp only at hy
                  rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
                  refine AuthHybridExtends.trans ?_
                    (authHybridExtends_bind_state_eq P _ hy
                      (state_eq_of_liftM _ _) (fun schedRes y hy => ?_))
                  · exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                      List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                      List.sublist_cons_self _ _⟩
                  · cases schedRes with
                  | none =>
                    exact authHybridExtends_pure_noneResp P _ hy
                  | some out =>
                    rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                    dsimp only at hy
                    cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | none =>
                      rw [hFS] at hy; dsimp only at hy
                      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                        mem_support_pure_iff] at hy
                      rcases hy with ⟨_, rfl⟩
                      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.Sublist.refl _⟩
                    | some se =>
                      rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                      split_ifs at hy <;>
                        (rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                          mem_support_pure_iff] at hy;
                         rcases hy with ⟨_, rfl⟩;
                         exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                           List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                             List.Sublist.refl _⟩)
  | initPrin u =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨sec0, _, secSign, _, _, rfl⟩
      exact ⟨List.sublist_cons_self _ _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | corruptIK u =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩
      refine ⟨?_, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
      dsimp only; rw [map_prin_ikAPk_corrupt]
  | genSPK u j =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp
        rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, _, rfl⟩
        exact ⟨List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _,
          List.sublist_cons_self _ _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | genOPK u j o =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨opkSk, _, _, rfl⟩
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.sublist_cons_self _ _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | registerKey sk =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roQuery secrets =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roRootQuery rk dh =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | revealDhSecrets =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst)

theorem isAuthG3Abort_mono_pqxdhAuthAdvStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (hAb : isAuthG3Abort P s.hyb = true)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl stage S P q).run s)) :
    isAuthG3Abort P y.2.hyb = true := by
  have hyHyb : (y.1, y.2.hyb) ∈ support ((pqxdhAuthHybridKoskImpl stage true true S P q).run
    s.hyb) := by
    cases q <;>
      (simp only [pqxdhAuthAdvStageImpl, StateT.run_mk, support_bind, Set.mem_iUnion,
        mem_support_pure_iff] at hy;
       rcases hy with ⟨⟨resp, h'⟩, hh', rfl⟩;
       exact hh')
  exact isAuthG3Abort_mono_of_extends P (authHybridExtends_pqxdhAuthHybridKoskImpl stage true true P
    q s.hyb hyHyb) hAb

theorem isAuthG3Abort_withBaseRoCache {S : Setup} (P : Primitives)
    (c : List (Bytes × DRKey)) (hst : AuthHybridState S) :
    isAuthG3Abort P { hst with base := { hst.base with roCache := c } } = isAuthG3Abort P hst := rfl

theorem nodup_principals_of_hasEcPkCollisionAuth_false {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) (hNoEc : hasEcPkCollisionAuth P hst = false) :
    (hst.base.principals.map (fun (_, e) => P.pow8 e.ikAPk)).Nodup := by
  have hNodup := nodup_of_hasDuplicateBytes_eq_false (allHonestEcPksAuth P hst) hNoEc
  unfold allHonestEcPksAuth HasAuthState.toAuthState instHasAuthStateAuthHybridState at hNodup
  dsimp only at hNodup
  exact (((List.nodup_append.mp hNodup).1 |> List.nodup_append.mp).1 |> List.nodup_append.mp).1

theorem nodup_spkBundles_of_hasEcPkCollisionAuth_false {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) (hNoEc : hasEcPkCollisionAuth P hst = false) :
    (hst.base.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)).Nodup := by
  have hNodup := nodup_of_hasDuplicateBytes_eq_false (allHonestEcPksAuth P hst) hNoEc
  unfold allHonestEcPksAuth HasAuthState.toAuthState instHasAuthStateAuthHybridState at hNodup
  dsimp only at hNodup
  exact (((List.nodup_append.mp hNodup).1 |> List.nodup_append.mp).1 |> List.nodup_append.mp).2.1

theorem nodup_spkBundles_of_hasKemPkCollisionAuth_false {S : Setup}
    (hst : AuthHybridState S) (hNoKem : hasKemPkCollisionAuth hst = false) :
    (hst.base.spkBundles.map (fun (_, b) => b.pqspkPk)).Nodup :=
  nodup_of_hasDuplicateBytes_eq_false (allHonestKemPksAuth hst) hNoKem

theorem fresh_imp_spkHonest_and_pqspkHonest_of_hasBadSigAuth_false {S : Setup}
    {hst : AuthHybridState S} {s : AuthInitiatorEntry S}
    (hNoBad : hasBadSigAuth hst = false)
    (hs : s ∈ hst.base.sessions) (hFresh : s.fresh = true) :
    s.spkHonest = true ∧ s.pqspkHonest = true := by
  unfold hasBadSigAuth HasAuthState.toAuthState instHasAuthStateAuthHybridState at hNoBad
  dsimp only at hNoBad
  have h : (s.fresh && (!s.spkHonest || !s.pqspkHonest)) = false :=
    Bool.eq_false_iff.mpr (List.any_eq_false.mp hNoBad s hs)
  simp only [hFresh, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  exact h

theorem eq_kemCt_and_pqspkPk_of_hasBadKemShCrAuth_false {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) (hNoBad : hasBadKemShCrAuth P hst = false)
    {i : _root_.SignalPqxdh.Security.InitKemRecord S}
    {r : _root_.SignalPqxdh.Security.RecvKemRecord}
    (hi : i ∈ hst.initKemRecs) (hr : r ∈ hst.recvKemRecs)
    (hDec : P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs)
    (hSs : r.kemSs = i.kemSs) :
    r.kemCt = i.kemCt ∧ i.pqspkPk = r.pqspkPk := by
  unfold hasBadKemShCrAuth _root_.SignalPqxdh.Security.hasBadKemShCrRecords
    HasAuthState.toInitKemRecs HasAuthState.toRecvKemRecs instHasAuthStateAuthHybridState at hNoBad
  dsimp only at hNoBad
  have hAnyR : (hst.recvKemRecs.any (fun r =>
      (P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs) &&
      (r.kemCt != i.kemCt || i.pqspkPk != r.pqspkPk))) = false :=
    Bool.eq_false_iff.mpr (List.any_eq_false.mp hNoBad i hi)
  have hPair : ((P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs) &&
      (r.kemCt != i.kemCt || i.pqspkPk != r.pqspkPk)) = false :=
    Bool.eq_false_iff.mpr (List.any_eq_false.mp hAnyR r hr)
  rw [hSs] at hDec
  simp only [hDec, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff,
    bne_eq_false_iff_eq] at hPair
  exact hPair

/-! ## Handshake secret matching -/

theorem eq_of_isCanonical_of_pow8_eq_auth (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {pk1 pk2 : Bytes} (hc1 : P.isCanonical pk1 = true) (hc2 : P.isCanonical pk2 = true)
    (hpow : P.pow8 pk1 = P.pow8 pk2) :
    pk1 = pk2 :=
  hP.toWellFormedPrimitivesδ.canon_pow8_inj pk1 pk2 hc1 hc2 hpow

theorem x25519_comm_of_pow8_eq_auth (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (a sk pk : Bytes) (hpow : P.pow8 pk = P.pow8 (P.x25519Base sk)) :
    P.x25519 a pk = P.x25519 sk (P.x25519Base a) := by
  rw [hP.x25519_pow8_congr a pk (P.x25519Base sk)
        (hP.pow8_base_len pk sk hpow) (hP.x25519Base_len sk) hpow,
      hP.toWellFormedPrimitivesδ.x25519_comm a sk]

theorem eq_of_nodup_map_auth {α β : Type} (f : α → β) {L : List α}
    (hNodup : (L.map f).Nodup) {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hEq : f a = f b) :
    a = b := by
  induction L with
  | nil => nomatch ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exfalso; exact hNodup.1 (hEq ▸ List.mem_map_of_mem hb')
    · exfalso; exact hNodup.1 (hEq.symm ▸ List.mem_map_of_mem ha')
    · exact ih hNodup.2 ha' hb'

/-- Key-store well-formedness invariant on `principals`, `spkBundles`, `opkEntries`, and `advKeys`. -/
def ValidAuthKeyStores (S : Setup) (P : Primitives) (st : AuthState S) : Prop :=
  ValidPrincipals S st.principals ∧
  ValidSpkBundles S st.spkBundles ∧
  ValidOpkEntries S st.opkEntries ∧
  (∀ kv ∈ st.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0) ∧
  (∀ kv ∈ st.spkBundles,
    kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    (∃ uEntry, (kv.1.1, uEntry) ∈ st.principals) ∧
    ∃ kpCoins, (P.kemKeyGen kpCoins).1 = kv.2.pqspkPk ∧ (P.kemKeyGen kpCoins).2 = kv.2.pqspkSk) ∧
  (∀ kv ∈ st.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ kv ∈ st.advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)

theorem validAuthKeyStores_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthKeyStores S P (AuthState.empty S secb) := by
  have hNil := validEcLists_nil S
  refine ⟨hNil.1, hNil.2.1, hNil.2.2.1, ?_, ?_, ?_, ?_⟩ <;> (intro _ h; cases h)

def idealSessionSecrets {S : Setup} (P : Primitives)
    (uEntry : PrincipalEntry) (ekASk ss : Bytes) (s : IdealAuthSession S) : Bytes :=
  buildSecrets
    (P.x25519 uEntry.secIKA0 s.peerSpkPk)
    (P.x25519 ekASk s.peerIkPk)
    (P.x25519 ekASk s.peerSpkPk)
    (s.peerOpkPk?.map (fun opkPk => P.x25519 ekASk opkPk))
    ss

def recvHandshakeSecrets (P : Primitives)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (dh4? : Option Bytes) (ss : Bytes) (hdr : HandshakeHdr) : Bytes :=
  buildSecrets
    (P.x25519 bEntry.spkSk hdr.ikAPk)
    (P.x25519 kEntry.secIKA0 hdr.ekAPk)
    (P.x25519 bEntry.spkSk hdr.ekAPk)
    dh4?
    ss

/-- Well-formedness witness for an `IdealAuthSession S` created during `runAuthHybridSendKosk`. -/
def ValidIdealAuthSession (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (s : IdealAuthSession S) (sessEntry : AuthInitiatorEntry S)
    (u : Nat) (uEntry : PrincipalEntry) (kemCoins ss_s : Bytes)
    (initRec : _root_.SignalPqxdh.Security.InitKemRecord S) : Prop :=
  sessEntry ∈ hst.base.sessions ∧
  sessEntry.sid = s.sid ∧
  sessEntry.ekASk.length = 32 ∧
  s.ekAPk = P.x25519Base sessEntry.ekASk ∧
  sessEntry.peerIkPk = s.peerIkPk ∧
  sessEntry.peerSpkPk = s.peerSpkPk ∧
  sessEntry.peerOpkPk? = s.peerOpkPk? ∧
  sessEntry.peerPqspkPk = s.peerPqspkPk ∧
  (u, uEntry) ∈ hst.base.principals ∧
  sessionSenderIdx s.sid = u ∧
  s.ikAPk = uEntry.ikAPk ∧
  P.kemEncaps s.peerPqspkPk kemCoins = some (ss_s, s.kemCt) ∧
  initRec ∈ hst.initKemRecs ∧
  initRec.pqspkPk = s.peerPqspkPk ∧
  initRec.kemCt = s.kemCt ∧
  initRec.kemSs = ss_s ∧
  (∃ skB, skB.length = 32 ∧ P.pow8 s.peerIkPk = P.pow8 (P.x25519Base skB)) ∧
  (∃ skSpk, skSpk.length = 32 ∧ P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base skSpk)) ∧
  (∀ opkPk, s.peerOpkPk? = some opkPk →
    ∃ skOpk, skOpk.length = 32 ∧ P.pow8 opkPk = P.pow8 (P.x25519Base skOpk))

/-- Well-formedness witness for a responder handshake at `evalAuthHybridRecvSchedule`. -/
def ValidAuthRespHandshake (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (k : Fin S.N_id) (j : Fin S.N_recv)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (dh4? : Option Bytes)
    (ss_r : Bytes) (recEntry : _root_.SignalPqxdh.Security.RecvKemRecord)
    (hdr : HandshakeHdr) : Prop :=
  (k.val, kEntry) ∈ hst.base.principals ∧
  ((k.val, j.val), bEntry) ∈ hst.base.spkBundles ∧
  hdr.ikAPk.length = 32 ∧
  hdr.ekAPk.length = 32 ∧
  P.isCanonical hdr.ekAPk = true ∧
  P.kemDecaps bEntry.pqspkSk hdr.kemCt = some ss_r ∧
  recEntry ∈ hst.recvKemRecs ∧
  recEntry.pqspkPk = bEntry.pqspkPk ∧
  recEntry.pqspkSk = bEntry.pqspkSk ∧
  recEntry.kemCt = hdr.kemCt ∧
  recEntry.kemSs = ss_r ∧
  ((opkPk? = none ∧ dh4? = none) ∨
   (∃ (o : Nat) (oEntry : OpkEntry),
     ((k.val, j.val, o), oEntry) ∈ hst.base.opkEntries ∧
     opkPk? = some oEntry.opkPk ∧
     dh4? = some (P.x25519 oEntry.opkSk hdr.ekAPk)))

theorem secrets_eq_imp_components {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : AuthHybridState S)
    (hNoBadKem : hasBadKemShCrAuth P hst = false)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hs : ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec)
    {k : Fin S.N_id} {j : Fin S.N_recv}
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {recEntry : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P hst k j kEntry bEntry opkPk? dh4? ss_r recEntry hdr)
    (hSecEq : idealSessionSecrets P uEntry sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr) :
    ss_s = ss_r ∧
    P.x25519 uEntry.secIKA0 s.peerSpkPk = P.x25519 bEntry.spkSk hdr.ikAPk ∧
    P.x25519 sessEntry.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 hdr.ekAPk ∧
    P.x25519 sessEntry.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk hdr.ekAPk ∧
    s.peerOpkPk?.map (fun opkPk => P.x25519 sessEntry.ekASk opkPk) = dh4? ∧
    hdr.kemCt = s.kemCt ∧
    s.peerPqspkPk = bEntry.pqspkPk := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, hEnc, hiMem, hiPq, hiCt, hiSs, _, _, _⟩
  rcases hr with ⟨_, _, _, _, _, hDec, hrMem, hrRecPq, hrRecSk, hrRecCt, hrRecSs, hrOpkCases⟩
  have hSsLen_s : ss_s.length = 32 := (hw.kemEncaps_len s.peerPqspkPk kemCoins ss_s s.kemCt hEnc).1
  have hSsLen_r : ss_r.length = 32 := hw.kemDecaps_len bEntry.pqspkSk hdr.kemCt ss_r hDec
  have h4_s : ∀ d, s.peerOpkPk?.map (fun opkPk => P.x25519 sessEntry.ekASk opkPk) = some d →
    d.length = 32 := by
    intro d hd
    cases hOpk : s.peerOpkPk? with
    | none => rw [hOpk] at hd; nomatch hd
    | some opkPk =>
      rw [hOpk, Option.map_some, Option.some.injEq] at hd
      subst hd
      exact hw.x25519_len sessEntry.ekASk opkPk
  have h4_r : ∀ d, dh4? = some d → d.length = 32 := by
    intro d hd
    rcases hrOpkCases with ⟨_, hNone⟩ | ⟨_, oEntry, _, _, hSome⟩
    · rw [hNone] at hd; nomatch hd
    · rw [hSome, Option.some.injEq] at hd
      subst hd
      exact hw.x25519_len oEntry.opkSk hdr.ekAPk
  unfold idealSessionSecrets recvHandshakeSecrets at hSecEq
  have hComp := (buildSecrets_eq_iff_of_len32
    (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _) h4_s hSsLen_s
    (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _) h4_r hSsLen_r).mp hSecEq
  rcases hComp with ⟨hSsEq, hDh1, hDh2, hDh3, hDh4⟩
  have hDecRec : P.kemDecaps recEntry.pqspkSk recEntry.kemCt = some recEntry.kemSs := by
    rw [hrRecSk, hrRecCt, hrRecSs]; exact hDec
  have hSsRec : recEntry.kemSs = initRec.kemSs := by
    rw [hrRecSs, hiSs, hSsEq]
  rcases eq_kemCt_and_pqspkPk_of_hasBadKemShCrAuth_false P hst hNoBadKem hiMem hrMem hDecRec hSsRec
    with
    ⟨hCtRec, hPqRec⟩
  rw [hrRecCt, hiCt] at hCtRec
  rw [hiPq, hrRecPq] at hPqRec
  exact ⟨hSsEq, hDh1, hDh2, hDh3, hDh4, hCtRec, hPqRec⟩

theorem secrets_eq_imp_matchIdealAuthHandshake_of_pow8_spk_eq {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : AuthHybridState S)
    (hKS : ValidAuthKeyStores S P hst.base)
    (hNoBadKem : hasBadKemShCrAuth P hst = false)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hs : ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec)
    {k : Fin S.N_id} {j : Fin S.N_recv}
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {recEntry : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P hst k j kEntry bEntry opkPk? dh4? ss_r recEntry hdr)
    (hPowSpk : P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk)
    (hSecEq : idealSessionSecrets P uEntry sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr) :
    matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr s = true := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases secrets_eq_imp_components P hP hst hNoBadKem hs hr hSecEq with
    ⟨_, hDh1, hDh2, hDh3, hDh4, hCtEq, hPqEq⟩
  rcases hKS with ⟨_, _, _, hPrins, hSpks, hOpks, _⟩
  rcases hs with ⟨_, _, hekLen, hekPk, _, _, _, _, huMem, _, hsIkPk, _, _, _, _, _,
    ⟨skB, _, hSkBPow⟩, _, hOpkKosk⟩
  rcases hr with ⟨hkMem, hbMem, hrIkLen, hrEkLen, hrEkCanon, _, _, _, _, _, _, hrOpkCases⟩
  have huIk := hPrins (u, uEntry) huMem
  have hkIk := hPrins (k.val, kEntry) hkMem
  rcases hSpks ((k.val, j.val), bEntry) hbMem with ⟨hbSkLen, hbSpkPk, _, _⟩
  have hSpkPowBase : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
    rw [← hPowSpk, hbSpkPk]
  have hPowEk : P.pow8 s.ekAPk = P.pow8 hdr.ekAPk := by
    rw [x25519_comm_of_pow8_eq_auth P hP sessEntry.ekASk bEntry.spkSk s.peerSpkPk hSpkPowBase,
      ← hekPk] at hDh3
    exact hP.x25519_inj_pow8 bEntry.spkSk s.ekAPk hdr.ekAPk
      hbSkLen (by rw [hekPk]; exact hw.x25519Base_len sessEntry.ekASk) hrEkLen hDh3
  have hEkEq : s.ekAPk = hdr.ekAPk :=
    eq_of_isCanonical_of_pow8_eq_auth P hP (by rw [hekPk]; exact hw.canon_base sessEntry.ekASk)
      hrEkCanon hPowEk
  have hPowIkB : P.pow8 kEntry.ikAPk = P.pow8 s.peerIkPk := by
    have h1 : P.x25519 sessEntry.ekASk s.peerIkPk = P.x25519 sessEntry.ekASk (P.x25519Base skB) :=
      hP.x25519_pow8_congr sessEntry.ekASk s.peerIkPk (P.x25519Base skB)
        (hP.pow8_base_len s.peerIkPk skB hSkBPow) (hw.x25519Base_len skB) hSkBPow
    have h2 : P.x25519 kEntry.secIKA0 hdr.ekAPk = P.x25519 sessEntry.ekASk (P.x25519Base
      kEntry.secIKA0) := by
      rw [← hEkEq, hekPk, hw.x25519_comm kEntry.secIKA0 sessEntry.ekASk]
    rw [h1, h2] at hDh2
    have hPowBase := hP.x25519_inj_pow8 sessEntry.ekASk (P.x25519Base skB) (P.x25519Base
      kEntry.secIKA0)
      hekLen (hw.x25519Base_len skB) (hw.x25519Base_len kEntry.secIKA0) hDh2
    rw [hkIk.2, ← hPowBase, ← hSkBPow]
  have hPowIkA : P.pow8 hdr.ikAPk = P.pow8 s.ikAPk := by
    rw [x25519_comm_of_pow8_eq_auth P hP uEntry.secIKA0 bEntry.spkSk s.peerSpkPk hSpkPowBase,
        ← huIk.2, ← hsIkPk] at hDh1
    exact (hP.x25519_inj_pow8 bEntry.spkSk s.ikAPk hdr.ikAPk
      hbSkLen (by rw [hsIkPk, huIk.2]; exact hw.x25519Base_len uEntry.secIKA0) hrIkLen hDh1).symm
  unfold matchIdealAuthHandshake
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨hPowIkA, hPowIkB⟩, hPowSpk⟩, ?_⟩, hPowEk.symm⟩, hPqEq.symm⟩, hCtEq⟩
  rcases hrOpkCases with ⟨hrOpkNone, hrDh4None⟩ | ⟨o, oEntry, hoMem, hrOpkSome, hrDh4Some⟩
  · rw [hrOpkNone]; rw [hrDh4None] at hDh4
    cases hsOpk : s.peerOpkPk? with
    | none => rfl
    | some _ => rw [hsOpk] at hDh4; nomatch hDh4
  · rw [hrOpkSome]; rw [hrDh4Some] at hDh4
    cases hsOpk : s.peerOpkPk? with
    | none => rw [hsOpk] at hDh4; nomatch hDh4
    | some sOpkPk =>
      rw [hsOpk, Option.map_some, Option.some.injEq] at hDh4
      rcases hOpkKosk sOpkPk hsOpk with ⟨skOpk, _, hSkOpkPow⟩
      have hoOpk := hOpks ((k.val, j.val, o), oEntry) hoMem
      have hOpk1 : P.x25519 sessEntry.ekASk sOpkPk = P.x25519 sessEntry.ekASk (P.x25519Base
        skOpk) :=
        hP.x25519_pow8_congr sessEntry.ekASk sOpkPk (P.x25519Base skOpk)
          (hP.pow8_base_len sOpkPk skOpk hSkOpkPow) (hw.x25519Base_len skOpk) hSkOpkPow
      have hOpk2 : P.x25519 oEntry.opkSk hdr.ekAPk = P.x25519 sessEntry.ekASk (P.x25519Base
        oEntry.opkSk) := by
        rw [← hEkEq, hekPk, hw.x25519_comm oEntry.opkSk sessEntry.ekASk]
      rw [hOpk1, hOpk2] at hDh4
      have hPowOpkBase := hP.x25519_inj_pow8 sessEntry.ekASk (P.x25519Base skOpk) (P.x25519Base
        oEntry.opkSk)
        hekLen (hw.x25519Base_len skOpk) (hw.x25519Base_len oEntry.opkSk) hDh4
      rw [beq_iff_eq, hoOpk.2, ← hPowOpkBase, ← hSkOpkPow]

/-- Equal `buildSecrets` under an honest `pqspk` and no KEM public-key collision implies `matchIdealAuthHandshake`. -/
theorem secrets_eq_imp_matchIdealAuthHandshake_of_pqspkHonest {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : AuthHybridState S)
    (hKS : ValidAuthKeyStores S P hst.base)
    (hNoBadKem : hasBadKemShCrAuth P hst = false)
    (hNoKemColl : hasKemPkCollisionAuth hst = false)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hs : ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec)
    {k : Fin S.N_id} {j : Fin S.N_recv}
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {recEntry : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P hst k j kEntry bEntry opkPk? dh4? ss_r recEntry hdr)
    (hPqHon : ∃ k_s j_s k_s_Entry b_s,
      (k_s, k_s_Entry) ∈ hst.base.principals ∧
      ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧
      P.pow8 s.peerIkPk = P.pow8 k_s_Entry.ikAPk ∧
      s.peerPqspkPk = b_s.pqspkPk)
    (hSecEq : idealSessionSecrets P uEntry sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr) :
    matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr s = true := by
  have hw := hP.toWellFormedPrimitivesδ
  have hs0 := hs
  have hr0 := hr
  rcases secrets_eq_imp_components P hP hst hNoBadKem hs hr hSecEq with
    ⟨_, _, hDh2, hDh3, _, _, hPqEq⟩
  rcases hKS with ⟨hValPrins, hValSpks, hValOpks, hPrins, hSpks, hOpks, hAdvs⟩
  rcases hs with ⟨_, _, hekLen, hekPk, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨skSpk, _, hSkSpkPow⟩,
    _⟩
  rcases hr with ⟨hkMem, hbMem, _, hrEkLen, hrEkCanon, _, _, _, _, _, _, _⟩
  have hkIk := hPrins (k.val, kEntry) hkMem
  rcases hSpks ((k.val, j.val), bEntry) hbMem with ⟨_, hbSpkPk, _, _⟩
  rcases hPqHon with ⟨k_s, j_s, k_s_Entry, b_s, hk_sMem, hb_sMem, hPowIk_s, hPq_s⟩
  have hNodupKem := nodup_spkBundles_of_hasKemPkCollisionAuth_false hst hNoKemColl
  have hBundleEq : ((k_s, j_s), b_s) = ((k.val, j.val), bEntry) :=
    eq_of_nodup_map_auth (fun (_, b) => b.pqspkPk) hNodupKem hb_sMem hbMem
      (by dsimp only; rw [← hPq_s, hPqEq])
  have hKsEq : k_s = k.val := by injection hBundleEq with hPair _; injection hPair
  subst hKsEq
  have hPrinEq : (k.val, k_s_Entry) = (k.val, kEntry) :=
    eq_of_nodup_map_auth Prod.fst hValPrins.2 hk_sMem hkMem rfl
  injection hPrinEq with _ hkEntryEq
  cases hkEntryEq
  have hPowIkBase : P.pow8 s.peerIkPk = P.pow8 (P.x25519Base kEntry.secIKA0) := by
    rw [hPowIk_s, hkIk.2]
  have hEkEq : s.ekAPk = hdr.ekAPk := by
    rw [x25519_comm_of_pow8_eq_auth P hP sessEntry.ekASk kEntry.secIKA0 s.peerIkPk hPowIkBase,
      ← hekPk] at hDh2
    have hPowEk := hP.x25519_inj_pow8 kEntry.secIKA0 s.ekAPk hdr.ekAPk
      hkIk.1 (by rw [hekPk]; exact hw.x25519Base_len sessEntry.ekASk) hrEkLen hDh2
    exact eq_of_isCanonical_of_pow8_eq_auth P hP (by
      rw [hekPk]; exact hw.canon_base sessEntry.ekASk) hrEkCanon hPowEk
  have hPowSpk : P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk := by
    have h1 : P.x25519 sessEntry.ekASk s.peerSpkPk = P.x25519 sessEntry.ekASk (P.x25519Base
      skSpk) :=
      hP.x25519_pow8_congr sessEntry.ekASk s.peerSpkPk (P.x25519Base skSpk)
        (hP.pow8_base_len s.peerSpkPk skSpk hSkSpkPow) (hw.x25519Base_len skSpk) hSkSpkPow
    have h2 : P.x25519 bEntry.spkSk hdr.ekAPk = P.x25519 sessEntry.ekASk (P.x25519Base
      bEntry.spkSk) := by
      rw [← hEkEq, hekPk, hw.x25519_comm bEntry.spkSk sessEntry.ekASk]
    rw [h1, h2] at hDh3
    have hPowBase := hP.x25519_inj_pow8 sessEntry.ekASk (P.x25519Base skSpk) (P.x25519Base
      bEntry.spkSk)
      hekLen (hw.x25519Base_len skSpk) (hw.x25519Base_len bEntry.spkSk) hDh3
    rw [hbSpkPk, ← hPowBase, ← hSkSpkPow]
  exact secrets_eq_imp_matchIdealAuthHandshake_of_pow8_spk_eq P hP hst
    ⟨hValPrins, hValSpks, hValOpks, hPrins, hSpks, hOpks, hAdvs⟩
    hNoBadKem hs0 hr0 hPowSpk hSecEq

/-! ## Matched receive case analysis -/

def lookupSpkSkTakeNonEmpty (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (spkPk : Bytes) : Bytes :=
  let wSpk := P.pow8 spkPk
  match (spkBundles.take S.N_dh).find? (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == wSpk)
    with
  | some (_, b) => b.spkSk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => sk
    | none => []

def initAuthDh1CandNonEmpty (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : AuthInitiatorEntry S) : Bytes :=
  let spkSk := lookupSpkSkTakeNonEmpty S P spkBundles advKeyPows s.peerSpkPk
  let ikAPk := lookupSenderIkPk principals (sessionSenderIdx s.sid)
  P.x25519 spkSk ikAPk

def badAuthFgDh1AtNonEmpty {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  match st.principals.find? (fun (u, _) => u == uIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some (_, uEntry), some (_, bEntry) =>
    let zTarget := P.x25519 uEntry.secIKA0 bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    let advKeyPows := st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))
    !uEntry.corrupted &&
    ((advRoLog.take maxLen).any (fun sec => extractDh1 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s =>
       initAuthDh1CandNonEmpty S P st.principals spkErased advKeyPows s == zTarget) ||
     (respRecs.take S.N_sess_tot).any (fun r =>
       respAuthDh1Cand S P spkErased r == zTarget))
  | _, _ => false

/-- Matching a `SentOPKEvent` whose responder SPK bundle already existed at send time implies an ideal send and `matchIdealAuthHandshake`. -/
theorem subcase4A_matchSentOPK_imp_idealSend_and_matchIdealAuthHandshake {S : Setup} (P :
    Primitives)
    (st0 : AuthState S) (hst : AuthHybridState S)
    (hNoEc : hasEcPkCollisionAuth P hst = false)
    {uEntry pEntry0 kEntry : PrincipalEntry} {k_s k j : Nat}
    {bEntry : SpkBundleEntry} {oEntry : OpkEntry}
    {bundle : PreKeyBundleInput} {opkId : KeyId} {opkPk ekAPk kemCt msgPlain : Bytes}
    {hdr : HandshakeHdr} {pt : Bytes}
    {s_ev : SentOPKEvent} {recvEv : RecvdOPKEvent} {idealEntry : IdealAuthSession S}
    (hSubPrin : ∀ x ∈ st0.principals, (x.1, x.2.ikAPk) ∈ hst.base.principals.map (fun (idx,
      e) => (idx, e.ikAPk)))
    (hFindPeer0 : findHonestPrincipal P st0.principals bundle.ikB = some (k_s, pEntry0))
    (hkMem : (k, kEntry) ∈ hst.base.principals)
    (hbMem0 : ((k, j), bEntry) ∈ st0.spkBundles)
    (_hOpkB : bundle.opkB? = some (opkId, opkPk))
    (hsEv : s_ev.a0 = uEntry.ikAPk ∧ s_ev.b0 = pEntry0.ikAPk ∧ s_ev.sb = bundle.spkB ∧
      s_ev.ob = opkPk ∧ s_ev.a1 = ekAPk ∧ s_ev.pk1 = bundle.pqspkB ∧ s_ev.ct = kemCt ∧ s_ev.m =
        msgPlain)
    (hrEv : recvEv.bCorr = kEntry.corrupted ∧ recvEv.a0 = hdr.ikAPk ∧ recvEv.b0 = kEntry.ikAPk ∧
      recvEv.sb = bEntry.spkPk ∧ recvEv.ob = oEntry.opkPk ∧ recvEv.a1 = hdr.ekAPk ∧
      recvEv.pk1 = bEntry.pqspkPk ∧ recvEv.ct = hdr.kemCt ∧ recvEv.m = pt)
    (hIdeal : idealEntry.ikAPk = uEntry.ikAPk ∧ idealEntry.peerIkPk = bundle.ikB ∧
      idealEntry.peerSpkPk = bundle.spkB ∧ idealEntry.peerOpkPk? = some opkPk ∧
      idealEntry.ekAPk = ekAPk ∧ idealEntry.peerPqspkPk = bundle.pqspkB ∧ idealEntry.kemCt = kemCt)
    (hMatchSent : matchSentOPK P recvEv s_ev = true) :
    (!pEntry0.corrupted ||
      (checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle &&
       (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2)) =
         true ∧
    matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk) bEntry.pqspkPk hdr
      idealEntry = true := by
  unfold matchSentOPK at hMatchSent
  simp only [Bool.and_eq_true, beq_iff_eq] at hMatchSent
  rcases hMatchSent with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hPowA0⟩, hPowB0⟩, hPowOb⟩, hPowA1⟩, hPowSb⟩, _⟩, hPk1⟩, hCt⟩,
    _⟩
  rcases hsEv with ⟨hsA0, hsB0, hsSb, hsOb, hsA1, hsPk1, hsCt, _⟩
  rcases hrEv with ⟨_, hrA0, hrB0, hrSb, hrOb, hrA1, hrPk1, hrCt, _⟩
  rcases hIdeal with ⟨hiIkA, hiIkB, hiSpk, hiOpk, hiEk, hiPq, hiCt⟩
  have hFindPeer0' : st0.principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) =
    some (k_s, pEntry0) := hFindPeer0
  have hPeerMem0 : (k_s, pEntry0) ∈ st0.principals := List.mem_of_find?_eq_some hFindPeer0'
  have hPeerPowIkB : P.pow8 pEntry0.ikAPk = P.pow8 bundle.ikB :=
    (beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => P.pow8 bundle.ikB ==
      P.pow8 x.2.ikAPk) hFindPeer0')).symm
  have hPeerMapMem := hSubPrin (k_s, pEntry0) hPeerMem0
  rw [List.mem_map] at hPeerMapMem
  rcases hPeerMapMem with ⟨⟨k_s', pEntry1⟩, hPeerMem1, hPairEq⟩
  have hks' : k_s' = k_s := congrArg Prod.fst hPairEq
  have hIkEq1 : pEntry1.ikAPk = pEntry0.ikAPk := congrArg Prod.snd hPairEq
  rw [hks'] at hPeerMem1
  have hNodupPrin := nodup_principals_of_hasEcPkCollisionAuth_false P hst hNoEc
  have hPrinEq : (k, kEntry) = (k_s, pEntry1) :=
    eq_of_nodup_map_auth (fun (_, e) => P.pow8 e.ikAPk) hNodupPrin hkMem hPeerMem1
      (by dsimp only; rw [← hrB0, hPowB0, hsB0, ← hIkEq1])
  have hksEq : k = k_s := congrArg Prod.fst hPrinEq
  refine ⟨?_, ?_⟩
  · cases hC0 : pEntry0.corrupted
    · rfl
    · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · unfold checkBundleSpkHonIdeal
        rw [hFindPeer0]
        dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hbMem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, hC0, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
        left; rw [← hrSb, hPowSb, hsSb]
      · unfold checkBundleProvenanceExact
        rw [hFindPeer0]
        dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hbMem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, Bool.true_and, beq_iff_eq]
        rw [← hrPk1, hPk1, hsPk1]
  · unfold matchIdealAuthHandshake
    rw [hiOpk]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [← hrA0, hPowA0, hsA0, hiIkA]
    · rw [← hrB0, hPowB0, hsB0, hPeerPowIkB, hiIkB]
    · rw [← hrSb, hPowSb, hsSb, hiSpk]
    · rw [← hrOb, hPowOb, hsOb]
    · rw [← hrA1, hPowA1, hsA1, hiEk]
    · rw [← hrPk1, hPk1, hsPk1, hiPq]
    · rw [← hrCt, hCt, hsCt, hiCt]

theorem subcase4A_matchSentNoOPK_imp_idealSend_and_matchIdealAuthHandshake {S : Setup} (P :
    Primitives)
    (st0 : AuthState S) (hst : AuthHybridState S)
    (hNoEc : hasEcPkCollisionAuth P hst = false)
    {uEntry pEntry0 kEntry : PrincipalEntry} {k_s k j : Nat}
    {bEntry : SpkBundleEntry}
    {bundle : PreKeyBundleInput} {ekAPk kemCt msgPlain : Bytes}
    {hdr : HandshakeHdr} {pt : Bytes}
    {s_ev : SentNoOPKEvent} {recvEv : RecvdNoOPKEvent} {idealEntry : IdealAuthSession S}
    (hSubPrin : ∀ x ∈ st0.principals, (x.1, x.2.ikAPk) ∈ hst.base.principals.map (fun (idx,
      e) => (idx, e.ikAPk)))
    (hFindPeer0 : findHonestPrincipal P st0.principals bundle.ikB = some (k_s, pEntry0))
    (hkMem : (k, kEntry) ∈ hst.base.principals)
    (hbMem0 : ((k, j), bEntry) ∈ st0.spkBundles)
    (_hOpkB : bundle.opkB? = none)
    (hsEv : s_ev.a0 = uEntry.ikAPk ∧ s_ev.b0 = pEntry0.ikAPk ∧ s_ev.sb = bundle.spkB ∧
      s_ev.a1 = ekAPk ∧ s_ev.pk1 = bundle.pqspkB ∧ s_ev.ct = kemCt ∧ s_ev.m = msgPlain)
    (hrEv : recvEv.bCorr = kEntry.corrupted ∧ recvEv.a0 = hdr.ikAPk ∧ recvEv.b0 = kEntry.ikAPk ∧
      recvEv.sb = bEntry.spkPk ∧ recvEv.a1 = hdr.ekAPk ∧
      recvEv.pk1 = bEntry.pqspkPk ∧ recvEv.ct = hdr.kemCt ∧ recvEv.m = pt)
    (hIdeal : idealEntry.ikAPk = uEntry.ikAPk ∧ idealEntry.peerIkPk = bundle.ikB ∧
      idealEntry.peerSpkPk = bundle.spkB ∧ idealEntry.peerOpkPk? = none ∧
      idealEntry.ekAPk = ekAPk ∧ idealEntry.peerPqspkPk = bundle.pqspkB ∧ idealEntry.kemCt = kemCt)
    (hMatchSent : matchSentNoOPK P recvEv s_ev = true) :
    (!pEntry0.corrupted ||
      (checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle &&
       (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2)) =
         true ∧
    matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk hdr idealEntry = true :=
      by
  unfold matchSentNoOPK at hMatchSent
  simp only [Bool.and_eq_true, beq_iff_eq] at hMatchSent
  rcases hMatchSent with ⟨⟨⟨⟨⟨⟨⟨⟨_, hPowA0⟩, hPowB0⟩, hPowA1⟩, hPowSb⟩, _⟩, hPk1⟩, hCt⟩, _⟩
  rcases hsEv with ⟨hsA0, hsB0, hsSb, hsA1, hsPk1, hsCt, _⟩
  rcases hrEv with ⟨_, hrA0, hrB0, hrSb, hrA1, hrPk1, hrCt, _⟩
  rcases hIdeal with ⟨hiIkA, hiIkB, hiSpk, hiOpk, hiEk, hiPq, hiCt⟩
  have hFindPeer0' : st0.principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) =
    some (k_s, pEntry0) := hFindPeer0
  have hPeerMem0 : (k_s, pEntry0) ∈ st0.principals := List.mem_of_find?_eq_some hFindPeer0'
  have hPeerPowIkB : P.pow8 pEntry0.ikAPk = P.pow8 bundle.ikB :=
    (beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => P.pow8 bundle.ikB ==
      P.pow8 x.2.ikAPk) hFindPeer0')).symm
  have hPeerMapMem := hSubPrin (k_s, pEntry0) hPeerMem0
  rw [List.mem_map] at hPeerMapMem
  rcases hPeerMapMem with ⟨⟨k_s', pEntry1⟩, hPeerMem1, hPairEq⟩
  have hks' : k_s' = k_s := congrArg Prod.fst hPairEq
  have hIkEq1 : pEntry1.ikAPk = pEntry0.ikAPk := congrArg Prod.snd hPairEq
  rw [hks'] at hPeerMem1
  have hNodupPrin := nodup_principals_of_hasEcPkCollisionAuth_false P hst hNoEc
  have hPrinEq : (k, kEntry) = (k_s, pEntry1) :=
    eq_of_nodup_map_auth (fun (_, e) => P.pow8 e.ikAPk) hNodupPrin hkMem hPeerMem1
      (by dsimp only; rw [← hrB0, hPowB0, hsB0, ← hIkEq1])
  have hksEq : k = k_s := congrArg Prod.fst hPrinEq
  refine ⟨?_, ?_⟩
  · cases hC0 : pEntry0.corrupted
    · rfl
    · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · unfold checkBundleSpkHonIdeal
        rw [hFindPeer0]
        dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hbMem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, hC0, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
        left; rw [← hrSb, hPowSb, hsSb]
      · unfold checkBundleProvenanceExact
        rw [hFindPeer0]
        dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hbMem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, Bool.true_and, beq_iff_eq]
        rw [← hrPk1, hPk1, hsPk1]
  · unfold matchIdealAuthHandshake
    rw [hiOpk]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, trivial⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [← hrA0, hPowA0, hsA0, hiIkA]
    · rw [← hrB0, hPowB0, hsB0, hPeerPowIkB, hiIkB]
    · rw [← hrSb, hPowSb, hsSb, hiSpk]
    · rw [← hrA1, hPowA1, hsA1, hiEk]
    · rw [← hrPk1, hPk1, hsPk1, hiPq]
    · rw [← hrCt, hCt, hsCt, hiCt]

/-- Matching an honest SPK bundle generated after send when `spkB` already matched an honest SPK triggers `hasEcPkCollisionAuth`. -/
theorem subcase4B_honest_spk_imp_hasEcPkCollisionAuth {S : Setup} (P : Primitives)
    (st0 : AuthState S) (hst : AuthHybridState S)
    {k j : Nat} {bEntry : SpkBundleEntry} {spkB : Bytes}
    (hNotIn0 : ∀ b0, ((k, j), b0) ∉ st0.spkBundles)
    (hSubSpk : ∀ x ∈ st0.spkBundles, (x.1, P.pow8 x.2.spkPk) ∈ hst.base.spkBundles.map (fun (idx,
      b) => (idx, P.pow8 b.spkPk)))
    (hbMem1 : ((k, j), bEntry) ∈ hst.base.spkBundles)
    (hGameSpk0 : isGameSpk P st0.spkBundles spkB = true)
    (hPowEq : P.pow8 bEntry.spkPk = P.pow8 spkB) :
    hasEcPkCollisionAuth P hst = true ∧ isAuthG3Abort P hst = true := by
  have hEc : hasEcPkCollisionAuth P hst = true := by
    cases hColl : hasEcPkCollisionAuth P hst
    · unfold isGameSpk at hGameSpk0
      rcases List.any_eq_true.mp hGameSpk0 with ⟨⟨k0, b0⟩, hb0Mem0, hb0Pow⟩
      have hPow0 : P.pow8 b0.spkPk = P.pow8 spkB := beq_iff_eq.mp hb0Pow
      have hk0Ne : k0 ≠ (k, j) := by
        intro hEq; subst hEq; exact hNotIn0 b0 hb0Mem0
      have hb0Map := hSubSpk (k0, b0) hb0Mem0
      rw [List.mem_map] at hb0Map
      rcases hb0Map with ⟨⟨k0', b0'⟩, hb0Mem1, hPairEq⟩
      injection hPairEq with hk0Eq hPow0Eq
      subst hk0Eq
      have hNodup := nodup_spkBundles_of_hasEcPkCollisionAuth_false P hst hColl
      have hEqEntry := eq_of_nodup_map_auth (fun (_, b) => P.pow8 b.spkPk) hNodup hb0Mem1 hbMem1
        (by dsimp only; rw [hPow0Eq, hPow0, hPowEq])
      exact False.elim (hk0Ne (congrArg Prod.fst hEqEntry))
    · rfl
  refine ⟨hEc, ?_⟩
  unfold isAuthG3Abort
  simp [hEc]

theorem find_nonEmpty_eraseSpkBundlesFg_eq_none_of_noEc {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) (hNoEc : hasEcPkCollisionAuth P hst = false)
    {k j bIdx : Nat} {bEntry : SpkBundleEntry} {pk : Bytes}
    (hbMem : ((k, j), bEntry) ∈ hst.base.spkBundles)
    (hbIdx : spkBundleFlatIdxVal S (k, j) = bIdx)
    (hPow : P.pow8 bEntry.spkPk = P.pow8 pk) :
    ((eraseSpkBundlesFg S bIdx hst.base.spkBundles).take S.N_dh).find?
      (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == P.pow8 pk) = none := by
  rw [List.find?_eq_none]
  intro ⟨k0, b0⟩ hMemTake
  have hMemErase := List.mem_of_mem_take hMemTake
  unfold eraseSpkBundlesFg at hMemErase
  rw [List.mem_map] at hMemErase
  rcases hMemErase with ⟨⟨k1, b1⟩, hb1Mem, hPairEq⟩
  injection hPairEq with hk1Eq hb0Eq
  subst hk1Eq
  intro hPred
  rcases Bool.and_eq_true_iff.mp hPred with ⟨hNonEmpty, hPow1⟩
  have hPow1Eq : P.pow8 b0.spkPk = P.pow8 pk := beq_iff_eq.mp hPow1
  have hSpkPkEq : b0.spkPk = b1.spkPk := by
    rw [← hb0Eq]; unfold eraseSpkBundleEntryFg; split_ifs <;> rfl
  rw [hSpkPkEq] at hPow1Eq
  have hNodup := nodup_spkBundles_of_hasEcPkCollisionAuth_false P hst hNoEc
  have hEntryEq := eq_of_nodup_map_auth (fun (_, b) => P.pow8 b.spkPk) hNodup hb1Mem hbMem
    (by dsimp only; rw [hPow1Eq, hPow])
  have hk1Eq' : k1 = (k, j) := congrArg Prod.fst hEntryEq
  subst hk1Eq'
  have hb0Empty : b0.spkSk = [] := by
    rw [← hb0Eq]; unfold eraseSpkBundleEntryFg
    have hbIdx' : FgGapDh.spkBundleFlatIdxVal S (k, j) = bIdx := hbIdx
    simp [hbIdx']
  rw [hb0Empty] at hNonEmpty
  nomatch hNonEmpty

/-- Matching an SPK bundle generated after send when `s.peerSpkPk` was adversary-registered triggers `badAuthFgDh1AtNonEmpty` outside EC collisions. -/
theorem subcase4B_advKey_imp_badAuthFgDh1AtNonEmpty {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen uIdx bIdx : ℕ)
    (hst : AuthHybridState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (hNoEc : hasEcPkCollisionAuth P hst = false)
    {uEntry : PrincipalEntry} {k j : Nat} {bEntry : SpkBundleEntry}
    {s : AuthInitiatorEntry S}
    (hFindU : hst.base.principals.find? (fun (u, _) => u == uIdx) = some (uIdx, uEntry))
    (hFindB : hst.base.spkBundles.find? (fun (k', _) => spkBundleFlatIdxVal S k' == bIdx) =
      some ((k, j), bEntry))
    (huNotCorr : (!uEntry.corrupted) = true)
    (huIk : uEntry.secIKA0.length = 32 ∧ uEntry.ikAPk = P.x25519Base uEntry.secIKA0)
    (hAdvSkLen : ∀ kv ∈ hst.base.advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hsMemTake : s ∈ hst.base.sessions.take S.N_dh)
    (hsSender : sessionSenderIdx s.sid = uIdx)
    (hAdvReg : isAdvRegistered P hst.base.advKeys s.peerSpkPk = true)
    (hPowEq : P.pow8 bEntry.spkPk = P.pow8 s.peerSpkPk) :
    initAuthDh1CandNonEmpty S P hst.base.principals
      (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
      (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s =
      P.x25519 uEntry.secIKA0 bEntry.spkPk ∧
    badAuthFgDh1AtNonEmpty P maxLen uIdx bIdx hst.base advRoLog respRecs = true := by
  have hw := hP.toWellFormedPrimitivesδ
  have hbMem : ((k, j), bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFindB
  have hbIdx : spkBundleFlatIdxVal S (k, j) = bIdx :=
    beq_iff_eq.mp (List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
      spkBundleFlatIdxVal S x.1 == bIdx) hFindB)
  have hFindNone := find_nonEmpty_eraseSpkBundlesFg_eq_none_of_noEc P hst hNoEc hbMem hbIdx hPowEq
  have hAdvPowsReg : isAdvRegisteredPows (hst.base.advKeys.map (fun (sk, pk) => (sk,
    P.pow8 pk))) (P.pow8 s.peerSpkPk) = true := by
    rw [isAdvRegisteredPows_map_eq]; exact hAdvReg
  unfold isAdvRegisteredPows at hAdvPowsReg
  have hCandEq :
      initAuthDh1CandNonEmpty S P hst.base.principals
        (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
        (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) s =
      P.x25519 uEntry.secIKA0 bEntry.spkPk := by
    unfold initAuthDh1CandNonEmpty lookupSpkSkTakeNonEmpty lookupSenderIkPk
    dsimp only
    rw [hFindNone, hsSender, hFindU]
    dsimp only
    cases hFA : (hst.base.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))).find? (fun (_,
      wPk) => wPk == P.pow8 s.peerSpkPk) with
    | none =>
      rcases List.any_eq_true.mp hAdvPowsReg with ⟨x, hxMem, hxPred⟩
      exact False.elim (List.find?_eq_none.mp hFA x hxMem hxPred)
    | some sp =>
      rcases sp with ⟨sk, wPk⟩
      dsimp only
      have hspMem := List.mem_of_find?_eq_some hFA
      have hPowAdv : wPk = P.pow8 s.peerSpkPk :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Bytes × Bytes) => x.2 == P.pow8 s.peerSpkPk)
          hFA)
      rw [List.mem_map] at hspMem
      rcases hspMem with ⟨⟨sk0, pk0⟩, hkvMem, hPairEq⟩
      injection hPairEq with hskEq hpow0Eq
      subst hskEq
      rcases hAdvSkLen (sk0, pk0) hkvMem with ⟨_, hPk0⟩
      dsimp only at hPk0
      have hPowSk0 : P.pow8 bEntry.spkPk = P.pow8 (P.x25519Base sk0) := by
        rw [hPowEq, ← hPowAdv, ← hpow0Eq, hPk0]
      rw [huIk.2, ← hw.x25519_comm uEntry.secIKA0 sk0,
          ← hP.x25519_pow8_congr uEntry.secIKA0 bEntry.spkPk (P.x25519Base sk0)
            (hP.pow8_base_len bEntry.spkPk sk0 hPowSk0) (hw.x25519Base_len sk0) hPowSk0]
  refine ⟨hCandEq, ?_⟩
  unfold badAuthFgDh1AtNonEmpty
  rw [hFindU, hFindB]
  dsimp only
  rw [huNotCorr, Bool.true_and, Bool.or_eq_true, Bool.or_eq_true]
  left; right
  exact List.any_eq_true.mpr ⟨s, hsMemTake, beq_iff_eq.mpr hCandEq⟩

end Proofs.SignalPqxdh.Security
