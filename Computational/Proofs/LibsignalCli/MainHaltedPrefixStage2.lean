/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedPrefixFactor

/-!
# Session-Tracked Stage-2 `bhPlugExtSessionTracked` Commutation

**Checked by Lean.** Establishes the Stage-1 output invariant `BHMidEval1PropsSessionTracked` and
commutes Stage 2 (`eval2`) of `bhPrefixRedWithSessionTracked` under `implExtSessionTracked` with
the plugged lazy driver on `bhPlugExtSessionTracked`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedPrefixStage2

open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey Spqr)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open ReductionDsl (Mid isGameQuery)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHModelInst BHPrefixCtx BHTargetQuery
  BHTargetResp BhShallowTwoStageRed Bytes ModelDriverInstanceMeta SampledSessionKey
  bhDecodePreKeyMsgE bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon
  bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhFwdU bhIsBobAcceptSMResp
  bhIsBobRecvSMQuery bhKeySOf bhLiftP bhNoOpkRespPromoted bhPackSmResp bhShallowCheckExtSm
  bhShallowCommitExtSm bhShallowImplOfHandle bhTargetGameSpec bhTargetQenc
  bhTargetRdec bhUnpackSmResp configRefuseEarlyBobCorr
  paramsIdsWithSpqr prob_bind_congr_of_support sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhE2EDrvImplGenWithSessionTracked bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery bhMkKeyBitConst
  bhPrefixHandlePostWithSessionTracked bhPrefixHandlePreWithSessionTracked
  bhPrefixRedWithSessionTracked bhShallowStepPostLocalSessionTracked
  bhShallowStepPreCtlSessionTracked bhShallowStepPreNonCtlSessionTracked
  oracleImplRSessionTracked stateT_run_lift stateT_run_liftM)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints (
  bhE2EStepLocalSmSessionTracked_insts_length_eq oracleImplRSessionTracked_preserves_b)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixFactor (BHAllInstsSome ExtState
  bhAllInstsSome_empty bhDefaultPrefixCtx bhE2EStepLocalSmSessionTracked_preserves_allInstsSome
  bhPlugExt bhPlugExtInst bhPlugExtInst_of_some bhPlugExtSessionTracked
  bhPrefixRedWithSessionTracked_run1_pure bhPrefixRedWithSessionTracked_run1_query_bind_inl
  bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ
  bhPrefixRedWithSessionTracked_run1_query_bind_inr_zero bhStage1ToProb_bhFwdU
  bhStage1ToProb_bhLiftP bhStage1ToProb_bind bhStage1ToProb_eval1_withSessionTracked_eq_run1_bind
  bhStage1ToProb_pure)

attribute [local simp] bhPlugExtInst_of_some
attribute [local irreducible] spqrV1SessionUniformCoins sessionSchemeFixedSpk

/-! ## `bhPlugExt` and list-set commutation helpers -/

private theorem list_set_set_self {α : Type} (l : List α) (k : ℕ) (x y : α) :
    (l.set k x).set k y = l.set k y := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.length_set]
  split_ifs <;> rfl

private theorem list_set_comm_ne {α : Type} (l : List α) {k i : ℕ} (hki : k ≠ i) (x y : α) :
    (l.set k x).set i y = (l.set i y).set k x := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.length_set]
  by_cases hij : i = j
  · subst hij
    have hkj : ¬(k = i) := hki
    simp [hkj]
  · simp [hij]

private theorem list_set_append_left_of_lt {α : Type} (l r : List α) {k : ℕ} (hk : k < l.length)
    (x : α) :
    (l.set k x) ++ r = (l ++ r).set k x := by
  apply List.ext_getElem?
  intro j
  by_cases hkj : k = j
  · subst hkj
    have hlt_set : k < (l.set k x).length := by simpa using hk
    have hlt_app : k < (l ++ r).length := by simp; omega
    rw [List.getElem?_append_left hlt_set]
    simp only [List.getElem?_set, hk, hlt_app, ↓reduceIte]
  · simp only [List.getElem?_set, hkj, ↓reduceIte]
    by_cases hjl : j < l.length
    · have hjl_set : j < (l.set k x).length := by simpa using hjl
      rw [List.getElem?_append_left hjl_set, List.getElem?_append_left hjl]
      simp [List.getElem?_set, hkj]
    · have hge : l.length ≤ j := Nat.le_of_not_lt hjl
      have hge_set : (l.set k x).length ≤ j := by simpa using hge
      rw [List.getElem?_append_right hge_set, List.getElem?_append_right hge]
      simp

@[local simp]
private theorem bhUnpackSmResp_bhPackSmResp {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    bhUnpackSmResp sq (bhPackSmResp sq r) = r := by
  rcases sq with ((((_ | _) | _) | _) | _) <;> rfl

@[local simp]
private theorem bhE2EGuard_with_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S) (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard { σ with st := st' } sid = bhE2EGuard σ sid := rfl

@[local simp]
theorem bhPlugExtInst_sid {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (d : BHModelInst S ℓ) :
    (bhPlugExtInst gs_ext d).sid = d.sid := by unfold bhPlugExtInst; cases d.gs <;> rfl

@[local simp]
theorem bhPlugExtInst_hdr {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (d : BHModelInst S ℓ) :
    (bhPlugExtInst gs_ext d).hdr = d.hdr := by unfold bhPlugExtInst; cases d.gs <;> rfl

@[local simp]
theorem bhPlugExtInst_of_none {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) (h : d.gs = none) :
    bhPlugExtInst gs_ext d = { d with gs := some gs_ext } := by simp [bhPlugExtInst, h]

@[local simp]
theorem getElem?_insts_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (i : ℕ) :
    (bhPlugExt gs_ext σ).insts[i]? = (σ.insts[i]?).map (bhPlugExtInst gs_ext) := by
  simp [bhPlugExt]

@[local simp]
theorem bhE2EGuard_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard (bhPlugExt gs_ext σ) sid = bhE2EGuard σ sid := by
  simp [bhE2EGuard, bhPlugExt, List.any_map, Function.comp_def]

@[local simp]
theorem bhE2EMirror_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror (bhPlugExt gs_ext σ) q r = bhPlugExt gs_ext (bhE2EMirror σ q r) := by
  cases q <;> cases r <;> rfl

@[local simp]
theorem bhE2EDrvInstClean_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (i : ℕ) :
    bhE2EDrvInstClean (bhPlugExt gs_ext σ) i = bhE2EDrvInstClean σ i := by
  unfold bhE2EDrvInstClean
  rw [getElem?_insts_bhPlugExt]
  have hm : (bhPlugExt gs_ext σ).instMeta[i]? = σ.instMeta[i]? := rfl
  have hr : (bhPlugExt gs_ext σ).revealedSpks = σ.revealedSpks := rfl
  rw [hm, hr]
  cases σ.insts[i]? <;> cases σ.instMeta[i]? <;> simp

@[local simp]
theorem bhE2EInstIkACorr_bhPlugExtInst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ) :
    bhE2EInstIkACorr σ (bhPlugExtInst gs_ext d) = bhE2EInstIkACorr σ d := by
  unfold bhE2EInstIkACorr; simp

@[local simp]
theorem bhE2EInstIkACorr_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ) :
    bhE2EInstIkACorr (bhPlugExt gs_ext σ) d = bhE2EInstIkACorr σ d := rfl

private theorem list_any_or_and_const' {α : Type} (l : List α) (f g : α → Bool) (c : Bool) :
    l.any (fun x => f x || (g x && c)) = (l.any f || (l.any g && c)) := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.any_cons, ih]
    cases f a <;> cases g a <;> cases c <;> cases tl.any f <;> cases tl.any g <;> rfl

theorem bhE2EDrvWon_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (b : Bool) :
    bhE2EDrvWon (bhPlugExt gs_ext σ) b =
      (bhE2EDrvWon σ b || (σ.insts.any (fun d => d.gs.isNone) && (gs_ext.b == b && gs_ext.win))) := by
  unfold bhE2EDrvWon bhPlugExt; rw [List.any_map]
  have hpoint : ((fun d : BHModelInst S ℓ =>
      match d.gs with | some gs => gs.b == b && gs.win | none => false) ∘ bhPlugExtInst gs_ext) =
      (fun d : BHModelInst S ℓ =>
        (match d.gs with | some gs => gs.b == b && gs.win | none => false) ||
          (d.gs.isNone && (gs_ext.b == b && gs_ext.win))) := by
    funext d; cases hgs : d.gs <;> simp [bhPlugExtInst, hgs]
  exact (congr_arg σ.insts.any hpoint).trans (list_any_or_and_const' σ.insts _ _ _)

/-- Only instance `k` in `σ.insts` can have `d.gs = none`. -/
def BHOnlyInstKNone {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ i d, σ.insts[i]? = some d → d.gs = none → i = k

theorem bhOnlyInstKNone_of_allInstsSome_mapIdx {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (h : BHAllInstsSome σ) :
    BHOnlyInstKNone k
      { σ with insts := σ.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d) } := by
  intro i d' hi hnone
  rw [List.getElem?_mapIdx] at hi
  rcases Option.map_eq_some_iff.mp hi with ⟨d, hd, rfl⟩
  by_cases hik : i = k
  · exact hik
  · simp only [hik, ↓reduceIte] at hnone
    exact False.elim (h d (List.mem_of_getElem? hd) hnone)

theorem bhOnlyInstKNone_append_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : BHOnlyInstKNone k σ)
    (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (st' : SignalPqxdh.KeyIndState S)
    (hd₀ : d₀.gs ≠ none) :
    BHOnlyInstKNone k { σ with st := st', insts := σ.insts ++ [d₀], instMeta := σ.instMeta ++ [im₀] } := by
  intro i d hi hnone
  by_cases hlt : i < σ.insts.length
  · rw [List.getElem?_append_left hlt] at hi
    exact h i d hi hnone
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    have hik : i - σ.insts.length = 0 := by
      by_contra hne
      have hge : 1 ≤ i - σ.insts.length := Nat.pos_of_ne_zero hne
      rw [List.getElem?_eq_none (by simp; omega)] at hi
      nomatch hi
    rw [hik] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact False.elim (hd₀ hnone)

theorem bhOnlyInstKNone_set_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : BHOnlyInstKNone k σ)
    (j : ℕ) (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (hd₀ : d₀.gs ≠ none) :
    BHOnlyInstKNone k { σ with insts := σ.insts.set j d₀, instMeta := σ.instMeta.set j im₀ } := by
  intro i d hi hnone
  rw [List.getElem?_set] at hi
  by_cases hji : j = i
  · subst hji
    simp only [↓reduceIte] at hi
    rcases Option.ite_none_right_eq_some.mp hi with ⟨_, hEq⟩
    injection hEq with hEq'
    subst hEq'
    exact False.elim (hd₀ hnone)
  · simp only [hji, ↓reduceIte] at hi
    exact h i d hi hnone

/-! ## Wire-filter lemmas and `BHPrefixPlugInvSessionTracked` -/

theorem bhIsBobRecvSMQuery_of_bhFilterSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {q q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (h : bhFilterSmQuery d im q = some q') :
    bhIsBobRecvSMQuery q' = bhIsBobRecvSMQuery q := by
  rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
  · injection h with h'; subst h'; rfl
  · injection h with h'; subst h'; rfl
  · cases p with
    | A =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      injection h with h'; subst h'; rfl
    | B =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      · cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
        · nomatch h
        · dsimp only at h
          split_ifs at h
          injection h with h'; subst h'; rfl
      · cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
        · injection h with h'; subst h'; rfl
        · dsimp only at h
          split_ifs at h
          injection h with h'; subst h'; rfl
  · cases p with
    | A =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      injection h with h'; subst h'; rfl
    | B =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
      · injection h with h'; subst h'; rfl
      · dsimp only at h
        split_ifs at h
        injection h with h'; subst h'; rfl
  · injection h with h'; subst h'; rfl

theorem checkExtSm_eval_eq_filter {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhShallowCheckExtSm k σ i sq =
      if i != k || !bhE2EDrvInstClean σ k then
        .inl (.inr (none, none, none))
      else
        match σ.insts[k]?, σ.instMeta[k]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
            .inl (.inr (none, none, none))
          else
            match bhFilterSmQuery d im sq with
            | some sq' => .inr sq'
            | none => .inl (.inr (none, none, none))
        | _, _ => .inl (.inr (none, none, none)) := by
  dsimp only [bhShallowCheckExtSm]
  by_cases h1 : (i != k || !bhE2EDrvInstClean σ k) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[k]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[k]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          rcases sq with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
          · rfl
          · rfl
          · cases p with
            | A =>
              dsimp only [bhFilterSmQuery]
              split_ifs <;> rfl
            | B =>
              dsimp only [bhFilterSmQuery]
              split_ifs
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
          · cases p with
            | A =>
              dsimp only [bhFilterSmQuery]
              split_ifs <;> rfl
            | B =>
              dsimp only [bhFilterSmQuery]
              split_ifs
              · rfl
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
          · rfl

/-- State invariant on `σ : BHE2EDrvState S ℓ` during Stage 2 after pausing at instance `k`. -/
structure BHPrefixPlugInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256) (σ : BHE2EDrvState S ℓ) : Prop where
  only_k : BHOnlyInstKNone k σ
  params_none : ∀ d ∈ σ.insts, d.gs = none →
    d.idA = idA ∧ d.idB = idB ∧ d.spkCoins = s
  inst_k_none : ∃ d, σ.insts[k]? = some d ∧ d.gs = none
  paused_true : σ.paused = true

/-- Session-tracked Stage-2 invariant bundling `BHPrefixPlugInv` with `σH.2.length = σH.1.insts.length`. -/
structure BHPrefixPlugInvSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (σH : BHE2EDrvState S ℓ × List τ) : Prop where
  plug : BHPrefixPlugInv k idA idB s σH.1
  tracks_len : σH.2.length = σH.1.insts.length

theorem BHPrefixPlugInv.any_isNone_true {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) :
    σ.insts.any (fun d => d.gs.isNone) = true := by
  rcases h.inst_k_none with ⟨d, hk, hd⟩
  exact List.any_eq_true.mpr ⟨d, List.mem_of_getElem? hk, by simp [hd]⟩

theorem BHPrefixPlugInvSessionTracked.lt_tracks_length {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH) :
    k < σH.2.length := by
  rcases h.plug.inst_k_none with ⟨d, hk, _⟩
  rw [h.tracks_len]
  exact (List.getElem?_eq_some_iff.mp hk).1

theorem bhPrefixPlugInv_with_b {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (b0 : Bool) :
    BHPrefixPlugInv k idA idB s { σ with b := b0 } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInvSessionTracked_with_b {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH) (b0 : Bool) :
    BHPrefixPlugInvSessionTracked k idA idB s ({ σH.1 with b := b0 }, σH.2) :=
  ⟨bhPrefixPlugInv_with_b h.plug b0, h.tracks_len⟩

theorem bhPrefixPlugInv_with_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (st' : SignalPqxdh.KeyIndState S) :
    BHPrefixPlugInv k idA idB s { σ with st := st' } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInv_set_instMeta {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (i : ℕ) (im' : ModelDriverInstanceMeta S) :
    BHPrefixPlugInv k idA idB s { σ with instMeta := σ.instMeta.set i im' } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInv_bhE2EMirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (st' : SignalPqxdh.KeyIndState S)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    BHPrefixPlugInv k idA idB s (bhE2EMirror { σ with st := st' } q r) where
  only_k i d hi hnone := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts] at hi
    exact h.only_k i d hi hnone
  params_none d hd hnone := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts] at hd
    exact h.params_none d hd hnone
  inst_k_none := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts]
    exact h.inst_k_none
  paused_true := by
    have hpaused : (bhE2EMirror { σ with st := st' } q r).paused = σ.paused := by
      cases q <;> cases r <;> rfl
    rw [hpaused]
    exact h.paused_true

theorem bhPrefixPlugInv_append_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (st' : SignalPqxdh.KeyIndState S)
    (hd₀ : d₀.gs ≠ none) :
    BHPrefixPlugInv k idA idB s
      { σ with st := st', insts := σ.insts ++ [d₀], instMeta := σ.instMeta ++ [im₀] } where
  only_k := bhOnlyInstKNone_append_some h.only_k d₀ im₀ st' hd₀
  params_none d hd hnone := by
    rcases List.mem_append.mp hd with hd | hd
    · exact h.params_none d hd hnone
    · rw [List.mem_singleton.mp hd] at hnone
      exact False.elim (hd₀ hnone)
  inst_k_none := by
    rcases h.inst_k_none with ⟨d, hk, hd⟩
    have hlt : k < σ.insts.length := (List.getElem?_eq_some_iff.mp hk).1
    exact ⟨d, by rw [List.getElem?_append_left hlt]; exact hk, hd⟩
  paused_true := h.paused_true

theorem bhPrefixPlugInv_set_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (j : ℕ) (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (hd₀ : d₀.gs ≠ none)
    (hj : ∀ d, σ.insts[j]? = some d → d.gs ≠ none) :
    BHPrefixPlugInv k idA idB s
      { σ with insts := σ.insts.set j d₀, instMeta := σ.instMeta.set j im₀ } where
  only_k := bhOnlyInstKNone_set_some h.only_k j d₀ im₀ hd₀
  params_none d hd hnone := by
    rcases List.mem_or_eq_of_mem_set hd with hd | rfl
    · exact h.params_none d hd hnone
    · exact False.elim (hd₀ hnone)
  inst_k_none := by
    rcases h.inst_k_none with ⟨d, hk, hd⟩
    have hjk : j ≠ k := fun heq => hj d (heq ▸ hk) hd
    exact ⟨d, by rw [List.getElem?_set_ne hjk]; exact hk, hd⟩
  paused_true := h.paused_true

theorem bhPlugExt_set_none_of_onlyInstKNone {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (hOnly : BHOnlyInstKNone k σ)
    (gs_ext gs_ext' : ExtState ℓ)
    {i : ℕ} {d : BHModelInst S ℓ} (hi : σ.insts[i]? = some d) (hd : d.gs = none)
    (im' : ModelDriverInstanceMeta S) :
    { bhPlugExt gs_ext σ with
        insts := (bhPlugExt gs_ext σ).insts.set i { d with gs := some gs_ext' },
        instMeta := σ.instMeta.set i im' } =
      bhPlugExt gs_ext' { σ with instMeta := σ.instMeta.set i im' } := by
  have hik : i = k := hOnly i d hi hd
  subst hik
  have hinsts :
      (bhPlugExt gs_ext σ).insts.set i { d with gs := some gs_ext' } =
        (bhPlugExt gs_ext' σ).insts := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_set]
    by_cases hji : i = j
    · subst hji
      rcases List.getElem?_eq_some_iff.mp hi with ⟨hlt, hdi⟩
      simp [bhPlugExt, hlt, hdi, bhPlugExtInst, hd]
    · simp only [hji, ↓reduceIte, bhPlugExt, List.getElem?_map]
      cases hj : σ.insts[j]? with
      | none => rfl
      | some dj =>
        simp only [Option.map_some, Option.some.injEq]
        cases hgs : dj.gs with
        | some gs_j => simp [bhPlugExtInst, hgs]
        | none =>
          exfalso
          exact hji (hOnly j dj hj hgs).symm
  cases σ
  simp only [bhPlugExt, BHE2EDrvState.mk.injEq, true_and, and_true]
  exact hinsts

theorem bhPrefixPlugInv_init {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ' : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ') (hk : k < σ'.insts.length) :
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => bhDefaultPrefixCtx
    let σ_p : BHE2EDrvState S ℓ :=
      { σ' with
        insts := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d),
        paused := true }
    BHPrefixPlugInv k ctx.idA ctx.idB ctx.spkCoins σ_p := by
  intro ctx σ_p
  have hOnly : BHOnlyInstKNone k σ_p := by
    intro i d' hi hnone
    exact bhOnlyInstKNone_of_allInstsSome_mapIdx k σ' hAll i d' hi hnone
  refine ⟨hOnly, fun d' hd' hnone => ?_, ?_, rfl⟩
  · rcases List.mem_iff_getElem?.mp hd' with ⟨i, hi⟩
    have hik : i = k := hOnly i d' hi hnone
    subst hik
    dsimp only [σ_p] at hi
    rw [List.getElem?_mapIdx] at hi
    rcases Option.map_eq_some_iff.mp hi with ⟨d, hd, rfl⟩
    simp [ctx, hd]
  · refine ⟨{ σ'.insts[k] with gs := none }, ?_, rfl⟩
    dsimp only [σ_p]
    rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hk]
    simp

/-! ## Stage-1 support invariants -/

def BHMidStage1PropsSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} (k q : ℕ) :
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx → Prop
  | .done _ σH' => σH'.1.paused = false
  | .paused _ c _ σH_p cont =>
    BHPrefixPlugInvSessionTracked k c.idA c.idB c.spkCoins σH_p ∧
    (∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q)

/-- Pair-level Stage-1 output invariant for `bhPrefixRedWithSessionTracked.eval1`. -/
def BHMidEval1PropsSessionTracked {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} (k qTot : ℕ)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ × List τ) BHPrefixCtx) : Prop :=
  match o.2 with
  | .done _ σH' => σH'.1.paused = false
  | .paused _ c _ σH_p cont =>
    o.1 = c ∧
    BHPrefixPlugInvSessionTracked k o.1.idA o.1.idB o.1.spkCoins σH_p ∧
    (∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)

private theorem bhE2EStepLocalSmSessionTracked_tracks_length_eq {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    p.2.2.length = σH.2.length := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hp
  by_cases hClean : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; rfl
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σH.1.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
    | some d =>
      rw [hi] at hp
      cases him : σH.1.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
      | some im =>
        rw [him] at hp; dsimp only at hp
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
        · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
          cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; rfl
          | some gs =>
            rw [hd] at hp
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              rw [hf] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
              subst hp; rfl
            | some q' =>
              rw [hf] at hp
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨⟨r, gs'⟩, tr'⟩, _, rfl⟩
              simp

theorem bhE2ELocalStartSessionTracked_preserves_allInstsSome {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (b : Bool)
    (σH : BHE2EDrvState S ℓ × List τ)
    (hAll : BHAllInstsSome σH.1) (hLen : σH.2.length = σH.1.insts.length)
    (sid : SignalPqxdh.SessionId S)
    {p : Option ℕ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2ELocalStartSessionTracked initTrack ki C K (some b) σH sid)) :
    BHAllInstsSome p.2.1 ∧ p.2.1.paused = σH.1.paused ∧ p.2.2.length = p.2.1.insts.length := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhE2ELocalStartSessionTracked] at hp
  cases hG : bhE2EGuard σ sid with
  | none =>
    rw [hG] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hAll, rfl, hLen⟩
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    rw [hG] at hp; dsimp only at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
    unfold bhE2EFinishStartSpk
    simp only [bhE2EGuard_with_st, hG]
    cases kr1 <;> cases kr2 <;> try exact ⟨hAll, rfl, hLen⟩
    dsimp only
    split_ifs
    · refine ⟨fun d' hd' => ?_, rfl, by simp [hLen]⟩
      rcases List.mem_append.mp hd' with hd' | hd'
      · exact hAll d' hd'
      · rw [List.mem_singleton.mp hd']; simp
    · exact ⟨hAll, rfl, hLen⟩

set_option maxHeartbeats 800000 in
theorem mem_support_bhStage1ToProb_run1_withSessionTracked_props {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) {oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool} {q f : ℕ}
    (hQ : oa.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q)
    (σH : BHE2EDrvState S ℓ × List τ)
    (hAll : BHAllInstsSome σH.1) (hpaused : σH.1.paused = false)
    (hLen : σH.2.length = σH.1.insts.length)
    {m}
    (hm : m ∈ support
      (stageOneAsProbComp
        ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).run1 false oa f σH))) :
    BHMidStage1PropsSessionTracked k q m := by
  induction oa using OracleComp.inductionOn generalizing q f σH m with
  | pure a =>
    rw [bhPrefixRedWithSessionTracked_run1_pure, bhStage1ToProb_pure, support_pure,
      Set.mem_singleton_iff] at hm
    subst hm
    exact hpaused
  | query_bind q_step mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    rcases q_step with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
    · rw [bhPrefixRedWithSessionTracked_run1_query_bind_inl, bhStage1ToProb_bind,
        bhStage1ToProb_bhFwdU] at hm
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hm
      rcases hm with ⟨u, _, hm⟩
      exact ih u (hQ.2 u) σH hAll hpaused hLen hm
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q :=
        fun v => (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
          bhShallowStepPreNonCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
          bhStage1ToProb_pure, bind_assoc, pure_bind] at hm
        split_ifs at hm
        · simp only [pure_bind, bhStage1ToProb_bind, bhStage1ToProb_pure] at hm
          exact ih .noneResp (hqm _) σH hAll hpaused hLen hm
        · simp only [pure_bind, bhStage1ToProb_bind, bhStage1ToProb_pure] at hm
          exact ih .noneResp (hqm _) σH hAll hpaused hLen hm
        · simp only [bind_assoc, pure_bind,
            bhStage1ToProb_bind, bhStage1ToProb_pure, support_bind, Set.mem_iUnion,
            exists_prop] at hm
          rcases hm with ⟨⟨kr, st'⟩, _, hm⟩
          dsimp only at hm
          have hinsts : (bhE2EMirror { σH.1 with st := st' } kq kr).insts = σH.1.insts := by
            cases kq <;> cases kr <;> rfl
          have hAll' : BHAllInstsSome (bhE2EMirror { σH.1 with st := st' } kq kr) := by
            intro d hd; rw [hinsts] at hd; exact hAll d hd
          have hpaused' : (bhE2EMirror { σH.1 with st := st' } kq kr).paused = false := by
            have hp : (bhE2EMirror { σH.1 with st := st' } kq kr).paused = σH.1.paused := by
              cases kq <;> cases kr <;> rfl
            exact hp.trans hpaused
          have hLen' : σH.2.length = (bhE2EMirror { σH.1 with st := st' } kq kr).insts.length := by
            rw [hinsts]; exact hLen
          exact ih kr (hqm _) (bhE2EMirror { σH.1 with st := st' } kq kr, σH.2) hAll' hpaused'
            hLen' hm
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q :=
        fun v => (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
          bhShallowStepPreCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
          bhStage1ToProb_pure, bind_assoc, pure_bind] at hm
        rw [support_bind, Set.mem_iUnion] at hm
        rcases hm with ⟨⟨idx?, σ', tracks'⟩, hm⟩
        rw [Set.mem_iUnion] at hm
        rcases hm with ⟨hstart, hm⟩
        dsimp only at hm
        obtain ⟨hAll', hpaused', hLen'⟩ :=
          bhE2ELocalStartSessionTracked_preserves_allInstsSome T.init ki C K true σH hAll hLen sid
            hstart
        by_cases hlt : k < σ'.insts.length
        · simp only [hlt, ↓reduceIte, pure_bind, bhStage1ToProb_pure, support_pure,
            Set.mem_singleton_iff] at hm
          subst hm
          refine ⟨⟨bhPrefixPlugInv_init k σ' hAll' hlt, ?_⟩, hqm⟩
          simpa using hLen'
        · simp only [hlt, Bool.false_eq_true, ↓reduceIte, pure_bind,
            bhStage1ToProb_bind, bhStage1ToProb_pure] at hm
          exact ih idx? (hqm _) (σ', tracks') hAll' (hpaused'.trans hpaused) hLen' hm
    · have hqm : ∀ v, (mx v).IsQueryBoundP
          (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q :=
        fun v => (hQ.2 v).mono (by simp [isGameQuery])
      cases f with
      | zero =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_zero, bhStage1ToProb_pure,
          support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact hpaused
      | succ f' =>
        rw [bhPrefixRedWithSessionTracked_run1_query_bind_inr_succ] at hm
        simp only [bhPrefixHandlePreWithSessionTracked, bhTargetQenc, bhTargetRdec,
          bhShallowStepPreNonCtlSessionTracked, bhStage1ToProb_bind, bhStage1ToProb_bhLiftP,
          bhStage1ToProb_pure, bind_assoc, pure_bind, support_bind, Set.mem_iUnion,
          exists_prop] at hm
        rcases hm with ⟨⟨sr, σH'⟩, hsm, hm⟩
        obtain ⟨hAll', hpaused'⟩ :=
          bhE2EStepLocalSmSessionTracked_preserves_allInstsSome T C K qep decT encT σH hAll i sq hsm
        obtain ⟨hInstLen, hTrLen⟩ :=
          bhE2EStepLocalSmSessionTracked_insts_length_eq T C K qep decT encT σH i sq hsm
        exact ih (bhUnpackSmResp sq sr) (hqm _) σH' hAll' (hpaused'.trans hpaused)
          (by dsimp only at hInstLen hTrLen; rw [hTrLen, hInstLen]; exact hLen) hm

theorem mem_support_bhStage1ToProb_eval1_withSessionTracked_props {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k qTot : ℕ) (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hQ : B.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)
    {o}
    (ho : o ∈ support (stageOneAsProbComp
      ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1 (fun _ => B) () qTot false))) :
    BHMidEval1PropsSessionTracked k qTot o := by
  rw [bhStage1ToProb_eval1_withSessionTracked_eq_run1_bind] at ho
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho
  rcases ho with ⟨m, hm, rfl⟩
  have hprops := mem_support_bhStage1ToProb_run1_withSessionTracked_props T P ki C K qep decT encT
    k hQ ({}, []) bhAllInstsSome_empty rfl rfl hm
  cases m with
  | done b' σH' => exact hprops
  | paused t c p σH_p cont => exact ⟨rfl, hprops.1, hprops.2⟩

/-! ## Stage-2 `bhPlugExtSessionTracked` commutation -/

/-- External single-session oracle implementation driven by `T : SessionHaltTracker`. -/
abbrev implExtSessionTracked {τ Pt : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (ExtState ℓ) (StateT τ ProbComp)) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ExtState ℓ) (StateT τ ProbComp)) +
    oracleImplRSessionTracked T
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ s) (2 + 1) qep
      (configRefuseEarlyBobCorr decT encT)

@[local simp]
theorem simulateQ_implExtSessionTracked_query_inl_run {τ Pt : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (n : ℕ) (gs_ext : ExtState ℓ) (tr_ext : τ) :
    ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
      (query (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (Sum.inl n))).run gs_ext).run tr_ext =
    ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u => pure ((u, gs_ext), tr_ext)) := by
  simp [implExtSessionTracked, stateT_run_liftM, stateT_run_lift]

@[local simp]
theorem simulateQ_implExtSessionTracked_bhFwdU_run {τ Pt : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (n : ℕ) (gs_ext : ExtState ℓ) (tr_ext : τ) :
    ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
      (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run
        gs_ext).run tr_ext =
    ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u => pure ((u, gs_ext), tr_ext)) :=
  simulateQ_implExtSessionTracked_query_inl_run T C spqr qep decT encT idA idB s n gs_ext tr_ext

@[local simp]
theorem simulateQ_implExtSessionTracked_bhLiftP_run {τ Pt α : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (mx : ProbComp α) (gs_ext : ExtState ℓ) (tr_ext : τ) :
    ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
      (bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) mx)).run
        gs_ext).run tr_ext =
    (mx >>= fun x => pure ((x, gs_ext), tr_ext)) := by
  unfold bhLiftP
  induction mx using OracleComp.inductionOn generalizing gs_ext tr_ext with
  | pure a => rfl
  | query_bind n k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hq :
        ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
          (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run
            gs_ext).run tr_ext =
        ((liftM (OracleSpec.query n) : ProbComp (Fin (n + 1))) >>=
          fun u => pure ((u, gs_ext), tr_ext)) :=
      simulateQ_implExtSessionTracked_query_inl_run T C spqr qep decT encT idA idB s n gs_ext tr_ext
    dsimp only [OracleSpec.query_def, liftM, monadLift] at hq ⊢
    change (do
      let p ← ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
        (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) n)).run
          gs_ext).run tr_ext
      ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
        (simulateQ (bhFwdU (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes))
          (k p.1.1))).run p.1.2).run p.2) = _
    rw [hq]
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u gs_ext tr_ext

@[local simp]
theorem bhE2EInstIkACorr_with_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ) (gs? : Option (ExtState ℓ)) :
    bhE2EInstIkACorr σ { d with gs := gs? } = bhE2EInstIkACorr σ d := rfl

@[local simp]
theorem bhFilterSmQuery_with_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S) (gs? : Option (ExtState ℓ))
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhFilterSmQuery { d with gs := gs? } im sq = bhFilterSmQuery d im sq := rfl

@[local simp]
theorem simulateQ_implExtSessionTracked_query_inr_run {τ Pt : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (gs_ext : ExtState ℓ) (tr_ext : τ) :
    ((simulateQ (implExtSessionTracked T C spqr qep decT encT idA idB s)
      (query (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (.inr sq'))).run gs_ext).run tr_ext =
    ((oracleImplRSessionTracked T
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ s)
      (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq').run gs_ext).run tr_ext := by
  simp [implExtSessionTracked]

theorem bhE2ELocalStartSessionTracked_false_bhPlugExtSessionTracked {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256}
    (σH : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (hInv : BHPrefixPlugInvSessionTracked k idA idB s σH)
    (sid : SignalPqxdh.SessionId S) :
    bhE2ELocalStartSessionTracked initTrack ki C K (some false)
        (bhPlugExtSessionTracked k gs_ext tr_ext σH) sid =
      (fun (idx?, σH1) => (idx?, bhPlugExtSessionTracked k gs_ext tr_ext σH1)) <$>
        bhE2ELocalStartSessionTracked initTrack ki C K (some false) σH sid ∧
    ∀ p ∈ support (bhE2ELocalStartSessionTracked initTrack ki C K (some false) σH sid),
      BHPrefixPlugInvSessionTracked k idA idB s p.2 := by
  have hk_tr : k < σH.2.length := hInv.lt_tracks_length
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhE2ELocalStartSessionTracked, bhPlugExtSessionTracked]
  rw [bhE2EGuard_bhPlugExt]
  cases hG : bhE2EGuard σ sid with
  | none =>
    simp only [map_pure, support_pure, Set.mem_singleton_iff, true_and]
    rintro p rfl
    exact hInv
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    have hst : (bhPlugExt gs_ext σ).st = σ.st := rfl
    rw [hst]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine ⟨?_, ?_⟩
    · refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun ac => ?_
      dsimp only
      unfold bhE2EFinishStartSpk
      have hPlugSt : { bhPlugExt gs_ext σ with st := st2 } =
          bhPlugExt gs_ext { σ with st := st2 } := rfl
      rw [hPlugSt, bhE2EGuard_bhPlugExt, bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;> try rfl
      dsimp only
      split_ifs with hLen
      · simp [bhPlugExtSessionTracked, bhPlugExt, bhPlugExtInst,
          list_set_append_left_of_lt _ _ hk_tr]
      · rfl
    · intro p hp
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      dsimp only
      unfold bhE2EFinishStartSpk
      rw [bhE2EGuard_with_st, hG]
      cases kr1 <;> cases kr2 <;>
        try exact ⟨bhPrefixPlugInv_with_st hInv.plug st2, hInv.tracks_len⟩
      dsimp only
      split_ifs with hLen
      · exact ⟨bhPrefixPlugInv_append_some hInv.plug _ _ st2 (by simp), by simp [hInv.tracks_len]⟩
      · exact ⟨bhPrefixPlugInv_with_st hInv.plug st2, hInv.tracks_len⟩

set_option maxHeartbeats 400000 in
theorem bhPrefixHandlePostWithSessionTracked_plugExt_sm_bind_eq {τ α : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (gs_ext : ExtState ℓ) (tr_ext : τ)
    (h : BHPrefixPlugInvSessionTracked k idA idB s σH)
    (k1 : (((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inr (.inr ⟨i, sq⟩)) ×
        (BHE2EDrvState S ℓ × List τ)) × ExtState ℓ) × τ → ProbComp α)
    (k2 : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range (.inr (.inr ⟨i, sq⟩)) ×
        (BHE2EDrvState S ℓ × List τ) → ProbComp α)
    (hk : ∀ r σH' gs_ext' tr_ext', BHPrefixPlugInvSessionTracked k idA idB s σH' →
      gs_ext'.b = gs_ext.b →
      k1 (((r, σH'), gs_ext'), tr_ext') =
        k2 (r, bhPlugExtSessionTracked k gs_ext' tr_ext' σH')) :
    (((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)
          (.inr (.inr ⟨i, sq⟩))).run σH)).run gs_ext).run tr_ext >>= k1) =
    ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false)
        (.inr (.inr ⟨i, sq⟩))).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) >>= k2) := by
  have hk_tr : k < σH.2.length := h.lt_tracks_length
  have hL :
      ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT idA idB s)
        ((bhShallowImplOfHandle bhTargetQenc bhTargetRdec
          (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k)
          (.inr (.inr ⟨i, sq⟩))).run σH)).run gs_ext).run tr_ext =
      match bhShallowCheckExtSm k σH.1 i sq with
      | .inl _ =>
        (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq >>= fun (sr, σH') =>
          pure (((bhUnpackSmResp sq sr, σH'), gs_ext), tr_ext))
      | .inr sq' =>
        (((oracleImplRSessionTracked T
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ s)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq').run gs_ext).run tr_ext >>=
          fun ((r, gs_ext'), tr_ext') =>
            let p := bhShallowCommitExtSm k σH.1 sq' (bhPackSmResp sq' r)
            pure (((bhUnpackSmResp sq (bhPackSmResp sq' r), (p.2, σH.2)), gs_ext'), tr_ext')) := by
    change
      ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT idA idB s)
        (bhPrefixHandlePostWithSessionTracked T P ki C K qep decT encT k σH
          (bhTargetQenc (.inr ⟨i, sq⟩)) >>=
          fun p => pure (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2))).run gs_ext).run tr_ext = _
    dsimp only [bhPrefixHandlePostWithSessionTracked, bhTargetQenc]
    cases bhShallowCheckExtSm k σH.1 i sq with
    | inl _ =>
      simp only [bhShallowStepPostLocalSessionTracked, bhTargetRdec,
        simulateQ_bind, StateT.run_bind, simulateQ_implExtSessionTracked_bhLiftP_run,
        simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    | inr sq' =>
      have hq_inr :
          ((simulateQ (implExtSessionTracked T C (spqrV1SessionUniformCoins C.F K) qep decT encT
              idA idB s)
            (liftM
              ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query
                (.inr sq')) :
              OracleComp
                (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
                _)).run gs_ext).run tr_ext =
          ((oracleImplRSessionTracked T
            (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
              ℓ s)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq').run gs_ext).run tr_ext := by
        simp [implExtSessionTracked]
      simp only [bhTargetRdec, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      rw [hq_inr]
      exact bind_congr fun ⟨⟨r, gs_ext'⟩, tr_ext'⟩ => rfl
  have hR :
      (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT (bhMkKeyBitConst false)
        (.inr (.inr ⟨i, sq⟩))).run (bhPlugExtSessionTracked k gs_ext tr_ext σH) =
      (bhE2EStepLocalSmSessionTracked T C K qep decT encT
        (bhPlugExtSessionTracked k gs_ext tr_ext σH) i sq >>= fun (sr, σH') =>
        pure (bhUnpackSmResp sq sr, σH')) := by
    dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set, StateT.run_pure,
      bind_assoc, pure_bind]
  rw [hL, hR, checkExtSm_eval_eq_filter]
  have hPlug1 : (bhPlugExtSessionTracked k gs_ext tr_ext σH).1 = bhPlugExt gs_ext σH.1 := rfl
  have hPlug2 : (bhPlugExtSessionTracked k gs_ext tr_ext σH).2 = σH.2.set k tr_ext := rfl
  by_cases hClean : (!bhE2EDrvInstClean σH.1 i) = true
  · have hOr : (i != k || !bhE2EDrvInstClean σH.1 k) = true := by
      rcases Decidable.em (i = k) with rfl | hik
      · simp [hClean]
      · simp [hik]
    rw [hOr]
    simp only [↓reduceIte, bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1,
      bhE2EDrvInstClean_bhPlugExt, hClean, pure_bind]
    exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
  · by_cases hik : i = k
    · subst hik
      have hOr : (i != i || !bhE2EDrvInstClean σH.1 i) = false := by simp [hClean]
      rw [hOr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases h.plug.inst_k_none with ⟨d, hi_d, hd_none⟩
      rw [hi_d]
      cases him : σH.1.instMeta[i]? with
      | none =>
        have him_plug : (bhPlugExt gs_ext σH.1).instMeta[i]? = none := him
        simp only [bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1, bhE2EDrvInstClean_bhPlugExt,
          hClean, Bool.false_eq_true, ↓reduceIte, getElem?_insts_bhPlugExt, hi_d, Option.map_some,
          him, him_plug, pure_bind]
        exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
      | some im =>
        have him_plug : (bhPlugExt gs_ext σH.1).instMeta[i]? = some im := him
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
        · simp only [hCorr, ↓reduceIte, bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1, hPlug2,
            bhE2EDrvInstClean_bhPlugExt, hClean, Bool.false_eq_true, getElem?_insts_bhPlugExt,
            hi_d, Option.map_some, him, him_plug, bhE2EInstIkACorr_bhPlugExt,
            bhE2EInstIkACorr_bhPlugExtInst, pure_bind]
          let im_c := { im with bobAccepted := true, ikACorrAtAccept := true }
          exact hk (bhUnpackSmResp sq (none, none, none))
            ({ σH.1 with instMeta := σH.1.instMeta.set i im_c }, σH.2)
            gs_ext tr_ext
            ⟨bhPrefixPlugInv_set_instMeta h.plug i im_c, h.tracks_len⟩ rfl
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases hfilt : bhFilterSmQuery d im sq with
          | none =>
            simp only [bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1,
              bhE2EDrvInstClean_bhPlugExt, hClean, Bool.false_eq_true, ↓reduceIte,
              getElem?_insts_bhPlugExt, hi_d, Option.map_some, him, him_plug,
              bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_bhPlugExtInst, bhE2EInstIkACorr_with_gs,
              hCorr, hd_none, bhPlugExtInst_of_none gs_ext d hd_none, bhFilterSmQuery_with_gs,
              hfilt, pure_bind]
            exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
          | some sq' =>
            rcases h.plug.params_none d (List.mem_of_getElem? hi_d) hd_none with ⟨hidA, hidB, hspk⟩
            have hRecvEq : bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq :=
              bhIsBobRecvSMQuery_of_bhFilterSmQuery hfilt
            have hCorr' : (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σH.1 d) = false := by
              rw [hRecvEq]; exact Bool.eq_false_iff.mpr hCorr
            have hTrGet : ((σH.2.set i tr_ext)[i]?).getD (T.init default) = tr_ext := by
              simp [List.getElem?_set, hk_tr]
            simp only [bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1, hPlug2,
              bhE2EDrvInstClean_bhPlugExt, hClean, Bool.false_eq_true, ↓reduceIte,
              getElem?_insts_bhPlugExt, hi_d, Option.map_some, him_plug,
              bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_bhPlugExtInst, bhE2EInstIkACorr_with_gs,
              hCorr, hd_none, bhPlugExtInst_of_none gs_ext d hd_none, bhFilterSmQuery_with_gs,
              hfilt, hTrGet, bind_assoc, pure_bind]
            have hSchEq :
                sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins =
                sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ s := by
              rw [hidA, hidB, hspk]
            rw [hSchEq]
            refine prob_bind_congr_of_support _ _ _ (fun p hsm => ?_)
            rcases p with ⟨⟨r, gs_ext'⟩, tr_ext'⟩
            have hb' : gs_ext'.b = gs_ext.b :=
              oracleImplRSessionTracked_preserves_b T _ _ _ _ sq' gs_ext tr_ext hsm
            dsimp only [bhShallowCommitExtSm]
            simp only [hClean, Bool.false_eq_true, ↓reduceIte, hi_d, him, hCorr',
              bhUnpackSmResp_bhPackSmResp, pure_bind, list_set_set_self]
            let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σH.1 d }
              else im
            have hSetNone :=
              bhPlugExt_set_none_of_onlyInstKNone h.plug.only_k gs_ext gs_ext' hi_d hd_none im'
            rw [hk (bhUnpackSmResp sq (bhPackSmResp sq' r))
              ({ σH.1 with instMeta := σH.1.instMeta.set i im' }, σH.2) gs_ext' tr_ext'
              ⟨bhPrefixPlugInv_set_instMeta h.plug i im', h.tracks_len⟩ hb']
            unfold bhPlugExtSessionTracked
            dsimp only
            erw [hSetNone]
    · have hne : (i != k) = true := bne_iff_ne.mpr hik
      have hOr : (i != k || !bhE2EDrvInstClean σH.1 k) = true := by simp [hne]
      rw [hOr]
      simp only [↓reduceIte, bhE2EStepLocalSmSessionTracked_eq_filter, hPlug1, hPlug2,
        bhE2EDrvInstClean_bhPlugExt, hClean, Bool.false_eq_true, getElem?_insts_bhPlugExt]
      cases hi : σH.1.insts[i]? with
      | none =>
        simp only [Option.map_none, pure_bind]
        exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
      | some d =>
        have hd_some : d.gs ≠ none := fun hnone => hik (h.plug.only_k i d hi hnone)
        cases hd : d.gs with
        | none => exact False.elim (hd_some hd)
        | some gs =>
          have him_eq : (bhPlugExt gs_ext σH.1).instMeta[i]? = σH.1.instMeta[i]? := rfl
          simp only [Option.map_some, bhPlugExtInst_of_some gs_ext d gs hd, him_eq]
          cases him : σH.1.instMeta[i]? with
          | none =>
            simp only [pure_bind]
            exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
          | some im =>
            simp only [bhE2EInstIkACorr_bhPlugExt, bhE2EInstIkACorr_with_gs]
            by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
            · simp only [hCorr, ↓reduceIte, pure_bind]
              let im_c := { im with bobAccepted := true, ikACorrAtAccept := true }
              exact hk (bhUnpackSmResp sq (none, none, none))
                ({ σH.1 with instMeta := σH.1.instMeta.set i im_c }, σH.2)
                gs_ext tr_ext
                ⟨bhPrefixPlugInv_set_instMeta h.plug i im_c, h.tracks_len⟩ rfl
            · simp only [hCorr, Bool.false_eq_true, ↓reduceIte, hd, bhFilterSmQuery_with_gs]
              cases hfilt : bhFilterSmQuery d im sq with
              | none =>
                simp only [pure_bind]
                exact hk (bhUnpackSmResp sq (none, none, none)) σH gs_ext tr_ext h rfl
              | some sq' =>
                have hki : k ≠ i := Ne.symm hik
                have hTrGet : (σH.2.set k tr_ext)[i]? = σH.2[i]? := by
                  simp [List.getElem?_set, hki]
                simp only [hTrGet, bind_assoc, pure_bind]
                refine bind_congr fun p => ?_
                rcases p with ⟨⟨r, gs'⟩, tr'⟩
                let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
                    { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σH.1 d }
                  else im
                have hSetPlug :
                    { bhPlugExt gs_ext σH.1 with
                      insts := (bhPlugExt gs_ext σH.1).insts.set i { d with gs := some gs' },
                      instMeta := (bhPlugExt gs_ext σH.1).instMeta.set i im' } =
                    bhPlugExt gs_ext
                      { σH.1 with
                        insts := σH.1.insts.set i { d with gs := some gs' },
                        instMeta := σH.1.instMeta.set i im' } := by
                  cases σH.1
                  simp [bhPlugExt, List.map_set, bhPlugExtInst]
                rw [hSetPlug, list_set_comm_ne σH.2 hki tr_ext tr']
                exact hk (bhUnpackSmResp sq (bhPackSmResp sq' r))
                  ({ σH.1 with
                      insts := σH.1.insts.set i { d with gs := some gs' },
                      instMeta := σH.1.instMeta.set i im' },
                    σH.2.set i tr')
                  gs_ext tr_ext
                  ⟨bhPrefixPlugInv_set_some h.plug i _ im' (by simp)
                    (fun d' hd' => by rw [hi] at hd'; injection hd' with hEq; rw [← hEq, hd]; simp),
                    by simp [h.tracks_len]⟩
                  rfl

end Computational.Proofs.LibsignalCli.MainHaltedPrefixStage2
