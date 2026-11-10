/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Event Decompositions and Unpinning Bridges for `Authenticator::encode`

Provides stage-by-stage `FitsEvents` and `AllocCostModel.stepEvents` decompositions for
`pushBytesStep`, `optBytesField1ByteTagStep`, `authEncodeStep`, and `authEncodeEvents`,
together with pinned-to-unpinned `subroutine_ok` bridges for `Authenticator::encode`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.Encode1Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget fitsEvents_append)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeBytesField)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost authenticatorPBAt authenticatorPBAt_eq_exists_pinned
   authenticatorPBEncodedLen authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.Auth
  (AuthEncodeGhost AuthEncodePinnedGhost authEncodeStackOf encodeAuthMsg
   authenticatorPBPinnedAt_bounds_of_satisfies)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (reserveStep pushBytesStep pushBytesStep_snd_eq optBytesField1ByteTagStep
   authEncodeStep authPinnedToUnpinned authEncodeEvents AuthEncodeEnv
   authEncodePinnedSpecOfEnv authEncodeSpecOfEnv authEncodePinnedSpecOf authEncodeSpecOf
   AuthEncode1PinnedPlacedOkExt AuthEncode1PlacedOkExt
   AuthEncode1PinnedPlacedOkX AuthEncode1PlacedOkX
   AuthEncode2PinnedPlacedOkExt AuthEncode2PlacedOkExt
   AuthEncode2PinnedPlacedOkX AuthEncode2PlacedOkX)

/-! ## `FitsEvents` and `stepEvents` Decompositions -/

theorem pushBytesStep_succ_snd (n cap len : Nat) :
    (pushBytesStep (n + 1) cap len).2 =
      (pushByteStep cap len).2 ++ pushBytesEvents n (pushByteStep cap len).1 (len + 1) := by
  simp only [pushBytesStep, pushBytesStep_snd_eq]

theorem fitsEvents_pushBytesStep_succ_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (n cap len : Nat) :
    FitsEvents M lim st (pushBytesStep (n + 1) cap len).2 ↔
      FitsEvents M lim st (pushByteStep cap len).2 ∧
        FitsEvents M lim (M.stepEvents (pushByteStep cap len).2 st)
          (pushBytesEvents n (pushByteStep cap len).1 (len + 1)) := by
  rw [pushBytesStep_succ_snd, fitsEvents_append]

theorem stepEvents_pushBytesStep_succ {M : AllocCostModel} (st : M.σ) (n cap len : Nat) :
    M.stepEvents (pushBytesStep (n + 1) cap len).2 st =
      M.stepEvents (pushBytesEvents n (pushByteStep cap len).1 (len + 1))
        (M.stepEvents (pushByteStep cap len).2 st) := by
  rw [pushBytesStep_succ_snd, AllocCostModel.stepEvents_append]

theorem optBytesField1ByteTagStep_of_isEmpty {cap len : Nat} {bs : List (BitVec 8)}
    (he : bs.isEmpty = true) :
    optBytesField1ByteTagStep cap len bs = (cap, []) := by
  simp only [optBytesField1ByteTagStep, he, ↓reduceIte]

theorem optBytesField1ByteTagStep_of_nonempty {cap len : Nat} {bs : List (BitVec 8)}
    (hne : bs.isEmpty = false) :
    optBytesField1ByteTagStep cap len bs =
      let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
      let s1 := pushBytesStep (vlen + 1) cap len
      let s2 := reserveStep s1.1 (len + 1 + vlen) bs.length
      (s2.1, s1.2 ++ s2.2) := by
  simp only [optBytesField1ByteTagStep, hne, Bool.false_eq_true, ↓reduceIte]

theorem fitsEvents_optBytesField1ByteTagStep_nonempty_iff {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {cap len : Nat} {bs : List (BitVec 8)}
    (hne : bs.isEmpty = false) :
    FitsEvents M lim st (optBytesField1ByteTagStep cap len bs).2 ↔
      let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
      let s1 := pushBytesStep (vlen + 1) cap len
      FitsEvents M lim st s1.2 ∧
        FitsEvents M lim (M.stepEvents s1.2 st)
          (reserveStep s1.1 (len + 1 + vlen) bs.length).2 := by
  rw [optBytesField1ByteTagStep_of_nonempty hne, fitsEvents_append]

theorem stepEvents_optBytesField1ByteTagStep_nonempty {M : AllocCostModel}
    (st : M.σ) {cap len : Nat} {bs : List (BitVec 8)} (hne : bs.isEmpty = false) :
    M.stepEvents (optBytesField1ByteTagStep cap len bs).2 st =
      let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
      let s1 := pushBytesStep (vlen + 1) cap len
      M.stepEvents (reserveStep s1.1 (len + 1 + vlen) bs.length).2
        (M.stepEvents s1.2 st) := by
  rw [optBytesField1ByteTagStep_of_nonempty hne, AllocCostModel.stepEvents_append]

theorem fitsEnv_authEncode_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : AuthEncodeGhost) :
    FitsEnv M lim st (AuthEncodeEnv x) ↔ FitsEvents M lim st (authEncodeEvents x) :=
  FitsEnv.eq_iff

theorem fitsEvents_authEncode_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : AuthEncodeGhost) :
    FitsEvents M lim st (authEncodeEvents x) ↔
      let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen x.auth))).length
      let s1 := pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length
      let rkLen := (encodeBytesField 1#32 x.auth.rootKey).length
      let s2 := optBytesField1ByteTagStep s1.1 (x.bs.length + 1 + hdrVlen) x.auth.rootKey
      let s3 := optBytesField1ByteTagStep s2.1 (x.bs.length + 1 + hdrVlen + rkLen) x.auth.macKey
      FitsEvents M lim st s1.2 ∧
        FitsEvents M lim (M.stepEvents s1.2 st) s2.2 ∧
        FitsEvents M lim (M.stepEvents s2.2 (M.stepEvents s1.2 st)) s3.2 := by
  unfold authEncodeEvents authEncodeStep
  dsimp only
  rw [List.append_assoc, fitsEvents_append, fitsEvents_append]

theorem stepEvents_authEncode_eq {M : AllocCostModel} (st : M.σ) (x : AuthEncodeGhost) :
    M.stepEvents (authEncodeEvents x) st =
      let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen x.auth))).length
      let s1 := pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length
      let rkLen := (encodeBytesField 1#32 x.auth.rootKey).length
      let s2 := optBytesField1ByteTagStep s1.1 (x.bs.length + 1 + hdrVlen) x.auth.rootKey
      let s3 := optBytesField1ByteTagStep s2.1 (x.bs.length + 1 + hdrVlen + rkLen) x.auth.macKey
      M.stepEvents s3.2 (M.stepEvents s2.2 (M.stepEvents s1.2 st)) := by
  unfold authEncodeEvents authEncodeStep
  dsimp only
  rw [List.append_assoc, AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append]

/-! ## `authenticatorPBPinnedAt` Bounds Extractor -/

/-- Polymorphic-outcome pure-bounds extractor for `authenticatorPBPinnedAt`. -/
theorem sepWPp_extract_authenticatorPBPinnedAt_bounds {prog : Program} {ret : BitVec 64}
    {s : State} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {g : AuthenticatorPBGhost} {authA : BitVec 64} {auth : AuthenticatorPB}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = authenticatorPBPinnedAt A.repAlloc g authA auth ∗ F)
    (hk : auth.rootKey.length < 2 ^ 63 → auth.macKey.length < 2 ^ 63 →
      (g.rootKey.cap = 0 → auth.rootKey = []) →
      (g.macKey.cap = 0 → auth.macKey = []) →
      SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ authenticatorPBPinnedAt A.repAlloc g authA auth ∗ (F ∗ R) := by
    rw [hP, sepConj_assoc] at hm; exact hm
  obtain ⟨hrk_lt, hmk_lt, hrk_nil, hmk_nil⟩ :=
    authenticatorPBPinnedAt_bounds_of_satisfies hm'
  exact hk hrk_lt hmk_lt hrk_nil hmk_nil R hm hL

/-! ## Pinned-to-Unpinned Bridges -/

theorem authEncode_post_unpinned_of_pinned_env {resStack : Nat}
    {Env : AuthEncodeGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : AuthEncodeGhost} {g : AuthenticatorPBGhost} {st : M.σ}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (authEncodePinnedSpecOfEnv resStack Env A lim).post
      (⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (authEncodeSpecOfEnv resStack Env A lim).post (x, st) s0 sf ∗ R := by
  dsimp only [authEncodePinnedSpecOfEnv, authPinnedToUnpinned] at hq
  dsimp only [authEncodeSpecOfEnv]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
    (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp (authEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ authenticatorPBPinnedAt A.repAlloc g x.authA x.auth ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; sep_ac_rfl
  have hgoal : sf.mem ⊨ authenticatorPBAt A.repAlloc x.authA x.auth ∗ Rest := by
    rw [authenticatorPBAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; sep_ac_rfl

theorem authEncode_post_unpinned_of_pinned {resStack : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : AuthEncodeGhost} {g : AuthenticatorPBGhost} {st : M.σ}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (authEncodePinnedSpecOf resStack A lim).post
      (⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (authEncodeSpecOf resStack A lim).post (x, st) s0 sf ∗ R :=
  authEncode_post_unpinned_of_pinned_env hq

theorem authEncode_unpinned_of_pinned_env {resStack : Nat}
    {Env : AuthEncodeGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (authEncodePinnedSpecOfEnv resStack Env A lim)) :
    subroutine_ok prog entry (authEncodeSpecOfEnv resStack Env A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [authEncodeSpecOfEnv] at hpre
  rw [authenticatorPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, authEncode_post_unpinned_of_pinned_env hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem authEncode_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (authEncodePinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (authEncodeSpecOf resStack A lim) :=
  authEncode_unpinned_of_pinned_env hpinned

theorem authEncode_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {Env : AuthEncodeGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOfEnv resStack Env A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodeSpecOfEnv resStack Env A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [authEncodeSpecOfEnv] at hpre
  rw [authenticatorPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOfEnv resStack Env A lim)).pre
        (⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre⟩
  refine hpinned.mono_outcome (⟨x.authA, g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, authEncode_post_unpinned_of_pinned_env hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem authEncode_unpinned_of_pinned_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (authEncodeSpecOf resStack A lim)) :=
  authEncode_unpinned_of_pinned_placed_env hpinned

theorem authEncode1_placed_of_pinned [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpinned : AuthEncode1PinnedPlacedOkExt A lim H) :
    AuthEncode1PlacedOkExt A lim H :=
  authEncode_unpinned_of_pinned_placed hpinned

theorem authEncode1_placed_of_pinned_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpinned : AuthEncode1PinnedPlacedOkX A lim H) :
    AuthEncode1PlacedOkX A lim H :=
  authEncode_unpinned_of_pinned_placed hpinned

theorem authEncode2_placed_of_pinned [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpinned : AuthEncode2PinnedPlacedOkExt A lim H) :
    AuthEncode2PlacedOkExt A lim H :=
  authEncode_unpinned_of_pinned_placed hpinned

theorem authEncode2_placed_of_pinned_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hpinned : AuthEncode2PinnedPlacedOkX A lim H) :
    AuthEncode2PlacedOkX A lim H :=
  authEncode_unpinned_of_pinned_placed hpinned

end LibsignalBinary.Proofs.SpqrV1.Auth.Encode1Budget
