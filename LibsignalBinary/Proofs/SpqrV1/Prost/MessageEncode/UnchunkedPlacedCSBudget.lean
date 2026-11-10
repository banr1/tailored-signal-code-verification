/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Helpers for `unchunked` `message::encode`

Defines placed budget contract propositions (`Blocks 155, 318, 156, 319`), pinned-to-unpinned
bridges, and polymorphic 64-byte-frame call steppers for `EkSentCt1Received::encode` and `Ct1Sent::encode`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_155 blkPl_156 blkPl_318 blkPl_319
   lsProg_155 lsProg_156 lsProg_318 lsProg_319 lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB V1State)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost PinnedEncLenGhost Unchunked4PBGhost Unchunked5PBGhost
   authenticatorPBPinnedAt ct1SentPBAt ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBAt ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   unchunked4At_eq_exists_pinned unchunked5At_eq_exists_pinned)
open CryptoVerification.SpqrV1.Auth
  (AuthEncodePinnedGhost authEncodeStackOf encodeAuthMsg sp_sub_64_aligned
   stackAt_encodeVarint_eq_doReserve64)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (Ct1SentEncodeGhost EkSentCt1ReceivedEncodeGhost UnchunkedEncodeCalleeSavedPlaced
   encodeCt1SentMsg encodeEkSentCt1ReceivedMsg stackAt_authEncode_eq_encodeVarint64
   stackAt_authEncode_eq_encodedLen unchunkedMsgEncodeStackOf withUnchunkedEncodeCSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
  (ct1SentEncodedLenPinnedSpec ekSentCt1ReceivedEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (AuthEncodeEnv authEncodePinnedSpecOf authEncodePinnedSpecOfEnv authPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (sepWPp_call_cs_placed_noPanic)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodePinnedSpecOfEnv ct1SentEncodeSpecOfEnv ct1SentPinnedToUnpinned
   ekSentCt1ReceivedEncodePinnedSpecOfEnv ekSentCt1ReceivedEncodeSpecOfEnv
   ekSentCt1ReceivedPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (ct1SentEncodePinnedSpecOfS ct1SentEncodePinnedSpecS ct1SentEncodePinnedSpecXS
   ct1SentEncodeSpecOfS ct1SentEncodeSpecS ct1SentEncodeSpecXS
   ekSentCt1ReceivedEncodePinnedSpecOfS ekSentCt1ReceivedEncodePinnedSpecS
   ekSentCt1ReceivedEncodePinnedSpecXS ekSentCt1ReceivedEncodeSpecOfS
   ekSentCt1ReceivedEncodeSpecS ekSentCt1ReceivedEncodeSpecXS)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Placed Budget Contract Propositions (`Blocks 155, 318, 156, 319`) -/

def EkSentCt1ReceivedEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_155 H) (blkPl_155).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecS A lim))

def EkSentCt1ReceivedEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_155 H) (blkPl_155).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecS A lim))

def EkSentCt1ReceivedEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_155 H) (blkPl_155).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecXS A lim))

def EkSentCt1ReceivedEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_155 H) (blkPl_155).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecXS A lim))

def EkSentCt1ReceivedEncode2PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_318 H) (blkPl_318).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecS A lim))

def EkSentCt1ReceivedEncode2PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_318 H) (blkPl_318).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecS A lim))

def EkSentCt1ReceivedEncode2PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_318 H) (blkPl_318).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecXS A lim))

def EkSentCt1ReceivedEncode2PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_318 H) (blkPl_318).base
    (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecXS A lim))

def Ct1SentEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_156 H) (blkPl_156).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecS A lim))

def Ct1SentEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_156 H) (blkPl_156).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecS A lim))

def Ct1SentEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_156 H) (blkPl_156).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecXS A lim))

def Ct1SentEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_156 H) (blkPl_156).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecXS A lim))

def Ct1SentEncode2PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_319 H) (blkPl_319).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecS A lim))

def Ct1SentEncode2PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_319 H) (blkPl_319).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecS A lim))

def Ct1SentEncode2PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_319 H) (blkPl_319).base
    (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecXS A lim))

def Ct1SentEncode2PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_319 H) (blkPl_319).base
    (withLsCodeLoaded lsmpl (ct1SentEncodeSpecXS A lim))

/-! ## 2. Pinned-to-Unpinned Bridges (`EkSentCt1Received` & `Ct1Sent`) -/

theorem ekSentCt1ReceivedEncode_post_unpinned_of_pinned_env {resStack : Nat}
    {Env : EkSentCt1ReceivedEncodeGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : EkSentCt1ReceivedEncodeGhost} {st : M.σ} {g : Unchunked4PBGhost}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOfEnv resStack Env A lim).post
      (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (ekSentCt1ReceivedEncodeSpecOfEnv resStack Env A lim).post (x, st) s0 sf ∗ R := by
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOfEnv, ekSentCt1ReceivedPinnedToUnpinned] at hq
  dsimp only [ekSentCt1ReceivedEncodeSpecOfEnv]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
    (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ ekSentCt1ReceivedPBPinnedAt A.repAlloc g x.msgA x.m ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; sep_ac_rfl
  have hgoal : sf.mem ⊨ ekSentCt1ReceivedPBAt A.repAlloc x.msgA x.m ∗ Rest := by
    rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned, sepExists_sepConj_left,
      satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; sep_ac_rfl

theorem ekSentCt1ReceivedEncode_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {Env : EkSentCt1ReceivedEncodeGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfEnv resStack Env A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecOfEnv resStack Env A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [ekSentCt1ReceivedEncodeSpecOfEnv] at hpre
  rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfEnv resStack Env A lim)).pre
        (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre⟩
  refine hpinned.mono_outcome (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, ekSentCt1ReceivedEncode_post_unpinned_of_pinned_env hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem ekSentCt1ReceivedEncode_unpinned_of_pinned_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecOfS resStack A lim)) :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed_env hpinned

theorem ct1SentEncode_post_unpinned_of_pinned_env {resStack : Nat}
    {Env : Ct1SentEncodeGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : Ct1SentEncodeGhost} {st : M.σ} {g : Unchunked5PBGhost}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (ct1SentEncodePinnedSpecOfEnv resStack Env A lim).post
      (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (ct1SentEncodeSpecOfEnv resStack Env A lim).post (x, st) s0 sf ∗ R := by
  dsimp only [ct1SentEncodePinnedSpecOfEnv, ct1SentPinnedToUnpinned] at hq
  dsimp only [ct1SentEncodeSpecOfEnv]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
    (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ ct1SentPBPinnedAt A.repAlloc g x.msgA x.m ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; sep_ac_rfl
  have hgoal : sf.mem ⊨ ct1SentPBAt A.repAlloc x.msgA x.m ∗ Rest := by
    rw [ct1SentPBAt, unchunked5At_eq_exists_pinned, sepExists_sepConj_left,
      satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; sep_ac_rfl

theorem ct1SentEncode_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {Env : Ct1SentEncodeGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOfEnv resStack Env A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ct1SentEncodeSpecOfEnv resStack Env A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [ct1SentEncodeSpecOfEnv] at hpre
  rw [ct1SentPBAt, unchunked5At_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOfEnv resStack Env A lim)).pre
        (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre⟩
  refine hpinned.mono_outcome (⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, ct1SentEncode_post_unpinned_of_pinned_env hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem ct1SentEncode_unpinned_of_pinned_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOfS resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (ct1SentEncodeSpecOfS resStack A lim)) :=
  ct1SentEncode_unpinned_of_pinned_placed_env hpinned

/-! ## 3. Polymorphic 64-Byte-Frame Call Steppers (`Q`, `Qp`, `oom`) -/

/-- Execute `bl memcpy` at `call_pc` with `s.sp = sp - 64#64`, propagating
`UnchunkedEncodeCalleeSavedPlaced s0 sm` and `VmPreserved s sm`. -/
theorem step_unchunked_memcpy_call_placed {prog : Program} {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    exact ProofLib.allowPanic_not_exited hm
  · intro _ _ _ hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)

theorem step_unchunked_encode_varint_call_placed {prog : Program} {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := (EncodeVarintGhost.mk val v curCap curPtr curBs, curSt))
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, encodeVarintFitSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt, FitsEnv.eq_iff.mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    rw [sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val))]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hev => ?_
    have hev_eq : evs = encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs) := hev
    subst hev_eq
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_unchunked_do_reserve2_call_placed {prog : Program} {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v
            (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, doReserve2SpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, doReserve2SpecOf, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_unchunked_do_reserve7_call_placed {prog : Program} {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (additional : Nat) (curSt : M.σ)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt
      (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v
            (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool lim
            (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine sepWPp_call_cs_placed_noPanic (x := (DoReserveCall.mk v curCap curPtr curBs additional, curSt))
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, doReserveSpecOf, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound, (fitsEnv_doReserve_iff _).mpr hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_unchunked_auth_encode_call_placed {prog : Program} {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hauthEnc : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A lim)))
    (authA : BitVec 64) (gAuth : AuthenticatorPBGhost) (auth : AuthenticatorPB)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_fit : curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat ∨
      curBs.length + (encodeAuthMsg auth).length + 10 < 2 ^ 62)
    (hfits : FitsEnv M lim curSt
      (AuthEncodeEnv ⟨authA, auth, v, curCap, curPtr, curBs⟩))
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (authenticatorPBPinnedAt A.repAlloc gAuth authA auth ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      AuthEncodeEnv ⟨authA, auth, v, curCap, curPtr, curBs⟩ evs →
      SepWPp prog ret sm
        ((authenticatorPBPinnedAt A.repAlloc gAuth authA auth ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeAuthMsg auth) ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic
    (x := (AuthEncodePinnedGhost.mk authA gAuth auth v curCap curPtr curBs, curSt))
    (F := F) hauthEnc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withUnchunkedEncodeCSPlaced, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv,
      authPinnedToUnpinned, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_fit, hfits⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv,
      authPinnedToUnpinned]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (authenticatorPBPinnedAt A.repAlloc gAuth authA auth)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hpure => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun evs => ?_
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (authenticatorPBPinnedAt A.repAlloc gAuth authA auth),
      sepConj_left_comm (vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeAuthMsg auth))]
    refine SepWPp.pure_elim fun hev => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm nextCap nextPtr evs hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call))
        hpure.1 hpure.2 hev)

/-- Execute `bl EkSentCt1Received::encoded_len` at `call_pc` with `s.sp = sp - 64#64`,
transporting `A.pool lim curSt` across the 0-allocation call via `VmPreserved`. -/
theorem step_ekSentCt1Received_encoded_len_call_placed {prog : Program} {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (curSt : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A.repAlloc)))
    (g : Unchunked4PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.EkSentCt1Received)
    (hfit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗ A.pool lim curSt sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := PinnedEncLenGhost.mk msgA g m)
    (F := A.pool lim curSt s ∗
      memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
        (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    dsimp only [ekSentCt1ReceivedPBPinnedAt] at hm
    simp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenPinnedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    exact ProofLib.allowPanic_not_exited hm
  · intro _ _ _ hm
    simp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenPinnedSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked4EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    rw [← A.pool_of_vmPreserved hvm, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    dsimp only [ekSentCt1ReceivedPBPinnedAt]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Execute `bl Ct1Sent::encoded_len` at `call_pc` with `s.sp = sp - 64#64`,
transporting `A.pool lim curSt` across the 0-allocation call via `VmPreserved`. -/
theorem step_ct1Sent_encoded_len_call_placed {prog : Program} {resStack : Nat}
    (hres : resStack + 48 + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (curSt : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A.repAlloc)))
    (g : Unchunked5PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.Ct1Sent)
    (hfit : ct1SentPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ct1SentPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗ A.pool lim curSt sm ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine sepWPp_call_cs_placed_noPanic (x := PinnedEncLenGhost.mk msgA g m)
    (F := A.pool lim curSt s ∗
      memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
        (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    dsimp only [ct1SentPBPinnedAt] at hm
    simp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ct1SentEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenPinnedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm
    exact ProofLib.allowPanic_not_exited hm
  · intro _ _ _ hm
    simp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ct1SentEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenPinnedSpec,
      satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro _ _ _ hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.ct1SentEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.unchunked5EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    rw [← A.pool_of_vmPreserved hvm, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    dsimp only [ct1SentPBPinnedAt]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
