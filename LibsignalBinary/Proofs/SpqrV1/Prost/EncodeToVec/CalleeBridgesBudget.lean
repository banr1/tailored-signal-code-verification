/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `PqRatchetState::encode_to_vec`: Budget-Threaded Callee Contract Bridges

Adapts budget-threaded and `VmPreserved` field-encoder contracts (`encode_varint`, `ChainParams`,
`EpochDirection`, `Authenticator`, `EkSent`/`Ct1Received`, `Ct1Sent`, `PolynomialEncoder`,
`PolynomialDecoder`, and leaf `encoded_len` specs) into the exact-capacity `withStepInv` forms
consumed by `AllocReservePhaseBudget` and `V1StateCommonBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (ProtoPolynomialDecoder ProtoPolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage)
open CryptoVerification.SpqrV1.Auth (authEncodeStackOf encodeAuthMsg)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (ProtoPolynomialDecoder.toPB ProtoPolynomialEncoder.toPB encodeChainParamsMsg encodeCt1SentMsg
   encodeEkSentCt1ReceivedMsg encodeEpochDirectionMsg encodePolyDecoderMsg encodePolyEncoderMsg
   msgEnc48RepeatedStackOf msgEnc48VarintStackOf unchunkedMsgEncodeStackOf)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (encodeToVecCalleeStackOf stackAt_callee_eq_authEncode stackAt_callee_eq_encodeVarint
   stackAt_callee_eq_msgEnc48Varint subroutine_ok_withStepInv withStepInv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (EncodeVarintEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (encodeVarintSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
  (encodeVarintEnv_eq_nil_of_spare encodeVarintFitSpecOf fitsEnv_encodeVarint_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (EncodeChainParamsEnv VecU8EncodeEnv encodeChainParamsSpecOf fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (EncodeEpochDirectionPinnedEnv encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (AuthEncodeEnv authEncodeEnv_eq_nil_of_spare authEncodePinnedSpecOf
   fitsEnv_authEncode_of_spare subroutine_ok_authEncodeExact_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (Ct1SentEncodeEnv EkSentCt1ReceivedEncodeEnv
   ct1SentEncodeEvents ct1SentEncodeEvents_of_spare
   ct1SentEncodeExactSpecOf ct1SentEncodePinnedSpecOf ct1SentEncodePinnedSpecOfEnv
   ct1SentPinnedToUnpinned
   ekSentCt1ReceivedEncodeEvents ekSentCt1ReceivedEncodeEvents_of_spare
   ekSentCt1ReceivedEncodeExactSpecOf ekSentCt1ReceivedEncodePinnedSpecOf
   ekSentCt1ReceivedEncodePinnedSpecOfEnv ekSentCt1ReceivedPinnedToUnpinned
   subroutine_ok_ct1SentExact_of_pinned subroutine_ok_ekSentCt1ReceivedExact_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf encodePolyDecoderExactVmSpecOf encodePolyEncoderExactVmSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvCt1SentEncodeSpecOf etvEkSentCt1ReceivedEncodeSpecOf etvPolyDecoderExactSpecOf
   etvPolyEncoderExactSpecOf leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)

/-! ## 1. Pure Stack & Varint Equivalence Helpers -/

theorem stackAt_callee_eq_allocHook {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
        (encodeToVecCalleeStackOf resStack - allocHookStack) ∗
        stackAt sp1 allocHookStack :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.stackAt_callee_eq_allocHook hlow hhigh sp1

theorem unchunkedMsgEncodeStackOf_eq (resStack : Nat) :
    unchunkedMsgEncodeStackOf resStack = encodeToVecCalleeStackOf resStack :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.unchunkedMsgEncodeStackOf_eq resStack

theorem msgEnc48RepeatedStackOf_eq (resStack : Nat) :
    msgEnc48RepeatedStackOf resStack = encodeToVecCalleeStackOf resStack :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.msgEnc48RepeatedStackOf_eq resStack

private theorem etv_or_80_truncate8_and_7f (a : BitVec 64) :
    (a.truncate 8 ||| 0x80#8) = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

private theorem etv_protoEncodeVarintAux_eq_codec_of_lt (fuel : Nat) (a : BitVec 64)
    (hbound : a >>> (7 * fuel) < 0x80#64) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux (fuel + 1) a =
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux (fuel + 1) a := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero] at hbound
    have h' : a.toNat < 0x80 := BitVec.lt_def.mp hbound
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux, hbound, h', ↓reduceIte]
  | succ fuel ih =>
    rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      have hb' : (a >>> 7) >>> (7 * fuel) < 0x80#64 := by
        have hsh : (a >>> 7) >>> (7 * fuel) = a >>> (7 * (fuel + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
            ← Nat.pow_add]
          congr 2; omega
        rw [hsh]; exact hbound
      simp only [h, h', ↓reduceIte, etv_or_80_truncate8_and_7f a, ih (a >>> 7) hb']
      rfl

theorem etv_protoEncodeVarint_eq_codec (a : BitVec 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint a =
      CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  refine etv_protoEncodeVarintAux_eq_codec_of_lt 9 a ?_
  change a >>> 63 < 0x80#64
  bv_bits

private theorem elim_exact_cap_ptr {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} (hfit : bs1.length + bs2.length ≤ cap.toNat) :
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜cap.toNat ≤ cap'.toNat ∧ (bs1.length + bs2.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr)⌝ ∗
      vecU8At A v cap' ptr' (bs1 ++ bs2)) ⊢
    vecU8At A v cap ptr (bs1 ++ bs2) :=
  Entails.sepExists_elim fun cap' =>
    Entails.sepExists_elim fun ptr' =>
      Entails.pure_left fun ⟨_, hpres⟩ => by
        obtain ⟨rfl, rfl⟩ := hpres hfit
        exact Entails.refl _

private theorem elim_exact_evs {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {sf : State} {P : List AllocEvent → Prop}
    (hnil : ∀ evs, P evs → evs = []) :
    (∃∗ evs : List AllocEvent, ⌜P evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ⊢
    A.pool lim st sf :=
  Entails.sepExists_elim fun evs =>
    Entails.pure_left fun hP => by
      rw [hnil evs hP]
      dsimp only [AllocCostModel.stepEvents]
      exact Entails.refl _

/-! ## 2. Exact-Capacity Bridges for `AllocReservePhaseBudget` Callees -/

theorem etv_encodeVarint_exact_of_fit {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hfit_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeVarintFitSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (AllocReservePhaseBudget.encodeVarintExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, AllocReservePhaseBudget.encodeVarintExactSpecOf] at hpre
  rw [stackAt_callee_eq_encodeVarint hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 128
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hfit' : x.bs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint x.val).length ≤
      x.cap.toNat := by
    rwa [← etv_protoEncodeVarint_eq_codec]
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeVarintFitSpecOf resStack A lim)).pre
      (⟨x.val, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeVarintFitSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit', fitsEnv_encodeVarint_of_spare hfit'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem]; sep_ac_rfl)) hm
  refine hfit_ok.mono_outcome (⟨x.val, x.v, x.cap, x.ptr, x.bs⟩, st) (F_rem ∗ R)
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeVarintFitSpecOf, encodeVarintSpecOf,
      AllocReservePhaseBudget.encodeVarintExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_encodeVarint hres s.sp, etv_protoEncodeVarint_eq_codec]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono (elim_exact_cap_ptr hfit')
            (sepConj_mono_left
              (elim_exact_evs (fun _ hev => encodeVarintEnv_eq_nil_of_spare hfit' hev)))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem]; sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_encodeChainParams_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hcp_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodeChainParamsSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (AllocReservePhaseBudget.encodeChainParamsExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, AllocReservePhaseBudget.encodeChainParamsExactSpecOf] at hpre
  rw [stackAt_callee_eq_msgEnc48Varint hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 80
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, hm⟩
  have hEnv : FitsEnv M lim st (EncodeChainParamsEnv ⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeChainParamsSpecOf resStack A lim)).pre
      (⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeChainParamsSpecOf, encodeChainParamsMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, Or.inl hfit, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; sep_ac_rfl)) hm
  refine hcp_ok.mono_outcome (⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩, st) (F_rem ∗ R)
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeChainParamsSpecOf, encodeChainParamsMsg,
      AllocReservePhaseBudget.encodeChainParamsExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_msgEnc48Varint hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono (elim_exact_cap_ptr hfit)
            (sepConj_mono_left (elim_exact_evs (fun _ hev => (hev.2 hfit).1)))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_encodeEpochDirection_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hed_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodeEpochDirectionPinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (AllocReservePhaseBudget.encodeEpochDirectionExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, AllocReservePhaseBudget.encodeEpochDirectionExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, hm⟩
  have hEnv : FitsEnv M lim st
      (EncodeEpochDirectionPinnedEnv ⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeEpochDirectionPinnedSpecOf resStack A lim)).pre
      (⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, Or.inl hfit, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl)) hm
  refine hed_ok.mono_outcome (⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩, st)
    (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg,
      AllocReservePhaseBudget.encodeEpochDirectionExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_authEncode hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left (elim_exact_evs (fun _ hev => (hev.2 hfit).1))))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_authEncode_exact_of_exact {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hauth_ok : subroutine_ok prog call_pc
      (withStepInv s0 (Auth.EncodeBaseBudget.authEncodeExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (AllocReservePhaseBudget.authEncodeExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, AllocReservePhaseBudget.authEncodeExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hpre' : s.mem ⊨
      (withStepInv s0 (Auth.EncodeBaseBudget.authEncodeExactSpecOf resStack A lim)).pre
        (⟨x.authA, x.g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, Auth.EncodeBaseBudget.authEncodeExactSpecOf, encodeAuthMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl)) hm
  refine hauth_ok.mono_outcome (⟨x.authA, x.g, x.auth, x.v, x.cap, x.ptr, x.bs⟩, st)
    (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, Auth.EncodeBaseBudget.authEncodeExactSpecOf, encodeAuthMsg,
      AllocReservePhaseBudget.authEncodeExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_authEncode hres s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_authEncode_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hauth_ok : subroutine_ok prog call_pc
      (withStepInv s0 (authEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (AllocReservePhaseBudget.authEncodeExactSpecOf resStack A lim)) := by
  refine etv_authEncode_exact_of_exact hres ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, Auth.EncodeBaseBudget.authEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withStepInv s0 (authEncodePinnedSpecOf resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, authEncodePinnedSpecOf, Auth.EncodeBaseBudget.authEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, fitsEnv_authEncode_of_spare hfit⟩, hm⟩
  refine hauth_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, authEncodePinnedSpecOf,
      Auth.EncodeBaseBudget.authEncodePinnedSpecOfEnv,
      Auth.EncodeBaseBudget.authEncodeExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left
                (elim_exact_evs (fun _ hev => authEncodeEnv_eq_nil_of_spare hfit hev))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Exact-Capacity Bridges for `V1StateCommon{Placed,}Budget` Callees -/

theorem etv_ekSentCt1ReceivedEncode_budget_exact_of_exact {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hek_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ekSentCt1ReceivedEncodeExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ (withStepInv s0 (ekSentCt1ReceivedEncodeExactSpecOf resStack A lim)).pre
      (⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ R := by
    dsimp only [withStepInv, ekSentCt1ReceivedEncodeExactSpecOf,
      etvEkSentCt1ReceivedBudgetExactSpecOf, encodeEkSentCt1ReceivedMsg] at hpre ⊢
    rwa [unchunkedMsgEncodeStackOf_eq]
  refine hek_ok.mono_outcome (⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ekSentCt1ReceivedEncodeExactSpecOf,
      etvEkSentCt1ReceivedBudgetExactSpecOf, encodeEkSentCt1ReceivedMsg] at hpost ⊢
    rwa [← unchunkedMsgEncodeStackOf_eq]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_ekSentCt1ReceivedEncode_of_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hek_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)) := by
  refine etv_ekSentCt1ReceivedEncode_budget_exact_of_exact ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, ekSentCt1ReceivedEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hevs0 :
      ekSentCt1ReceivedEncodeEvents (ekSentCt1ReceivedPinnedToUnpinned x) = [] :=
    ekSentCt1ReceivedEncodeEvents_of_spare hfit
  have hfits : FitsEnv M lim st
      (EkSentCt1ReceivedEncodeEnv (ekSentCt1ReceivedPinnedToUnpinned x)) := by
    unfold EkSentCt1ReceivedEncodeEnv
    rw [FitsEnv.eq_iff, hevs0]; trivial
  have hpre' : s.mem ⊨
      (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOf resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOf,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hfits⟩, hm⟩
  refine hek_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOf,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv,
      ekSentCt1ReceivedEncodeExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left
                (elim_exact_evs (fun _ hev => by
                  dsimp only [EkSentCt1ReceivedEncodeEnv] at hev
                  exact hev.trans hevs0))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_ekSentCt1ReceivedEncode_of_vecEnv_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hek_ok : subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, etvEkSentCt1ReceivedBudgetExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hEnv : FitsEnv M lim st
      (VecU8EncodeEnv x.cap.toNat
        (x.bs.length +
          (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length)) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  have hpre' : s.mem ⊨
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hEnv⟩, hm⟩
  refine hek_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, etvEkSentCt1ReceivedEncodeSpecOf,
      etvEkSentCt1ReceivedBudgetExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left (elim_exact_evs (fun _ hev => (hev.2 hfit).1))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_ct1SentEncode_budget_exact_of_exact {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hct1_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ct1SentEncodeExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ (withStepInv s0 (ct1SentEncodeExactSpecOf resStack A lim)).pre
      (⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ R := by
    dsimp only [withStepInv, ct1SentEncodeExactSpecOf,
      etvCt1SentBudgetExactSpecOf, encodeCt1SentMsg] at hpre ⊢
    rwa [unchunkedMsgEncodeStackOf_eq]
  refine hct1_ok.mono_outcome (⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩, st) R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ct1SentEncodeExactSpecOf,
      etvCt1SentBudgetExactSpecOf, encodeCt1SentMsg] at hpost ⊢
    rwa [← unchunkedMsgEncodeStackOf_eq]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_ct1SentEncode_of_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hct1_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ct1SentEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)) := by
  refine etv_ct1SentEncode_budget_exact_of_exact ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, ct1SentEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hevs0 :
      ct1SentEncodeEvents (ct1SentPinnedToUnpinned x) = [] :=
    ct1SentEncodeEvents_of_spare hfit
  have hfits : FitsEnv M lim st
      (Ct1SentEncodeEnv (ct1SentPinnedToUnpinned x)) := by
    unfold Ct1SentEncodeEnv
    rw [FitsEnv.eq_iff, hevs0]; trivial
  have hpre' : s.mem ⊨
      (withStepInv s0 (ct1SentEncodePinnedSpecOf resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOf,
      ct1SentEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hfits⟩, hm⟩
  refine hct1_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOf,
      ct1SentEncodePinnedSpecOfEnv,
      ct1SentEncodeExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left
                (elim_exact_evs (fun _ hev => by
                  dsimp only [Ct1SentEncodeEnv] at hev
                  exact hev.trans hevs0))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_ct1SentEncode_of_vecEnv_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hct1_ok : subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, etvCt1SentBudgetExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hEnv : FitsEnv M lim st
      (VecU8EncodeEnv x.cap.toNat
        (x.bs.length +
          (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length)) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hfit
  have hpre' : s.mem ⊨
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hEnv⟩, hm⟩
  refine hct1_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, etvCt1SentEncodeSpecOf,
      etvCt1SentBudgetExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left (elim_exact_evs (fun _ hev => (hev.2 hfit).1))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_polyEncoderEncode_exact_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hpe_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodePolyEncoderExactVmSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialEncoder := ⟨x.enc.idx, x.enc.pts, x.enc.polys⟩
  have hpb : ProtoPolynomialEncoder.toPB pb = x.enc := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyEncoderExactVmSpecOf resStack A)).pre
      ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, encodePolyEncoderExactVmSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpe_ok.mono_outcome ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyEncoderExactVmSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_polyEncoderEncode_budget_exact_of_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hpe_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodePolyEncoderExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialEncoder := ⟨x.enc.idx, x.enc.pts, x.enc.polys⟩
  have hpb : ProtoPolynomialEncoder.toPB pb = x.enc := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyEncoderExactSpecOf resStack A lim)).pre
      (⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ R := by
    dsimp only [withStepInv, encodePolyEncoderExactSpecOf, etvPolyEncoderBudgetExactSpecOf,
      encodePolyEncoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpe_ok.mono_outcome (⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩, st) R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyEncoderExactSpecOf, etvPolyEncoderBudgetExactSpecOf,
      encodePolyEncoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_polyDecoderEncode_exact_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hpd_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodePolyDecoderExactVmSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialDecoder := ⟨x.dec.ptsNeeded, x.dec.polys, x.dec.pts, x.dec.isComplete⟩
  have hpb : ProtoPolynomialDecoder.toPB pb = x.dec := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyDecoderExactVmSpecOf resStack A)).pre
      ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, encodePolyDecoderExactVmSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpd_ok.mono_outcome ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyDecoderExactVmSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_polyDecoderEncode_budget_exact_of_spec {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hpd_ok : subroutine_ok prog call_pc
      (withStepInv s0 (encodePolyDecoderExactSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialDecoder := ⟨x.dec.ptsNeeded, x.dec.polys, x.dec.pts, x.dec.isComplete⟩
  have hpb : ProtoPolynomialDecoder.toPB pb = x.dec := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyDecoderExactSpecOf resStack A lim)).pre
      (⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩, st) s ∗ R := by
    dsimp only [withStepInv, encodePolyDecoderExactSpecOf, etvPolyDecoderBudgetExactSpecOf,
      encodePolyDecoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpd_ok.mono_outcome (⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩, st) R
    s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyDecoderExactSpecOf, etvPolyDecoderBudgetExactSpecOf,
      encodePolyDecoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem etv_leafEncLen16_withStepInv {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen16Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen16Spec reprAt encLen)) :=
  subroutine_ok_withStepInv s0 hok

theorem etv_leafEncLen48_withStepInv {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen48Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen48Spec reprAt encLen)) :=
  subroutine_ok_withStepInv s0 hok

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
