/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeaderPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncodePlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `spqr::send`: `V1State::encode_raw` Branches (`idx = 1, 8`)

Relocatable symbolic execution of the `.keysSampled` (`idx = 1`, `+8612..+10916`) and
`.ekReceivedCt1Sampled` (`idx = 8`, `+8960..+11748`) encoding branches in `spqr::send::<HookRng>`
(Block `124`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option linter.style.longLine false
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet (spqrSendName)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

set_option linter.unusedTactic false
attribute [-simp, -arm64_norm] CryptoVerification.SpqrV1.Prost.MessageMerge.bv64_ofNat_add_one

attribute [local arm64_norm]
  spqrSendPlacedEntry blkPl_124_ρ
  ls_resolve_blk_148 ls_resolve_blk_150 ls_resolve_blk_151 ls_resolve_blk_152
  ls_resolve_blk_153 ls_resolve_blk_154 ls_resolve_blk_155 ls_resolve_blk_156
  ls_resolve_blk_157 ls_resolve_blk_162 ls_resolve_blk_163 ls_resolve_blk_171
  ls_resolve_blk_172 ls_resolve_blk_173 ls_resolve_blk_175 ls_resolve_blk_177
  ls_resolve_blk_178 ls_resolve_blk_179 ls_resolve_blk_180 ls_resolve_blk_185
  ls_resolve_blk_186 ls_resolve_blk_188 ls_resolve_blk_189 ls_resolve_blk_192
  ls_resolve_blk_193

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Variant `idx = 1`: `.keysSampled` (`+8612 .. +10916`) -/

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_1_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 185) (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent) (bs : List (BitVec 8))
    (hu_lt : headerSentPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 10520#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hx26 : s.readReg64 .x26 = sp + 4704#64) (hinv0 : StepInv s0 s)
    (hP : P = (headerSentPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (h10656 : ∀ sm4 : State, sm4.pc = spqrSendPlacedEntry + 10656#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x20 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 → sm4.readReg64 .x26 = sp + 4704#64 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr
          ((((bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))) ++
            Proto.encodeUint64Field 1#32 u.epoch) ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  rw [etv2_encodeOptHeaderSent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 185); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
  refine step_send_leaf_encLen16_call_placed hres ext (headerSentPBPinnedAt A) headerSentPBEncodedLen hhsLen (sp + 4840#64) sp (spqrSendPlacedEntry + 10564#64) g u hu_lt
    (F := ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv1) (by rw [← hpack1]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, hm26, hm27, hm28, hmfp, _⟩ hinv_m1
  simp only [arm64_norm, hx22, hx25, hx26] at hm19 hm20 hm21 hm22 hm23 hm25 hm26 hm27 hm28 hmfp
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))
  have hfit_var : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine step_send_encode_varint_call_placed A hvarint (BitVec.ofNat 64 (headerSentPBEncodedLen u)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10572#64) (bs ++ [0x0a#8]) hfit_var
    (F := headerSentPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
  simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm26, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
  dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
  have ⟨h4840_24, h4840_48, h4840_96⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧ (sp + 4840#64) + 0x30#64 = sp + 4888#64 ∧ (sp + 4840#64) + 0x60#64 = sp + 4936#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
  rw [h4840_24, h4840_48, h4840_96]
  refine sepWPp_extract_pure
    ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
    (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4888#64)
      (R := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; ac_rfl)) hm))
    fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
  suffices h10624 : ∀ sm3 : State, sm3.pc = spqrSendPlacedEntry + 10624#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = s.readReg64 .x20 → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x22 = sp + 4704#64 → sm3.readReg64 .x23 = s.readReg64 .x23 →
      sm3.readReg64 .x25 = w25 → sm3.readReg64 .x26 = sp + 4704#64 →
      sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (spqrSendPlacedProg ext) ret sm3 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hep : u.epoch == 0#64
    · have hfit_ep : bs1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
        rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]; simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
      have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
      refine step_send_encode_varint_call_placed A hvarint u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10624#64) (bs1 ++ [0x08#8])
        (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
        (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3) (by rw [← hpack_ep]) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, _, hm3_25, hm3_26, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
      simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_26 hm3_27 hm3_28 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
        (h10624 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_26 hm3_27 hm3_28 hm3_fp hinv_m3)
    · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10624#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
        (h10624 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hinv_3
  cases hauth : u.auth with
  | none =>
    rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4888#64) none]; simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10656#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4888#64) none]; simp +zetaDelta only [bs2, bs1, hauth, Proto.encodeOptMessage, List.append_nil]))
      (h10656 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
  | some auth =>
    rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4888#64) (some auth)]; simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
    have hfit_auth : bs2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
      rw [hauth] at hfit; dsimp only [bs2, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 151); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
    rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4888#64) (some auth)]
    refine step_send_encode_auth_call_placed A ext hauthEnc (sp + 4888#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10656#64) g.auth auth bs2 hfit_auth
      (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4) (by dsimp only [optAuthenticatorPBPinnedAt]; ac_rfl) ?_
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, hm4_26, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
    simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx23_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10656 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp hinv_m4)
    simp +zetaDelta only [bs2, bs1, hauth, Proto.encodeOptMessage, optAuthenticatorPBPinnedAt]; ac_rfl

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_2_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 sm4 : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent) (bs3 : List (BitVec 8))
    (hfit3 : bs3.length + (Proto.encodeBytesField 3#32 u.ek).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {F : SepProp} {Q : State → SepProp → Prop}
    (hpcm4 : sm4.pc = spqrSendPlacedEntry + 10656#64) (hrunm4 : sm4.status = .Running) (hspm4 : sm4.sp = sp) (htrm4 : sm4.trace = s0.trace)
    (hx25_4 : sm4.readReg64 .x25 = w25) (hx26_4 : sm4.readReg64 .x26 = sp + 4704#64) (hinv_4 : StepInv s0 sm4)
    (h10776 : ∀ sm7 : State, sm7.pc = spqrSendPlacedEntry + 10776#64 → sm7.status = .Running → sm7.sp = sp → sm7.trace = s0.trace →
      sm7.readReg64 .x19 = sm4.readReg64 .x19 → sm7.readReg64 .x20 = sm4.readReg64 .x20 → sm7.readReg64 .x21 = sm4.readReg64 .x21 →
      sm7.readReg64 .x23 = sm4.readReg64 .x23 → sm7.readReg64 .x25 = w25 → sm7.readReg64 .x26 = sp + 4704#64 →
      sm7.readReg64 .x27 = sm4.readReg64 .x27 → sm7.readReg64 .x28 = sm4.readReg64 .x28 → sm7.readReg64 .fp = sm4.readReg64 .fp → StepInv s0 sm7 →
      SepWPp (spqrSendPlacedProg ext) ret sm7 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs3 ++ Proto.encodeBytesField 3#32 u.ek) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret sm4 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4840#64) (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.ek)
    (F := vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun hek_le hek_cap _ => ?_
  have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧ (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
  rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]
  have hek_lt : u.ek.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz_ek, hbnez_ek⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hek_lt
  cases hemp : u.ek.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz_ek hbnez_ek
    have hne_ek : u.ek ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 3#32 u.ek = [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.ek.length) ++ u.ek := by
      rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all : bs3.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.ek.length)).length + u.ek.length ≤ cap.toNat := by
      rw [henc_eq] at hfit3; simp only [List.length_append, List.length_singleton] at hfit3 ⊢; omega
    have hlt_tag : bs3.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine send3a_step_bytes_varint_placed A ext hvarint 0x1a#8 sp cap ptr (spqrSendPlacedEntry + 10716#64) bs3 u.ek hemp hfit_all hcap hptr halign
      (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
        EncodedLen.vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5) (by ac_rfl) ?_
    intro sm5 bs_ek hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_26, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5 hfit_mc hcmp_mc
    simp only [arm64_norm, hx25_4, hx26_4] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_26 hm5_27 hm5_28 hm5_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
    refine send3a_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr (spqrSendPlacedEntry + 10756#64) bs_ek u.ek hemp hek_le halign
      (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
        vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hek_lt (hinv_m5.trans hinv6) (by ac_rfl) ?_
    intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
    simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_26, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10776#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs_ek u.ek hfit_mc hcap hptr hne_ek
    have hbs_eq : bs_ek ++ u.ek = bs3 ++ Proto.encodeBytesField 3#32 u.ek := by dsimp only [bs_ek]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (h10776 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7))
    rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, ← hpack_mc]; ac_rfl
  · simp only [hemp, Bool.not_true] at hbeqz_ek hbnez_ek
    have henc_nil : Proto.encodeBytesField 3#32 u.ek = [] := by rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10776#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (h10776 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]; simp +zetaDelta only [henc_nil, List.append_nil]

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 185) (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent) (bs : List (BitVec 8))
    (hu_lt : headerSentPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 10520#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hx26 : s.readReg64 .x26 = sp + 4704#64) (hinv0 : StepInv s0 s)
    (hP : P = (headerSentPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = spqrSendPlacedEntry + 10896#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 → sm.readReg64 .x26 = sp + 4704#64 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm ((headerSentPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  refine send3_step_keysSampled_some_1_placed hres A ext hhsLen hvarint hauthEnc
    sp cap ptr w25 g u bs hu_lt hfit hcap hptr halign hpc hrun hsp htr hx22 hx25 hx26 hinv0 hP ?_
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hinv_4
  rw [etv2_encodeOptHeaderSent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))
  set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
  set bs3 := bs2 ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
  have hfit3 : bs3.length + (Proto.encodeBytesField 3#32 u.ek).length ≤ cap.toNat := by
    dsimp only [bs3, bs2, bs1]; simp only [List.length_append, List.length_singleton]; omega
  refine send3_step_keysSampled_some_2_placed A ext hvarint hmemcpy sp cap ptr w25 g u bs3 hfit3 hcap hptr halign
    hpcm4 hrunm4 hspm4 htrm4 hx25_4 hx26_4 hinv_4 ?_
  intro sm7 hpcm7 hrunm7 hspm7 htrm7 hx19_7 hx20_7 hx21_7 hx23_7 hx25_7 hx26_7 hx27_7 hx28_7 hfp_7 hinv_7
  rw [hx19_4] at hx19_7; rw [hx20_4] at hx20_7; rw [hx21_4] at hx21_7; rw [hx23_4] at hx23_7
  rw [hx27_4] at hx27_7; rw [hx28_4] at hx28_7; rw [hfp_4] at hfp_7
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have ⟨h4840_24, h4840_48, h4840_96⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧ (sp + 4840#64) + 0x30#64 = sp + 4888#64 ∧ (sp + 4840#64) + 0x60#64 = sp + 4936#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
  set bs4 := bs3 ++ Proto.encodeBytesField 3#32 u.ek
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4864#64) (cap := g.f4.cap) (ptr := g.f4.ptr) (bs := u.dk)
    (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs4 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by dsimp only [bs4]; ac_rfl) fun hdk_le hdk_cap _ => ?_
  have ⟨h4872, h4880⟩ : (sp + 4864#64) + 8#64 = sp + 4872#64 ∧ (sp + 4864#64) + 16#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega⟩
  rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880]
  have hdk_lt : u.dk.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz_dk, hbnez_dk⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hdk_lt
  cases hemp_dk : u.dk.isEmpty
  · simp only [hemp_dk, Bool.not_false] at hbeqz_dk hbnez_dk
    have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp_dk
    have henc_dk : Proto.encodeBytesField 4#32 u.dk = [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
      rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_dk : bs4.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤ cap.toNat := by
      rw [henc_dk] at hfit; dsimp only [bs4, bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    have hlt_tag : bs4.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs4 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b3 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv8
    refine send3a_step_bytes_varint_placed A ext hvarint 0x22#8 sp cap ptr (spqrSendPlacedEntry + 10836#64) bs4 u.dk hemp_dk hfit_dk hcap hptr halign
      (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗ ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
        EncodedLen.vecU8Buf A g.f4.cap g.f4.ptr u.dk ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_7.trans hinv8) (by ac_rfl) ?_
    intro sm8 bs_dk hpcm8 hrunm8 hspm8 htrm8 ⟨hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_25, hm8_26, hm8_27, hm8_28, hm8_fp, _⟩ hinv_m8 hfit_mc hcmp_mc
    simp only [arm64_norm, hx19_7, hx20_7, hx21_7, hx23_7, hx26_7, hx27_7, hx28_7, hfp_7] at hm8_19 hm8_20 hm8_21 hm8_22 hm8_23 hm8_24 hm8_25 hm8_26 hm8_27 hm8_28 hm8_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv9
    refine send3a_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f4.cap g.f4.ptr (spqrSendPlacedEntry + 10876#64) bs_dk u.dk hemp_dk hdk_le halign
      (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗ (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗ ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4888#64) u.auth ∗ ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hdk_lt (hinv_m8.trans hinv9) (by ac_rfl) ?_
    intro sm9 hpcm9 hrunm9 hspm9 htrm9 ⟨hm9_19, hm9_20, hm9_21, hm9_22, hm9_23, hm9_24, _, hm9_26, hm9_27, hm9_28, hm9_fp, _⟩ hinv_m9
    simp only [arm64_norm, hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_26, hm8_27, hm8_28, hm8_fp] at hm9_19 hm9_20 hm9_21 hm9_22 hm9_23 hm9_24 hm9_26 hm9_27 hm9_28 hm9_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10896#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv10
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs_dk u.dk hfit_mc hcap hptr hne_dk
    have hbs_eq : bs_dk ++ u.dk = bs ++ Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u) := by
      rw [etv2_encodeOptHeaderSent_some_eq, henc_dk]; dsimp only [bs_dk, bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_m9.trans hinv10))
    dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
    rw [h4840_24, h4840_48, h4840_96, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880, ← hpack_mc]; ac_rfl
  · simp only [hemp_dk, Bool.not_true] at hbeqz_dk hbnez_dk
    have henc_nil : Proto.encodeBytesField 4#32 u.dk = [] := by rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [↓reduceIte]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10896#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv8
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_7.trans hinv8))
    dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
    rw [h4840_24, h4840_48, h4840_96, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880, etv2_encodeOptHeaderSent_some_eq, henc_nil]
    dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_send_v1_keysSampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 185) (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 173) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost) (v : V1State.Chunked.KeysSampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysSampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysSampled v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 8612#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) v.sendingHdr) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm (((optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) v.sendingHdr) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.keysSampled v)) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; rcases v with ⟨uc, sendingHdr⟩
  rw [etv2_encodeInnerState_keysSampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x12#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optHeaderSentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optHeaderSentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyEncCap g.2 sendingHdr + 1#64 == 0#64) = !sendingHdr.isSome ∧ (Prost.EncodeToVec.optPolyEncCap g.2 sendingHdr + 1#64 != 0#64) = sendingHdr.isSome))
    (fun R' hm => ⟨Prost.EncodeToVec.optHeaderSentPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x12#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9720 : ∀ sm1 : State, sm1.pc = spqrSendPlacedEntry + 9720#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = s.readReg64 .x27 → sm1.readReg64 .x21 = s.readReg64 .x21 →
      sm1.readReg64 .x22 = sp + 4704#64 → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x24 = Prost.EncodeToVec.optHeaderSentCap g.1 uc → sm1.readReg64 .x25 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1 (((optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optHeaderSentPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optHeaderSentPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]))
        (h9720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optHeaderSentPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    | some u =>
      rw [Prost.EncodeToVec.optHeaderSentPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : headerSentPBEncodedLen u < 2 ^ 64 ∧ optHeaderSentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u)) < optHeaderSentPBFieldEncodedLen (some u) := by dsimp only [optHeaderSentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ProtoRepr.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optHeaderSent_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 185); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optHeaderSentPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call_placed hres ext (headerSentPBPinnedAt A) headerSentPBEncodedLen hhsLen (sp + 4840#64) sp (spqrSendPlacedEntry + 8680#64) g.1 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optHeaderSentPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, hm24, _, _, _, hm28, hmfp, _⟩ hinv_m1
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm24 hm28 hmfp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9720#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optHeaderSentPBPinnedAt]; ac_rfl))
        (h9720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx28_1 hfp_1 hinv_1
  suffices h10492 : ∀ sm2 : State, sm2.pc = spqrSendPlacedEntry + 10492#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingHdr) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = s.readReg64 .x27 → sm2.readReg64 .x21 = s.readReg64 .x21 →
      sm2.readReg64 .x22 = sp + 4704#64 → sm2.readReg64 .x23 = s.readReg64 .x23 →
      sm2.readReg64 .x24 = Prost.EncodeToVec.optHeaderSentCap g.1 uc → sm2.readReg64 .x25 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm2.readReg64 .x26 = sp + 4704#64 → sm2.readReg64 .x27 = Prost.EncodeToVec.optPolyEncCap g.2 sendingHdr →
      sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2 (((optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingHdr with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10492#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) none]))
        (h10492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ProtoRepr.ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 173); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4944#64) (some enc)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen (sp + 4944#64) sp (spqrSendPlacedEntry + 9748#64) g.2 enc henc_fit
        (F := optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10492#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl))
        (h10492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingHdr) (b := optHeaderSentPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
  refine step_send_encode_varint_call_placed A hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10508#64) (bs ++ [0x12#8]) hfit_var
    (F := (optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, hm3_26, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_26 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 uc
  suffices h10896 : ∀ sm4 : State, sm4.pc = spqrSendPlacedEntry + 10896#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x27 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 → sm4.readReg64 .x26 = sp + 4704#64 →
      sm4.readReg64 .x27 = Prost.EncodeToVec.optPolyEncCap g.2 sendingHdr → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4 (((optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10896#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl))
        (h10896 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerSentPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (Proto.encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10520#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine send3_step_keysSampled_some_placed hres A ext hhsLen hvarint hauthEnc hmemcpy sp cap ptr w25 g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4944#64) sendingHdr ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4) (by dsimp only [bs1, optHeaderSentPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_23, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [bs2, bs1, optHeaderSentPBPinnedAt]; ac_rfl))
        (h10896 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp hinv_m4)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingHdr with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv2_encodeInnerState_keysSampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11748#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_11748_polyEnc_placed A ext hpolyEnc (sp + 4944#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optHeaderSentPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx23_4, hx25_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_keysSampled_eq]
    simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl

theorem step_send_v1_keysSampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64}
    {s0 : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 185) (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 173) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysSampled) :
    StepSendInnerStateAt6616Placed resStack A ext roBase s0 (.keysSampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 1#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8612#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4944⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 112#64 = sp + 4944#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944]
  refine step_send_v1_keysSampled_placed hres A ext
    hhsLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    sp cap ptr w25 g.a.gKeysSampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000001#64) ∗ memRegion (sp + 4832#64 + 168#64) 56 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Variant `idx = 8`: `.ekReceivedCt1Sampled` (`+8960 .. +11748`) -/

set_option maxHeartbeats 1200000 in
theorem send3_step_ekReceivedCt1Sampled_some_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hct1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 162) (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked5PBGhost) (u : V1State.Unchunked.Ct1SentEkReceived) (bs : List (BitVec 8))
    (hu_lt : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 11256#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentEkReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = spqrSendPlacedEntry + 11724#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm ((ct1SentEkReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptCt1SentEkReceived_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 162); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
  refine step_send_leaf_encLen16_call_placed hres ext (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen hct1Len (sp + 4840#64) sp (spqrSendPlacedEntry + 11300#64) g u hu_lt
    (F := ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv1) (by rw [← hpack1]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1
  simp only [arm64_norm, hx22, hx25] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))
  have hfit_var : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))).length ≤ cap.toNat := by simp only [List.length_append, List.length_singleton]; omega
  refine step_send_encode_varint_call_placed A hvarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11308#64) (bs ++ [0x0a#8]) hfit_var
    (F := ct1SentEkReceivedPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
  simp only [arm64_norm, hm19, hm20, hm21, hm23, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_23 hm2_27 hm2_28 hm2_fp
  dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
  have ⟨h4840_24, h4840_48, h4840_72, h4840_120⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧ (sp + 4840#64) + 0x30#64 = sp + 4888#64 ∧ (sp + 4840#64) + 0x48#64 = sp + 4912#64 ∧ (sp + 4840#64) + 0x78#64 = sp + 4960#64 := ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩
  rw [h4840_24, h4840_48, h4840_72, h4840_120]
  refine sepWPp_extract_pure
    ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
    (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4912#64)
      (R := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗
        ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; ac_rfl)) hm))
    fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
  set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
  suffices h11360 : ∀ sm3 : State, sm3.pc = spqrSendPlacedEntry + 11360#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = s.readReg64 .x20 → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (spqrSendPlacedProg ext) ret sm3 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hep : u.epoch == 0#64
    · have hfit_ep : bs1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
        rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]; simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
      have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
      refine step_send_encode_varint_call_placed A hvarint u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11360#64) (bs1 ++ [0x08#8])
        (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
        (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3) (by rw [← hpack_ep]) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, _, hm3_23, _, _, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
      simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_23, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_23 hm3_27 hm3_28 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl))
        (h11360 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_23 hm3_27 hm3_28 hm3_fp hinv_m3)
    · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11360#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl))
        (h11360 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx23_3 hx27_3 hx28_3 hfp_3 hinv_3
  set bs3 := bs2 ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
  suffices h11392 : ∀ sm4 : State, sm4.pc = spqrSendPlacedEntry + 11392#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x20 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases hauth : u.auth with
    | none =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4912#64) none]; simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11392#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4912#64) none]; simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, List.append_nil]))
        (h11392 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
    | some auth =>
      rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4912#64) (some auth)]; simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
      have hfit_auth : bs2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
        rw [hauth] at hfit; dsimp only [bs2, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 151); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4912#64) (some auth)]
      refine step_send_encode_auth_call_placed A ext hauthEnc (sp + 4912#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11392#64) g.auth auth bs2 hfit_auth
        (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4) (by dsimp only [optAuthenticatorPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, _, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
      simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx23_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_) (h11392 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, optAuthenticatorPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx27_4 hx28_4 hfp_4 hinv_4
  set bs4 := bs3 ++ Proto.encodeBytesField 3#32 u.es
  suffices h11500 : ∀ sm7 : State, sm7.pc = spqrSendPlacedEntry + 11500#64 → sm7.status = .Running → sm7.sp = sp → sm7.trace = s0.trace →
      sm7.readReg64 .x19 = s.readReg64 .x19 → sm7.readReg64 .x20 = s.readReg64 .x20 → sm7.readReg64 .x21 = s.readReg64 .x21 →
      sm7.readReg64 .x23 = s.readReg64 .x23 → sm7.readReg64 .x27 = s.readReg64 .x27 → sm7.readReg64 .x28 = s.readReg64 .x28 → sm7.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm7 →
      SepWPp (spqrSendPlacedProg ext) ret sm7 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs4 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4840#64) (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.es)
      (F := vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp only [bs3]; ac_rfl) fun hes_le hes_cap _ => ?_
    have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧ (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
    rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]
    have hes_lt : u.es.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz_es, hbnez_es⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hes_lt
    cases hemp_es : u.es.isEmpty
    · simp only [hemp_es, Bool.not_false] at hbeqz_es hbnez_es
      have hne_es : u.es ≠ [] := List.isEmpty_eq_false_iff.mp hemp_es
      have henc_es : Proto.encodeBytesField 3#32 u.es = [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.es.length) ++ u.es := by
        rw [etv2_encodeBytesField_3_eq, hemp_es]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_es : bs3.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.es.length)).length + u.es.length ≤ cap.toNat := by
        rw [henc_es] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_tag : bs3.length < cap.toNat := by omega
      have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      refine send3a_step_bytes_varint_placed A ext hvarint 0x1a#8 sp cap ptr (spqrSendPlacedEntry + 11452#64) bs3 u.es hemp_es hfit_es hcap hptr halign
        (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.es.length)) ∗ EncodedLen.vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
          vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5) (by ac_rfl) ?_
      intro sm5 bs_es hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5 hfit_mc hcmp_mc
      simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
      refine send3a_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr (spqrSendPlacedEntry + 11492#64) bs_es u.es hemp_es hes_le halign
        (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.es.length)) ∗
          vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hes_lt (hinv_m5.trans hinv6) (by ac_rfl) ?_
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
      simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11500#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
      have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs_es u.es hfit_mc hcap hptr hne_es
      have hbs_eq : bs_es ++ u.es = bs4 := by dsimp only [bs4, bs_es]; rw [henc_es]; simp only [List.append_assoc]
      rw [h1432, h1440, hbs_eq] at hpack_mc
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h11500 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7))
      rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, ← hpack_mc]; ac_rfl
    · simp only [hemp_es, Bool.not_true] at hbeqz_es hbnez_es
      have henc_nil : Proto.encodeBytesField 3#32 u.es = [] := by rw [etv2_encodeBytesField_3_eq, hemp_es]; simp only [↓reduceIte]
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11500#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h11500 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
      rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]; simp +zetaDelta only [bs4, henc_nil, List.append_nil]
  intro sm7 hpcm7 hrunm7 hspm7 htrm7 hx19_7 hx20_7 hx21_7 hx23_7 hx27_7 hx28_7 hfp_7 hinv_7
  set bs5 := bs4 ++ Proto.encodeBytesField 4#32 u.ek
  suffices h11608 : ∀ sm10 : State, sm10.pc = spqrSendPlacedEntry + 11608#64 → sm10.status = .Running → sm10.sp = sp → sm10.trace = s0.trace →
      sm10.readReg64 .x19 = s.readReg64 .x19 → sm10.readReg64 .x20 = s.readReg64 .x20 → sm10.readReg64 .x21 = s.readReg64 .x21 →
      sm10.readReg64 .x23 = s.readReg64 .x23 → sm10.readReg64 .x27 = s.readReg64 .x27 → sm10.readReg64 .x28 = s.readReg64 .x28 → sm10.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm10 →
      SepWPp (spqrSendPlacedProg ext) ret sm10 (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs5 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4864#64) (cap := g.f4.cap) (ptr := g.f4.ptr) (bs := u.ek)
      (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs4 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp only [bs4]; ac_rfl) fun hek_le hek_cap _ => ?_
    have ⟨h4872, h4880⟩ : (sp + 4864#64) + 8#64 = sp + 4872#64 ∧ (sp + 4864#64) + 16#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega⟩
    rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880]
    have hek_lt : u.ek.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz_ek, hbnez_ek⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hek_lt
    cases hemp_ek : u.ek.isEmpty
    · simp only [hemp_ek, Bool.not_false] at hbeqz_ek hbnez_ek
      have hne_ek : u.ek ≠ [] := List.isEmpty_eq_false_iff.mp hemp_ek
      have henc_ek : Proto.encodeBytesField 4#32 u.ek = [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.ek.length) ++ u.ek := by
        rw [etv2_encodeBytesField_4_eq, hemp_ek]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_ek : bs4.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.ek.length)).length + u.ek.length ≤ cap.toNat := by
        rw [henc_ek] at hfit; dsimp only [bs4, bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_tag : bs4.length < cap.toNat := by omega
      have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs4 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b3 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv8
      refine send3a_step_bytes_varint_placed A ext hvarint 0x22#8 sp cap ptr (spqrSendPlacedEntry + 11560#64) bs4 u.ek hemp_ek hfit_ek hcap hptr halign
        (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗ ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
          EncodedLen.vecU8Buf A g.f4.cap g.f4.ptr u.ek ∗ vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_7.trans hinv8) (by ac_rfl) ?_
      intro sm8 bs_ek hpcm8 hrunm8 hspm8 htrm8 ⟨hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_25, _, hm8_27, hm8_28, hm8_fp, _⟩ hinv_m8 hfit_mc hcmp_mc
      simp only [arm64_norm, hx19_7, hx20_7, hx21_7, hx23_7, hx27_7, hx28_7, hfp_7] at hm8_19 hm8_20 hm8_21 hm8_22 hm8_23 hm8_24 hm8_25 hm8_27 hm8_28 hm8_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv9
      refine send3a_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f4.cap g.f4.ptr (spqrSendPlacedEntry + 11600#64) bs_ek u.ek hemp_ek hek_le halign
        (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗ ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
          vecU8At A (sp + 4888#64) g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hek_lt (hinv_m8.trans hinv9) (by ac_rfl) ?_
      intro sm9 hpcm9 hrunm9 hspm9 htrm9 ⟨hm9_19, hm9_20, hm9_21, hm9_22, hm9_23, hm9_24, _, hm9_26, hm9_27, hm9_28, hm9_fp, _⟩ hinv_m9
      simp only [arm64_norm, hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_27, hm8_28, hm8_fp] at hm9_19 hm9_20 hm9_21 hm9_22 hm9_23 hm9_24 hm9_26 hm9_27 hm9_28 hm9_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11608#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv10
      have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs_ek u.ek hfit_mc hcap hptr hne_ek
      have hbs_eq : bs_ek ++ u.ek = bs5 := by dsimp only [bs5, bs_ek]; rw [henc_ek]; simp only [List.append_assoc]
      rw [h1432, h1440, hbs_eq] at hpack_mc
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h11608 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m9.trans hinv10))
      rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880, ← hpack_mc]; ac_rfl
    · simp only [hemp_ek, Bool.not_true] at hbeqz_ek hbnez_ek
      have henc_nil : Proto.encodeBytesField 4#32 u.ek = [] := by rw [etv2_encodeBytesField_4_eq, hemp_ek]; simp only [↓reduceIte]
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11608#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv8
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h11608 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_7.trans hinv8))
      rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4864#64), vecHeader, h4872, h4880]; simp +zetaDelta only [bs5, henc_nil, List.append_nil]
  intro sm10 hpcm10 hrunm10 hspm10 htrm10 hx19_10 hx20_10 hx21_10 hx23_10 hx27_10 hx28_10 hfp_10 hinv_10
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4888#64) (cap := g.f5.cap) (ptr := g.f5.ptr) (bs := u.ct1)
    (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
      optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs5 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by dsimp only [bs5]; ac_rfl) fun hct1_le hct1_cap _ => ?_
  have ⟨h4896, h4904⟩ : (sp + 4888#64) + 8#64 = sp + 4896#64 ∧ (sp + 4888#64) + 16#64 = sp + 4904#64 := ⟨by bv_omega, by bv_omega⟩
  rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4888#64), vecHeader, h4896, h4904]
  have hct1_lt : u.ct1.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz_ct1, hbnez_ct1⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hct1_lt
  cases hemp_ct1 : u.ct1.isEmpty
  · simp only [hemp_ct1, Bool.not_false] at hbeqz_ct1 hbnez_ct1
    have hne_ct1 : u.ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hemp_ct1
    have henc_ct1 : Proto.encodeBytesField 5#32 u.ct1 = [0x2a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.ct1.length) ++ u.ct1 := by
      rw [etv3_encodeBytesField_5_eq, hemp_ct1]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_ct1 : bs5.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.ct1.length)).length + u.ct1.length ≤ cap.toNat := by
      rw [henc_ct1] at hfit; dsimp only [bs5, bs4, bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    have hlt_tag : bs5.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs5 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b4 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv11
    refine send3a_step_bytes_varint_placed A ext hvarint 0x2a#8 sp cap ptr (spqrSendPlacedEntry + 11672#64) bs5 u.ct1 hemp_ct1 hfit_ct1 hcap hptr halign
      (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        (((sp + 4888#64) ↦₆₄ g.f5.cap) ∗ ((sp + 4896#64) ↦₆₄ g.f5.ptr) ∗ ((sp + 4904#64) ↦₆₄ BitVec.ofNat 64 u.ct1.length)) ∗
        EncodedLen.vecU8Buf A g.f5.cap g.f5.ptr u.ct1 ∗ optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_10.trans hinv11) (by ac_rfl) ?_
    intro sm11 bs_ct1 hpcm11 hrunm11 hspm11 htrm11 ⟨hm11_19, hm11_20, hm11_21, hm11_22, hm11_23, hm11_24, hm11_25, _, hm11_27, hm11_28, hm11_fp, _⟩ hinv_m11 hfit_mc hcmp_mc
    simp only [arm64_norm, hx19_10, hx20_10, hx21_10, hx23_10, hx27_10, hx28_10, hfp_10] at hm11_19 hm11_20 hm11_21 hm11_22 hm11_23 hm11_24 hm11_25 hm11_27 hm11_28 hm11_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv12
    refine send3a_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f5.cap g.f5.ptr (spqrSendPlacedEntry + 11712#64) bs_ct1 u.ct1 hemp_ct1 hct1_le halign
      (F := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.es ∗ vecU8At A (sp + 4864#64) g.f4.cap g.f4.ptr u.ek ∗
        (((sp + 4888#64) ↦₆₄ g.f5.cap) ∗ ((sp + 4896#64) ↦₆₄ g.f5.ptr) ∗ ((sp + 4904#64) ↦₆₄ BitVec.ofNat 64 u.ct1.length)) ∗
        optAuthenticatorPBPinnedAt A g.auth (sp + 4912#64) u.auth ∗ ((sp + 4960#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hct1_lt (hinv_m11.trans hinv12) (by ac_rfl) ?_
    intro sm12 hpcm12 hrunm12 hspm12 htrm12 ⟨hm12_19, hm12_20, hm12_21, hm12_22, hm12_23, hm12_24, _, hm12_26, hm12_27, hm12_28, hm12_fp, _⟩ hinv_m12
    simp only [arm64_norm, hm11_19, hm11_20, hm11_21, hm11_22, hm11_23, hm11_24, hm11_27, hm11_28, hm11_fp] at hm12_19 hm12_20 hm12_21 hm12_22 hm12_23 hm12_24 hm12_26 hm12_27 hm12_28 hm12_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv13
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs_ct1 u.ct1 hfit_mc hcap hptr hne_ct1
    have hbs_eq : bs_ct1 ++ u.ct1 = bs ++ Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) := by
      rw [etv3_encodeOptCt1SentEkReceived_some_eq, henc_ct1]; dsimp only [bs_ct1, bs5, bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m12.trans hinv13))
    dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
    rw [h4840_24, h4840_48, h4840_72, h4840_120, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4888#64), vecHeader, h4896, h4904, ← hpack_mc]; ac_rfl
  · simp only [hemp_ct1, Bool.not_true] at hbeqz_ct1 hbnez_ct1
    have henc_nil : Proto.encodeBytesField 5#32 u.ct1 = [] := by rw [etv3_encodeBytesField_5_eq, hemp_ct1]; simp only [↓reduceIte]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv11
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_10.trans hinv11))
    dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
    rw [h4840_24, h4840_48, h4840_72, h4840_120, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4888#64), vecHeader, h4896, h4904, etv3_encodeOptCt1SentEkReceived_some_eq, henc_nil]
    dsimp only [bs5, bs4, bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_send_v1_ekReceivedCt1Sampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hct1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 162) (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 173) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked5PBGhost × PolynomialEncoderPBGhost) (v : V1State.Chunked.EkReceivedCt1Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekReceivedCt1Sampled v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 8960#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) v.sendingCt1) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm (((optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) v.sendingCt1) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ekReceivedCt1Sampled v)) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; rcases v with ⟨uc, sendingCt1⟩
  rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x4a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1 ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optCt1SentEkReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optCt1SentEkReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyEncCap g.2 sendingCt1 + 1#64 == 0#64) = !sendingCt1.isSome ∧ (Prost.EncodeToVec.optPolyEncCap g.2 sendingCt1 + 1#64 != 0#64) = sendingCt1.isSome))
    (fun R' hm => ⟨Prost.EncodeToVec.optCt1SentEkReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
      Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4968#64)
        (R := optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x4a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9872 : ∀ sm1 : State, sm1.pc = spqrSendPlacedEntry + 9872#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = s.readReg64 .x27 → sm1.readReg64 .x21 = s.readReg64 .x21 →
      sm1.readReg64 .x22 = sp + 4704#64 → sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x24 = Prost.EncodeToVec.optCt1SentEkReceivedCap g.1 uc → sm1.readReg64 .x25 = BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1 (((optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optCt1SentEkReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9872#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optCt1SentEkReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) none, ← hpack]))
        (h9872 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [optCt1SentEkReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    | some u =>
      rw [Prost.EncodeToVec.optCt1SentEkReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64 ∧ optCt1SentEkReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentEkReceivedPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u)) < optCt1SentEkReceivedPBFieldEncodedLen (some u) := by dsimp only [optCt1SentEkReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ProtoRepr.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv3_bv_optCt1SentEkReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 162); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optCt1SentEkReceivedPBPinnedAt_eq A g.1 (sp + 4840#64) (some u)]
      refine step_send_leaf_encLen16_call_placed hres ext (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen hct1Len (sp + 4840#64) sp (spqrSendPlacedEntry + 9028#64) g.1 u hu_fit
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1) (by rw [← hpack]; dsimp only [optCt1SentEkReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, hm24, _, _, _, hm28, hmfp, _⟩ hinv_m1
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm24 hm28 hmfp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9872#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optCt1SentEkReceivedPBPinnedAt]; ac_rfl))
        (h9872 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx28_1 hfp_1 hinv_1
  suffices h11228 : ∀ sm2 : State, sm2.pc = spqrSendPlacedEntry + 11228#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt1) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = s.readReg64 .x27 → sm2.readReg64 .x21 = s.readReg64 .x21 →
      sm2.readReg64 .x22 = sp + 4704#64 → sm2.readReg64 .x23 = s.readReg64 .x23 →
      sm2.readReg64 .x24 = Prost.EncodeToVec.optCt1SentEkReceivedCap g.1 uc → sm2.readReg64 .x25 = BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = Prost.EncodeToVec.optPolyEncCap g.2 sendingCt1 →
      sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2 (((optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases sendingCt1 with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4968#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11228#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4968#64) none]))
        (h11228 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4968#64) (some enc)]; simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ : polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega, by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) < optPolynomialEncoderPBFieldEncodedLen (some enc) := by dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ := (⟨EncodedLen.cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ProtoRepr.ult_of_lt_of_fit hvar_e_lt hopt_e_lt, bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 173); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.2 (sp + 4968#64) (some enc)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen hpolyEncLen (sp + 4968#64) sp (spqrSendPlacedEntry + 9900#64) g.2 enc henc_fit
        (F := optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11228#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl))
        (h11228 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingCt1) (b := optCt1SentEkReceivedPBFieldEncodedLen uc) (c := v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x4a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))
  refine step_send_encode_varint_call_placed A hvarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11244#64) (bs ++ [0x4a#8]) hfit_var
    (F := (optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 uc
  suffices h11724 : ∀ sm4 : State, sm4.pc = spqrSendPlacedEntry + 11724#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x27 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = Prost.EncodeToVec.optPolyEncCap g.2 sendingCt1 → sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4 (((optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq (by simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl))
        (h11724 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4))
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentEkReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (Proto.encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11256#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine send3_step_ekReceivedCt1Sampled_some_placed hres A ext hct1Len hvarint hauthEnc hmemcpy sp cap ptr w25 g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialEncoderPBPinnedAt A g.2 (sp + 4968#64) sendingCt1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4) (by dsimp only [bs1, optCt1SentEkReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_23, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [bs2, bs1, optCt1SentEkReceivedPBPinnedAt]; ac_rfl))
        (h11724 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingCt1 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11748#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_11748_polyEnc_placed A ext hpolyEnc (sp + 4968#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optCt1SentEkReceivedPBPinnedAt A g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx23_4, hx25_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq]
    simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]; ac_rfl

theorem step_send_v1_ekReceivedCt1Sampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64}
    {s0 : State}
    (hct1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 162) (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 173) (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.EkReceivedCt1Sampled) :
    StepSendInnerStateAt6616Placed resStack A ext roBase s0 (.ekReceivedCt1Sampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 8#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8960#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4968⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 136#64 = sp + 4968#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968]
  refine step_send_v1_ekReceivedCt1Sampled_placed hres A ext
    hct1Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    sp cap ptr w25 g.b.gEkReceivedCt1Sampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (sp + 4832#64 + 192#64) 32 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
