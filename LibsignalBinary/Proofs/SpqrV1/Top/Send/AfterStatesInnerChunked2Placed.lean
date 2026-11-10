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
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncodePlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `spqr::send`: `V1State::encode_raw` Branches (`idx = 0, 2, 5`)

Relocatable symbolic execution of the `.keysUnsampled` (`idx = 0`), `.headerSent` (`idx = 2`), and
`.noHeaderReceived` (`idx = 5`) encoding branches in `spqr::send::<HookRng>` (Block `124`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet (spqrSendName)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open V1State.InnerState

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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Slice `memcpy` Helper at `s.sp = sp` (`vecU8At` at `sp + 1424#64`) -/

/-- Execute `bl memcpy` (`lsρ "memcpy"`) on a non-empty `Vec<u8>` buffer slice at `sp +
    1424#64`. -/
theorem send2_step_memcpy_slice_placed {resStack : Nat}
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsρ "memcpy") (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length) (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ EncodedLen.vecU8Buf A srcCap srcPtr srcBs ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; rw [vecU8Buf_eq_of_nonempty A srcCap srcPtr srcBs hemp hsrc_le]
  have hlen_toNat : (BitVec.ofNat 64 srcBs.length).toNat = srcBs.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  refine step_send_memcpy_call_placed hmemcpy (ptr + BitVec.ofNat 64 bs4.length) srcPtr sp ret_pc srcBs
    (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗ ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
      memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length) (cap.toNat - bs4.length - srcBs.length) ∗
      (⌜srcBs.length ≤ srcCap.toNat ∧ srcCap.toNat < 2 ^ 63 ∧ srcPtr ≠ 0⌝ ∗ A.live srcPtr srcCap.toNat 1 ∗
        memRegion (srcPtr + BitVec.ofNat 64 srcBs.length) (srcCap.toNat - srcBs.length)) ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 (by simp only [hx2, hlen_toNat]) hinv0 (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm hpcm hrunm hspm htrm hcsm hinvm)
  rw [vecU8Buf_eq_of_nonempty A srcCap srcPtr srcBs hemp hsrc_le]; ac_rfl

/-! ## 2. Variant `idx = 0`: `.keysUnsampled` (`+6632 .. +6708`, `+9072 .. +9260`, join `+6216`) -/

/-- Step `+6632 .. +6216` for `is = .keysUnsampled v`. -/
theorem step_send_v1_keysUnsampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 172)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : Unchunked2PBGhost)
    (v : V1State.Chunked.KeysUnsampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysUnsampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 6632#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = (optKeysUnsampledPBPinnedAt A g (sp + 4840#64) v.uc ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((optKeysUnsampledPBPinnedAt A g (sp + 4840#64) v.uc ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.keysUnsampled v)) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [etv2_encodeInnerState_keysUnsampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have h4840_48 : (sp + 4840#64) + 48#64 = sp + 4888#64 := by bv_omega
  refine sepWPp_extract_pure
    ((Prost.EncodeToVec.optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧ (Prost.EncodeToVec.optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (fun R' hm => Prost.EncodeToVec.optKeysUnsampledPBPinnedAt_cap_bounds (p := sp + 4840#64)
      (R := vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  cases huc : v.uc with
  | none =>
    have huc_eq : v = ⟨none⟩ := by cases v; subst huc; rfl
    subst huc_eq; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    rw [Prost.EncodeToVec.optKeysUnsampledPBPinnedAt_eq A g (sp + 4840#64) none]
    have hvar0 : Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled ⟨none⟩))) = [0x00#8] := rfl
    have hlt1 : bs.length < cap.toNat := by change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    have hlt2 : (bs ++ [0x0a#8]).length < cap.toNat := by
      simp only [List.length_append, List.length_singleton]; change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((sp + 4840#64) ↦₆₄ Prost.EncodeToVec.optKeysUnsampledCap g none) ∗ Prost.EncodeToVec.optKeysUnsampledRest A g (sp + 4840#64) none ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    have hbeq2 : (cap == BitVec.ofNat 64 bs.length + 1#64) = false := by
      simpa only [List.length_append, List.length_singleton, BitVec.ofNat_add] using cap_beq_len_false_of_lt hlt2 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6680#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
    refine SepWPp.weaken_pre (P' := ((sp + 4840#64) ↦₆₄ Prost.EncodeToVec.optKeysUnsampledCap g none) ∗ Prost.EncodeToVec.optKeysUnsampledRest A g (sp + 4840#64) none ∗
      vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by rw [← hpack1]; exact Entails.of_eq (by ac_rfl)) ?_
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) hlt2 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
    have hlen_add1 : BitVec.ofNat 64 (bs ++ [0x0a#8]).length = BitVec.ofNat 64 bs.length + 1#64 := by simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]
    rw [hlen_add1]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hpack2 := vecU8At_pack_one A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) 0x00#8 hlt2 hcap hptr; rw [h1432, h1440, hlen_add1] at hpack2
    rw [show BitVec.ofNat 64 bs.length + 1#64 + 1#64 = BitVec.ofNat 64 bs.length + 2#64 by bv_omega] at hpack2
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ((hinv0.trans hinv1).trans hinv2))
    rw [Prost.EncodeToVec.optKeysUnsampledPBPinnedAt_eq A g (sp + 4840#64), hpack2, etv2_encodeInnerState_keysUnsampled_eq, hvar0]
    simp only [Proto.encodeOptMessage, List.append_nil, List.append_assoc]; ac_rfl
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [Prost.EncodeToVec.optKeysUnsampledPBPinnedAt_eq A g (sp + 4840#64) (some u)]
    have hpay_eq : v1StateInnerPayloadEncodedLen (.keysUnsampled v) =
        1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u := by rw [v1StateInnerPayloadEncodedLen, huc]; rfl
    have hpay_lt : 1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      dsimp only [v1StatePBEncodedLen] at hv_len; rw [hpay_eq] at hv_len; omega
    have hu_lt : keysUnsampledPBEncodedLen u < 2 ^ 64 := by omega
    obtain ⟨hbv_sum, hbv_ule, hbv_ult⟩ := etv2_bv_msgFieldLen hpay_lt
    have hlt1 : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((sp + 4840#64) ↦₆₄ Prost.EncodeToVec.optKeysUnsampledCap g (some u)) ∗ Prost.EncodeToVec.optKeysUnsampledRest A g (sp + 4840#64) (some u) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 172); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
    have hku_pin : ((sp + 4840#64) ↦₆₄ Prost.EncodeToVec.optKeysUnsampledCap g (some u)) ∗ Prost.EncodeToVec.optKeysUnsampledRest A g (sp + 4840#64) (some u) =
        keysUnsampledPBPinnedAt A g (sp + 4840#64) u := by simpa only [optKeysUnsampledPBPinnedAt] using (Prost.EncodeToVec.optKeysUnsampledPBPinnedAt_eq A g (sp + 4840#64) (some u)).symm
    refine step_send_leaf_encLen16_call_placed hres ext (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen hkuLen
      (sp + 4840#64) sp (spqrSendPlacedEntry + 9088#64) g u hu_lt (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by rw [← hpack1, ← hku_pin]; ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
    rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))
    have hfit_var1 : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_send_encode_varint_call_placed A hvarint
      (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v))) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9136#64) (bs ++ [0x0a#8]) hfit_var1
      (F := keysUnsampledPBPinnedAt A g (sp + 4840#64) u ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [hpay_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2) (by ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
    rw [huc, etv2_encodeOptKeysUnsampled_some_eq] at hfit
    simp only [List.length_append, List.length_singleton] at hfit
    have hlt2 : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hbeq2 := cap_beq_len_false_of_lt hlt2 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt2 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 172); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack2 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x0a#8 hlt2 hcap hptr; rw [h1432, h1440] at hpack2
    refine step_send_leaf_encLen16_call_placed hres ext (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen hkuLen
      (sp + 4840#64) sp (spqrSendPlacedEntry + 9180#64) g u hu_lt (F := vecU8At A (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3) (by rw [← hpack2]; ac_rfl) ?_
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx0m3 hcsm3 hinv_m3
    rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
    simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
    set bs2 := (bs1 ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))
    have hfit_var2 : (bs1 ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))).length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    refine step_send_encode_varint_call_placed A hvarint
      (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9188#64) (bs1 ++ [0x0a#8]) hfit_var2
      (F := keysUnsampledPBPinnedAt A g (sp + 4840#64) u ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m3.trans hinv4) (by ac_rfl) ?_
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
    rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
    simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_25, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
    dsimp only [keysUnsampledPBPinnedAt, unchunked2PinnedAt]
    rw [h4840_48]
    refine sepWPp_extract_pure
      ((optAuthCap g u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4840#64)
        (R := ((sp + 4888#64) ↦₆₄ u.epoch) ∗ vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs2]; ac_rfl)) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    let bs3 := bs2 ++ Proto.encodeUint64Field 1#32 u.epoch
    suffices h9240 : ∀ sm5 : State,
        sm5.pc = spqrSendPlacedEntry + 9240#64 → sm5.status = .Running → sm5.sp = sp → sm5.trace = s0.trace →
        sm5.readReg64 .x19 = s.readReg64 .x19 → sm5.readReg64 .x20 = Prost.EncodeToVec.optKeysUnsampledCap g (some u) →
        sm5.readReg64 .x21 = s.readReg64 .x21 → sm5.readReg64 .x22 = sp + 4704#64 →
        sm5.readReg64 .x23 = s.readReg64 .x23 → sm5.readReg64 .x25 = s.readReg64 .x25 →
        sm5.readReg64 .x27 = s.readReg64 .x27 → sm5.readReg64 .x28 = s.readReg64 .x28 →
        sm5.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm5 →
        SepWPp (spqrSendPlacedProg ext) ret sm5
          (((optAuthenticatorPBPinnedAt A g (sp + 4840#64) u.auth ∗ ((sp + 4888#64) ↦₆₄ u.epoch)) ∗
            vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗
            stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
      cases hep : (u.epoch == 0#64)
      · have hfit_ep : bs2.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
          rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs2, bs1]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
        have hlt_ep : bs2.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
        have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
        rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs2 hlt_ep hcap hptr, h1432, h1440]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
        have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs2 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
        refine step_send_encode_varint_call_placed A hvarint
          u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9240#64) (bs2 ++ [0x08#8])
          (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
          (F := (optAuthenticatorPBPinnedAt A g (sp + 4840#64) u.auth ∗ ((sp + 4888#64) ↦₆₄ u.epoch)) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m4.trans hinv5) (by rw [← hpack_ep]) ?_
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
        rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, _, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩
        simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_25, hm4_27, hm4_28, hm4_fp] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9240 sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
        simp +zetaDelta only [bs3, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl
      · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9240#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9240 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m4.trans hinv5))
        simp +zetaDelta only [bs3, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx25_5 hx27_5 hx28_5 hfp_5 hinv_5
    have hx20_cap : Prost.EncodeToVec.optKeysUnsampledCap g (some u) = optAuthCap g u.auth := rfl; rw [hx20_cap] at hx20_5
    cases hauth : u.auth with
    | none =>
      simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_5.trans hinv6))
      rw [etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
      simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, Proto.encodeOptMessage, optKeysUnsampledPBPinnedAt,
        keysUnsampledPBPinnedAt, unchunked2PinnedAt, h4840_48, List.append_nil, List.append_assoc]
    | some auth =>
      simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
      have hfit_auth : bs3.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
        rw [hauth] at hfit; dsimp only [bs3, bs2, bs1, Proto.encodeOptMessage] at hfit ⊢
        simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 151); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
      refine step_send_encode_auth_call_placed A ext hauthEnc
        (sp + 4840#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9260#64) g auth bs3 hfit_auth (F := ((sp + 4888#64) ↦₆₄ u.epoch) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_5.trans hinv6) (by simp only [hauth, optAuthenticatorPBPinnedAt]; ac_rfl) ?_
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
      rcases hcsm6 with ⟨hm6_19, _, hm6_21, _, hm6_23, _, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩
      simp only [arm64_norm, hx19_5, hx21_5, hx23_5, hx25_5, hx27_5, hx28_5, hfp_5] at hm6_19 hm6_21 hm6_23 hm6_25 hm6_27 hm6_28 hm6_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7))
      rw [etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
      simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, Proto.encodeOptMessage, optKeysUnsampledPBPinnedAt,
        keysUnsampledPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h4840_48, List.append_assoc]; ac_rfl

/-! ## 3. Variant `idx = 2`: `.headerSent` (`+8000 .. +8368`, `+10352 .. +10364`) -/

/-- Sub-step `+8060 .. +8320`: encode field 1 (`v.uc : Option EkSent`) of `HeaderSent`. -/
private theorem send2_step_headerSent_uc_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State}
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 189)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost) (uc : Option V1State.Unchunked.EkSent) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 uc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 8060#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (optEkSentPBPinnedAt A g (sp + 4840#64) uc ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 8320#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((optEkSentPBPinnedAt A g (sp + 4840#64) uc ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 uc) ∗
          A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentPBPinnedAt A g (sp + 4840#64) uc ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    ((Prost.EncodeToVec.optEkSentCap g uc + 1#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optEkSentCap g uc + 1#64 != 0#64) = uc.isSome)
    (fun R' hm => etv2_optEkSentPBPinnedAt_cap_bounds (p := sp + 4840#64)
      (R := vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have h4704_136 : (sp + 4704#64) + 136#64 = sp + 4840#64 := by bv_omega
  cases huc : uc with
  | none =>
    rw [Prost.EncodeToVec.optEkSentPBPinnedAt_eq A g (sp + 4840#64) none]
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8320#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    rw [← Prost.EncodeToVec.optEkSentPBPinnedAt_eq A g (sp + 4840#64) none, huc]
    simp only [Proto.encodeOptMessage, List.append_nil]
  | some u =>
    rw [Prost.EncodeToVec.optEkSentPBPinnedAt_eq A g (sp + 4840#64) (some u)]
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [huc, etv2_encodeOptEkSent_some_eq] at hfit
    simp only [List.length_append, List.length_singleton] at hfit
    have hlt1 : bs.length < cap.toNat := by omega
    have hu_lt : ekSentPBEncodedLen u < 2 ^ 64 := by
      rw [← ekSentPBEncodedLen_eq_proto, V1State.Unchunked.EkSent.encodedLen]
      dsimp only [V1State.Unchunked.EkSent.encodeRaw]; simp only [List.length_append]; have := BitVec.isLt cap; omega
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 189); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack1 := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
    have hek_pin : ((sp + 4840#64) ↦₆₄ Prost.EncodeToVec.optEkSentCap g (some u)) ∗ Prost.EncodeToVec.optEkSentRest A g (sp + 4840#64) (some u) =
        ekSentPBPinnedAt A g (sp + 4840#64) u := by simpa only [optEkSentPBPinnedAt] using (Prost.EncodeToVec.optEkSentPBPinnedAt_eq A g (sp + 4840#64) (some u)).symm
    refine step_send_leaf_encLen16_call_placed hres ext (ekSentPBPinnedAt A) ekSentPBEncodedLen hekSentLen
      (sp + 4840#64) sp (spqrSendPlacedEntry + 8116#64) g u hu_lt
      (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by rw [← hpack1, ← hek_pin]; ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
    rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20, hx25] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    set bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_send_encode_varint_call_placed A hvarint
      (BitVec.ofNat 64 (ekSentPBEncodedLen u)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8124#64) (bs ++ [0x0a#8]) hfit_var
      (F := ekSentPBPinnedAt A g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2) (by ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
    dsimp only [ekSentPBPinnedAt, unchunked3PinnedAt]
    have ⟨h4840_24, h4840_72⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧ (sp + 4840#64) + 0x48#64 = sp + 4912#64 := ⟨by bv_omega, by bv_omega⟩
    rw [h4840_24, h4840_72]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4864#64)
        (R := vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗
          vecU8At A (sp + 1424#64) cap ptr bs1 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; ac_rfl)) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ Proto.encodeUint64Field 1#32 u.epoch
    suffices h8176 : ∀ sm3 : State,
        sm3.pc = spqrSendPlacedEntry + 8176#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x21 = s.readReg64 .x21 →
        sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x25 = w25 →
        sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 →
        sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp (spqrSendPlacedProg ext) ret sm3
          (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
            vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
            stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
      cases hep : u.epoch == 0#64
      · have hfit_ep : bs1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
          rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
        have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
        have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
        rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
        have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
        refine step_send_encode_varint_call_placed A hvarint u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8176#64) (bs1 ++ [0x08#8])
          (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
          (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3) (by rw [← hpack_ep]) ?_
        intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
        rcases hcsm3 with ⟨hm3_19, _, hm3_21, _, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
        simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8176 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp hinv_m3)
        simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl
      · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8176#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8176 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
        simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
    set bs3 := bs2 ++ Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
    suffices h8208 : ∀ sm4 : State,
        sm4.pc = spqrSendPlacedEntry + 8208#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
        sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
        sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
        sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
        SepWPp (spqrSendPlacedProg ext) ret sm4
          (((vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
            vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
            stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
      cases hauth : u.auth with
      | none =>
        rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) none]
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8208#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8208 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
        rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) none]
        simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, List.append_nil]
      | some auth =>
        rw [optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) (some auth)]
        simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
        have hfit_auth : bs2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
          rw [hauth] at hfit; dsimp only [bs2, bs1, Proto.encodeOptMessage] at hfit ⊢
          simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 151); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
        rw [← optAuthenticatorPBPinnedAt_eq A g.auth (sp + 4864#64) (some auth)]
        have h4704_160 : ((sp + 4096#64) + 608#64) + 160#64 = sp + 4864#64 := by bv_omega
        refine step_send_encode_auth_call_placed A ext hauthEnc
          (sp + 4864#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8208#64) g.auth auth bs2 hfit_auth
          (F := (vecU8At A (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4704_160]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4) (by dsimp only [optAuthenticatorPBPinnedAt]; ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
        rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
        simp only [arm64_norm, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8208 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, hauth, Proto.encodeOptMessage, optAuthenticatorPBPinnedAt]; ac_rfl
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 4840#64) (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.dk)
      (F := optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗
        vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun hdk_le hdk_cap _ => ?_
    have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧ (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
    rw [EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856]
    have hdk_lt : u.dk.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hdk_lt
    cases hemp : u.dk.isEmpty
    · simp only [hemp, Bool.not_false] at hbeqz hbnez
      have hpos_dk : 0 < u.dk.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
      have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp
      have henc_eq : Proto.encodeBytesField 3#32 u.dk = [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
        rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_all : bs3.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤ cap.toNat := by
        rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_tag : bs3.length < cap.toNat := by omega
      have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      have hpack_tag := vecU8At_pack_one A (sp + 1424#64) cap ptr bs3 0x1a#8 hlt_tag hcap hptr; rw [h1432, h1440] at hpack_tag
      refine step_send_encode_varint_call_placed A hvarint
        (BitVec.ofNat 64 u.dk.length) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8268#64) (bs3 ++ [0x1a#8])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (F := ((((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
          EncodedLen.vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
          optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_4.trans hinv5) (by rw [← hpack_tag]; ac_rfl) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
      rcases hcsm5 with ⟨hm5_19, _, hm5_21, _, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩
      simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
      let bs4 := (bs3 ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 u.dk.length)
      have hfit_mc : bs4.length + u.dk.length ≤ cap.toNat := by dsimp only [bs4]; simp only [List.length_append, List.length_singleton]; omega
      have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
      rw [vecU8At_expose_slice A (sp + 1424#64) cap ptr bs4 u.dk.length hfit_mc hcap hptr hpos_dk, h1432, h1440]
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsρ "memcpy"); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
      refine send2_step_memcpy_slice_placed A ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr (spqrSendPlacedEntry + 8308#64) bs4 u.dk hemp hdk_le halign
        (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗ ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
          optAuthenticatorPBPinnedAt A g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hdk_lt (hinv_m5.trans hinv6) (by ac_rfl) ?_
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
      rcases hcsm6 with ⟨hm6_19, _, hm6_21, _, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩
      simp only [arm64_norm, hm5_19, hm5_21, hm5_23, hm5_24, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_21 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8320#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
      have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs4 u.dk hfit_mc hcap hptr hne_dk
      have hbs_eq : bs4 ++ u.dk = bs ++ Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) := by
        rw [etv2_encodeOptEkSent_some_eq, henc_eq]; dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
      rw [h1432, h1440, hbs_eq] at hpack_mc
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7))
      rw [huc]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
      rw [h4840_24, h4840_72, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, ← hpack_mc]; ac_rfl
    · simp only [hemp, Bool.not_true] at hbeqz hbnez
      have henc_nil : Proto.encodeBytesField 3#32 u.dk = [] := by rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8320#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
      rw [huc]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
      rw [h4840_24, h4840_72, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4840#64), vecHeader, h4848, h4856, etv2_encodeOptEkSent_some_eq, henc_nil]
      dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

/-- Step `+8000 .. +6216` for `is = .headerSent v`. -/
theorem step_send_v1_headerSent_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 188) (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 189) (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 152) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : ChunkedHeaderSentPBGhost) (v : V1State.Chunked.HeaderSent) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerSent v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 8000#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedHeaderSentPBPinnedAt A g (sp + 4840#64) v ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chunkedHeaderSentPBPinnedAt A g (sp + 4840#64) v ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.headerSent v)) ∗
          A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  rw [etv2_encodeInnerState_headerSent_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x1a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedHeaderSentPBPinnedAt A g (sp + 4840#64) v ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have ⟨h4704, h4840⟩ : (sp + 4096#64) + 608#64 = sp + 4704#64 ∧ (sp + 4704#64) + 136#64 = sp + 4840#64 := ⟨by bv_omega, by bv_omega⟩
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 188); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x1a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  refine step_send_chunked_encLen48_call_placed hres ext (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen hhsLen
    (sp + 4840#64) sp (spqrSendPlacedEntry + 8052#64) g v hsub_len
    (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4840, ← h4704]; simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm, h4704, hx25] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  set bs1 := (bs ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))
  refine step_send_encode_varint_call_placed A hvarint
    (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8060#64)
    (bs ++ [0x1a#8]) hfit_var (F := chunkedHeaderSentPBPinnedAt A g (sp + 4840#64) v ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
  simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
  dsimp only [chunkedHeaderSentPBPinnedAt]
  have ⟨h4840_80, h4840_136⟩ : (sp + 4840#64) + 80#64 = sp + 4920#64 ∧ (sp + 4840#64) + 136#64 = sp + 4976#64 := ⟨by bv_omega, by bv_omega⟩
  rw [h4840_80, h4840_136]
  have hfit_uc : bs1.length + (Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc).length ≤ cap.toNat := by
    dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
  refine send2_step_headerSent_uc_placed hres A ext hekSentLen hvarint hauthEnc hmemcpy
    sp cap ptr w25 g.uc v.uc bs1 hfit_uc halign
    (F := optPolynomialEncoderPBPinnedAt A g.sendingEk (sp + 4920#64) v.sendingEk ∗
      optPolynomialDecoderPBPinnedAt A g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗ F)
    hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_25 hinv_m2 (by dsimp only [bs1]; ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
  simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_27, hm2_28, hm2_fp] at hx19_3 hx21_3 hx23_3 hx27_3 hx28_3 hfp_3
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optPolyEncCap g.sendingEk v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
      (Prost.EncodeToVec.optPolyEncCap g.sendingEk v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 == 0#64) = !v.receivingCt1.isSome ∧
      (Prost.EncodeToVec.optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 != 0#64) = v.receivingCt1.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4920#64)
        (R := optEkSentPBPinnedAt A g.uc (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗
          vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4976#64)
        (R := optEkSentPBPinnedAt A g.uc (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingEk (sp + 4920#64) v.sendingEk ∗
          vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  set bs3 := bs2 ++ Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk
  have ⟨h4920, h4976⟩ : (sp + 4704#64) + 216#64 = sp + 4920#64 ∧ (sp + 4704#64) + 272#64 = sp + 4976#64 := ⟨by bv_omega, by bv_omega⟩
  suffices h8352 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 8352#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x25 = w25 → sm4.readReg64 .x27 = s.readReg64 .x27 →
      sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optEkSentPBPinnedAt A g.uc (sp + 4840#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A g.sendingEk (sp + 4920#64) v.sendingEk ∗
          optPolynomialDecoderPBPinnedAt A g.receivingCt1 (sp + 4976#64) v.receivingCt1) ∗
          vecU8At A (sp + 1424#64) cap ptr bs3 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases henc : v.sendingEk with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (sp + 4920#64) none]
      simp only [henc, Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8352#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8352 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [← h4704]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4))
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (sp + 4920#64) none]
      simp +zetaDelta only [bs3, henc, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some enc =>
      rw [Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (sp + 4920#64) (some enc)]
      simp only [henc, Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have hfit_enc : bs2.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
        rw [henc] at hfit; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 153); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      rw [← Prost.EncodeToVec.optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (sp + 4920#64) (some enc)]
      refine step_send_encode_polyEncoder_call_placed A ext hpolyEnc
        (sp + 4920#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8352#64) g.sendingEk enc bs2 hfit_enc
        (F := optEkSentPBPinnedAt A g.uc (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4920, ← h4704]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_3.trans hinv4) (by dsimp only [optPolynomialEncoderPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
      simp only [arm64_norm, h4704, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8352 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, henc, Proto.encodeOptMessage, optPolynomialEncoderPBPinnedAt]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases hdec : v.receivingCt1 with
  | none =>
    rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (sp + 4976#64) none]
    simp only [hdec, Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (sp + 4976#64) none, etv2_encodeInnerState_headerSent_eq]
    simp +zetaDelta only [bs3, bs2, bs1, hdec, Proto.encodeOptMessage, chunkedHeaderSentPBPinnedAt, List.append_nil, h4840_80, h4840_136, List.append_assoc]
  | some dec =>
    rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (sp + 4976#64) (some dec)]
    simp only [hdec, Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs3.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by
      rw [hdec] at hfit; simp +zetaDelta only [bs3, bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10352#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (sp + 4976#64) (some dec)]
    refine step_send_tail_10352_polyDec3_placed A ext hpolyDec
      (sp + 4976#64) sp cap ptr g.receivingCt1 dec bs3 hfit_dec halign
      (F := optEkSentPBPinnedAt A g.uc (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A g.sendingEk (sp + 4920#64) v.sendingEk ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by rw [← h4976]; simp only [arm64_norm, *]) (hinv_4.trans hinv5)
      (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_headerSent_eq]
    simp +zetaDelta only [bs3, bs2, bs1, hdec, Proto.encodeOptMessage, chunkedHeaderSentPBPinnedAt, optPolynomialDecoderPBPinnedAt, h4840_80, h4840_136, List.append_assoc]; ac_rfl

/-! ## 4. Variant `idx = 5`: `.noHeaderReceived` (`+8724 .. +11220`) -/

/-- Step `+8724 .. +6216` for `is = .noHeaderReceived v`. -/
theorem step_send_v1_noHeaderReceived_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) {s0 s : State}
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 193) (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 186) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 152) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (sp cap ptr w25 : BitVec 64) (g : PolynomialDecoderPBGhost × Unchunked2PBGhost)
    (v : V1State.Chunked.NoHeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.noHeaderReceived v)).length ≤ cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 8724#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) v.uc) ∗ vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) v.receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) v.uc) ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.noHeaderReceived v)) ∗
          A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP; rcases v with ⟨uc, receivingHdr⟩
  rw [etv2_encodeInnerState_noHeaderReceived_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩) < 2 ^ 64 := by dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x32#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc ∗ A.pool ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((Prost.EncodeToVec.optNoHeaderReceivedCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧ (Prost.EncodeToVec.optNoHeaderReceivedCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((Prost.EncodeToVec.optPolyDecCap g.1 receivingHdr + 1#64 == 0#64) = !receivingHdr.isSome ∧ (Prost.EncodeToVec.optPolyDecCap g.1 receivingHdr + 1#64 != 0#64) = receivingHdr.isSome))
    (fun R' hm =>
      ⟨Prost.EncodeToVec.optNoHeaderReceivedPBPinnedAt_cap_bounds (p := sp + 4880#64)
        (R := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm),
       Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc ∗
          vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have ⟨h4704, h4840, h4880⟩ :
      (sp + 4096#64) + 608#64 = sp + 4704#64 ∧ (sp + 4704#64) + 136#64 = sp + 4840#64 ∧
      (sp + 4704#64) + 176#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x32#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack
  suffices h9312 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9312#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = Prost.EncodeToVec.optNoHeaderReceivedCap g.2 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x25 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc) ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [Prost.EncodeToVec.optNoHeaderReceivedPBPinnedAt_eq A g.2 (sp + 4880#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9312#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9312 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [← h4704]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [optNoHeaderReceivedPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
      rw [← Prost.EncodeToVec.optNoHeaderReceivedPBPinnedAt_eq A g.2 (sp + 4880#64) none, ← hpack]
    | some u =>
      rw [Prost.EncodeToVec.optNoHeaderReceivedPBPinnedAt_eq A g.2 (sp + 4880#64) (some u)]; simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : noHeaderReceivedPBEncodedLen u < 2 ^ 64 ∧ optNoHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u)) < optNoHeaderReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optNoHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_u_lt hopt_u_lt, etv2_bv_optNoHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 193); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      rw [← Prost.EncodeToVec.optNoHeaderReceivedPBPinnedAt_eq A g.2 (sp + 4880#64) (some u)]
      refine step_send_leaf_encLen16_call_placed hres ext (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen hnhrLen
        (sp + 4880#64) sp (spqrSendPlacedEntry + 9272#64) g.2 u hu_fit
        (F := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4880, ← h4704]; simp only [arm64_norm, *]) (hinv0.trans hinv1)
        (by rw [← hpack]; dsimp only [optNoHeaderReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
      rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm, h4704] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9312#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9312 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2))
      dsimp only [optNoHeaderReceivedPBPinnedAt]; ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h9956 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 9956#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingHdr) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = Prost.EncodeToVec.optNoHeaderReceivedCap g.2 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = Prost.EncodeToVec.optPolyDecCap g.1 receivingHdr →
      sm2.readReg64 .x25 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc) ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases receivingHdr with
    | none =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.1 (sp + 4840#64) none]; simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9956#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9956 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2))
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.1 (sp + 4840#64) none]
    | some dec =>
      rw [Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.1 (sp + 4840#64) (some dec)]; simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ : polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : ProtoRepr.varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) < optPolynomialDecoderPBFieldEncodedLen (some dec) := by
        dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨hd1, hd2, hd3, hd4, hd5⟩, hult_d, hopt_d_eq⟩ :=
        (⟨EncodedLen.cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, Prost.EncodeToVec.ult_of_lt_of_fit hvar_d_lt hopt_d_lt, bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 186); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
      rw [← Prost.EncodeToVec.optPolynomialDecoderPBPinnedAt_eq A g.1 (sp + 4840#64) (some dec)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4840#64) sp (spqrSendPlacedEntry + 9332#64) g.1 dec hdec_fit
        (F := optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4840]; simp only [arm64_norm, *]) (hinv_1.trans hinv2)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hfp_1] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 9956#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9956 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3))
      dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := EncodedLen.adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingHdr) (b := optNoHeaderReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  set bs1 := (bs ++ [0x32#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
  refine step_send_encode_varint_call_placed A hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9972#64) (bs ++ [0x32#8]) hfit_var
    (F := (optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗ optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3) (by ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, _, hm3_27, hm3_28, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2, hx28_2, hfp_2] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ Proto.encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 uc
  suffices h10108 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10108#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x24 = Prost.EncodeToVec.optPolyDecCap g.1 receivingHdr → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc) ∗
          vecU8At A (sp + 1424#64) cap ptr bs2 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10108#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10108 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4))
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil]; ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv2_encodeOptNoHeaderReceived_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : noHeaderReceivedPBEncodedLen u < 2 ^ 64 := by dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs1 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 193); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv4
      have hpack_tag := vecU8At_pack_one A (sp + 1424#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr; rw [h1432, h1440] at hpack_tag
      refine step_send_leaf_encLen16_call_placed hres ext (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen hnhrLen
        (sp + 4880#64) sp (spqrSendPlacedEntry + 10028#64) g.2 u hu_lt
        (F := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
          vecU8At A (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4880]; simp only [arm64_norm, *]) (hinv_m3.trans hinv4)
        (by rw [← hpack_tag]; dsimp only [optNoHeaderReceivedPBPinnedAt]; ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
      set bs_u1 := (bs1 ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))
      have hfit_uvar : (bs1 ++ [0x0a#8]).length + (Proto.encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      refine step_send_encode_varint_call_placed A hvarint
        (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10036#64) (bs1 ++ [0x0a#8]) hfit_uvar
        (F := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗ noHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m4.trans hinv5) (by ac_rfl) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
      rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩
      simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, hm4_27, hm4_28, hm4_fp] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
      dsimp only [noHeaderReceivedPBPinnedAt, unchunked2PinnedAt]
      have h4880_48 : (sp + 4880#64) + 0x30#64 = sp + 4928#64 := by clear *- ; bv_omega
      rw [h4880_48]
      refine sepWPp_extract_pure
        ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
        (fun R' hm => etv2_optAuth_cap_bounds (A := A) (p := sp + 4880#64)
          (R := optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗ ((sp + 4928#64) ↦₆₄ u.epoch) ∗
            vecU8At A (sp + 1424#64) cap ptr bs_u1 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp only [bs_u1]; ac_rfl)) hm))
        fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
      set bs_u2 := bs_u1 ++ Proto.encodeUint64Field 1#32 u.epoch
      suffices h10088 : ∀ sm6 : State,
          sm6.pc = spqrSendPlacedEntry + 10088#64 → sm6.status = .Running → sm6.sp = sp → sm6.trace = s0.trace →
          sm6.readReg64 .x19 = s.readReg64 .x19 → sm6.readReg64 .x20 = sp + 4704#64 →
          sm6.readReg64 .x21 = s.readReg64 .x21 → sm6.readReg64 .x22 = Prost.EncodeToVec.optNoHeaderReceivedCap g.2 (some u) →
          sm6.readReg64 .x23 = s.readReg64 .x23 → sm6.readReg64 .x24 = Prost.EncodeToVec.optPolyDecCap g.1 receivingHdr →
          sm6.readReg64 .x25 = w25 → sm6.readReg64 .x27 = s.readReg64 .x27 →
          sm6.readReg64 .x28 = s.readReg64 .x28 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
          SepWPp (spqrSendPlacedProg ext) ret sm6
            (((optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗
              optAuthenticatorPBPinnedAt A g.2 (sp + 4880#64) u.auth ∗ ((sp + 4928#64) ↦₆₄ u.epoch)) ∗
              vecU8At A (sp + 1424#64) cap ptr bs_u2 ∗ A.pool ∗ ((sp + 16#64) ↦₆₄ w25) ∗
              stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) by
        cases hep : u.epoch == 0#64
        · have hfit_ep : bs_u1.length + 1 + (Proto.encodeVarint u.epoch).length ≤ cap.toNat := by
            rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
          have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
          have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
          rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs_u1 hlt_ep hcap hptr, h1432, h1440]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 148); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
          have hpack_ep := vecU8At_pack_one A (sp + 1424#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
          refine step_send_encode_varint_call_placed A hvarint
            u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10088#64) (bs_u1 ++ [0x08#8]) (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗ optAuthenticatorPBPinnedAt A g.2 (sp + 4880#64) u.auth ∗ ((sp + 4928#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6) (by rw [← hpack_ep]; ac_rfl) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
          rcases hcsm6 with ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩
          simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_27, hm5_28, hm5_fp] at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10088 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp hinv_m6)
          simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; ac_rfl
        · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10088#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv6
          refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10088 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6))
          simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; ac_rfl
      intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx27_6 hx28_6 hfp_6 hinv_6
      have hx22_eq : Prost.EncodeToVec.optNoHeaderReceivedCap g.2 (some u) = optAuthCap g.2 u.auth := rfl; rw [hx22_eq] at hx22_6
      cases hauth : u.auth with
      | none =>
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 10108#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
        refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10108 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_6.trans hinv7))
        dsimp only [bs2]; rw [etv2_encodeOptNoHeaderReceived_some_eq]
        simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt, h4880_48, List.append_nil, List.append_assoc]
      | some auth =>
        simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
        have hfit_auth : bs_u2.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
          rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, Proto.encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := lsmpl.base 151); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv7
        refine step_send_encode_auth_call_placed A ext hauthEnc (sp + 4880#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10108#64) g.2 auth bs_u2 hfit_auth
          (F := (optPolynomialDecoderPBPinnedAt A g.1 (sp + 4840#64) receivingHdr ∗ ((sp + 4928#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4880]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_6.trans hinv7) (by simp only [hauth, optAuthenticatorPBPinnedAt]; ac_rfl) ?_
        intro sm7 hpcm7 hrunm7 hspm7 htrm7 hcsm7 hinv_m7
        rcases hcsm7 with ⟨hm7_19, hm7_20, hm7_21, _, hm7_23, hm7_24, hm7_25, _, hm7_27, hm7_28, hm7_fp, _⟩
        simp only [arm64_norm, hx19_6, hx20_6, hx21_6, hx23_6, hx24_6, hx25_6, hx27_6, hx28_6, hfp_6] at hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_) (h10108 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp hinv_m7)
        dsimp only [bs2]; rw [etv2_encodeOptNoHeaderReceived_some_eq]
        simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, Proto.encodeOptMessage, optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h4880_48, List.append_assoc]; ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingHdr with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6216#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5))
    rw [etv2_encodeInnerState_noHeaderReceived_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 11208#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
    refine step_send_tail_11208_polyDec2_placed A ext hpolyDec (sp + 4840#64) sp cap ptr g.1 dec bs2 hfit_dec halign
      (F := optNoHeaderReceivedPBPinnedAt A g.2 (sp + 4880#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by rw [← h4840]; simp only [arm64_norm, *]) (hinv_4.trans hinv5) (by dsimp only [optPolynomialDecoderPBPinnedAt]; ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_noHeaderReceived_eq]; simp +zetaDelta only [bs2, bs1, Proto.encodeOptMessage, optPolynomialDecoderPBPinnedAt, List.append_assoc]; ac_rfl

/-! ## 5. `StepSendInnerStateAt6616` Bridges (`idx = 0, 2, 5`) -/

theorem step_send_v1_keysUnsampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 172) (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysUnsampled) : StepSendInnerStateAt6616Placed resStack A ext roBase s0 (.keysUnsampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 0#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 6632#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have h4840 : (sp + 4832#64) + 8#64 = sp + 4840#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840]
  refine step_send_v1_keysUnsampled_placed hres A ext hkuLen hvarint hauthEnc sp cap ptr g.a.gKeysUnsampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000000#64) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ memRegion (sp + 4832#64 + 64#64) 160 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm, hx25] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, spqrSendEncodeJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_send_v1_headerSent_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 188) (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 189) (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 153) (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 152) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderSent) : StepSendInnerStateAt6616Placed resStack A ext roBase s0 (.headerSent v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 2#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8000#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have h4840 : (sp + 4832#64) + 8#64 = sp + 4840#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840]
  refine step_send_v1_headerSent_placed hres A ext hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec sp cap ptr w25 g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp + 4832#64 + 184#64) 40 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, spqrSendEncodeJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_send_v1_noHeaderReceived_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 193) (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 186) (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 148) (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 151) (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 152) (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.NoHeaderReceived) : StepSendInnerStateAt6616Placed resStack A ext roBase s0 (.noHeaderReceived v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 5#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 8724#64); wp_steps; apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have ⟨h4840, h4880⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧ (sp + 4832#64) + 48#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4880]
  refine step_send_v1_noHeaderReceived_placed hres A ext hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec sp cap ptr w25 g.a.gNoHeaderReceived v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (sp + 4832#64 + 104#64) 120 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by dsimp only [spqrSendEncodeJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m; simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4880, spqrSendEncodeJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
