/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import ProofLib.SepLogic.WPp

/-!
# Phase 2c (`0x6d4cc .. 0x6d6dc`): `Option<Chain>` Encoding

Proves symbolic execution of the inline `Option<Chain>` encoding phase
(`+1212 .. +1740`, `0x6d4cc .. 0x6d6dc`) in
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`,
appending `Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain` to
`vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr bs` and reaching
`entry + 1740#64` (`0x6d6dc`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Protobuf Encoding Bridge Lemmas for `ChainPB` and `ChainEpochPB` -/

theorem encodeKey_1_varint :
    Proto.encodeKey 1#32 .varint = [0x08#8] := by decide

theorem encodeKey_2_lengthDelimited :
    Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := by decide

theorem encodeKey_3_lengthDelimited :
    Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := by decide

theorem encodeKey_4_lengthDelimited :
    Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := by decide

theorem encodeKey_5_varint :
    Proto.encodeKey 5#32 .varint = [0x28#8] := by decide

theorem encodeInt32Field_1_eq (v : BitVec 32) :
    Proto.encodeInt32Field 1#32 v =
      if v == 0#32 then []
      else [0x08#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_1_varint]

theorem encodeUint64Field_2_eq (v : BitVec 64) :
    Proto.encodeUint64Field 2#32 v =
      if v == 0#64 then []
      else [0x10#8] ++ Proto.encodeVarint v := by
  unfold Proto.encodeUint64Field
  rw [encodeKey_2_varint]

theorem encodeUint64Field_5_eq (v : BitVec 64) :
    Proto.encodeUint64Field 5#32 v =
      if v == 0#64 then []
      else [0x28#8] ++ Proto.encodeVarint v := by
  unfold Proto.encodeUint64Field
  rw [encodeKey_5_varint]

theorem encodeBytesField_4_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 4#32 bs =
      if bs.isEmpty then []
      else [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  rw [encodeKey_4_lengthDelimited]

theorem encodeMessage_epoch_3_eq (ep : ChainEpochPB) :
    Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep =
      [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)) ++
        Proto.encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send ++
        Proto.encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv := by
  have hlen : (ChainEpochPB.encodeRaw ep).length = chainEpochPBEncodedLen ep :=
    chainEpochPBEncodedLen_eq_proto ep
  dsimp only [Proto.encodeMessage]
  rw [encodeKey_3_lengthDelimited, hlen]
  dsimp only [ChainEpochPB.encodeRaw]
  simp only [List.append_assoc]

theorem encodeOptMessage_chain_some (ch : ChainPB) :
    Proto.encodeOptMessage ChainPB.encodeRaw 2#32 (some ch) =
      [0x12#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch)) ++
        Proto.encodeInt32Field 1#32 ch.direction ++
        Proto.encodeUint64Field 2#32 ch.currentEpoch ++
        Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++
        Proto.encodeBytesField 4#32 ch.nextRoot ++
        Proto.encodeUint64Field 5#32 ch.sendEpoch ++
        Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params := by
  have hlen : (ChainPB.encodeRaw ch).length = chainPBEncodedLen ch :=
    chainPBEncodedLen_eq_proto ch
  dsimp only [Proto.encodeOptMessage, Proto.encodeMessage]
  rw [encodeKey_2_lengthDelimited, hlen]
  dsimp only [ChainPB.encodeRaw, Proto.encodeOptMessage, Proto.encodeMessage]
  simp only [List.append_assoc]

theorem optChainPB_encode_len_le (st : PqRatchetState) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation).length +
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain).length ≤
      pqRatchetStatePBEncodedLen st := by
  rw [optVersionNegotiationPBFieldEncodedLen_eq_proto 1#32 st.versionNegotiation ⟨by decide, by decide⟩,
    optChainPBFieldEncodedLen_eq_proto 2#32 st.chain ⟨by decide, by decide⟩]
  unfold pqRatchetStatePBEncodedLen
  omega

/-- First word (`[a]`) of `optEpochDirectionPBPinnedAt A g a opt`. -/
def optEpochDirCap (g : EpochDirectionPBGhost) : Option EpochDirectionPB → BitVec 64
  | none => noneCap
  | some _ => g.next.cap

/-- Remainder (`48` bytes at `a + 8#64`) of `optEpochDirectionPBPinnedAt A g a opt` after
splitting off `(a ↦₆₄ optEpochDirCap g opt)`. -/
def optEpochDirRest (A : RustAlloc) (g : EpochDirectionPBGhost) (a : BitVec 64) :
    Option EpochDirectionPB → SepProp
  | none => memRegion (a + 8#64) 48
  | some d =>
    ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      EncodedLen.vecU8Buf A g.next.cap g.next.ptr d.next ∗
      vecU8At A (a + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
      ((a + 0x30#64) ↦₃₂ d.ctr) ∗
      memRegion (a + 0x34#64) 4

theorem optEpochDirectionPBPinnedAt_eq (A : RustAlloc) (g : EpochDirectionPBGhost)
    (a : BitVec 64) (opt : Option EpochDirectionPB) :
    optEpochDirectionPBPinnedAt A g a opt =
      (a ↦₆₄ optEpochDirCap g opt) ∗ optEpochDirRest A g a opt := by
  cases opt with
  | none => rfl
  | some d =>
    dsimp only [optEpochDirectionPBPinnedAt, epochDirectionPBPinnedAt,
      optEpochDirCap, optEpochDirRest]
    rw [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl

theorem optEpochDirRest_cap_bounds {A : RustAlloc} {g : EpochDirectionPBGhost} {p : BitVec 64}
    {opt : Option EpochDirectionPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEpochDirRest A g p opt ∗ R) :
    (optEpochDirCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEpochDirCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp only [optEpochDirCap, Option.isSome_none, Bool.not_false]
    exact ⟨by decide, by decide⟩
  | some d =>
    simp only [optEpochDirRest] at hm
    have hbuf : m ⊨ EncodedLen.vecU8Buf A g.next.cap g.next.ptr d.next ∗
        (((p + 8#64) ↦₆₄ g.next.ptr) ∗
         ((p + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
         vecU8At A (p + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
         ((p + 0x30#64) ↦₃₂ d.ctr) ∗
         memRegion (p + 0x34#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
    dsimp only [optEpochDirCap, Option.isSome_some, Bool.not_true]
    exact ⟨EncodedLen.cap_add_one_beq_zero_false hcap, EncodedLen.cap_add_one_bne_zero_true hcap⟩

/-! ## 2. Sub-Step Lemmas for `ChainPB` Scalar & Bytes Fields -/

/-- Step `+1220 .. +1272` (`0x6d4d4 .. 0x6d508`): writes tag `0x12#8`, calls `Chain::encoded_len [local#2]`
(`0x68790`), and calls `encode_varint` (`0x4d710`). -/
theorem step_encodeToVec_chain_push_tag_len {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hch_len : chainPBEncodedLen ch < 2 ^ 64)
    (hfit : bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1220#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx22 : s.readReg64 .x22 = a + 48#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1272#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = a + 48#64 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr
            ((bs ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1220 1272
  have hbl := encodeToVec_chainEncodedLen_fnAddr_eq b ext hfn
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chainPBPinnedAt A g (a + 48#64) ch ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  apply SepWPp.of_sepWP_cs (mid := (spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, hbl, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x12#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine SepWPp.call_cs (x := ChainEncodedLenPinnedGhost.mk (a + 48#64) g ch)
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗
      memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗ F)
    hChainLen (by simp only [arm64_norm, hbl]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
    (ret_pc := entry + 1264#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)] at hm
    simp only [withStepInv, chainEncodedLenPinnedSpec, arm64_norm, hsp, hx22,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hinv0.trans hinv1, hch_len⟩, ?_⟩
    rw [← hpack]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, chainEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hinv_call1
    simp only [arm64_norm, hsp] at hspm1
    dsimp only [withStepInv, chainEncodedLenPinnedSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m1, htrm1⟩ => ?_
    simp only [arm64_norm, htr] at htrm1
    rcases hcsm1 with ⟨_, hm20, hm21, hm22, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20, hx22] at hm20 hm21 hm22 hm27 hm28 hmfp
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 (chainPBEncodedLen ch)) (sp - 120#64) cap ptr sp (entry + 1272#64)
      (bs ++ [0x12#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
      (F := chainPBPinnedAt A g (a + 48#64) ch ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (((hinv0.trans hinv1).trans hinv_call1).trans hinv2)
      (by rw [stackAt_callee_eq_chainEncodedLen (by omega) (sp - 144#64)]; simp only [arm64_norm, hsp]; ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨_, hm2_20, hm2_21, hm2_22, _, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm20, hm21, hm22, hm27, hm28, hmfp] at hm2_20 hm2_21 hm2_22 hm2_27 hm2_28 hm2_fp
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_21 hm2_22 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `+1272 .. +1324` (`0x6d508 .. 0x6d53c`): encodes `ch.direction` (`tag = 1`, `0x08#8`). -/
theorem step_encodeToVec_chain_dir {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 1#32 ch.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1272#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1324#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeInt32Field 1#32 ch.direction) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1272 1324
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h124 : a + 48#64 + 0x4c#64 = a + 124#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h124]
  cases hdir : ch.direction == 0#32
  · have hfit' : bs.length + 1 + (Proto.encodeVarint (ch.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [encodeInt32Field_1_eq, hdir] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos (ch.direction.signExtend 64); omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 124#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    rw [h112, h104]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x08#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call b A ext hvarint
      (ch.direction.signExtend 64) (sp - 120#64) cap ptr sp (entry + 1324#64)
      (bs ++ [0x08#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 124#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨_, hm20, hm21, hm22, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm20 hm21 hm22 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h124, encodeInt32Field_1_eq, hdir]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm20 hm21 hm22 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 1324#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h124, encodeInt32Field_1_eq, hdir]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+1324 .. +1376` (`0x6d53c .. 0x6d570`): encodes `ch.currentEpoch` (`tag = 2`, `0x10#8`). -/
theorem step_encodeToVec_chain_currentEpoch {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 2#32 ch.currentEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1376#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1324 1376
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h96 : a + 48#64 + 0x30#64 = a + 96#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h96]
  cases hep : ch.currentEpoch == 0#64
  · have hfit' : bs.length + 1 + (Proto.encodeVarint ch.currentEpoch).length ≤ cap.toNat := by
      rw [encodeUint64Field_2_eq, hep] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos ch.currentEpoch; omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 96#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    rw [h112, h104]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x10#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call b A ext hvarint
      ch.currentEpoch (sp - 120#64) cap ptr sp (entry + 1376#64)
      (bs ++ [0x10#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 96#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨_, hm20, hm21, hm22, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm20 hm21 hm22 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h96, encodeUint64Field_2_eq, hep]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm20 hm21 hm22 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 1376#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h96, encodeUint64Field_2_eq, hep]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+1552 .. +1660` (`0x6d620 .. 0x6d68c`): encodes `ch.nextRoot` (`tag = 4`, `0x22#8`). -/
theorem step_encodeToVec_chain_nextRoot {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 4#32 ch.nextRoot).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1552#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1660#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 4#32 ch.nextRoot) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1552 1660
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h72 : a + 48#64 + 0x18#64 = a + 72#64 := by bv_omega
  have h80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h88 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  dsimp only [chainPBPinnedAt]
  rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88]
  refine sepWPp_extract_pure
    (ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63)
    (fun R' hm => by
      have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
          (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
           ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
           ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
           ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
           ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
           optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
           ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact EncodedLen.vecU8Buf_bounds hm')
    fun ⟨hnr_le, hnr_cap⟩ => ?_
  have hnr_lt : ch.nextRoot.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hnr_lt
  cases hemp : ch.nextRoot.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz hbnez
    have hpos_nr : 0 < ch.nextRoot.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_nr : ch.nextRoot ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 4#32 ch.nextRoot =
        [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length) ++ ch.nextRoot := by
      rw [encodeBytesField_4_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length)).length +
          ch.nextRoot.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x22#8 hlt_tag hcap hptr
    rw [h112, h104] at hpack_tag
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 ch.nextRoot.length) (sp - 120#64) cap ptr sp (entry + 1612#64) (bs ++ [0x22#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨_, hs1_20, hs1_21, hs1_22, hs1_23, _, _, _, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx20] at hs1_20 hs1_21 hs1_22 hs1_23 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length)
    have hfit_mc : bs1.length + ch.nextRoot.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp - 120#64) cap ptr bs1 ch.nextRoot.length hfit_mc hcap hptr hpos_nr,
      h112, h104, vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_nr_toNat : (BitVec.ofNat 64 ch.nextRoot.length).toNat = ch.nextRoot.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_etv_memcpy_call b ext hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.nextRoot.ptr sp (entry + 1652#64) ch.nextRoot
      (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 ch.nextRoot.length)
          (cap.toNat - bs1.length - ch.nextRoot.length) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        (((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        (⌜ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
          A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
          memRegion (g.nextRoot.ptr + BitVec.ofNat 64 ch.nextRoot.length)
            (g.nextRoot.cap.toNat - ch.nextRoot.length)) ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_nr_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨_, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, _, _, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_20, hs1_21, hs1_22, hs1_23, hs1_27, hs1_28, hs1_fp]
      at hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_27 hs2_28 hs2_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 1660#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp - 120#64) cap ptr bs1 ch.nextRoot hfit_mc hcap hptr hne_nr
    have hbs_eq : bs1 ++ ch.nextRoot = bs ++ Proto.encodeBytesField 4#32 ch.nextRoot := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h112, h104, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88,
            vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le, ← hpack_mc]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 4#32 ch.nextRoot = [] := by
      rw [encodeBytesField_4_eq, hemp]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 1660#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h72, EncodedLen.vecU8At_eq_header_sep_buf A (a + 72#64), vecHeader, h80, h88,
            henc_nil, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+1660 .. +1712` (`0x6d68c .. 0x6d6c0`): encodes `ch.sendEpoch` (`tag = 5`, `0x28#8`). -/
theorem step_encodeToVec_chain_sendEpoch {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 5#32 ch.sendEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1660#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1712#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeUint64Field 5#32 ch.sendEpoch) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1660 1712
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h104_a : a + 48#64 + 0x38#64 = a + 104#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h104_a]
  cases hep : ch.sendEpoch == 0#64
  · have hfit' : bs.length + 1 + (Proto.encodeVarint ch.sendEpoch).length ≤ cap.toNat := by
      rw [encodeUint64Field_5_eq, hep] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos ch.sendEpoch; omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 104#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    rw [h112, h104]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x28#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call b A ext hvarint
      ch.sendEpoch (sp - 120#64) cap ptr sp (entry + 1712#64)
      (bs ++ [0x28#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 104#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (a + 48#64 + 0x40#64) ch.params ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm20 hm21 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h104_a, encodeUint64Field_5_eq, hep]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm20 hm21 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 1712#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h104_a, encodeUint64Field_5_eq, hep]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+1712 .. +1740` (`0x6d6c0 .. 0x6d6dc`): encodes `ch.params` (`tag = 6#32`). -/
theorem step_encodeToVec_chain_params {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hcp_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1712#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1740#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr
            (bs ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1712 1740
  examples_hide_fetches; subst hP
  have h112_a : a + 48#64 + 0x40#64 = a + 112#64 := by bv_omega
  have h116_a : (a + 112#64) + 4#64 = a + 116#64 := by bv_omega
  have h120_a : (a + 116#64) + 4#64 = a + 120#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h112_a]
  cases hcp : ch.params with
  | none =>
    dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
    apply SepWPp.of_sepWP_cs (mid := entry + 1740#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h112_a, hcp]
          dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
          rw [List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some cp =>
    rw [hcp] at hfit
    dsimp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage] at hfit ⊢
    rw [h116_a, h120_a]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709441376#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine step_etv_encode_chainParams_call b A ext hcp_call
      6#32 cp (sp - 120#64) cap ptr sp (entry + 1740#64) bs
      (by decide) (by decide) hfit
      (F := (chainLinksVecPinnedAt A g.links (a + 48#64) ch.links ∗
        vecU8At A (a + 48#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((a + 48#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((a + 48#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        (((a + 112#64) ↦₃₂ 1#32) ∗ ((a + 116#64) ↦₃₂ cp.maxJump) ∗ ((a + 120#64) ↦₃₂ cp.maxOooKeys)) ∗
        ((a + 48#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm20 hm21 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h112_a, hcp]
          dsimp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage]
          rw [h116_a, h120_a]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm20 hm21 hm27 hm28 hmfp hinv_m)


end CryptoVerification.SpqrV1.Prost.EncodeToVec
