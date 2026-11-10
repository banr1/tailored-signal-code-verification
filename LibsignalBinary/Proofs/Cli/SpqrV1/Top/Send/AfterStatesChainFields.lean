/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainFields
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# `spqr::send` Phase 3d `ChainPB` Scalar and Bytes Fields (`+5612..+6140`)

Proves the scalar and bytes field sub-steps (`+5612..+5776` and `+5944..+6140`) of
`Option<Chain>` encoding in `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec


open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Prost.EncodeToVec

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

/-! ## `ChainPB` Scalar and Bytes Field Steps -/

/-- `+5612 .. +5672`: writes tag `0x12#8`, calls `Chain::encoded_len`, and calls
`encode_varint`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_push_tag_len_31e48 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hChainLen : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hch_len : chainPBEncodedLen ch < 2 ^ 64)
    (hfit : bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5612#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 5672#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          vecU8At A (sp + 1424#64) cap ptr
            ((bs ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 5612 5672
  examples_hide_fetches; subst hP
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chainPBPinnedAt A g (sp + 4752#64) ch ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  rw [h1432, h1440]
  apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x12#8 hlt1 hcap hptr
  rw [h1432, h1440] at hpack
  refine SepWPp.call_cs (x := ChainEncodedLenPinnedGhost.mk (sp + 4752#64) g ch)
    (F := vecU8At A (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗
      memRegion (sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗ F)
    hChainLen (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
    (ret_pc := entry + 5664#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_callee_eq_chainEncodedLen (by omega) sp] at hm
    simp only [withStepInv, chainEncodedLenPinnedSpec, arm64_norm, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hinv0.trans hinv1, hch_len⟩, ?_⟩
    rw [← hpack]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact ProofLib.allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, chainEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm1 hpcm1 hrunm1 hspm1 hcsm1 hinv_call1
    simp only [arm64_norm, hsp] at hspm1
    dsimp only [withStepInv, chainEncodedLenPinnedSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m1, htrm1⟩ => ?_
    simp only [arm64_norm, htr] at htrm1
    rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_send_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 (chainPBEncodedLen ch)) (sp + 1424#64) cap ptr sp (entry + 5672#64)
      (bs ++ [0x12#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
      (F := chainPBPinnedAt A g (sp + 4752#64) ch ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (((hinv0.trans hinv1).trans hinv_call1).trans hinv2)
      (by rw [stackAt_callee_eq_chainEncodedLen (by omega) sp]; simp only [arm64_norm, hsp]; ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm27, hm28, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_28 hm2_fp
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- `+5672 .. +5724`: encodes `ch.direction` (`tag = 1`, `0x08#8`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_dir_31e84 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 1#32 ch.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 5724#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeInt32Field 1#32 ch.direction) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 5672 5724
  examples_hide_fetches; subst hP
  have h4828 : sp + 4752#64 + 0x4c#64 = sp + 4828#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h4828]
  cases hdir : ch.direction == 0#32
  · have hfit' : bs.length + 1 + (Proto.encodeVarint (ch.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [encodeInt32Field_1_eq, hdir] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos (ch.direction.signExtend 64); omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4828#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
    have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
    rw [h1432, h1440]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x08#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack
    refine step_send_encode_varint_call b A ext hvarint
      (ch.direction.signExtend 64) (sp + 1424#64) cap ptr sp (entry + 5724#64)
      (bs ++ [0x08#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4828#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4828, encodeInt32Field_1_eq, hdir]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 5724#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4828, encodeInt32Field_1_eq, hdir]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- `+5724 .. +5776`: encodes `ch.currentEpoch` (`tag = 2`, `0x10#8`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_currentEpoch_31eb8 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 2#32 ch.currentEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5724#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 5776#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 5724 5776
  examples_hide_fetches; subst hP
  have h4800 : sp + 4752#64 + 0x30#64 = sp + 4800#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h4800]
  cases hep : ch.currentEpoch == 0#64
  · have hfit' : bs.length + 1 + (Proto.encodeVarint ch.currentEpoch).length ≤ cap.toNat := by
      rw [encodeUint64Field_2_eq, hep] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos ch.currentEpoch; omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4800#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
    have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
    rw [h1432, h1440]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x10#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack
    refine step_send_encode_varint_call b A ext hvarint
      ch.currentEpoch (sp + 1424#64) cap ptr sp (entry + 5776#64)
      (bs ++ [0x10#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4800#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4800, encodeUint64Field_2_eq, hep]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 5776#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4800, encodeUint64Field_2_eq, hep]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- `+5944 .. +6052`: encodes `ch.nextRoot` (`tag = 4`, `0x22#8`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_nextRoot_31f94 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) etvMemcpyRegionSpec)
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 4#32 ch.nextRoot).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 5944#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6052#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeBytesField 4#32 ch.nextRoot) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 5944 6052
  examples_hide_fetches; subst hP
  have h4776 : sp + 4752#64 + 0x18#64 = sp + 4776#64 := by bv_omega
  have h4784 : (sp + 4776#64) + 8#64 = sp + 4784#64 := by bv_omega
  have h4792 : (sp + 4776#64) + 16#64 = sp + 4792#64 := by bv_omega
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  dsimp only [chainPBPinnedAt]
  rw [h4776, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4776#64), vecHeader, h4784, h4792]
  refine sepWPp_extract_pure
    (ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63)
    (fun R' hm => by
      have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
          (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
           ((sp + 4776#64) ↦₆₄ g.nextRoot.cap) ∗ ((sp + 4784#64) ↦₆₄ g.nextRoot.ptr) ∗
           ((sp + 4792#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length) ∗
           ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
           ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
           optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
           ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction) ∗
           vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
           stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
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
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        (((sp + 4776#64) ↦₆₄ g.nextRoot.cap) ∗ ((sp + 4784#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((sp + 4792#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x22#8 hlt_tag hcap hptr
    rw [h1432, h1440] at hpack_tag
    refine step_send_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 ch.nextRoot.length) (sp + 1424#64) cap ptr sp (entry + 6004#64) (bs ++ [0x22#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        (((sp + 4776#64) ↦₆₄ g.nextRoot.cap) ∗ ((sp + 4784#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((sp + 4792#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        EncodedLen.vecU8Buf A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, _, hs1_23, hs1_24, hs1_25, _, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm] at hs1_19 hs1_20 hs1_21 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x22#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 ch.nextRoot.length)
    have hfit_mc : bs1.length + ch.nextRoot.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp + 1424#64) cap ptr bs1 ch.nextRoot.length hfit_mc hcap hptr hpos_nr,
      h1432, h1440, vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_nr_toNat : (BitVec.ofNat 64 ch.nextRoot.length).toNat = ch.nextRoot.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_send_memcpy_call b ext hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.nextRoot.ptr sp (entry + 6044#64) ch.nextRoot
      (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 ch.nextRoot.length)
          (cap.toNat - bs1.length - ch.nextRoot.length) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
        chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        (((sp + 4776#64) ↦₆₄ g.nextRoot.cap) ∗ ((sp + 4784#64) ↦₆₄ g.nextRoot.ptr) ∗
          ((sp + 4792#64) ↦₆₄ BitVec.ofNat 64 ch.nextRoot.length)) ∗
        (⌜ch.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
          A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
          memRegion (g.nextRoot.ptr + BitVec.ofNat 64 ch.nextRoot.length)
            (g.nextRoot.cap.toNat - ch.nextRoot.length)) ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_nr_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, _, hs2_23, hs2_24, _, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_23, hs1_24, hs1_27, hs1_28, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_23 hs2_24 hs2_26 hs2_27 hs2_28 hs2_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 6052#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp + 1424#64) cap ptr bs1 ch.nextRoot hfit_mc hcap hptr hne_nr
    have hbs_eq : bs1 ++ ch.nextRoot = bs ++ Proto.encodeBytesField 4#32 ch.nextRoot := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h1432, h1440, hbs_eq] at hpack_mc
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h4776, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4776#64), vecHeader, h4784, h4792,
            vecU8Buf_eq_of_nonempty A g.nextRoot.cap g.nextRoot.ptr ch.nextRoot hemp hnr_le, ← hpack_mc]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have henc_nil : Proto.encodeBytesField 4#32 ch.nextRoot = [] := by
      rw [encodeBytesField_4_eq, hemp]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 6052#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]
          rw [h4776, EncodedLen.vecU8At_eq_header_sep_buf A (sp + 4776#64), vecHeader, h4784, h4792,
            henc_nil, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- `+6052 .. +6108`: reloads `x25` from `[sp, #0x10]` and encodes `ch.sendEpoch` (`tag = 5`, `0x28#8`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_sendEpoch_32000 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr v16 : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 5#32 ch.sendEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 6052#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      ((sp + 16#64) ↦₆₄ v16) ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6108#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = v16 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          ((sp + 16#64) ↦₆₄ v16) ∗
          vecU8At A (sp + 1424#64) cap ptr (bs ++ Proto.encodeUint64Field 5#32 ch.sendEpoch) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 6052 6108
  examples_hide_fetches; subst hP
  have h4808 : sp + 4752#64 + 0x38#64 = sp + 4808#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h4808]
  cases hep : ch.sendEpoch == 0#64
  · have hfit' : bs.length + 1 + (Proto.encodeVarint ch.sendEpoch).length ≤ cap.toNat := by
      rw [encodeUint64Field_5_eq, hep] at hfit
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit; omega
    have hlt1 : bs.length < cap.toNat := by
      have := encodeVarint_length_pos ch.sendEpoch; omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4808#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗
        ((sp + 16#64) ↦₆₄ v16) ∗
        A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hcap hptr => ?_
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
    have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
    rw [h1432, h1440]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp + 1424#64) cap ptr bs 0x28#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack
    refine step_send_encode_varint_call b A ext hvarint
      ch.sendEpoch (sp + 1424#64) cap ptr sp (entry + 6108#64)
      (bs ++ [0x28#8]) (by simpa only [List.length_append, List.length_singleton] using hfit')
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4808#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ ((sp + 16#64) ↦₆₄ v16) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4808, encodeUint64Field_5_eq, hep]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  · apply SepWPp.of_sepWP_cs (mid := entry + 6108#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4808, encodeUint64Field_5_eq, hep]
          simp only [↓reduceIte, List.append_nil]
          exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- `+6108 .. +6140`: encodes `ch.params` (`tag = 6#32`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_chain_params_32038 {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry)
    {s0 s : State}
    (hcp_call : subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 6108#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (sp + 4752#64) ch ∗
      vecU8At A (sp + 1424#64) cap ptr bs ∗ A.pool ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 6140#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((chainPBPinnedAt A g (sp + 4752#64) ch ∗
          vecU8At A (sp + 1424#64) cap ptr
            (bs ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  send_fetches_cli b (Rust.withPanics ext) hfn 6108 6140
  examples_hide_fetches; subst hP
  have h4816 : sp + 4752#64 + 0x40#64 = sp + 4816#64 := by bv_omega
  have h4820 : (sp + 4816#64) + 4#64 = sp + 4820#64 := by bv_omega
  have h4824 : (sp + 4820#64) + 4#64 = sp + 4824#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h4816]
  cases hcp : ch.params with
  | none =>
    dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
    apply SepWPp.of_sepWP_cs (mid := entry + 6140#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4816, hcp]
          dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
          rw [List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some cp =>
    rw [hcp] at hfit
    dsimp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage] at hfit ⊢
    rw [h4820, h4824]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% ((2^64 + ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::ChainParams, alloc::vec::Vec<u8>> [local#3]" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine step_send_encode_chainParams_call b A ext hcp_call
      6#32 cp (sp + 1424#64) cap ptr sp (entry + 6140#64) bs
      (by decide) (by decide) hfit
      (F := (chainLinksVecPinnedAt A g.links (sp + 4752#64) ch.links ∗
        vecU8At A (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        (((sp + 4816#64) ↦₃₂ 1#32) ∗ ((sp + 4820#64) ↦₃₂ cp.maxJump) ∗ ((sp + 4824#64) ↦₃₂ cp.maxOooKeys)) ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt]; rw [h4816, hcp]
          dsimp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage]
          rw [h4820, h4824]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

end CryptoVerification.SpqrV1.Top.Send
