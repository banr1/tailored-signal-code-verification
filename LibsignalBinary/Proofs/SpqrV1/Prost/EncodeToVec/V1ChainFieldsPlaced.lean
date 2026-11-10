/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainFields
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Phase 2c (`Block 426`, `+1212 .. +1740`): `Option<Chain>` Fields Encoding

Proves `[LibsignalPlacement]` symbolic execution of the scalar, bytes, and `Option<ChainParams>`
sub-steps of `Option<Chain>` encoding in `PqRatchetState::encode_to_vec` (`Block 426`).
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

set_option autoImplicit false
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

/-- Step `+1220 .. +1272` (`Block 426`): writes tag `0x12#8`, calls `Chain::encoded_len [local#2]`
(`lsmpl.base 406`), and calls `encode_varint` (`lsmpl.base 292`). -/
theorem step_encodeToVec_chain_push_tag_len_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hChainLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hch_len : chainPBEncodedLen ch < 2 ^ 64)
    (hfit : bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1220#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx22 : s.readReg64 .x22 = a + 48#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1272#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = a + 48#64 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr
            ((bs ++ [0x12#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 406)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x12#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine SepWPp.call_cs (x := ChainEncodedLenPinnedGhost.mk (a + 48#64) g ch)
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool ∗
      memRegion (sp - 144#64 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (80 + resStack) ∗ F)
    hChainLen (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
    (ret_pc := (blkPl_426).base + 1264#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_etv_encode_varint_call_prog A hvarint
      (BitVec.ofNat 64 (chainPBEncodedLen ch)) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1272#64)
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

/-- Step `+1272 .. +1324` (`Block 426`): encodes `ch.direction` (`tag = 1`, `0x08#8`). -/
theorem step_encodeToVec_chain_dir_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 1#32 ch.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1272#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1324#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeInt32Field 1#32 ch.direction) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x08#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call_prog A hvarint
      (ch.direction.signExtend 64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1324#64)
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
  · apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1324#64); wp_steps
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

/-- Step `+1324 .. +1376` (`Block 426`): encodes `ch.currentEpoch` (`tag = 2`, `0x10#8`). -/
theorem step_encodeToVec_chain_currentEpoch_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 2#32 ch.currentEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1376#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeUint64Field 2#32 ch.currentEpoch) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x10#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call_prog A hvarint
      ch.currentEpoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 1376#64)
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
  · apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1376#64); wp_steps
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

/-- Step `+1552 .. +1660` (`Block 426`): encodes `ch.nextRoot` (`tag = 4`, `0x22#8`). -/
theorem step_encodeToVec_chain_nextRoot_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 4#32 ch.nextRoot).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1552#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1660#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 4#32 ch.nextRoot) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x22#8 hlt_tag hcap hptr
    rw [h112, h104] at hpack_tag
    refine step_etv_encode_varint_call_prog A hvarint
      (BitVec.ofNat 64 ch.nextRoot.length) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1612#64) (bs ++ [0x22#8])
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).ρ "memcpy"); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_nr_toNat : (BitVec.ofNat 64 ch.nextRoot.length).toNat = ch.nextRoot.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_etv_memcpy_call_prog hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.nextRoot.ptr sp ((blkPl_426).base + 1652#64) ch.nextRoot
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1660#64); wp_steps
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
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1660#64); wp_steps
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

/-- Step `+1660 .. +1712` (`Block 426`): encodes `ch.sendEpoch` (`tag = 5`, `0x28#8`). -/
theorem step_encodeToVec_chain_sendEpoch_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeUint64Field 5#32 ch.sendEpoch).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1660#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1712#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeUint64Field 5#32 ch.sendEpoch) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x28#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call_prog A hvarint
      ch.sendEpoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 1712#64)
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
  · apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1712#64); wp_steps
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

/-- Step `+1712 .. +1740` (`Block 426`): encodes `ch.params` (`tag = 6#32`). -/
theorem step_encodeToVec_chain_params_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1712#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A g (a + 48#64) ch ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1740#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chainPBPinnedAt A g (a + 48#64) ch ∗
          vecU8At A (sp - 120#64) cap ptr
            (bs ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have h112_a : a + 48#64 + 0x40#64 = a + 112#64 := by bv_omega
  have h116_a : (a + 112#64) + 4#64 = a + 116#64 := by bv_omega
  have h120_a : (a + 116#64) + 4#64 = a + 120#64 := by bv_omega
  dsimp only [chainPBPinnedAt]; rw [h112_a]
  cases hcp : ch.params with
  | none =>
    dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1740#64); wp_steps
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
    apply SepWPp.of_sepWP_cs (mid := lsmpl.base 313); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine step_etv_encode_chainParams_call_prog A hcp_call
      6#32 cp (sp - 120#64) cap ptr sp ((blkPl_426).base + 1740#64) bs
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
