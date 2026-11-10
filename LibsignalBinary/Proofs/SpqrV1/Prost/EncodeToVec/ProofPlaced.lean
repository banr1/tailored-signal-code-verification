/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlaced
import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Relocatable `[LibsignalPlacement]` Phase 2d & Master Composition for `PqRatchetState::encode_to_vec` (`Block 426`)

Defines `StepInnerStateAt1880Placed`, proves `step_encodeToVec_phase2d_placed` (`+1740 .. +1808`)
and the 4 `V1StateChunked1Placed` variant bridges, and composes Phases 1–2d into
`pqRatchetStateEncodeToVec_gen_placed_ok` and `.rodata`-explicit / `LibsignalRoLoaded` `subroutine_ok` wrappers.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-- Execute the `.rodata` half-word (`↦₁₆ᵣ`) jump table dispatch at `+1880 .. +1896` (`Block 426`)
from `(blkPl_426).base + 1880#64` to `(blkPl_426).base + off`. -/
macro "step_etv_jump16_to_placed " off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    generalize _hro : (blkPl_426).ρ etvJumpTableRoSym = roBase at *
    dsimp only [encodeToVecJumpTableBytesAt]
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    subst _hro))

/-- Unified stepping obligation from `(blkPl_426).base + 1880#64` (jump-table dispatch)
to `(blkPl_426).base + 1808#64` (epilogue) for a `V1State.InnerState` value `is`. -/
def StepInnerStateAt1880Placed [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) (s0 : State) (is : V1State.InnerState) : Prop :=
  ∀ (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (bs : List (BitVec 8)),
    v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 →
    bs.length + (V1State.InnerState.encode is).length ≤ cap.toNat →
    sp &&& 15#64 = 0#64 →
    ∀ {R : SepProp} {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop},
      s.pc = (blkPl_426).base + 1880#64 →
      s.status = .Running →
      s.sp = sp - 144#64 →
      s.trace = s0.trace →
      s.readReg64 .x8 =
        (if BitVec.ult (v1StateInnerCap g is ^^^ 0x8000000000000000#64) 11#64
         then v1StateInnerCap g is ^^^ 0x8000000000000000#64 else 7#64) →
      s.readReg64 .x9 = (blkPl_426).ρ etvJumpTableRoSym →
      s.readReg64 .x20 = a →
      s.readReg64 .x21 = a + 128#64 →
      s.readReg64 .x28 = v1StateInnerCap g is →
      StepInv s0 s →
      P = (v1StateInnerPBPinnedAt A g (a + 128#64) is ∗
        ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
          ((v1StateInnerPBPinnedAt A g (a + 128#64) is ∗
            ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
            vecU8At A (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode is) ∗ A.pool ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))

theorem step_encodeToVec_v1_ct1Sampled_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 : State}
    (hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 407)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Sampled) :
    StepInnerStateAt1880Placed resStack A H s0 (.ct1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  simp only [v1StateInnerPBPinnedAt, v1StateInnerCap] at hx8 hx28 ⊢
  refine sepWPp_extract_pure
    (((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false)
    (fun R' hm => by
      dsimp only [chunkedCt1SampledPBPinnedAt] at hm
      rw [optCt1SentPBPinnedAt_eq A g.b.gCt1Sampled.uc (a + 128#64) v.uc] at hm
      have hm' : s.mem ⊨ optCt1SentRest A g.b.gCt1Sampled.uc (a + 128#64) v.uc ∗
          (((a + 128#64) ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
           optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64 + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 128#64 + 184#64) v.receivingEk ∗
           ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact (optCt1SentRest_disc_bounds hm').2.2)
    fun hult => ?_
  simp only [hult, Bool.false_eq_true, ↓reduceIte] at hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2620 s 7#64 hx8
  intro hinv1
  refine step_encodeToVec_v1_ct1Sampled_placed hres A H
    hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec
    a sp cap ptr g.b.gCt1Sampled v bs hv_len hfit halign
    (F := encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ekSentCt1Received_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.EkSentCt1Received) :
    StepInnerStateAt1880Placed resStack A H s0 (.ekSentCt1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 4#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 1976 s 4#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ekSentCt1Received_placed hres A H
    hekLen hpolyDecLen hvarint hekEnc hpolyDec
    a sp cap ptr g.a.gEkSentCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000004#64) ∗
      memRegion (a + 128#64 + 152#64) 72 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct1Acknowledged_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 : State}
    (hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepInnerStateAt1880Placed resStack A H s0 (.ct1Acknowledged v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 9#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2076 s 9#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264]
  refine step_encodeToVec_v1_ct1Acknowledged_placed hres A H
    hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec
    a sp cap ptr g.b.gCt1Acknowledged v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (a + 128#64 + 176#64) 48 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct1Received_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct1Received) :
    StepInnerStateAt1880Placed resStack A H s0 (.ct1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 3#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2520 s 3#64 hx8
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ct1Received_placed hres A H
    hekLen hpolyEncLen hvarint hekEnc hpolyEnc
    a sp cap ptr g.a.gCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000003#64) ∗
      memRegion (a + 128#64 + 168#64) 56 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

/-! ## Master Phase 2d Theorem (`+1740 .. +1808`, `Block 426`) -/

/-- Step `+1740 .. +1808` (`Block 426`): encodes `st.inner`
into `vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr`,
producing `PqRatchetState.encodeRaw st`. -/
theorem step_encodeToVec_phase2d_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    (roV1 : BitVec 64)
    {s0 s : State}
    (hv1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hInnerAt1880 : ∀ is : V1State.InnerState, StepInnerStateAt1880Placed resStack A H s0 is)
    (sret a sp ptr : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
          Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = sret → sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
    Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hin : st.inner with
  | none =>
    rw [hin] at hx28
    refine step_encodeToVec_inner_none_placed H sp hpc hrun hsp htr hx28 hinv0 ?_
    intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
    rw [hx27] at hx27m; rw [hfp] at hfpm
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
    have henc : PqRatchetState.encodeRaw st = bs0 := by
      unfold PqRatchetState.encodeRaw
      rw [hin]; simp only [bs0, List.append_nil]
    rw [henc]
    exact Entails.of_eq (by ac_rfl)
  | some inner =>
    cases inner with
    | v1 v1 =>
      rw [hin] at hx28
      have ⟨hv1_len64, _, _⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
      have hv1_all : bs0.length + (PqRatchetState.Inner.encode (.v1 v1)).length ≤ cap.toNat := by
        rw [hcap_toNat, ← pqRatchetStatePBEncodedLen_eq_proto st]
        unfold PqRatchetState.encodeRaw
        rw [hin]; simp only [bs0, List.length_append]
        exact Nat.le_refl _
      rw [encodeInner_v1_eq v1] at hv1_all
      simp only [List.length_append, List.length_singleton,
        show (V1State.encodeRaw v1).length = v1StatePBEncodedLen v1 from v1StatePBEncodedLen_eq_proto v1] at hv1_all
      let F_outer : SepProp :=
        optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
          optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
          ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ F
      refine step_encodeToVec_inner_some_hdr_placed hres A H hv1Len hvarint
        a sp cap ptr g.inner v1 bs0 hv1_len64 (by omega) halign
        (F := F_outer)
        hpc hrun hsp htr hx20 hx21 hx28 hinv0
        (by unfold pqRatchetStatePBPinnedAt; rw [hin]; dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs0, F_outer]; ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_20 hs1_21 hs1_27 hs1_28 hs1_fp hinv_s1
      rw [hx27] at hs1_27; rw [hfp] at hs1_fp
      let bs_hdr := (bs0 ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))
      cases his : v1.innerState with
      | none =>
        have hx28_none : s1.readReg64 .x28 = noneCap2 := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine step_encodeToVec_inner_v1_none_placed H sp hpcs1 hruns1 hsps1 htrs1
          hx28_none hinv_s1 ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs1_27] at hm27; rw [hs1_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [List.append_nil, bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs_hdr, F_outer]
        exact Entails.of_eq (by ac_rfl)
      | some is =>
        have hx28_some : s1.readReg64 .x28 = v1StateInnerCap g.inner is := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine sepWPp_extract_pure
          ((v1StateInnerCap g.inner is + 2#64 == 0#64) = false ∧
            (v1StateInnerCap g.inner is + 2#64 != 0#64) = true)
          (fun R' hm => by
            dsimp only [v1StatePBPinnedAt] at hm
            rw [his] at hm
            dsimp only at hm
            have hm' : s1.mem ⊨ v1StateInnerPBPinnedAt A g.inner (a + 128#64) is ∗
                ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
                 vecU8At A (sp - 120#64) cap ptr bs_hdr ∗ A.pool ∗
                 stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F_outer ∗ R') := by
              convert hm using 1; dsimp only [bs_hdr]; ac_rfl
            exact v1StateInnerCap_add_two_bounds hm')
          fun ⟨hw_beq2, hw_bne2⟩ => ?_
        refine step_encodeToVec_inner_to_1880_placed H rfl sp (v1StateInnerCap g.inner is)
          hw_beq2 hw_bne2 hpcs1 hruns1 hsps1 htrs1 hx28_some hinv_s1 ?_
        intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_27 hs2_28 hs2_fp hinv_s2
        rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_27] at hs2_27; rw [hs1_fp] at hs2_fp
        have hv_len64' : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 := by
          have : v1 = ⟨some is⟩ := by cases v1; subst his; rfl
          rw [← this]; exact hv1_len64
        have his_fit : bs_hdr.length + (V1State.InnerState.encode is).length ≤ cap.toNat := by
          have hlen_is : (V1State.InnerState.encode is).length = v1StatePBEncodedLen v1 := by
            rw [← v1StatePBEncodedLen_eq_proto v1]
            dsimp only [V1State.encodedLen, V1State.encodeRaw]; rw [his]
          simp only [bs_hdr, List.length_append, List.length_singleton, hlen_is]
          omega
        refine hInnerAt1880 is a sp cap ptr g.inner bs_hdr hv_len64' his_fit halign
          hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_28 hinv_s2
          (F := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
          (by dsimp only [v1StatePBPinnedAt, bs_hdr, F_outer]; rw [his]; dsimp only; ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs2_27] at hm27; rw [hs2_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr ++ V1State.InnerState.encode is := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, v1StatePBPinnedAt, cap]
        rw [his]
        exact Entails.of_eq (by ac_rfl)

/-! ## Master End-to-End Composition (`Block 426`) -/

/-- `.rodata`-explicit pinned `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`) under `[LibsignalPlacement]`. -/
def pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    (A : RustAlloc) : Spec PqRatchetStateEncodeToVecPinnedGhost where
  pre x s0 :=
    ⌜s0.readReg64 .x0 = x.sret ∧
     s0.readReg64 .x1 = x.a ∧
     (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
    memRegion x.sret 24 ∗
    pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
    (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
    ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
    A.pool ∗
    stackAt s0.sp (encodeToVecStackOf resStack)
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
    pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
    (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
    ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
    A.pool ∗
    stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic _ s0 sf := encodeToVecOnPanic s0 sf

/-- `.rodata`-explicit existential `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`) under `[LibsignalPlacement]`. -/
def pqRatchetStateEncodeToVecRoPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    (A : RustAlloc) : Spec PqRatchetStateEncodeToVecGhost where
  pre x s0 :=
    ⌜s0.readReg64 .x0 = x.sret ∧
     s0.readReg64 .x1 = x.a ∧
     (PqRatchetState.encodeRaw x.st).length < 2 ^ 63⌝ ∗
    memRegion x.sret 24 ∗
    pqRatchetStatePBAt A x.a x.st ∗
    (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
    ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
    A.pool ∗
    stackAt s0.sp (encodeToVecStackOf resStack)
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
    pqRatchetStatePBAt A x.a x.st ∗
    (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
    ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
    A.pool ∗
    stackAt s0.sp (encodeToVecStackOf resStack)
  onPanic _ s0 sf := encodeToVecOnPanic s0 sf

/-- General end-to-end `SepWPp` execution of `PqRatchetState::encode_to_vec` (`Block 426`),
chaining Phase 1, Phase 2a, Phase 2b, Phase 2c, Phase 2d, and Epilogue. -/
theorem pqRatchetStateEncodeToVec_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {A : RustAlloc} {H : String → Option (State → State)}
    {x : PqRatchetStateEncodeToVecPinnedGhost} {R : SepProp} {s0 : State}
    (hChainLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hV1StateLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2))))
    (hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (withStepInv s0 (rustAllocStackSpecOf resStack A)))
    (hhandle : ((blkPC_426).rebase (blkPl_426).base H).externAt?
      ((blkPl_426).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hInnerAt1880 : ∀ is : V1State.InnerState, StepInnerStateAt1880Placed resStack A H s0 is)
    (hpc : s0.pc = (blkPl_426).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) (s0.readReg64 .lr) s0 P
        (fun sf Q =>
          ((sf.mem ⊨ Q ∗ R) →
            StepInv s0 sf ∧
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hpre_pure := hpre; dsimp only [pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hlen_raw⟩, hpre_mem⟩ := hpre_pure
  have hlen : pqRatchetStatePBEncodedLen x.st < 2 ^ 63 := by
    rw [← pqRatchetStatePBEncodedLen_eq_proto x.st]; exact hlen_raw
  have hpre_rewritten : s0.mem ⊨
      ((pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt s0.sp (encodeToVecStackOf resStack)) ∗
       (memRegion x.sret 24 ∗ ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  refine step_encodeToVec_phase1_placed hres A H (lsρ v1StateJtSymLocal2) hChainLen hV1StateLen
    x.sret x.a s0.sp x.g x.st hlen halign
    hpc hrun rfl hx0 hx1 rfl ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
  refine step_encodeToVec_alloc_placed A H hshim halloc hhandle
    x.sret x.a s0.sp v0 v1 v2 v3 v4 v5 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
    (by ac_rfl) ?_
  intro s2 ptr hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2 hfp2 hinv2
  refine step_encodeToVec_versionNeg_placed A H hvarint hmemcpy hcp_call
    x.sret x.a s0.sp ptr v0 v1 v2 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2 hfp2 hinv2
    rfl ?_
  intro s3 w1 w2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
  refine step_encodeToVec_chain_placed hres A H hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0 ∗ memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
  refine step_encodeToVec_phase2d_placed hres A H (lsρ v1StateJtSymLocal2) hV1StateLen hvarint hInnerAt1880
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
    (by ac_rfl) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx27_5 hfp5 hinv5
  refine step_encodeToVec_epilogue_placed hres A H
    x.sret s0.sp (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen x.st)) ptr v0 w1 w2
    (PqRatchetState.encodeRaw x.st)
    (F := pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)
    hpc5 hrun5 hsp5 halign htr5 hx27_5 hinv5
    (by ac_rfl) ?_
  intro sf _ _ hspf htrf hcsf hinvf
  refine ⟨fun hm => ⟨hinvf, ?_⟩, hspf, hcsf⟩
  dsimp only [pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm using 1; ac_rfl

/-! ## `.rodata` Jump-Table Facts and Top-Level `subroutine_ok` Wrappers -/

theorem etvJumpTableBytes_lsro_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ P := by
  have h : m ⊨ (lsmpl.ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ P :=
    lsro_slice_intro hro (sym := etvJumpTableRoSym) (off := 0)
      (by simp) (by decide +kernel) hP
  have hρ : (blkPl_426).ρ etvJumpTableRoSym = lsmpl.ρ etvJumpTableRoSym :=
    ls_resolve_data (by decide +kernel)
  rwa [hρ]

abbrev withLsRoLoaded {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPlacedSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.sret, x.a, g, x.st⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPlacedSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem pqRatchetStateEncodeToVec_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecOf resStack A)))) :
    subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecSpecOf resStack A))) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.sret, x.a, g, x.st⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem etv_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q sf P_f → Q' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)`,
discharging the 4 `V1StateChunked1Placed` variants and taking the remaining 7 `StepInnerStateAt1880Placed`
variants plus the message-encode callee contracts as hypotheses. -/
theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A)))
    (hKeysUnsampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) :=
    etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0
  have hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStack A)) :=
    etv_epochEncodedLen_placed_ok (by decide) A ext s0 hcl0
  have hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 is := by
    intro is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 hcl0 v
    | keysSampled v => exact hKeysSampled s0 hcl0 v
    | headerSent v => exact hHeaderSent s0 hcl0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880_placed (by decide) A (Rust.withPanics ext)
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed (by decide) A (Rust.withPanics ext)
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 hcl0 v
    | headerReceived v => exact hHeaderReceived s0 hcl0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880_placed (by decide) A (Rust.withPanics ext)
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 hcl0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed (by decide) A (Rust.withPanics ext)
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 hcl0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A ext s0 hcl0)
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    (etv_handle_alloc_error_placed h_panic)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre hsp
  exact ⟨P, R, hP, etv_sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => (hq hm).2, hspf, hcsf⟩) hwp⟩

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_variants [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A)))
    (hKeysUnsampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A))`,
eliminating both `.rodata` jump-table atoms via `LibsignalRoLoaded lsmpl`. -/
theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A)))
    (hKeysUnsampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A))) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hpre_ro1 := v1StateJumpTableBytes_lsro_local2_intro hro0 hpre
  have hpre_ro2 := etvJumpTableBytes_lsro_intro hro0 hpre_ro1
  have hpre_ro : s0.mem ⊨
      (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStackX A).pre x s0 ∗ R := by
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf,
      pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf, lsρ] at hpre_ro2 ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_ro2
  have hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) :=
    etv_encodeVarint_exact_of_fit_placed (by decide)
      (etv_subroutine_ok_placed_of_lscl hcl0
        (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))
  have hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStackX A)) :=
    etv_epochEncodedLen_placed_ok (by decide) A ext s0 hcl0
  have hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 is := by
    intro is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 hcl0 v
    | keysSampled v => exact hKeysSampled s0 hcl0 v
    | headerSent v => exact hHeaderSent s0 hcl0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880_placed (by decide) A (Rust.withPanics ext)
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed (by decide) A (Rust.withPanics ext)
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 hcl0 v
    | headerReceived v => exact hHeaderReceived s0 hcl0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880_placed (by decide) A (Rust.withPanics ext)
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 hcl0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed (by decide) A (Rust.withPanics ext)
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 hcl0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A ext s0 hcl0)
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    (etv_handle_alloc_error_placed h_panic)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre_ro hsp
  refine ⟨P, R, hP, etv_sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩) hwp⟩
  obtain ⟨_, hpost_ro⟩ := hq hm
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf,
    pqRatchetStateEncodeToVecPinnedSpecOf] at hpost_ro ⊢
  have hpost_perm : sf.mem ⊨
      ((lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
       ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes)) ∗
      ((⌜sf.trace = s0.trace⌝ ∗
        vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        A.pool ∗ stackAt s0.sp (encodeToVecStackOf doReserveStackX)) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost_ro
  exact Satisfies.of_sep_right hpost_perm

theorem pqRatchetStateEncodeToVec_placed_ok_of_variants [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A)))
    (hKeysUnsampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ s0 : State, LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecSpecOf doReserveStackX A))) :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

end CryptoVerification.SpqrV1.Prost.EncodeToVec
