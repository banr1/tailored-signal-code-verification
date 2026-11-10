/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridge

/-!
# `<PolyDecoder as Decoder>::decoded_message` & `add_chunk` Relocatable Bridges

Relocatable `[LibsignalPlacement]` bridges lifting `decodedMessagePlacedSpec` (Block `418`) to
`polyDecoderDecodedMessagePlacedSpec` and `RecvCt2Chunk.PolyDecodedMessagePlacedOkX`, and lifting
`addChunkSpec` (Block `419`) to `addChunkSpecX` by framing the unused bottom stack region.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (PolyDecodedMessageCall polyDecodedMessageStackX
   polyDecodedMessagePlacedSpec PolyDecodedMessagePlacedOkX)

private theorem optVecU8Of_eq_optKeyBytesAt' (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

private theorem satisfies_anyHeap_frame_cl {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- Lift `withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A)` to
    `withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)`. -/
theorem polyDecoderDecodedMessage_placed_cro_of_decodedMessage [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hdm : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre_pts : s0.mem ⊨
      (⌜s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
        memRegion x.outA 24 ∗
        (⌜x.dec.pts.length = 16⌝ ∗ polyDecoderAt A x.decA x.dec) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗
        stackAt s0.sp polyDecoderDecodedMessageStack) ∗ R := by
    refine Satisfies.mono ?_ hpre0
    dsimp only [polyDecoderDecodedMessagePlacedSpec]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (polyDecoderAt_dup_pts_len A x.decA x.dec))))
  have hpts_sort :
      x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec ∧
        spqrPolyApi.decoded_message x.dec = .ok x.outMsg := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16⌝ ∗
        ⌜s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
        (memRegion x.outA 24 ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool ∗
          stackAt s0.sp polyDecoderDecodedMessageStack ∗ R) := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_pts
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨hlen, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2.1, h2.1.2.2.2⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2.1
  have hout_eq : x.outMsg = decodedMessageTotal x.dec := by
    have hdm_ok := hpts_sort.2.2
    dsimp only [spqrPolyApi] at hdm_ok
    rw [hdec_eq] at hdm_ok
    exact (Except.ok.inj hdm_ok).symm
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A)).pre x' s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec, polyDecoderDecodedMessagePlacedSpec,
      x', Poly.vecHeaderBytes, polyDecoderDecodedMessageStack, decodedMessageStack] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
  refine subroutine_ok.mono_outcome hdm x' R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec, x'] at hpost
    dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec, polyDecoderDecodedMessageStack]
    rw [hout_eq, ← optVecU8Of_eq_optVecU8At]
    exact hpost
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- Lift `withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A)` on Block `418` to
    `RecvCt2Chunk.PolyDecodedMessagePlacedOkX A ext`. -/
theorem polyDecodedMessagePlacedOkX_of_decodedMessage [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdm : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (blkPl_418).base (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A))) :
    PolyDecodedMessagePlacedOkX A ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre_pts : s0.mem ⊨
      (⌜s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec⌝ ∗
        memRegion x.outA vecHeaderBytes ∗
        (⌜x.dec.pts.length = 16⌝ ∗ polyDecoderAt A x.decA x.dec) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗
        stackAt s0.sp polyDecodedMessageStackX) ∗ R := by
    refine Satisfies.mono ?_ hpre0
    dsimp only [polyDecodedMessagePlacedSpec]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (polyDecoderAt_dup_pts_len A x.decA x.dec))))
  have hpts_sort : x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16⌝ ∗
        ⌜s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec⌝ ∗
        (memRegion x.outA vecHeaderBytes ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool ∗
          stackAt s0.sp polyDecodedMessageStackX ∗ R) := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_pts
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨hlen, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (decodedMessagePlacedSpec A)).pre x' s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec, polyDecodedMessagePlacedSpec, x'] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcro, hpre0⟩
  refine subroutine_ok.mono_outcome hdm x' R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, decodedMessagePlacedSpec, x'] at hpost
    dsimp only [withLsCodeRoLoaded, polyDecodedMessagePlacedSpec]
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left ?_
    rw [optVecU8Of_eq_optKeyBytesAt']
    refine Entails.pure_left fun htr => ?_
    refine Entails.trans (Entails.of_eq (show
        optKeyBytesAt A x.outA (decodedMessageTotal x.dec) ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp decodedMessageStack =
        optKeyBytesAt A x.outA (decodedMessageTotal x.dec) ∗
          (polyDecoderAt A x.decA x.dec ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt s0.sp polyDecodedMessageStackX) by
        ac_rfl)) ?_
    refine sepConj_mono_left ?_
    exact Entails.sepExists_right (decodedMessageTotal x.dec)
      (Entails.pure_right ⟨hdec_eq, htr⟩ (Entails.refl _))
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- Lift `subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpec A))` to
    `subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpecX A))` by framing the
    unused bottom stack region. -/
theorem addChunkSpecX_cl_of_addChunkSpec_cl [LibsignalPlacement]
    {prog : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpec A))) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl (addChunkSpecX A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  have hle : addChunkStack ≤ addChunkStackX := by decide
  have hsplit : stackAt s0.sp addChunkStackX =
      memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
        (addChunkStackX - addChunkStack) ∗
        stackAt s0.sp addChunkStack := by
    have h1 := stackAt_split_bottom s0.sp addChunkStack
      (addChunkStackX - addChunkStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
      (addChunkStackX - addChunkStack) ∗ R
  have hpre0' : s0.mem ⊨ (addChunkSpec A).pre x s0 ∗ R' := by
    dsimp only [addChunkSpecX, addChunkSpec, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    ac_nf at hpre0 ⊢
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (addChunkSpec A)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre0'⟩
  refine subroutine_ok.mono_outcome h x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, addChunkSpecX, addChunkSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame_cl hpost⟩)
  · dsimp only [withLsCodeLoaded, addChunkSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SpqrV1.States.Leaves
