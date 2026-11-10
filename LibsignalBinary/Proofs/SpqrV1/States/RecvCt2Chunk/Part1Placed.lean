/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable `None` Return Path

Relocatable `[LibsignalPlacement]` proof of the `None` (`StillReceiving`) branch (`+112 .. +200`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 800000 in
theorem recv_ct2_chunk_none_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (s0 st : State) (R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (_hsort : PolyDecoderStrictSorted receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok none)
    (hpc : st.pc = (blkPl_350).base + 152#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = x.selfA) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvCt2RoPlacedAt ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        ekSentCt1ReceivedUcAt A x.selfA x.self.uc ∗
        memRegion (x.selfA + 104#64) 400 ∗
        cells (s0.sp - 2496#64) 9 ∗
        polyDecoderAt A ((s0.sp - 2496#64) + 0x48#64) receivingCt2 ∗
        optKeyBytesAt A ((s0.sp - 2496#64) + 0x1d8#64) none ∗
        memRegion ((s0.sp - 2496#64) + 0x280#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗
        stackAt (s0.sp - 2496#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have hmc_raw := hA.memcpy_region_at_block
    (prog := lsProg_350 (Rust.withPanics ext)) polyDecodedMessageStackX
  have h_mc_dec := (polyDecoderSplit A receivingCt2).memcpy_withStack_lscro_ok
    (pl := lsmpl) (by decide) polyDecodedMessageStackX hmc_raw
  have h_mc_st :=
    (ekSentCt1ReceivedSplit A { uc := x.self.uc, receiving_ct2 := receivingCt2 }).memcpy_withStack_lscro_ok
      (pl := lsmpl) (by decide) polyDecodedMessageStackX hmc_raw
  clear hA hmc_raw
  simp only [lsProg_350] at h_mc_dec h_mc_st ⊢
  refine SepWPp.rw_pre (by rw [memRegion_504_at_fsp_280_split (s0.sp - 2496#64)]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvCt2 h_mc_dec
    ((s0.sp - 2496#64) + 0x2e8#64, (s0.sp - 2496#64) + 0x48#64) hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
  rcases hpost1 with ⟨htr1, _⟩
  refine SepWPp.of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf ?_
  refine SepWP.fold (ekSentCt1ReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (ekSentCt1ReceivedAt_fsp_280_entails A s0.sp x.self.uc receivingCt2 _ _ _ _ _)
    (by sep_focus) ?_
  refine SepWP.fold
    (ekSentCt1ReceivedCells_entails_memRegion_504 x.selfA _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvCt2 h_mc_st (x.outA, s0.sp - 1856#64) hinv2
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost2 => ?_
  rcases hpost2 with ⟨htr2, _⟩
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold
    (optKeyBytesAt_none_entails_memRegion_24 A (s0.sp - 2024#64))
    (by sep_focus) ?_
  unfold savedRegsAt
  wp_steps
  have hfold_saved :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  have hfold_active :
      cells (s0.sp - 2496#64) 9 ∗
        memRegion (s0.sp - 2424#64) 400 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 1856#64) 504 ∗
        someBranchFrameAt (s0.sp - 2496#64) ⊢
      activeFrameRegionsAt (s0.sp - 2496#64) := by
    unfold activeFrameRegionsAt
    have ha1 : (s0.sp - 2496#64) + 0x48#64 = s0.sp - 2424#64 := by bv_omega
    have ha2 : (s0.sp - 2496#64) + 0x1d8#64 = s0.sp - 2024#64 := by bv_omega
    have ha3 : (s0.sp - 2496#64) + 0x280#64 = s0.sp - 1856#64 := by bv_omega
    rw [ha1, ha2, ha3]
    exact Entails.refl _
  refine SepWP.fold hfold_active (by sep_focus) ?_
  have hstack_eq : stackAt sf.sp polyDecodedMessageStackX ⊢
      stackAt (s0.sp - 2496#64) polyDecodedMessageStackX := by
    rw [hsp_sf, hsp]; exact Entails.refl _
  refine SepWP.fold hstack_eq (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvCt2Chunk s0) (by sep_focus) ?_
  have hres := recv_ct2_chunk_eq_stillReceiving (K := K) x.self x.epoch x.chunk receivingCt2
    hepoch hadd hdec
  unfold recvCt2PlacedPostQ
  dsimp only [recvCt2ChunkPlacedSpec]
  rw [hres]
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt]
  wp_done

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
