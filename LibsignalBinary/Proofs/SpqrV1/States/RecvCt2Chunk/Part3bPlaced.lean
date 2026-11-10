/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3Placed
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable `Ok(Done)` Write-Out

Relocatable `[LibsignalPlacement]` proof of the two-part `Ok(Done)` write-out (`+1520 .. +1708`
and `+1708 .. +1848`), folding `x.outA` into `ekSentCt1ReceivedRecvChunkResultAt`.
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
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `Ok(Done)` Write-Out Part 2 (`+1708 .. +1848` -> `+1188`) -/

set_option maxHeartbeats 1600000 in
/-- `+1708 .. +1848`: writes `epoch + 1`, all 16 `SortedSetPt.new` slots + tail of
`polyDecoderNew96`, `b0 rootKey.ptr`, and `epochSecret` to `x.outA`, folds `outA` into
`ekSentCt1ReceivedRecvChunkResultAt` and the stack into `someBranchFrameAt`, and branches to
`+1188` (`recv_ct2_chunk_epilogue_placed_wpp`). -/
theorem recv_ct2_chunk_ok_done_write_out_part2_placed_wpp [LibsignalPlacement] {K : MlKem}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (cap_ct2 ptr_ct2 ptr_sec w40_0 w40_1 : BitVec 64) (ob16 : BitVec 8)
    (auth' : Authenticator) (g_auth' : AuthenticatorGhost) (ss : Bytes)
    (s0 st : State) (R : SepProp)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hss_len : ss.length = 32) (hptr_sec_ne : ptr_sec ≠ 0#64)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk =
      .ok (.done ({ uc := { epoch := x.epoch + 1#64, auth := auth' },
                     receiving_hdr := polyDecoderNew96 },
                   { epoch := x.epoch, secret := ss })))
    (hpc : st.pc = (blkPl_350).base + 1708#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx8 : st.readReg64 .x8 = x.epoch + 1#64)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx24 : st.readReg64 .x24 = cap_ct2)
    (hx26 : st.readReg64 .x26 = ptr_sec)
    (hx28 : st.readReg64 .x28 = (b0 g_auth'.rootKey.ptr).zeroExtend 64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        (x.outA ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗
        ((x.outA + 8#64) ↦₆₄ g_auth'.rootKey.cap) ∗
        ((x.outA + 16#64) ↦₈ ob16) ∗
        ((x.outA + 17#64) ↦₆₄ shiftWord8 g_auth'.rootKey.ptr 32#64) ∗
        low7At (x.outA + 25#64) (shiftWord8 32#64 g_auth'.macKey.cap) ∗
        ((x.outA + 32#64) ↦₆₄ g_auth'.macKey.cap) ∗
        vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((x.outA + 40#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((x.outA + 48#64) ↦₆₄ 32#64) ∗
        vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey ∗
        memRegion (x.outA + 56#64) 24 ∗
        ((x.outA + 80#64) ↦₆₄ 0#64) ∗ ((x.outA + 88#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 96#64) 8 ∗
        ((x.outA + 104#64) ↦₆₄ 0#64) ∗ ((x.outA + 112#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 120#64) 8 ∗
        ((x.outA + 128#64) ↦₆₄ 0#64) ∗ ((x.outA + 136#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 144#64) 8 ∗
        ((x.outA + 152#64) ↦₆₄ 0#64) ∗ ((x.outA + 160#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 168#64) 8 ∗
        ((x.outA + 176#64) ↦₆₄ 0#64) ∗ ((x.outA + 184#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 192#64) 8 ∗
        ((x.outA + 200#64) ↦₆₄ 0#64) ∗ ((x.outA + 208#64) ↦₆₄ 0#64) ∗
        memRegion (x.outA + 216#64) 288 ∗
        (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1 ∗
        memRegion (s0.sp - 2000#64) 80 ∗
        ((s0.sp - 1920#64) ↦₆₄ w40_0) ∗ ((s0.sp - 1912#64) ↦₆₄ w40_1) ∗
        memRegion (s0.sp - 1904#64) 48 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1328#64) 48 ∗
        ((s0.sp - 1280#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1272#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 1264#64) 8 ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 152#64) 32 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 1856#64) 504 ∗ polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        cells (s0.sp - 2496#64) 9 ∗ memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have hep := @recv_ct2_chunk_epilogue_placed_wpp _ K F A ext hA x receivingCt2 cap_ct2 ptr_ct2 s0
  dsimp only [ct2DeallocAt]
  refine SepWPp.pure_left_focus (cap_ct2 ≠ 0#64 ∧ cap_ct2.toNat < 2 ^ 63 ∧ ptr_ct2 ≠ 0#64)
    (by sep_focus) fun ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ => ?_
  have hcap_ct2_beq : (cap_ct2 == 0#64) = false := beq_false_of_ne hcap_ct2_ne
  have hfold_ct2 :
      memRegion ptr_ct2 cap_ct2.toNat ∗ A.live ptr_ct2 cap_ct2.toNat 1 ⊢
        ct2DeallocAt A cap_ct2 ptr_ct2 := by
    dsimp only [ct2DeallocAt]
    exact Entails.pure_right ⟨hcap_ct2_ne, hmax_ct2, hptr_ct2_ne⟩ (Entails.refl _)
  refine SepWPp.fold hfold_ct2 (by sep_focus) ?_
  refine SepWPp.fold (memRegion_24_eq_3cells (x.outA + 56#64) (x.outA + 64#64) (x.outA + 72#64)
    (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  sep_elim_exists; rename_i w56 w64 w72
  refine SepWPp.fold (memRegion_8_eq_cell (x.outA + 96#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i w96
  refine SepWPp.fold (memRegion_8_eq_cell (x.outA + 120#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i w120
  refine SepWPp.fold (memRegion_8_eq_cell (x.outA + 144#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i w144
  refine SepWPp.fold (memRegion_8_eq_cell (x.outA + 168#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i w168
  refine SepWPp.fold (memRegion_8_eq_cell (x.outA + 192#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i w192
  refine SepWPp.fold (memRegion_split_8cells
    (x.outA + 216#64) (x.outA + 224#64) (x.outA + 232#64) (x.outA + 240#64)
    (x.outA + 248#64) (x.outA + 256#64) (x.outA + 264#64) (x.outA + 272#64)
    (x.outA + 280#64) 288 224 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w216 w224 w232 w240 w248 w256 w264 w272
  refine SepWPp.fold (memRegion_split_8cells
    (x.outA + 280#64) (x.outA + 288#64) (x.outA + 296#64) (x.outA + 304#64)
    (x.outA + 312#64) (x.outA + 320#64) (x.outA + 328#64) (x.outA + 336#64)
    (x.outA + 344#64) 224 160 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w280 w288 w296 w304 w312 w320 w328 w336
  refine SepWPp.fold (memRegion_split_8cells
    (x.outA + 344#64) (x.outA + 352#64) (x.outA + 360#64) (x.outA + 368#64)
    (x.outA + 376#64) (x.outA + 384#64) (x.outA + 392#64) (x.outA + 400#64)
    (x.outA + 408#64) 160 96 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w344 w352 w360 w368 w376 w384 w392 w400
  refine SepWPp.fold (memRegion_split_4cells
    (x.outA + 408#64) (x.outA + 416#64) (x.outA + 424#64) (x.outA + 432#64)
    (x.outA + 440#64) 96 64 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w408 w416 w424 w432
  refine SepWPp.fold (memRegion_split_2cells
    (x.outA + 440#64) (x.outA + 448#64) (x.outA + 456#64) 64 48 rfl
    (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w440 w448
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 456#64) (n := 8) (k := 40) (b' := x.outA + 464#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_8_split_1_7
    (x.outA + 456#64) (x.outA + 457#64) (by bv_omega)) (by sep_focus) ?_
  sep_elim_exists; rename_i ob456
  refine SepWPp.fold (memRegion_split_4cells
    (x.outA + 464#64) (x.outA + 472#64) (x.outA + 480#64) (x.outA + 488#64)
    (x.outA + 496#64) 40 8 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w464 w472 w480 w488
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx8 hx19 hx21 hx22 hx24 hx26 hx28
  clear hA
  simp only [lsProg_350] at hep ⊢
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 1188#64) hinv ?_
  wp_steps
  have h16_rejoin := rejoin_2words_from_shifted (x.outA + 16#64) (x.outA + 17#64)
    (x.outA + 24#64) (x.outA + 25#64) g_auth'.rootKey.ptr 32#64 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
  refine SepWP.fold h16_rejoin (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 64#64 72#64 80#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 88#64 96#64 104#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 112#64 120#64 128#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 136#64 144#64 152#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 160#64 168#64 176#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 184#64 192#64 200#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 208#64 216#64 224#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 232#64 240#64 248#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 256#64 264#64 272#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 280#64 288#64 296#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 304#64 312#64 320#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 328#64 336#64 344#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 352#64 360#64 368#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 376#64 384#64 392#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 400#64 408#64 416#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (sortedSetPtOf_new_at A x.outA 424#64 432#64 440#64 (by bv_omega) (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (polyDecoderNew96_of_slots A x.outA) (by sep_focus) ?_
  have hout := rejoin_outA_ok_done A (F := F) x.outA x.epoch auth' g_auth' ss ptr_sec
    hrk_len hmk_len hss_len hptr_sec_ne
  rw [← hres] at hout
  refine SepWP.fold hout (by sep_focus) ?_
  refine SepWP.fold (rejoin_someBranchFrameAt_part2a s0.sp 0#64 0#64 0#64 0#64) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  refine SepWPp.rw_pre (by ac_rfl)
    (hep _ R (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv1
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

/-! ## `Ok(Done)` Write-Out Part 1 (`+1520 .. +1708`) -/

set_option maxHeartbeats 1600000 in
/-- `+1520 .. +1708`: writes the `Ok(Done)` discriminant (`-1`), `auth'` Vec headers,
and the first six 16-byte zero pairs to `x.outA`, folds the stack temporaries, and hands off
to `recv_ct2_chunk_ok_done_write_out_part2_placed_wpp` (`+1708 .. +1848`). -/
theorem recv_ct2_chunk_ok_done_write_out_placed_wpp [LibsignalPlacement] {K : MlKem}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc A ext)
    (x : RecvCt2ChunkGhost F) (receivingCt2 : PolyDecoder)
    (cap_ct2 ptr_ct2 ptr_sec w_sp1 w_sp3 : BitVec 64) (b_pad : BitVec 8)
    (auth' : Authenticator) (g_auth' : AuthenticatorGhost) (ss : Bytes)
    (s0 st : State) (R : SepProp)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hss_len : ss.length = 32) (hptr_sec_ne : ptr_sec ≠ 0#64)
    (hcap_rk_lt : g_auth'.rootKey.cap.toNat < 2 ^ 63)
    (hres : x.self.recv_ct2_chunk K x.epoch x.chunk =
      .ok (.done ({ uc := { epoch := x.epoch + 1#64, auth := auth' },
                     receiving_hdr := polyDecoderNew96 },
                   { epoch := x.epoch, secret := ss })))
    (hpc : st.pc = (blkPl_350).base + 1520#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64)
    (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx24 : st.readReg64 .x24 = cap_ct2)
    (hx26 : st.readReg64 .x26 = ptr_sec)
    (hx28 : st.readReg64 .x28 = (b0 g_auth'.rootKey.ptr).zeroExtend 64)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (ct2DeallocAt A cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey ∗
        (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1 ∗
        memRegion (s0.sp - 2000#64) 32 ∗
        ((s0.sp - 1968#64) ↦₆₄ shiftWord8 g_auth'.rootKey.ptr 32#64) ∗
        low7At (s0.sp - 1960#64) (shiftWord8 32#64 g_auth'.macKey.cap) ∗
        ((s0.sp - 1953#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((s0.sp - 1945#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1937#64) ↦₆₄ 32#64) ∗
        ((s0.sp - 1929#64) ↦₈ b_pad) ∗
        memRegion (s0.sp - 1928#64) 72 ∗
        memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1328#64) 48 ∗
        memRegion (s0.sp - 1280#64) 24 ∗
        memRegion (s0.sp - 1248#64) 960 ∗
        memRegion (s0.sp - 288#64) 128 ∗
        memRegion (s0.sp - 152#64) 32 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗
        memRegion (s0.sp - 1856#64) 504 ∗ polyDecoderAt A (s0.sp - 2424#64) receivingCt2 ∗
        ((s0.sp - 2496#64) ↦₆₄ (x.epoch + 1#64)) ∗
        ((s0.sp - 2488#64) ↦₆₄ w_sp1) ∗
        ((s0.sp - 2480#64) ↦₆₄ g_auth'.rootKey.cap) ∗
        ((s0.sp - 2472#64) ↦₆₄ w_sp3) ∗
        cells (s0.sp - 2464#64) 5 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQ K F A x s0 R)
      (recvCt2PlacedPostQp K F A x s0 R) := by
  have hpart2 := @recv_ct2_chunk_ok_done_write_out_part2_placed_wpp _ K F A ext hA x receivingCt2
    cap_ct2 ptr_ct2 ptr_sec
  have hcap_rk_beq : (g_auth'.rootKey.cap + 1#64 == 0#64) = false :=
    cap_add_one_beq_zero_false hcap_rk_lt
  refine SepWPp.rw_pre (by
    rw [show memRegion (s0.sp - 2000#64) 32 =
          memRegion (s0.sp - 2000#64) 24 ∗ memRegion (s0.sp - 1976#64) 8 from
        ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 24) (k := 8) (b' := s0.sp - 1976#64) rfl (by bv_omega) (by decide),
      show memRegion (s0.sp - 1928#64) 72 =
          memRegion (s0.sp - 1928#64) 8 ∗ memRegion (s0.sp - 1920#64) 64 from
        ProofLib.memRegion_split' (b := s0.sp - 1928#64) (n := 8) (k := 64) (b' := s0.sp - 1920#64) rfl (by bv_omega) (by decide),
      show memRegion (s0.sp - 1920#64) 64 =
          memRegion (s0.sp - 1920#64) 32 ∗ memRegion (s0.sp - 1888#64) 32 from
        ProofLib.memRegion_split' (b := s0.sp - 1920#64) (n := 32) (k := 32) (b' := s0.sp - 1888#64) rfl (by bv_omega) (by decide),
      show memRegion (s0.sp - 1888#64) 32 =
          memRegion (s0.sp - 1888#64) 24 ∗ memRegion (s0.sp - 1864#64) 8 from
        ProofLib.memRegion_split' (b := s0.sp - 1888#64) (n := 24) (k := 8) (b' := s0.sp - 1864#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 2000#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i u0 u1 u2
  refine SepWPp.fold (memRegion_split_4cells
    (s0.sp - 1920#64) (s0.sp - 1912#64) (s0.sp - 1904#64) (s0.sp - 1896#64)
    (s0.sp - 1888#64) 32 0 rfl
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w40_0 w40_1 w50_0 w50_1
  refine SepWPp.fold (memRegion_24_split_23_1 (s0.sp - 1888#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i z0 z1 z2
  have ha0 : (s0.sp - 2000#64) + 8#64 = s0.sp - 1992#64 := by bv_omega
  have ha1 : (s0.sp - 2000#64) + 16#64 = s0.sp - 1984#64 := by bv_omega
  have ha2 : (s0.sp - 2000#64) + 23#64 = s0.sp - 1977#64 := by bv_omega
  have hc0 : (s0.sp - 1888#64) + 8#64 = s0.sp - 1880#64 := by bv_omega
  have hc1 : (s0.sp - 1888#64) + 16#64 = s0.sp - 1872#64 := by bv_omega
  have hc2 : (s0.sp - 1888#64) + 23#64 = s0.sp - 1865#64 := by bv_omega
  refine SepWPp.rw_pre (by simp only [ha0, ha1, ha2, hc0, hc1, hc2, memRegion_zero, sepConj_emp]; rfl) ?_
  refine SepWPp.fold (Entails.of_eq (left_and_low7_to_mid_at_7
    (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64) u1 u2 (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 1344#64) (s0.sp - 1336#64) (s0.sp - 1328#64)
    16 0 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w480_0 w480_1
  refine SepWPp.rw_pre (by simp only [memRegion_zero, sepConj_emp]; rfl) ?_
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 1328#64) (s0.sp - 1320#64) (s0.sp - 1312#64)
    48 32 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w490_0 w490_1
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 1280#64) (s0.sp - 1272#64) (s0.sp - 1264#64)
    24 8 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w4c0_0 w4c0_1
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 1248#64) (s0.sp - 1240#64) (s0.sp - 1232#64)
    960 944 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w4e0_0 w4e0_1
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 288#64) (s0.sp - 280#64) (s0.sp - 272#64)
    128 112 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w8a0_0 w8a0_1
  refine SepWPp.fold (memRegion_split_2cells (s0.sp - 152#64) (s0.sp - 144#64) (s0.sp - 136#64)
    32 16 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i w928_0 w928_1
  refine SepWPp.fold (memRegion_split_2cells x.outA (x.outA + 8#64) (x.outA + 16#64)
    chunkedEkSentCt1ReceivedSize 488 rfl rfl (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o0 o8
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 16#64) (n := 24) (k := 464) (b' := x.outA + 40#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_24_split_1_16_7 (x.outA + 16#64)) (by sep_focus) ?_
  sep_elim_exists; rename_i ob16 ow17 ow25 ow33
  have ho17 : (x.outA + 16#64) + 1#64 = x.outA + 17#64 := by bv_omega
  have ho25 : (x.outA + 16#64) + 9#64 = x.outA + 25#64 := by bv_omega
  have ho33 : (x.outA + 16#64) + 17#64 = x.outA + 33#64 := by bv_omega
  refine SepWPp.rw_pre (by simp only [ho17, ho25, ho33]; rfl) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 40#64) (x.outA + 48#64) (x.outA + 56#64)
    464 448 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o40 o48
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 56#64) (n := 24) (k := 424) (b' := x.outA + 80#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 80#64) (x.outA + 88#64) (x.outA + 96#64)
    424 408 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o80 o88
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 96#64) (n := 8) (k := 400) (b' := x.outA + 104#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 104#64) (x.outA + 112#64) (x.outA + 120#64)
    400 384 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o104 o112
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 120#64) (n := 8) (k := 376) (b' := x.outA + 128#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 128#64) (x.outA + 136#64) (x.outA + 144#64)
    376 360 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o128 o136
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 144#64) (n := 8) (k := 352) (b' := x.outA + 152#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 152#64) (x.outA + 160#64) (x.outA + 168#64)
    352 336 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o152 o160
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 168#64) (n := 8) (k := 328) (b' := x.outA + 176#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 176#64) (x.outA + 184#64) (x.outA + 192#64)
    328 312 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o176 o184
  refine SepWPp.rw_pre (by
    rw [ProofLib.memRegion_split' (b := x.outA + 192#64) (n := 8) (k := 304) (b' := x.outA + 200#64) rfl (by bv_omega) (by decide)]) ?_
  refine SepWPp.fold (memRegion_split_2cells (x.outA + 200#64) (x.outA + 208#64) (x.outA + 216#64)
    304 288 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  sep_elim_exists; rename_i o200 o208
  have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx24 hx26 hx28 hx29
  clear hA
  simp only [lsProg_350] at hpart2 ⊢
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_350).base + 1708#64) hinv ?_
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (mid_at_7_to_left_shift
    (s0.sp - 1960#64) (s0.sp - 1953#64) (s0.sp - 1952#64) 32#64 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (mid_at_7_to_left
    (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64) u1 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (left_and_mid7_to_mid_at_7_shift
    (s0.sp - 1992#64) (s0.sp - 1985#64) (s0.sp - 1984#64) 32#64 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (left_and_low7_to_mid_at_7
    (s0.sp - 1880#64) (s0.sp - 1873#64) (s0.sp - 1872#64)
    (shiftWord8 32#64 g_auth'.macKey.cap) z2 (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (mid_at_7_to_left_shift
    (s0.sp - 1880#64) (s0.sp - 1873#64) (s0.sp - 1872#64) 32#64 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.fold (Entails.of_eq (left_and_mid7_to_mid_at_7_shift
    (s0.sp - 1880#64) (s0.sp - 1873#64) (s0.sp - 1872#64) 32#64 g_auth'.macKey.cap
    (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (left_and_mid7_to_mid_at_7_any
    (x.outA + 25#64) (x.outA + 32#64) (x.outA + 33#64)
    (shiftWord8 32#64 g_auth'.macKey.cap) ow33 (by bv_omega) (by bv_omega))) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (rejoin_cells_9 s0.sp (x.epoch + 1#64) w_sp1
    g_auth'.rootKey.cap w_sp3) (by sep_focus) ?_
  have hrejoin_2000 :
      ((s0.sp - 2000#64) ↦₆₄ shiftWord8 g_auth'.rootKey.ptr 32#64) ∗
        low7At (s0.sp - 1992#64) (shiftWord8 32#64 g_auth'.macKey.cap) ∗
        ((s0.sp - 1985#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((s0.sp - 1977#64) ↦₈ b7 u2) ⊢
      memRegion (s0.sp - 2000#64) 24 := by
    have h := rejoin_memRegion_24_mid (s0.sp - 2000#64)
      (shiftWord8 g_auth'.rootKey.ptr 32#64) (shiftWord8 32#64 g_auth'.macKey.cap)
      g_auth'.macKey.cap (b7 u2)
    have h15 : (s0.sp - 2000#64) + 15#64 = s0.sp - 1985#64 := by bv_omega
    rwa [ha0, h15, ha2] at h
  have hrejoin_1888 :
      ((s0.sp - 1888#64) ↦₆₄ shiftWord8 g_auth'.rootKey.ptr 32#64) ∗
        low7At (s0.sp - 1880#64) (shiftWord8 32#64 g_auth'.macKey.cap) ∗
        ((s0.sp - 1873#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((s0.sp - 1865#64) ↦₈ b7 z2) ⊢
      memRegion (s0.sp - 1888#64) 24 := by
    have h := rejoin_memRegion_24_mid (s0.sp - 1888#64)
      (shiftWord8 g_auth'.rootKey.ptr 32#64) (shiftWord8 32#64 g_auth'.macKey.cap)
      g_auth'.macKey.cap (b7 z2)
    have h15 : (s0.sp - 1888#64) + 15#64 = s0.sp - 1873#64 := by bv_omega
    rwa [hc0, h15, hc2] at h
  refine SepWP.fold hrejoin_2000 (by sep_focus) ?_
  refine SepWP.fold hrejoin_1888 (by sep_focus) ?_
  refine SepWP.fold (rejoin_memRegion_40_x20_20 s0.sp 0#64 0#64
    g_auth'.macKey.cap g_auth'.macKey.ptr 32#64 b_pad) (by sep_focus) ?_
  have hrejoin_80 :
      memRegion (s0.sp - 2000#64) 24 ∗ memRegion (s0.sp - 1976#64) 8 ∗
        memRegion (s0.sp - 1968#64) 40 ∗ memRegion (s0.sp - 1928#64) 8 ⊢
      memRegion (s0.sp - 2000#64) 80 := by
    rw [← sepConj_assoc, ← sepConj_assoc,
        ← ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 24) (k := 8) (b' := s0.sp - 1976#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 32) (k := 40) (b' := s0.sp - 1968#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 72) (k := 8) (b' := s0.sp - 1928#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hrejoin_48 :
      ((s0.sp - 1904#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1896#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 1888#64) 24 ∗ memRegion (s0.sp - 1864#64) 8 ⊢
      memRegion (s0.sp - 1904#64) 48 := by
    have h32 : memRegion (s0.sp - 1888#64) 24 ∗ memRegion (s0.sp - 1864#64) 8 = memRegion (s0.sp - 1888#64) 32 :=
      (ProofLib.memRegion_split' (b := s0.sp - 1888#64) (n := 24) (k := 8) (b' := s0.sp - 1864#64) rfl (by bv_omega) (by decide)).symm
    rw [h32]
    exact rejoin_2cells_memRegion (s0.sp - 1904#64) (s0.sp - 1896#64) (s0.sp - 1888#64) 0#64 0#64
      48 32 rfl (by bv_omega) (by bv_omega) (by decide)
  refine SepWP.fold hrejoin_80 (by sep_focus) ?_
  refine SepWP.fold hrejoin_48 (by sep_focus) ?_
  refine SepWP.fold (rejoin_2cells_16 (s0.sp - 1344#64) (s0.sp - 1336#64)
    g_auth'.macKey.ptr 32#64 (by bv_omega)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_2cells_memRegion (s0.sp - 1328#64) (s0.sp - 1320#64) (s0.sp - 1312#64)
    0#64 0#64 48 32 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_2cells_memRegion (s0.sp - 1248#64) (s0.sp - 1240#64) (s0.sp - 1232#64)
    0#64 0#64 960 944 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_2cells_memRegion (s0.sp - 288#64) (s0.sp - 280#64) (s0.sp - 272#64)
    0#64 0#64 128 112 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  refine SepWP.fold (rejoin_2cells_memRegion (s0.sp - 152#64) (s0.sp - 144#64) (s0.sp - 136#64)
    0#64 0#64 32 16 rfl (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  refine SepWPp.rw_pre (by ac_rfl)
    (hpart2 w40_0 w40_1 ob16 auth' g_auth' ss s0 _ R
      hrk_len hmk_len hss_len hptr_sec_ne hres
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *]) hsp_s0
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hinv1
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
