/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Arm (`+2588..+3068` and Top-Level Arm)

**Checked by Lean.**

Verifies `step_keysUnsampled_2588_to_3068` (`PolyEncoder::encode_bytes`, `next_chunk`,
and `chunkedKeysSampledAt` assembly) and the complete `.keysUnsampled` arm
`step_send_arm_keysUnsampled` (`0x309d0 -> 0x31458`, `+372..+3068`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

abbrev spqrLogLevelZeroAt (b : BitVec 64) : SepProp :=
  (b + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP") + 256)) ↦₆₄ 0#64

theorem chunkAt_5208_4192_1360_eq (sp : BitVec 64) (chunk : Chunk)
    (cw0 cw1 cw2 cw3 : BitVec 64)
    (hchunk : ∀ a : BitVec 64,
      chunkAt a chunk =
        (a ↦₆₄ cw0) ∗ ((a + 8#64) ↦₆₄ cw1) ∗ ((a + 16#64) ↦₆₄ cw2) ∗
        ((a + 24#64) ↦₆₄ cw3) ∗ ((a + 32#64) ↦₁₆ chunk.index)) :
    chunkAt (sp + 5208#64) chunk =
      ((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗
      ((sp + 5224#64) ↦₆₄ cw2) ∗ ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 4192#64) chunk =
      ((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗
      ((sp + 4208#64) ↦₆₄ cw2) ∗ ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 1360#64) chunk =
      ((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗
      ((sp + 1376#64) ↦₆₄ cw2) ∗ ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index) :=
  ⟨chunkAt_sp_add_eq sp 5208#64 5216#64 5224#64 5232#64 5240#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 4192#64 4200#64 4208#64 4216#64 4224#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 1360#64 1368#64 1376#64 1384#64 1392#64 chunk cw0 cw1 cw2 cw3 hchunk⟩

theorem words3_7104_entails_memRegion (sp w0 w1 w2 : BitVec 64) :
    ((sp + 7104#64) ↦₆₄ w0) ∗ ((sp + 7112#64) ↦₆₄ w1) ∗ ((sp + 7120#64) ↦₆₄ w2) ⊢
    memRegion (sp + 7104#64) 24 := by
  have h := words3_entails_memRegion (sp + 7104#64) w0 w1 w2
  rwa [show (sp + 7104#64) + 8#64 = sp + 7112#64 by rw [BitVec.add_assoc]; rfl,
       show (sp + 7104#64) + 16#64 = sp + 7120#64 by rw [BitVec.add_assoc]; rfl] at h

/-- Sub-step 2 (`entry + 2588#64 -> entry + 3068#64`):
    calls `PolyEncoder::encode_bytes` on `hdr ++ mac` (96 bytes), relocates the encoder
    to `sp + 7536#64`, calls `PolyEncoder::next_chunk`, assembles `chunkedKeysSampledAt`
    at `sp + 4192#64`, relocates it through `sp + 4704#64` and `sp + 3552#64` to `sp + 1424#64`,
    deallocates the temporary `mac` and `hdr` buffers, and writes `chunk` to `sp + 1360#64`. -/
theorem step_keysUnsampled_2588_to_3068 {F : ShaCompress}
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hbase : img.base &&& 0xfff#64 = 0#64)
    (henc_call : EncodeBytesOkX img A ext)
    (hnc_call : PolyNextChunkOkX img A ext)
    (sp epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (sending_hdr : PolyEncoder)
    (outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hmac_len : mac.length = 32)
    (henc_res : encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok sending_hdr)
    (hnc : sending_hdr.nextChunk = .ok (outSt.sending_hdr, chunk))
    (huc : outSt.uc = { epoch := epoch, auth := auth,
                        ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList })
    (_hhdr_ne : hdr_ptr' ≠ 0)
    (_hmac_ne : mac_ptr ≠ 0)
    (hmac_cap_b : (mac_cap == 0#64) = false)
    (hmac_cap_ge : 32 ≤ mac_cap.toNat)
    (hmac_cap_lt : mac_cap.toNat < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 2588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = mac_cap)
    (hx21 : s.readReg64 .x21 = mac_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = hdr_ptr')
    (hx24 : s.readReg64 .x24 = 64#64)
    (hx25 : s.readReg64 .x25 = 32#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 7536#64) 400 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 1424#64) 504 ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      authHeapBufs A g auth ∗
      ((sp + 7104#64) ↦₆₄ 128#64) ∗
      ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
      ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live hdr_ptr' 128 1 ∗
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
      memRegion (hdr_ptr' + 96#64) 32 ∗
      A.live mac_ptr mac_cap.toNat 1 ∗
      (mac_ptr ↦ₛ mac) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      tokenInitAt img.base ∗
      reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = 3#64 →
      sf.readReg64 .x21 = noneCap →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 1#64 →
      sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((chunkedKeysSampledAt A (sp + 1424#64) outSt ∗
          chunkAt (sp + 1360#64) chunk ∗
          memRegion (sp + 1394#64) 4 ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400 ∗
          tokenInitAt img.base ∗
          reduceTableAt img.base ∗
          spqrLogLevelZeroAt img.base ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have henc_at := spqrSend_encodeBytes_ok henc_call
  have hnc_at := spqrSend_polyNextChunk_ok hnc_call
  have hmemcpy := spqrSend_memcpy_ok hA
  have hdealloc := spqrSend_dealloc_ok hA
  have h96 : ((K.fromSeed seed).1.toList ++ mac).length = 96 := hdr_mac_len_96 K seed hmac_len
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  have hadrp := fnAddr_adrp_31380 (H := Rust.withPanics ext) hbase
  spqr_send_fetches_range img.base (Rust.withPanics ext) 2588 480
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26] at hx20 hx21 hx22 hx23 hx24 hx25 hx26
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")) img hinv
  have hfold_7136 := authInlineWordsAt_352_entails_memRegion_400 g (sp + 7136#64) auth
  rw [show (sp + 7136#64) + 48#64 = sp + 7184#64 by rw [BitVec.add_assoc]; rfl] at hfold_7136
  refine SepWP.fold hfold_7136 (by sep_focus) ?_
  clear hfold_7136
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_1
  refine call_inImage_calleeStack (x := ({
      out := sp + 7136#64, msgRO := false, msgA := hdr_ptr',
      msg := (K.fromSeed seed).1.toList ++ mac } : EncodeBytesGhost))
    (s0 := s0) sp encodeBytesStackX (by decide)
    (T_pre := memRegion (sp + 7136#64) polyEncoderSize ∗
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗ A.pool)
    (T_post := fun _ => polyEncoderAt A (sp + 7136#64) sending_hdr ∗
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗ A.pool)
    (F := memRegion (sp + 7536#64) 400 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      authHeapBufs A g auth ∗
      ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
      A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗ Frame)
    (φ_pre := _) (φ_post := _) henc_at hinv_1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := entry + 2608#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by dsimp only [encodeBytesSpecX, encodeBytesSpec]; rw [bytesAt_false_eq]; ac_rfl)
    (by simp only [h96, Reg.x8, Reg.x0, Reg.x1, wp_norm, arm64_norm, *])
    (by dsimp only [polyEncoderSize]; ac_rfl)
    (fun _ _ => rfl)
    (fun sf => encodeBytes_onPanic_of_ok _ henc_res _ sf)
    (by intro sf; dsimp only [encodeBytesSpecX, encodeBytesSpec]; rw [henc_res, resultPolyEncoderAt, bytesAt_false_eq]; ac_rfl) ?_
  intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 htr_sm1 hinv_sm1
    hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 _ _ hx26_sm1 _ hx28_sm1 hvregs_sm1
  simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x26, Reg.x28,
    wp_norm, arm64_norm, *] at htr_sm1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx26_sm1 hx28_sm1 hvregs_sm1
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) img hinv_sm1
  have h2640 : ∀ s_m : State,
      s_m.pc = entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy") → s_m.status = .Running → s_m.sp = sp → s_m.trace = s0.trace →
      s_m.readReg64 Reg.lr = entry + 2644#64 →
      s_m.readReg64 Reg.x0 = sp + 7536#64 → s_m.readReg64 Reg.x1 = sp + 7136#64 →
      (s_m.readReg64 Reg.x2).toNat = 400 →
      s_m.readReg64 .x19 = s.readReg64 .x19 → s_m.readReg64 .x20 = mac_cap →
      s_m.readReg64 .x21 = mac_ptr → s_m.readReg64 .x22 = epoch →
      s_m.readReg64 .x23 = hdr_ptr' → s_m.readReg64 .x26 = sp + 4704#64 →
      s_m.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s_m = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) s_m
        ((stackAt sp spqrSendCalleeStack ∗
          (polyEncoderAt A (sp + 7136#64) sending_hdr ∗
           (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗ A.pool)) ∗
         memRegion (sp + 7536#64) 400 ∗ memRegion (sp + 3552#64) 504 ∗
         memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
         memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
         ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
         authHeapBufs A g auth ∗
         ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
         A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
         A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
         memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
         RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
         RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
         tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗ Frame)
        (fun sm Pm => ImgCallInv img sm → SepWPp (tripleRatchetProgAtExt img.base ext) ret sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
    intro s_m hpcm hrunm hspm htrm hlrm hx0m hx1m hx2m hx19m hx20m hx21m hx22m hx23m hx26m hx28m hvregsm
    refine call_memcpy_relocate hmemcpy (Relocatable.of_polyEncoderAt A sending_hdr)
      (sp + 7536#64) (sp + 7136#64) (s0 := s0) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗ A.pool ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 1360#64) 38 ∗
        memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗ Frame)
      hpcm hrunm hspm hsp_align hlrm htrm hx0m hx1m hx2m
      (by ac_rfl) ?_
    intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 htr_sf1 hx19_sf1 hx20_sf1 hx21_sf1 hx22_sf1 hx23_sf1 _ _ hx26_sf1 _ hx28_sf1 hvregs_sf1
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf1 hx20_sf1 hx21_sf1 hx22_sf1 hx23_sf1 hx26_sf1 hx28_sf1 hvregs_sf1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_2
    rw [memRegion_4704_2400_split_nextChunk sp]
    refine call_inImage_calleeStack (x := ({
        outA := sp + 5208#64, encA := sp + 7536#64,
        enc := sending_hdr, enc' := outSt.sending_hdr, chunk := chunk } : PolyNextChunkGhost))
      (s0 := s0) sp polyNextChunkStack (by decide)
      (T_pre := memRegion (sp + 5208#64) chunkSize ∗
        polyEncoderAt A (sp + 7536#64) sending_hdr ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
      (T_post := fun _ => polyEncoderAt A (sp + 7536#64) outSt.sending_hdr ∗
        chunkAt (sp + 5208#64) chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
      (F := memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        spqrLogLevelZeroAt img.base ∗ Frame)
      (φ_pre := _) (φ_post := _) hnc_at hinv_2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (by simp only [wp_norm, arm64_norm, *])
      (ret_pc := entry + 2672#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
      (by dsimp only [polyNextChunkSpec]; ac_rfl)
      (by simp only [hbase, hnc, Reg.x8, Reg.x0, wp_norm, arm64_norm, *])
      (by dsimp only [polyEncoderSize, chunkSize]; ac_rfl)
      (fun _ _ => rfl)
      (fun sf => polyNextChunk_onPanic_of_ok img.base _ hnc _ sf)
      (by intro sf; dsimp only [polyNextChunkSpec]; ac_rfl) ?_
    intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 _ hx26_sm2 _ hx28_sm2 hvregs_sm2
    simp only [wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx26_sm2 hx28_sm2 hvregs_sm2
    apply of_sepWP_inImage (mid := entry + 3068#64) img hinv_sm2
    rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 400) (k := 104) (b' := sp + 4592#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    wp_steps
    refine call_memcpy_relocate hmemcpy (Relocatable.of_polyEncoderAt A outSt.sending_hdr)
      (sp + 4192#64) (sp + 7536#64) (s0 := s0) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        chunkAt (sp + 5208#64) chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4592#64) 104 ∗
        memRegion (sp + 4704#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        spqrLogLevelZeroAt img.base ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := entry + 2696#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by ac_rfl) ?_
    intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 htr_sf2 hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 _ hx26_sf2 _ hx28_sf2 hvregs_sf2
    simp only [wp_norm, arm64_norm, *] at hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx26_sf2 hx28_sf2 hvregs_sf2
    rw [memRegion_104_eq_words13 (sp + 4592#64)]
    wp_conv_pre =>
      dsimp only [ekSentInlineWordsAt, authInlineWordsAt]
      simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 13 (apply SepWP.exists_elim; intro _)
    wp_steps
    have hfold_ks :
        polyEncoderAt A (sp + 4192#64) outSt.sending_hdr ∗
        (((sp + 4592#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4600#64) ↦₆₄ g.rootKey.ptr) ∗
         ((sp + 4608#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp + 4616#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4624#64) ↦₆₄ g.macKey.ptr) ∗
         ((sp + 4632#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         ((sp + 4640#64) ↦₆₄ 1152#64) ∗ ((sp + 4648#64) ↦₆₄ ek_ptr) ∗ ((sp + 4656#64) ↦₆₄ 1152#64) ∗
         ((sp + 4664#64) ↦₆₄ 2400#64) ∗ ((sp + 4672#64) ↦₆₄ dk_ptr) ∗ ((sp + 4680#64) ↦₆₄ 2400#64) ∗
         ((sp + 4688#64) ↦₆₄ epoch)) ∗
        authHeapBufs A g auth ∗
        RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        (((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
         ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
         ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
         ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
         ((sp + 4176#64) ↦₆₄ epoch)) ⊢
        chunkedKeysSampledAt A (sp + 4192#64) outSt ∗
        memRegion (sp + 4080#64) 104 := by
      have h1 := fold_chunkedKeysSampledAt (A := A) (sp + 4192#64) g outSt auth epoch
        (K.fromSeed seed).2.1.toList (K.fromSeed seed).2.2.toList ek_ptr dk_ptr huc
        (by rw [hek_len]) (by rw [hdk_len])
      have h2 := ekSentInlineWordsAt_entails_memRegion (sp + 4080#64) g auth
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch
      dsimp only [ekSentInlineWordsAt, authInlineWordsAt] at h1 h2
      simp only [BitVec.add_assoc, arm64_norm] at h1 h2
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 h2)
    refine SepWP.fold hfold_ks (by sep_focus) ?_
    clear hfold_ks
    refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedKeysSampledAt A outSt)
      (sp + 4704#64) (sp + 4192#64) (s0 := s0) (sp_call := sp)
      (Frame := memRegion (sp + 4080#64) 104 ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion (sp + 7536#64) 400 ∗ chunkAt (sp + 5208#64) chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
        memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        spqrLogLevelZeroAt img.base ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := entry + 2776#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by ac_rfl) ?_
    intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 htr_sf3 hx19_sf3 hx20_sf3 hx21_sf3 hx22_sf3 hx23_sf3 hx24_sf3 _ hx26_sf3 _ hx28_sf3 hvregs_sf3
    simp only [wp_norm, arm64_norm, *] at hx19_sf3 hx20_sf3 hx21_sf3 hx22_sf3 hx23_sf3 hx24_sf3 hx26_sf3 hx28_sf3 hvregs_sf3
    have hmac_mem := pointsToBytes_and_tail_entails_memRegion mac_ptr mac 32 mac_cap.toNat
      hmac_len hmac_cap_ge (by omega)
    have hhdr_mem := pointsToBytes_and_tail_entails_memRegion hdr_ptr'
      ((K.fromSeed seed).1.toList ++ mac) 96 128 h96 (by decide) (by decide)
    refine SepWP.fold hmac_mem (by sep_focus) ?_
    refine SepWP.fold hhdr_mem (by sep_focus) ?_
    refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp) (by sep_focus) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp)
      (by simp only [‹sf_1.sp = _›, ‹sf.sp = _›, hsp_sf3]; sep_focus) ?_
    wp_steps
    refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedKeysSampledAt A outSt)
      (sp + 3552#64) (sp + 4704#64) (s0 := s0) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4080#64) 104 ∗
        memRegion (sp + 7536#64) 400 ∗ chunkAt (sp + 5208#64) chunk ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
        memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        spqrLogLevelZeroAt img.base ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := entry + 2840#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by ac_rfl) ?_
    intro sf4 hpc_sf4 hrun_sf4 hsp_sf4 htr_sf4 hx19_sf4 _ _ hx22_sf4 _ hx24_sf4 hx25_sf4 hx26_sf4 _ hx28_sf4 hvregs_sf4
    simp only [wp_norm, arm64_norm, *] at hx19_sf4 hx22_sf4 hx24_sf4 hx25_sf4 hx26_sf4 hx28_sf4 hvregs_sf4
    obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
    obtain ⟨hchunk_5208, hchunk_4192, hchunk_1360⟩ := chunkAt_5208_4192_1360_eq sp chunk cw0 cw1 cw2 cw3 hchunk
    have h1360_slot : memRegion (sp + 1360#64) 38 =
        (∃∗ d0 : BitVec 64, (sp + 1360#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 1368#64) ↦₆₄ d1) ∗
        (∃∗ d2 : BitVec 64, (sp + 1376#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 1384#64) ↦₆₄ d3) ∗
        (∃∗ d4 : BitVec 16, (sp + 1392#64) ↦₁₆ d4) ∗ memRegion (sp + 1394#64) 4 :=
      memRegion_38_eq_chunk_slot sp
    rw [hchunk_5208, memRegion_504_expose_chunk_slot sp, h1360_slot]
    wp_conv_pre =>
      dsimp only [spqrLogLevelZeroAt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 10 (apply SepWP.exists_elim; intro _)
    wp_steps
    have hfold_chunks :
        (((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗
         ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index)) ∗
        ((((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗
          ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index)) ∗
         memRegion (sp + 4226#64) 470) ∗
        (memRegion (sp + 4704#64) 504 ∗
         (((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗ ((sp + 5224#64) ↦₆₄ cw2) ∗
          ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index)) ∗
         memRegion (sp + 5242#64) 1862) ∗
        (((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64)) ⊢
        chunkAt (sp + 1360#64) chunk ∗
        memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗
        memRegion (sp + 7104#64) 24 := by
      rw [← hchunk_1360, ← hchunk_4192, ← hchunk_5208, memRegion_4704_2400_split_nextChunk sp]
      have h4192 := chunkAt_and_470_entails_memRegion_504 sp chunk
      have h5208 := chunkAt_entails_memRegion (sp + 5208#64) chunk
      have h7104 := words3_7104_entails_memRegion sp 128#64 hdr_ptr' 64#64
      exact sepConj_mono (Entails.refl _)
        (sepConj_mono h4192
          (sepConj_mono (sepConj_mono (Entails.refl _) (sepConj_mono h5208 (Entails.refl _))) h7104))
    refine SepWP.fold hfold_chunks (by sep_focus) ?_
    clear hfold_chunks
    refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedKeysSampledAt A outSt)
      (sp + 1424#64) (sp + 3552#64) (s0 := s0) (sp_call := sp)
      (Frame := chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
        memRegion (sp + 1394#64) 4 ∗ stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7536#64) 400 ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗
        memRegion (sp + 7136#64) 400 ∗
        spqrLogLevelZeroAt img.base ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := entry + 3056#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by dsimp only [spqrLogLevelZeroAt]; ac_rfl) ?_
    intro sf5 hpc_sf5 hrun_sf5 hsp_sf5 htr_sf5 hx19_sf5 _ _ hx22_sf5 _ _ hx25_sf5 hx26_sf5 _ hx28_sf5 hvregs_sf5
    simp only [wp_norm, arm64_norm, *] at hx19_sf5 hx22_sf5 hx25_sf5 hx26_sf5 hx28_sf5 hvregs_sf5
    wp_steps
    refine finish_sepWP_inImage (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (fun hinv_f => hnext _ hinv_f
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, noneCap, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x24, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x28, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (Entails.of_eq (by ac_rfl))
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (sp + 7136#64) sending_hdr
  rcases htag01 with rfl | rfl
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    exact h2640 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    exact h2640 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])

theorem step_keysUnsampled_372_to_512_at
    {img : Obj.Image} {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64)
    (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      tapeAt ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64) sf
        ((authenticatorPinAt A g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          tapeAfter ctl cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64) s P post := by
  have hrng_call := spqrSend_rngFill_ok (b := img.base) hrng
  have hseed_call := spqrSend_mlkemFromSeed_ok (b := img.base) hseed
  have hpk1_call := spqrSend_mlkemPk1_ok (b := img.base) hpk1
  spqr_send_fetches_range img.base (Rust.withPanics ext) 372 140
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 48) (k := 352) (b' := sp + 7184#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_eight (sp + 7184#64),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      memRegion_64_eq_words8 (sp + 4192#64),
      memRegion_48_eq_words6 (sp + 7136#64),
      memRegion_64_eq_words8 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 23 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine SepWP.fold (words8At_entails_memRegion (sp + 7536#64) _ _ _ _ _ _ _ _)
    (by dsimp only [words8At]; sep_focus) ?_
  wp_apply
  wp_conv_pre => rw [List.take_append_of_le_length h64, Nat.min_eq_left h64, ← hseed_val]
  obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7, hseed_words⟩ :=
    exists_words8_of_len64 seed.toList (List.Vector.toList_length seed)
  wp_conv_pre => rw [hseed_words (sp + 7536#64)]; dsimp only [words8At]
  wp_steps
  have hfold_seed_4192 :
      words8At (sp + 4192#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ⊢ ((sp + 4192#64) ↦ₛ seed.toList) := by
    rw [hseed_words (sp + 4192#64)]
    exact Entails.refl _
  refine SepWP.fold hfold_seed_4192 (by dsimp only [words8At]; sep_focus) ?_
  clear hseed_words hfold_seed_4192
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
  wp_apply; wp_steps; wp_apply; wp_steps
  refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
    (by simp only [‹sf_1.sp = _›, ‹sf.sp = _›, hsp]; sep_focus) ?_
  have hfold_end :
      authInlineWordsAt g (sp + 7136#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 7184#64) ↦₆₄ epoch) ∗
      memRegion (sp + 7192#64) 344 ∗
      ((sp + 4192#64) ↦ₛ seed.toList) ∗
      memRegion (sp + 4256#64) 440 ∗
      words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
      memRegion (sp + 7600#64) 336 ⊢
      authenticatorPinAt A g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 7536#64) 400 := by
    rw [authenticatorPinAt_eq_inline_heap A g (sp + 7136#64) auth,
        ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
        ProofLib.memRegion_eight (sp + 7184#64),
        ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
        ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    have h7184 : ((sp + 7184#64) ↦₆₄ epoch) ⊢ ∃∗ d : BitVec 64, (sp + 7184#64) ↦₆₄ d :=
      Entails.sepExists_right _ (Entails.refl _)
    have h4192 := pointsToBytes_entails_memRegion (sp + 4192#64) seed.toList
    rw [List.Vector.toList_length] at h4192
    simp only [sepConj_assoc]
    exact sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono h7184
          (sepConj_mono (Entails.refl _)
            (sepConj_mono h4192
              (sepConj_mono (Entails.refl _)
                (sepConj_mono (words8At_entails_memRegion (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7)
                  (Entails.refl _)))))))
  refine SepWP.fold hfold_end
    (by dsimp only [authInlineWordsAt, words8At]; sep_focus) ?_
  refine finish_sepWP
    (hnext _
      (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by ac_rfl))

theorem keysUnsampled_src_entails_memRegion_928 (sp epoch : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) :
    ((sp + 2384#64) ↦₆₄ 2#64) ∗
    authInlineWordsAt g (sp + 2392#64) auth ∗
    ((sp + 2440#64) ↦₆₄ epoch) ∗
    memRegion (sp + 2448#64) 864 ⊢
    memRegion (sp + 0x950#64) 928 := by
  rw [ProofLib.memRegion_split' (b := sp + 2384#64) (n := 8) (k := 920) (b' := sp + 2392#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 2392#64) (n := 48) (k := 872) (b' := sp + 2440#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 2440#64) (n := 8) (k := 864) (b' := sp + 2448#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (authInlineWordsAt_entails_memRegion g (sp + 2392#64) auth)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (Entails.refl _)))

theorem authenticatorAt_entails_exists_inline_heap (A : RustAlloc) (a : BitVec 64) (auth : Authenticator) :
    authenticatorAt A a auth ⊢
    ∃∗ g : AuthenticatorGhost, authInlineWordsAt g a auth ∗ authHeapBufs A g auth := by
  unfold authenticatorAt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.Entails.sepExists_elim; intro mcap
  apply ProofLib.Entails.sepExists_elim; intro mptr
  apply ProofLib.Entails.sepExists_elim; intro rcap
  apply ProofLib.Entails.sepExists_elim; intro rptr
  refine Entails.sepExists_right ⟨⟨rcap, rptr⟩, ⟨mcap, mptr⟩⟩ ?_
  dsimp only [authInlineWordsAt, authHeapBufs, vecU8At, vecHeader, RustHeap.vecU8Buf]
  rw [show (a + 0x18#64 : BitVec 64) = a + 24#64 from rfl,
      show (a + 24#64) + 8#64 = a + 32#64 by rw [BitVec.add_assoc]; rfl,
      show (a + 24#64) + 16#64 = a + 40#64 by rw [BitVec.add_assoc]; rfl]
  exact Entails.of_eq (by ac_rfl)

theorem SepWPp.mono_pre' {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q onPanic : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q onPanic) :
    SepWPp prog ret s P Q onPanic :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem take_64_len {α : Type} {l : List α} (h : 64 ≤ l.length) : (l.take 64).length = 64 := by
  rw [List.length_take]; omega

theorem sub_drop_64_len {α : Type} {l : List α} (h : 64 ≤ l.length) :
    l.length - (l.drop 64).length = 64 := by
  rw [List.length_drop]; omega

set_option maxHeartbeats 800000 in
/-- Complete inlined `.keysUnsampled` arm (`0x309d0 -> 0x31458`, offsets `372..3068`). -/
theorem step_send_arm_keysUnsampled {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) (hbase : img.base &&& 0xfff#64 = 0#64)
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec)
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (hmac_call : AuthMacHdrPinnedOkX img F A ext)
    (hres_call : DoReserve2OkX img A ext)
    (henc_call : EncodeBytesOkX img A ext)
    (hnc_call : PolyNextChunkOkX img A ext)
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hsend : st.send_hdr_chunk K spqrPolyApi tape = .ok (outSt, chunk, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      stackAt sp spqrSendCalleeStack ∗ A.pool ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗
      tapeAt ctl cur tape ∗
      chunkedStatesAt A (sp + 0x950#64) (.keysUnsampled st) ∗
      memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4056#64) 8 ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ sf : State, ImgCallInv img sf →
      SpqrSendJoinState img.base sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          spqrLogLevelZeroAt img.base ∗
          tapeAfter ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.keysSampled outSt) ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4056#64) 8 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  obtain ⟨h64, sending_hdr, hmac, henc_res, hnc, huc, rfl⟩ :=
    send_hdr_chunk_ok_elim K st hsend
  clear hsend
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, take_64_len h64⟩
  generalize hmac_def : st.uc.auth.macHdrUnchecked F st.uc.epoch (K.fromSeed seed).1.toList = mac at hmac henc_res
  have hmac_len : mac.length = 32 := by
    rw [← hmac_def]; exact macHdrUnchecked_length F st.uc.auth st.uc.epoch _
  clear hmac_def
  subst hP
  rw [chunkedStatesAt_keysUnsampled_unfold A (sp + 0x950#64) st,
      show (sp + 0x950#64 : BitVec 64) = sp + 2384#64 from rfl,
      show (sp + 2384#64) + 8#64 = sp + 2392#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 2384#64) + 56#64 = sp + 2440#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 2384#64) + 64#64 = sp + 2448#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
      ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416)
        (b' := sp + 1928#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      ProofLib.memRegion_eight (sp + 4056#64)]
  apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64) img hinv
  refine SepWP.fold (authenticatorAt_entails_exists_inline_heap A (sp + 2392#64) st.uc.auth) (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro g
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056
  refine step_keysUnsampled_372_to_512_at (A := A) hrng hseed hpk1 g st.uc.auth st.uc.epoch
    sp cur tape h64 seed rfl d4056
    (Frame := A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7104#64) 24 ∗ Frame)
    hsp_align hpc hrun hsp
    hx24 htr (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 _ hx24_1 hx26_1 hx28_1 htr1 hvregs_1
  apply SepWP.done hpc1 hrun1; intro hinv1
  refine step_keysUnsampled_512_to_684 hA hpk2 sp st.uc.epoch seed
    (hpk1_slice seed) (hpk2_slice seed)
    (Frame := authenticatorPinAt A g (sp + 7136#64) st.uc.auth ∗
      memRegion (sp + 7184#64) 352 ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 7536#64) 400 ∗
      tapeAfter ctl cur tape 64 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7104#64) 24 ∗ Frame)
    hinv1 hsp_align hpc1 hrun1 hsp1 hx21_1 hx22_1 htr1
    (by ac_rfl) ?_
  intro s2 hdr_ptr ek_ptr dk_ptr hinv2 hhdr_ne _ hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx2_2 hx3_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2 hvregs_2
  refine step_keysUnsampled_684_to_2588 hA hmac_call hres_call sp st.uc.epoch hdr_ptr ek_ptr dk_ptr
    g st.uc.auth seed mac hmac hhdr_ne
    (Frame := memRegion (sp + 7184#64) 352 ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 7536#64) 400 ∗
      tapeAfter ctl cur tape 64 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗ Frame)
    hinv2 hsp_align hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx2_2 hx3_2 hx8_2 hx20_2 hx21_2 hx22_2 hx23_2
    (by rw [hx24_2, hx24_1]) hx25_2 (by rw [hx26_2, hx26_1, hx26]) hx27_2 htr2
    (by ac_rfl) ?_
  intro s3 hdr_ptr' mac_cap mac_ptr hinv3 hhdr'_ne hmac_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
    hpc3 hrun3 hsp3 _ hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3 hvregs_3
  refine step_keysUnsampled_2588_to_3068 hA hbase henc_call hnc_call
    sp st.uc.epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr g st.uc.auth seed mac
    sending_hdr outSt chunk hmac_len henc_res hnc huc
    hhdr'_ne hmac_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
    (Frame := authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      tapeAfter ctl cur tape 64 ∗
      ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗
      memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 1928#64) 416 ∗ Frame)
    hinv3 hsp_align hpc3 hrun3 hsp3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 htr3
    (by ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f htr_f hvregs_f
  have htape_sub : tape.length - (tape.drop 64).length = 64 := sub_drop_64_len h64
  refine SepWPp.mono_pre' ?_
    (hnext sf hinv_f ⟨hpc_f, hrun_f, hsp_f, htr_f,
      by rw [hx19_f, hx19_3, hx19_2, hx19_1, hx19],
      by rw [hx20_f]; rfl,
      hx22_f, hx25_f, hx26_f,
      by rw [hx28_f, hx28_3, hx28_2, hx28_1, hx28],
      by rw [hvregs_f, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩)
  rw [htape_sub, hx24_f, hx21_f,
      chunkedStatesTail920At_keysSampled_eq A (sp + 0x590#64) outSt,
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      show (sp + 1424#64) + 504#64 = sp + 1928#64 by rw [BitVec.add_assoc]; rfl]
  have hsrc := keysUnsampled_src_entails_memRegion_928 sp st.uc.epoch g st.uc.auth
  have h4056 : ((sp + 4056#64) ↦₆₄ st.uc.epoch) ⊢ memRegion (sp + 4056#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + 4056#64) st.uc.epoch
  have hpay : chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ⊢
      spqrSendPayloadSlotAt sp ((1#64 : BitVec 64).setWidth 8) (.hdr chunk) := by
    dsimp only [spqrSendPayloadSlotAt]
    rw [show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
        show (sp + 0x572#64 : BitVec 64) = sp + 1394#64 from rfl]
    exact Entails.pure_right rfl (Entails.refl _)
  have hkey : memRegion (sp + 0x580#64) 16 ⊢
      spqrSendKeySlotAt A sp noneCap (sf.readReg64 .x27) none := by
    dsimp only [spqrSendKeySlotAt]
    exact Entails.pure_right rfl (Entails.refl _)
  have hrearr_lhs :
      (chunkedKeysSampledAt A (sp + 1424#64) outSt ∗
       chunkAt (sp + 1360#64) chunk ∗
       memRegion (sp + 1394#64) 4 ∗
       memRegion (sp + 3552#64) 504 ∗
       memRegion (sp + 4080#64) 104 ∗
       memRegion (sp + 4192#64) 504 ∗
       memRegion (sp + 4704#64) 2400 ∗
       memRegion (sp + 7104#64) 24 ∗
       memRegion (sp + 7136#64) 400 ∗
       memRegion (sp + 7536#64) 400 ∗
       tokenInitAt img.base ∗
       reduceTableAt img.base ∗
       spqrLogLevelZeroAt img.base ∗
       A.pool ∗
       stackAt sp spqrSendCalleeStack) ∗
      (authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
       ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
       tapeAfter ctl cur tape 64 ∗
       ((sp + 2384#64) ↦₆₄ 2#64) ∗
       memRegion (sp + 2448#64) 864 ∗
       memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 1928#64) 416 ∗
       Frame) =
      (((sp + 2384#64) ↦₆₄ 2#64) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (sp + 2448#64) 864) ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      (chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4) ∗
      memRegion (sp + 0x580#64) 16 ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
       tokenInitAt img.base ∗ reduceTableAt img.base ∗
       spqrLogLevelZeroAt img.base ∗
       tapeAfter ctl cur tape 64 ∗
       (chunkedKeysSampledAt A (sp + 1424#64) outSt ∗ memRegion (sp + 1928#64) 416) ∗
       memRegion (sp + 3552#64) 504 ∗
       memRegion (sp + 4080#64) 104 ∗
       memRegion (sp + 4192#64) 504 ∗
       memRegion (sp + 4704#64) 2400 ∗
       memRegion (sp + 7104#64) 24 ∗
       memRegion (sp + 7136#64) 400 ∗
       memRegion (sp + 7536#64) 400 ∗ Frame) := by ac_rfl
  rw [hrearr_lhs]
  refine Entails.trans
    (sepConj_mono hsrc
      (sepConj_mono h4056
        (sepConj_mono hpay
          (sepConj_mono hkey (Entails.refl _)))))
    (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.Top.Send
