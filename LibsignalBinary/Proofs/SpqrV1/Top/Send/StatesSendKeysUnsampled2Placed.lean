/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1Placed
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable Inlined `.keysUnsampled` Sub-Step (`+684..+2588`, Block 124)

Verifies `step_keysUnsampled_684_to_2588_placed` inside Block 124 (`spqr::send::<HookRng>`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

set_option maxHeartbeats 1600000 in
/-- Step `.keysUnsampled` from `+684` (at `Authenticator::mac_hdr`) to `+2588`
(at `<PolyEncoder as Encoder>::encode_bytes`) on `spqrSendPlacedProg ext`. -/
theorem step_keysUnsampled_684_to_2588_placed {F : ShaCompress}
    {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F A ext)
    (hres_call : DoReserve2PlacedOkX A ext)
    (sp epoch hdr_ptr ek_ptr dk_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (hmac : auth.macHdr F epoch (K.fromSeed seed).1.toList = .ok mac)
    (hhdr_ne : hdr_ptr ≠ 0)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 684#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = sp + 7136#64)
    (hx1 : s.readReg64 .x1 = epoch)
    (hx2 : s.readReg64 .x2 = hdr_ptr)
    (hx3 : s.readReg64 .x3 = 64#64)
    (hx8 : s.readReg64 .x8 = sp + 4832#64)
    (hx20 : s.readReg64 .x20 = hdr_ptr)
    (hx21 : s.readReg64 .x21 = ek_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = dk_ptr)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx25 : s.readReg64 .x25 = 2400#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = 64#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authenticatorPinAt A g (sp + 7136#64) auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      A.live hdr_ptr 64 1 ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr' mac_cap mac_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr' ≠ 0 →
      mac_ptr ≠ 0 → (mac_cap == 0#64) = false →
      32 ≤ mac_cap.toNat → mac_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 2588#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = hdr_ptr' + 64#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = mac_cap →
      sf.readReg64 .x21 = mac_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = hdr_ptr' →
      sf.readReg64 .x24 = 64#64 →
      sf.readReg64 .x25 = 32#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((authInlineWordsAt g (sp + 2392#64) auth ∗
          authInlineWordsAt g (sp + 7136#64) auth ∗
          authHeapBufs A g auth ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          memRegion (sp + 4704#64) 2400 ∗
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
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hmac_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F A)) := hmac_call
  have hres_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 157)
      (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A)) := hres_call
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hhdr_len : (K.fromSeed seed).1.toList.length = 64 := List.Vector.toList_length _
  obtain ⟨rfl, _, _⟩ := macHdr_ok_elim hmac
  have hmac_len : (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length = 32 :=
    macHdrUnchecked_length F auth epoch _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hmac_at hres_at hmemcpy hnext ⊢
  subst hP
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
    Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx0 hx1 hx2 hx3 hx8 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
  rw [memRegion_4704_2400_split_macHdr sp]
  apply of_sepWP_lscro (mid := lsmpl.base 342) hinv; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_1
  refine call_lscro_calleeStack (x := ({
      outVec := sp + 4832#64, selfA := sp + 7136#64, g := g, auth := auth,
      ep := epoch, hdrRO := false, hdrA := hdr_ptr, hdr := (K.fromSeed seed).1.toList } : AuthMacHdrPinnedGhost))
    (s0 := s0) sp authMacHdrStackX (by decide)
    (T_pre := memRegion (sp + 4832#64) 24 ∗ authenticatorPinAt A g (sp + 7136#64) auth ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (T_post := fun _ => vecU8 A (sp + 4832#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
      authenticatorPinAt A g (sp + 7136#64) auth ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (F := authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 128 ∗ memRegion (sp + 4856#64) 2248 ∗
      memRegion (sp + 7104#64) 24 ∗ A.live hdr_ptr 64 1 ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
    (φ_pre := _) (φ_post := _) hmac_at hinv_1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 688#64) (by simp only [Reg.lr, arm64_norm, *])
    (by dsimp only [authMacHdrPinnedSpec]; rw [ChainProofs.bytesAt_false]; ac_rfl)
    (by simp only [hhdr_len, Reg.x8, Reg.x0, Reg.x1, Reg.x2, Reg.x3, wp_norm, arm64_norm, *])
    (by ac_rfl) (fun _ _ => rfl)
    (fun sf => authMacHdrPinned_onPanic_of_ok _ hmac _ sf)
    (by intro sf; dsimp only [authMacHdrPinnedSpec]; rw [ChainProofs.bytesAt_false]; ac_rfl) ?_
  intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 ⟨htr_sm1, _⟩ hinv_sm1
    hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    wp_norm, arm64_norm, *] at htr_sm1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  apply of_sepWP_lscro (mid := lsmpl.base 157) hinv_sm1
  refine SepWP.fold (vecU8_len32_expose (sp + 4832#64) _ hmac_len) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro mac_cap
  apply SepWP.exists_elim; intro mac_ptr
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hmac_cap_ge, hmac_cap_lt, hmac_ptr_ne, hmac_cap_b⟩ => ?_
  rw [authenticatorPinAt_eq_inline_heap A g (sp + 7136#64) auth,
      memRegion_104_eq_words13 (sp + 4080#64),
      memRegion_128_eq_words16 (sp + 4704#64),
      memRegion_24_eq_words3 (sp + 7104#64)]
  wp_conv_pre =>
    dsimp only [authInlineWordsAt, words16At, words8At]
    simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 32 (apply SepWP.exists_elim; intro _)
  wp_steps
  have hfold_pre_res :
      authInlineWordsAt g (sp + 4080#64) auth ∗
      ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
      ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
      ((sp + 4176#64) ↦₆₄ epoch) ∗
      words16At (sp + 4704#64)
        g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
        g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
      (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
      memRegion (sp + 4856#64) 2248 ⊢
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      memRegion (sp + 4704#64) 2400 := by
    have h128 := words16At_entails_memRegion (sp + 4704#64)
      g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
      g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
      1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64
    have h24 := words3_entails_memRegion (sp + 4832#64) mac_cap mac_ptr 32#64
    rw [show (sp + 4832#64) + 8#64 = sp + 4840#64 by bv_omega,
        show (sp + 4832#64) + 16#64 = sp + 4848#64 by bv_omega] at h24
    have hlhs :
        authInlineWordsAt g (sp + 4080#64) auth ∗
        ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
        ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
        ((sp + 4176#64) ↦₆₄ epoch) ∗
        words16At (sp + 4704#64)
          g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
          g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
          1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
        (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
        memRegion (sp + 4856#64) 2248 =
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        words16At (sp + 4704#64)
          g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
          g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
          1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
        (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
        memRegion (sp + 4856#64) 2248 := by
      dsimp only [ekSentInlineWordsAt]
      simp only [BitVec.add_assoc, arm64_norm]
    rw [hlhs, memRegion_4704_2400_split_macHdr sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h128 (sepConj_mono h24 (Entails.refl _)))
  refine SepWP.fold hfold_pre_res
    (by
      (conv => rhs; arg 1; dsimp only [authInlineWordsAt, words16At, words8At]; simp only [BitVec.add_assoc, arm64_norm])
      sep_focus) ?_
  clear hfold_pre_res
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_2
  refine call_lscro_calleeStack (x := ({
      v := sp + 7104#64, cap := 64#64, ptr := hdr_ptr,
      bs := (K.fromSeed seed).1.toList, additional := 32 } : DoReserveCall))
    (s0 := s0) sp doReserve32Stack (by decide)
    (T_pre := ((sp + 7104#64) ↦₆₄ 64#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr) ∗
      A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool)
    (T_post := fun _ => (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ p') ∗
      A.live p' 128 1 ∗ (p' ↦ₛ (K.fromSeed seed).1.toList) ∗
      memRegion (p' + 64#64) 64) ∗ A.pool)
    (F := authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      memRegion (sp + 4704#64) 2400 ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live mac_ptr mac_cap.toNat 1 ∗
      (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
    (φ_pre := _) (φ_post := _) hres_at hinv_2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_124).base + 11900#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by
      dsimp only [doReserve1Raw32Spec]
      have h64_ne : ((64#64 : BitVec 64) = 0#64) = False := propext (by decide)
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      simp only [hhdr_len, h64_ne, h64_toNat, ↓reduceIte, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp,
        show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc]
      ac_rfl)
    (by
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      have hhdr_ne' : hdr_ptr ≠ 0#64 := hhdr_ne
      simp only [hhdr_len, h64_toNat, reserveCap_64_64_32,
        Reg.x0, Reg.x1, Reg.x2, hhdr_ne', ne_eq, not_false_eq_true, wp_norm, arm64_norm, *])
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (by
      intro sf
      dsimp only [doReserve1Raw32Spec]
      have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
      simp only [hhdr_len, h64_toNat, reserveCap_64_64_32,
        show BitVec.ofNat 64 128 = 128#64 from rfl,
        show BitVec.ofNat 64 64 = 64#64 from rfl,
        show 128 - 64 = 64 from rfl,
        show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc]
      ac_rfl) ?_
  intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
    hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
  simp only [wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
  apply of_sepWP_lscro (mid := (blkPl_124).base + 2588#64) hinv_sm2
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro hdr_ptr'
  refine SepWP.fold (Entails.refl ⌜hdr_ptr' ≠ 0#64⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_ptr'_ne => ?_
  have hsplit_64 :
      memRegion (hdr_ptr' + 64#64) 64 =
      memRegion (hdr_ptr' + 64#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length ∗
      memRegion (hdr_ptr' + 96#64) 32 := by
    rw [hmac_len,
        ProofLib.memRegion_split' (b := hdr_ptr' + 64#64) (n := 32) (k := 32)
          (b' := hdr_ptr' + 96#64) rfl (by bv_omega) (by decide)]
  wp_conv_pre => rw [hsplit_64]
  wp_steps; wp_apply; wp_steps
  have hjoin_hdr_mac :
      (hdr_ptr' ↦ₛ (K.fromSeed seed).1.toList) ∗
      ((hdr_ptr' + 64#64) ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ⊢
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList)) := by
    rw [pointsToBytes_append, hhdr_len]
    exact Entails.refl _
  refine SepWP.fold hjoin_hdr_mac (by sep_focus) ?_
  refine finish_sepWP_lscro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (fun hinv_3 => hnext _ hdr_ptr' mac_cap mac_ptr hinv_3
      hhdr_ptr'_ne hmac_ptr_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (Entails.of_eq (by ac_rfl))

theorem polyNextChunkPlaced_onPanic_of_ok {A : RustAlloc} (x : PolyNextChunkGhost)
    (_h : x.enc.nextChunk = .ok (x.enc', x.chunk)) (s0 sf : State) :
    (polyNextChunkPlacedSpec A).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  dsimp only [polyNextChunkPlacedSpec, polyNextChunkSpec]

end CryptoVerification.SpqrV1.Top.Send
