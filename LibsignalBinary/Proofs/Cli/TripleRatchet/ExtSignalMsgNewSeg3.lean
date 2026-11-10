/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Statements
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes

/-!
# `<SignalMessage>::new` Segment 3 (`+0x3dc .. +0x5d8`)

Proves Phase 3 segment lemmas for `<SignalMessage>::new`: `compute_mac` and 8-byte MAC append,
ciphertext cloning, and deallocation of temporary ratchet-key and ciphertext buffers.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self
attribute [local simp]
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self

/-! ## `4K` Callee Discharges -/

private theorem new_shim_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      sessionShimSpec :=
  hA.shim_ok_at signalMessageNewName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

private theorem new_alloc_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at signalMessageNewName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

private theorem new_memcpy_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (withStack sessionMemcpyRegionSpec allocHookStack) :=
  hA.session_memcpy_region_ok_at signalMessageNewName
    (num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

private theorem new_dealloc_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at signalMessageNewName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

/-! ## `compute_mac` and 8-Byte MAC Append (`+0x3dc → +0x440`) -/

private theorem computeMac_inImage_ok_at_new_ext32 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName +
        bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") -
          (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img) := by
  rw [fnAddr_new_add_eq_ext (target := computeMacName)]
  exact h

section FnOffShieldComputeMac
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem new_compute_mac_and_append_wpp_ext32 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img))
    (x : SignalMessageNewGhost) (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1088#64)
      s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       A.pool ∗ stackAt (sp0 - 416#64) Statements.computeMacStackExt32)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗
          memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool ∗ stackAt (sp0 - 416#64) Statements.computeMacStackExt32))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29
  have hser6_bounds : 36 ≤ (x.serPrefix6 uuidTryParse).length ∧ (x.serPrefix6 uuidTryParse).length < 2 ^ 35 := by
    have ⟨_, _⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
    have := serPrefix6_length x
    omega
  have htotCap_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat =
        (x.serPrefix6 uuidTryParse).length + 8 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser6_toNat : (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length).toNat = (x.serPrefix6 uuidTryParse).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrem8 :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat -
        (x.serPrefix6 uuidTryParse).length = 8 := by omega
  have h176_8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_lin
  have h176_16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := by bv_lin
  rw [totCap_eq_serLen_add_8 x,
    vecU8At_eq_of_pos A (sp0 - 176#64)
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
      serPtr (x.serPrefix6 uuidTryParse) (by omega),
    hrem8, ProofLib.memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [NewMacAndBoxesCallees.pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  have hmac_call := computeMac_inImage_ok_at_new_ext32 hMac
  clear hMac
  new_fetches_range (img.base) (Rust.withPanics ext) 0x3dc 0x428
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  refine signalMessageNew_of_sepWP_inImage (entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))) hF hsym ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF1 hsym1
  refine SepWPp.call
    (x := ⟨sp0 - 152#64, x.senderIkA, x.senderIk, x.receiverIkA, x.receiverIk,
      x.macKeyA, x.macKey, serPtr, x.serPrefix6 uuidTryParse⟩)
    (F := ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 176#64) ↦₆₄ (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ∗
          A.live serPtr (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ wmac_dst))
    hmac_call (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [Spec.inImage, Mac.VerifyMacWithAddresses.computeMacSpecWithStack,
        allocFailedIn, State.trace_setPC, State.trace_writeReg64,
        arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    simp only [Spec.inImage, Mac.VerifyMacWithAddresses.computeMacSpecWithStack, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨by omega, ?_⟩
    exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [Spec.inImage, Mac.VerifyMacWithAddresses.computeMacSpecWithStack,
    okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  obtain ⟨macW, hmacW⟩ := exists_unpack64_of_length_8
    (signalMessageNew_computeMac_length C.F x.senderIk x.receiverIk x.macKey (x.serPrefix6 uuidTryParse))
  rw [hmacW, ← pointsTo64_eq_pointsToBytes (sp0 - 144#64) macW]
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [model_serialized_length, totCap_eq_serLen_add_8 x]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [hsp, arm64_norm]
    have hbox :
        A.live serPtr (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
           ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢
        boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized := by
      rw [htotCap_toNat, pointsTo64_eq_pointsToBytes, ← hmacW, ← pointsToBytes_append,
        ← model_serialized_eq]
      have hlen_ser := model_serialized_length C.F x
      have hser6_len := serPrefix6_length x
      have hne_nil := model_serialized_ne_nil C.F x
      unfold boxU8Buf
      simp only [hne_nil, ↓reduceIte, hser6_len, hlen_ser]
      refine Entails.pure_right ⟨hserPtr_ne, by omega⟩ (Entails.refl _)
    have hcells3 :=
      three_words_entails_cells3 (sp0 - 176#64)
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
        serPtr
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    rw [h176_8, h176_16] at hcells3
    have hmem16 :
        ((sp0 - 152#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((sp0 - 144#64) ↦₆₄ macW) ⊢
        memRegion (sp0 - 152#64) 16 := by
      rw [memRegion_16_eq_cells2 (sp0 - 152#64), bv_sub_add_lit sp0 152 8]
      exact sepConj_mono (Entails.sepExists_intro 0xFFFFFFFFFFFFFFFE#64)
        (Entails.sepExists_intro macW)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hcells3 (sepConj_mono hmem16 (sepConj_mono_left hbox)))))))))
    exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

end FnOffShieldComputeMac

/-! ## Clone `ciphertext` (`+0x440 → +0x46c / +0x55c`) -/

theorem new_ct_clone_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1088#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1132#64)
      s
      (((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          boxU8Buf A (sm.readReg64 .x25) x.ciphertext ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · have hct_nil : x.ciphertext = [] := by
      have h := congrArg BitVec.toNat hct0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    new_fetches_range b (Rust.withPanics ext) 0x440 0x440
    new_fetches_range b (Rust.withPanics ext) 0x554 0x558
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;> simp [hpq, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      simp only [hct_nil, ↓reduceIte, sepConj_emp, List.length_nil, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
    have hct_ne_nil : x.ciphertext ≠ [] := by
      intro h; simp [h] at hct_pos
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hct_beq : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hct0
    have hshim := new_shim_ok_4k hA
    have halloc := new_alloc_ok_4k hA
    have hmemcpy := new_memcpy_ok_4k hA
    have ho898 := @oom_at_898_ext b ext
    new_fetches_range b (Rust.withPanics ext) 0x440 0x468
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ()) (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp (config := { decide := true }) only [sessionShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [sessionShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    have hsp_align1 : sf1.spAligned = true := by
      rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.ciphertext.length, 1))
      (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align1)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp (config := { decide := true }) only [rustAllocSpec,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨hct_pos, ⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    have hsp_align2 : sf2.spAligned = true := by
      rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2200))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho898 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
        (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
              A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
              A.pool ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align2)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp (config := { decide := true }) only [withStack, sessionMemcpyRegionSpec,
          memcpyRegionSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
        exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      have hsp_align3 : sf3.spAligned = true := by
        rw [State.spAligned, hsp3]; simpa [State.spAligned, arm64_norm] using hsp_align2
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;> simp [hpq, arm64_norm]
      · refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simpa [State.spAligned, arm64_norm] using hsp_align3,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
      · unfold boxU8Buf
        have h25_eq : sf3.readReg64 (Reg.gpr 25#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hct_ne_nil, ↓reduceIte, h25_eq, hsp2, hsp1, hsp, arm64_norm]
        refine Entails.pure_right ⟨hoom, by omega⟩ ?_
        exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

/-! ## Deallocate Temporary Copies (`+0x5ac → +0x5d8`) -/

theorem new_dealloc_rk_and_ct_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1496#64)
      s
      (boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = pqCopyPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hdealloc := new_dealloc_ok_4k hA
  have hrk_len := publicKey_serialize_length x.senderRatchetKey
  have hrk_ne : x.senderRatchetKey.serialize ≠ [] := by
    intro h; rw [h] at hrk_len; simp at hrk_len
  unfold boxU8Buf
  simp only [hrk_ne, ↓reduceIte, hrk_len, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hrkPtr_ne, _⟩ => ?_
  have hpull_ct :
      A.live rkPtr 33 1 ∗
        (rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
        ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
        (if x.ciphertext = [] then emp
         else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
        ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
        ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
        ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
        A.pool ∗ stackAt (sp0 - 416#64) computeMacStack =
      ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
        (A.live rkPtr 33 1 ∗
         (rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
         (if x.ciphertext = [] then emp
          else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
         ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
         ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
         ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
         A.pool ∗ stackAt (sp0 - 416#64) computeMacStack) := by sep_focus
  rw [hpull_ct]
  clear hpull_ct
  refine SepWPp.pure_elim fun ⟨hctPtr_ne, _⟩ => ?_
  new_fetches_range b (Rust.withPanics ext) 0x5ac 0x5d4
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (rkPtr, 33, 1))
    (F := (if x.ciphertext = [] then emp
           else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          memRegion (sp0 - 416#64 - 4624#64) 528)
    hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hmem_rk := pointsToBytes_entails_memRegion rkPtr x.senderRatchetKey.serialize
    rw [hrk_len] at hmem_rk
    rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_rk)))
    exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hsp_align1 : sf1.spAligned = true := by
    rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · have hct_nil : x.ciphertext = [] := by
      have h := congrArg BitVec.toNat hct0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    simp only [hct_nil, ↓reduceIte, emp_sepConj]
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align1,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
      simp only [hsp, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
    have hct_ne_nil : x.ciphertext ≠ [] := by
      intro h; simp [h] at hct_pos
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_beq : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hct0
    simp only [hct_ne_nil, ↓reduceIte, sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (ctCopyPtr, x.ciphertext.length, 1))
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align1)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hmem_ct := pointsToBytes_entails_memRegion ctCopyPtr x.ciphertext
      simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_ct)))
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [rustDeallocSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hsp_align2 : sf2.spAligned = true := by
      rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
    apply SepWPp.of_sepWP_ret
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align2,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
      simp only [hsp1, hsp, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg3
