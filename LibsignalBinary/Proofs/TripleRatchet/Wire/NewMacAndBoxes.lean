/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue

import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
/-!
# `<SignalMessage>::new` Phase 3 (`+0x3dc .. +0x628`)

Proves MAC computation and 8-byte tag append, `ciphertext`/`pq_ratchet`/`addresses` boxing and
cloning, 120-byte `sret` packing, temporary buffer deallocation, and epilogue for
`<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem sp_sub_96_sub_56 (a : BitVec 64) : a - 96#64 - 56#64 = a - 152#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_sub_64 (a : BitVec 64) : a - 96#64 - 64#64 = a - 160#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_sub_72 (a : BitVec 64) : a - 96#64 - 72#64 = a - 168#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_sub_80 (a : BitVec 64) : a - 96#64 - 80#64 = a - 176#64 := by bv_lin

@[local simp, local arm64_norm]
theorem add_one_eq_zero_iff_noneCap (x : BitVec 64) :
    (x + 1#64 = 0#64) ↔ x = 0xFFFFFFFFFFFFFFFF#64 := by
  constructor
  · intro h
    calc x = (x + 1#64) - 1#64 := by bv_lin
      _ = 0xFFFFFFFFFFFFFFFF#64 := by rw [h]; rfl
  · rintro rfl; rfl

@[local simp, local arm64_norm]
theorem add_one_beq_zero_iff_noneCap (x : BitVec 64) :
    ((x + 1#64 == 0#64) = true) ↔ x = 0xFFFFFFFFFFFFFFFF#64 := by
  rw [beq_iff_eq, add_one_eq_zero_iff_noneCap]

@[local simp, local arm64_norm]
theorem add_one_bne_zero_iff_ne_noneCap (x : BitVec 64) :
    ((x + 1#64 != 0#64) = true) ↔ ¬(x = 0xFFFFFFFFFFFFFFFF#64) := by
  rw [bne_iff_ne, ne_eq, add_one_eq_zero_iff_noneCap]

namespace NewMacAndBoxesCallees

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem new_shim_ok_ext {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) noAllocShimSpec :=
  shim_ok_at2_ext hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_shim_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) noAllocShimSpec :=
  noAllocShim_ok_at (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustAllocSpec A) :=
  alloc_ok_at_norm_ext hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustAllocSpec A) :=
  alloc_ok_at_norm hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok_ext {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  memcpy_ok_at2_ext hA (name := signalMessageNewName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  framelessMemcpy_ok_at (name := signalMessageNewName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_dealloc_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustDeallocSpec A) :=
  dealloc_ok_at_norm hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem pull_pure_mid9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 Q : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ P9 ∗ ⌜φ⌝ ∗ Q =
      ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ P9 ∗ Q) := by ac_rfl

end NewMacAndBoxesCallees

/-! ## `compute_mac`, 8-byte MAC append, and inlined `into_boxed_slice` (`+0x3dc..+0x440`) -/

@[local simp, local arm64_norm]
theorem bv_add_8_sub_self (a : BitVec 64) : a + 8#64 - a = 8#64 := by bv_lin

theorem totCap_eq_serLen_add_8 (x : SignalMessageNewGhost) :
    BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8) =
      BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64 := by
  rw [← serPrefix6_length x, BitVec.ofNat_add]

theorem three_words_entails_cells3 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ cells a 3 := by
  rw [← memRegion_cells' a 24 3,
    memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) rfl rfl (by decide),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8) rfl
      (by bv_lin) (by decide),
    memRegion_eight a, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

theorem model_serialized_ne_nil (F : ShaCompress)
    (x : SignalMessageNewGhost) :
    (x.model F uuidTryParse).serialized ≠ [] := by
  intro h
  have hlen := model_serialized_length F x
  rw [h] at hlen
  simp at hlen

theorem new_compute_mac_and_append_wpp_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hMac : ComputeMacOkExt img C A ext)
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
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
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
    hrem8, memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [NewMacAndBoxesCallees.pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  have hmac_call := signalMessageNew_computeMac_inImage_ok_at_new_ext hMac
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
    (fun _ _ R' hm => by
      simpa only [Spec.inImage, computeMacSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
        arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    simp only [Spec.inImage, computeMacSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨by omega, ?_⟩
    exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [Spec.inImage, computeMacSpec, okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
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

theorem new_compute_mac_and_append_wpp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hMac : ComputeMacOk img C A ctl abs)
    (x : SignalMessageNewGhost) (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr signalMessageNewName + 988#64)
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
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr signalMessageNewName + 1088#64)
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
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_compute_mac_and_append_wpp_ext hMac x sp0 serPtr addrCap hct_bound hpq_bound s
    hF hsym hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29

/-! ## Clone `ciphertext` (`+0x440..+0x468 / +0x554..+0x558`) -/

theorem new_ct_clone_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
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
    have hshim := NewMacAndBoxesCallees.new_shim_ok_ext hA
    have halloc := NewMacAndBoxesCallees.new_alloc_ok_ext hA
    have hmemcpy := NewMacAndBoxesCallees.new_memcpy_ok_ext hA
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
      simp (config := { decide := true }) only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [noAllocShimSpec]
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
      simp (config := { decide := true }) only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
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
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align2)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp (config := { decide := true }) only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [framelessMemcpySpec, sepConj_assoc]
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

theorem new_ct_clone_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1088#64)
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
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1132#64)
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
      (PanicAllocPost s) :=
  new_ct_clone_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 serPtr serLen addrCap
    hct_bound s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx26 hx27 hx28 hx29

/-! ## Clone `pq_ratchet` (`+0x46c..+0x494 / +0x55c..+0x564`) -/

section FnOffShieldClone
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem new_pq_clone_wpp_opt {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hbnd : hookStack + 528 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (memcpySpecWithStack hookStack)))
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hinv : OptCallInv oimg s)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if addrCap = noneCap then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) (hookStack + 528)))
      (PanicAllocPost s) := by
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_nil : x.pqRatchet = [] := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    new_fetches_range b (Rust.withPanics ext) 0x55c 0x564
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases had : addrCap = noneCap <;> simp_all [noneCap, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      simp only [hpq_nil, ↓reduceIte, sepConj_emp, List.length_nil, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hpq0
    have hpq_ne_nil : x.pqRatchet ≠ [] := by
      intro h; simp [h] at hpq_pos
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)

    have ho858 := @oom_at_858_ext b ext
    new_fetches_range b (Rust.withPanics ext) 0x46c 0x494
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv0
    refine signalMessageNew_call_opt (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ A.pool ∗
            memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
      hinv0 hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [signalMessageNew_stackAt_split_bottom (sp0 - 416#64) hookStack 528 hbnd] at hm
      simp (config := { decide := true }) only [shimSpecWithStack, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hinv1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [shimSpecWithStack, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    have hsp_align1 : sf1.spAligned = true := by
      rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv1'
    refine signalMessageNew_call_opt (x := (x.pqRatchet.length, 1))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
      hinv1' halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align1)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp (config := { decide := true }) only [rustAllocSpecWithStack, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hinv2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    have hsp_align2 : sf2.spAligned = true := by
      rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpecWithStack, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2136))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho858 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpecWithStack, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv2
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hinv2'
      refine signalMessageNew_call_opt (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
        (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
              A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
              A.pool ∗
              memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
        hinv2' hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align2)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp (config := { decide := true }) only [memcpySpecWithStack, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 _ hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [memcpySpecWithStack, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      have hsp_align3 : sf3.spAligned = true := by
        rw [State.spAligned, hsp3]; simpa [State.spAligned, arm64_norm] using hsp_align2
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases had : addrCap = noneCap <;> simp_all [noneCap, arm64_norm]
      · refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simpa [State.spAligned, arm64_norm] using hsp_align3,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      · unfold boxU8Buf
        have h23_eq : sf3.readReg64 (Reg.gpr 23#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [signalMessageNew_stackAt_split_bottom (sp0 - 416#64) hookStack 528 hbnd]
        simp only [hpq_ne_nil, ↓reduceIte, h23_eq, hsp2, hsp1, hsp, arm64_norm]
        refine Entails.pure_right ⟨hoom, by omega⟩ ?_
        exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)


end FnOffShieldClone

theorem new_pq_clone_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if addrCap = noneCap then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_pq_clone_wpp_opt (oimg := none) (hookStack := allocHookStack) (by decide)
    (shim_opt_of_base hA (by fnoff_eq))
    (alloc_opt_of_base hA (by fnoff_eq))
    (memcpy_opt_of_base hA (by fnoff_eq))
    x sp0 serPtr serLen ctBoxPtr addrCap hpq_bound s trivial
    hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_pq_clone_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (if addrCap = noneCap then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_pq_clone_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 serPtr serLen ctBoxPtr
    addrCap hpq_bound s hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## `addresses` inlined `into_boxed_slice` (`+0x498..+0x4a0 / +0x568..+0x56c → +0x578`) -/

/-- Heap ownership of `addresses: Option<Box<[u8]>>` before its `(ptr, len)` header is stored at
`ret + 0x58`: `ptr = 0` on `none`, and `len = 36 = ad.length` with `boxU8Buf A ptr ad` on `some ad`. -/
def optAddrBoxBuf (A : RustAlloc) (ptr len : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => ⌜ptr = 0#64⌝ ∗ emp
  | some ad => ⌜len = BitVec.ofNat 64 ad.length ∧ ad.length = 36⌝ ∗ boxU8Buf A ptr ad

theorem optBoxU8At_of_optAddrBoxBuf (A : RustAlloc) (a ptr len : BitVec 64)
    (o : Option (List (BitVec 8))) :
    (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗ optAddrBoxBuf A ptr len o ⊢
      optBoxU8At A a ptr o := by
  cases o with
  | none =>
    simp only [optAddrBoxBuf, optBoxU8At, sepConj_emp]
    rw [show ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗ ⌜ptr = 0#64⌝) =
      (⌜ptr = 0#64⌝ ∗ ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len))) by sep_focus]
    refine Entails.pure_left fun hptr => ?_
    subst hptr
    exact sepConj_mono_right (pointsTo64_entails_memRegion (a + 8#64) len)
  | some ad =>
    simp only [optAddrBoxBuf, optBoxU8At]
    rw [show ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗
        (⌜len = BitVec.ofNat 64 ad.length ∧ ad.length = 36⌝ ∗ boxU8Buf A ptr ad)) =
      (⌜len = BitVec.ofNat 64 ad.length ∧ ad.length = 36⌝ ∗
        ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗ boxU8Buf A ptr ad)) by sep_focus]
    refine Entails.pure_left fun ⟨hlen, _⟩ => ?_
    subst hlen
    rw [boxU8At_eq_boxU8Buf]
    exact Entails.refl _

theorem new_addr_into_boxed_wp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr pqBoxPtr addrCap : BitVec 64)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc =
      (if addrCap = noneCap then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1176#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1400#64)
      s
      (optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse))
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = pqBoxPtr ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          cells (sp0 - 216#64) 3 ∗
          optAddrBoxBuf A (sm.readReg64 .x0) (sm.readReg64 .x20) (x.addresses uuidTryParse))) := by
  have h216_8 : sp0 - 216#64 + 8#64 = sp0 - 208#64 := by bv_lin
  have h216_16 : sp0 - 216#64 + 16#64 = sp0 - 200#64 := by bv_lin
  cases had : x.addresses uuidTryParse with
  | none =>
    simp only [had, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at haddrCap
    subst haddrCap
    simp only [↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_none_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => ?_
    new_fetches_range b (Rust.withPanics ext) 0x568 0x56c
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, sepConj_emp, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) noneCap w1 w0
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ hc3
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  | some ad =>
    have had_len := addresses_length had
    simp only [had, Option.isSome_some, ↓reduceIte] at haddrCap
    subst haddrCap
    have h36_ne : (36#64 = noneCap) = False := by decide
    simp only [h36_ne, ↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_some_eq A (sp0 - 216#64) had_len]
    refine SepWP.exists_elim fun addrPtr => ?_
    rw [h216_8, h216_16]
    new_fetches_range b (Rust.withPanics ext) 0x498 0x4a0
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, had_len, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) 36#64 addrPtr 36#64
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ (sepConj_mono_left hc3)
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_addr_into_boxed_wp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr pqBoxPtr addrCap : BitVec 64)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc =
      (if addrCap = noneCap then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1176#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1400#64)
      s
      (optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse))
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = pqBoxPtr ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          cells (sp0 - 216#64) 3 ∗
          optAddrBoxBuf A (sm.readReg64 .x0) (sm.readReg64 .x20) (x.addresses uuidTryParse))) :=
  new_addr_into_boxed_wp_ext x sp0 serPtr serLen ctBoxPtr pqBoxPtr addrCap haddrCap s
    hpc hrun hsp hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## 120-byte `sret` stores (`+0x578..+0x5a8 → +0x5ac`) -/

@[local simp, local arm64_norm]
theorem append64_extract_lo (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
@[local simp, local arm64_norm]
theorem append64_extract_hi (lo hi : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
@[local simp, local arm64_norm]
theorem zeroExtend32_truncate8_eq (v : BitVec 32) :
    (v.zeroExtend 64).truncate 8 = v.setWidth 8 := by bv_bits

theorem sret_cells_entails_signalMessageAt (F : ShaCompress) (A : RustAlloc)
    (x : SignalMessageNewGhost) (serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen : BitVec 64)
    (rk0 rk1 rk2 rk3 : BitVec 64)
    (hrk_eq : ∀ a : BitVec 64, (a ↦ₛ x.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32) :
    boxU8Buf A pqBoxPtr x.pqRatchet ∗
      boxU8Buf A ctBoxPtr x.ciphertext ∗
      boxU8Buf A serPtr (x.model F uuidTryParse).serialized ∗
      optAddrBoxBuf A addrBoxPtr addrBoxLen (x.addresses uuidTryParse) ∗
      (x.ret ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
      ((x.ret + 8#64) ↦₆₄ pqBoxPtr) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
      ((x.ret + 24#64) ↦₆₄ ctBoxPtr) ∗
      ((x.ret + 32#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
      ((x.ret + 40#64) ↦₆₄ serPtr) ∗
      ((x.ret + 48#64) ↦₆₄ BitVec.ofNat 64 (x.model F uuidTryParse).serialized.length) ∗
      ((x.ret + 56#64) ↦₆₄ rk0) ∗
      ((x.ret + 64#64) ↦₆₄ rk1) ∗
      ((x.ret + 72#64) ↦₆₄ rk2) ∗
      ((x.ret + 80#64) ↦₆₄ rk3) ∗
      ((x.ret + 88#64) ↦₆₄ addrBoxPtr) ∗
      ((x.ret + 96#64) ↦₆₄ addrBoxLen) ∗
      ((x.ret + 104#64) ↦₃₂ x.counter) ∗
      ((x.ret + 108#64) ↦₃₂ x.previousCounter) ∗
      ((x.ret + 112#64) ↦₈ x.messageVersion) ∗
      memRegion (x.ret + 113#64) 7 ⊢
    ∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model F uuidTryParse) := by
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
  have hser_len := model_serialized_length F x
  refine Entails.trans ?_
    (Entails.sepExists_intro
      ⟨BitVec.ofNat 64 x.pqRatchet.length, pqBoxPtr, ctBoxPtr, serPtr, addrBoxPtr⟩)
  unfold signalMessageAt
  have hmod_pq : (x.model F uuidTryParse).pqRatchet = x.pqRatchet := rfl
  have hmod_ct : (x.model F uuidTryParse).ciphertext = x.ciphertext := rfl
  have hmod_rk : (x.model F uuidTryParse).senderRatchetKey = x.senderRatchetKey := rfl
  have hmod_ad : (x.model F uuidTryParse).addresses = x.addresses uuidTryParse := rfl
  have hmod_cnt : (x.model F uuidTryParse).counter = x.counter := rfl
  have hmod_pcnt : (x.model F uuidTryParse).previousCounter = x.previousCounter := rfl
  have hmod_ver : (x.model F uuidTryParse).messageVersion = x.messageVersion := rfl
  rw [hmod_pq, hmod_ct, hmod_rk, hmod_ad, hmod_cnt, hmod_pcnt, hmod_ver,
    vecU8At_exact_eq_boxU8Buf A x.ret pqBoxPtr x.pqRatchet (by omega),
    boxU8At_eq_boxU8Buf A (x.ret + 0x18#64) ctBoxPtr x.ciphertext,
    boxU8At_eq_boxU8Buf A (x.ret + 0x28#64) serPtr (x.model F uuidTryParse).serialized,
    hrk_eq (x.ret + 0x38#64)]
  simp only [arm64_norm]
  have hpure_bounds :
      macLength + 1 ≤ (x.model F uuidTryParse).serialized.length ∧
      (x.model F uuidTryParse).serialized.length < 2 ^ 40 ∧
      x.ciphertext.length < 2 ^ 40 ∧
      x.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, x.addresses uuidTryParse = some ad → ad.length < 2 ^ 40) := by
    refine ⟨by unfold macLength; omega, by omega, by omega, by omega, fun ad had => ?_⟩
    have := addresses_length had
    omega
  have had_ent := optBoxU8At_of_optAddrBoxBuf A (x.ret + 88#64) addrBoxPtr addrBoxLen (x.addresses uuidTryParse)
  simp only [arm64_norm] at had_ent
  refine Entails.pure_right hpure_bounds ?_
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left had_ent)))))))))))))))
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_sret_stores_wp_ext {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : SignalMessageNewGhost)
    (sp0 serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen : BitVec 64) (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1400#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = addrBoxPtr)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = addrBoxLen)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1452#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       boxU8Buf A pqBoxPtr x.pqRatchet ∗
       boxU8Buf A ctBoxPtr x.ciphertext ∗
       boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized ∗
       optAddrBoxBuf A addrBoxPtr addrBoxLen (x.addresses uuidTryParse) ∗
       memRegion x.ret 120)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)))) := by
  new_fetches_range b (Rust.withPanics ext) 0x578 0x5a8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_eq⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.senderRatchetKey.bytes)
  rw [hrk_eq x.senderRatchetKeyA, memRegion_sret_120 x.ret]
  simp only [cells, sepConj_emp, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simpa [State.spAligned, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [← sepExists_sepConj_right]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sret_cells_entails_signalMessageAt C.F A x serPtr ctBoxPtr pqBoxPtr
          addrBoxPtr addrBoxLen rk0 rk1 rk2 rk3 hrk_eq hct_bound hpq_bound))))))))

theorem new_sret_stores_wp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (x : SignalMessageNewGhost)
    (sp0 serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen : BitVec 64) (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1400#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = addrBoxPtr)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = addrBoxLen)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1452#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       boxU8Buf A pqBoxPtr x.pqRatchet ∗
       boxU8Buf A ctBoxPtr x.ciphertext ∗
       boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized ∗
       optAddrBoxBuf A addrBoxPtr addrBoxLen (x.addresses uuidTryParse) ∗
       memRegion x.ret 120)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)))) :=
  new_sret_stores_wp_ext x sp0 serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen verW32
    hver hct_bound hpq_bound s hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Deallocate temporaries and epilogue (`+0x5ac..+0x628`) -/

theorem new_dealloc_rk_and_ct_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
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
  have hdealloc := NewMacAndBoxesCallees.new_dealloc_ok_ext hA
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

theorem new_dealloc_rk_and_ct_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1496#64)
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
      (PanicAllocPost s) :=
  new_dealloc_rk_and_ct_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 rkPtr ctCopyPtr
    pqCopyPtr hct_bound s hpc hrun hsp hsp_align hx19 hx21 hx29

/-- Stack slots in `sp0 - 416#64 .. sp0 - 96#64` other than `(sp0 - 320#64) ↦₆₄ pqCap`. -/
def newFrameRest (sp0 : BitVec 64) : SepProp :=
  newUnusedPad sp0 ∗
  cells (sp0 - 408#64) 3 ∗
  (∃∗ w384 : BitVec 32, (sp0 - 384#64) ↦₃₂ w384) ∗
  (∃∗ w380 : BitVec 32, (sp0 - 380#64) ↦₃₂ w380) ∗
  cells (sp0 - 376#64) 5 ∗
  (∃∗ w332 : BitVec 32, (sp0 - 332#64) ↦₃₂ w332) ∗
  (∃∗ w328 : BitVec 64, (sp0 - 328#64) ↦₆₄ w328) ∗
  memRegion (sp0 - 312#64) 24 ∗
  cells (sp0 - 288#64) 12 ∗
  (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
  (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
  (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
  (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
  cells (sp0 - 176#64) 3 ∗
  memRegion (sp0 - 152#64) 16

theorem cells2_sub_328 (sp0 pqCap : BitVec 64) :
    (∃∗ w328 : BitVec 64, (sp0 - 328#64) ↦₆₄ w328) ∗ ((sp0 - 320#64) ↦₆₄ pqCap) ⊢
    cells (sp0 - 328#64) 2 := by
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 328#64 + 8#64 = sp0 - 320#64 by bv_lin]
  exact sepConj_mono_right (Entails.sepExists_intro pqCap)

theorem newSavedRegs_entails_cells12 (sp0 : BitVec 64) (s0 : State) :
    newSavedRegs sp0 s0 ⊢ cells (sp0 - 96#64) 12 := by
  unfold newSavedRegs
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 96#64 + 8#64 = sp0 - 88#64 by bv_lin,
    show sp0 - 88#64 + 8#64 = sp0 - 80#64 by bv_lin,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
      (sepConj_mono (Entails.sepExists_intro _)
        (sepConj_mono (Entails.sepExists_intro _)
          (sepConj_mono (Entails.sepExists_intro _)
            (sepConj_mono (Entails.sepExists_intro _)
              (sepConj_mono (Entails.sepExists_intro _)
                (sepConj_mono (Entails.sepExists_intro _)
                  (sepConj_mono (Entails.sepExists_intro _)
                    (sepConj_mono (Entails.sepExists_intro _)
                      (sepConj_mono (Entails.sepExists_intro _)
                        (Entails.sepExists_intro _)))))))))))

theorem newFrameRest_entails_stackAt (sp0 pqCap : BitVec 64) (s0 : State) :
    stackAt (sp0 - 416#64) computeMacStack ∗
      newFrameRest sp0 ∗
      ((sp0 - 320#64) ↦₆₄ pqCap) ∗
      newSavedRegs sp0 s0 ⊢
    stackAt sp0 signalMessageNewStack := by
  rw [stackAt_signalMessageNewStack_split sp0]
  unfold newFrameRest
  have hc2 := cells2_sub_328 sp0 pqCap
  have hc12 := newSavedRegs_entails_cells12 sp0 s0
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hc2
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              hc12))))))))))))))))
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem newFrameRest_entails_stackAtX (sp0 pqCap : BitVec 64) (s0 : State) :
    stackAt (sp0 - 416#64) computeMacStackX ∗
      newFrameRest sp0 ∗
      ((sp0 - 320#64) ↦₆₄ pqCap) ∗
      newSavedRegs sp0 s0 ⊢
    stackAt sp0 signalMessageNewStackX := by
  rw [stackAt_signalMessageNewStackX_split sp0]
  unfold newFrameRest
  have hc2 := cells2_sub_328 sp0 pqCap
  have hc12 := newSavedRegs_entails_cells12 sp0 s0
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hc2
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              hc12))))))))))))))))
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)


section FnOffShieldDeallocPq
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem stackAt_signalMessageNewGen_to_hook (sp0 : BitVec 64) (hookStack : Nat)
    (hbnd : hookStack + 944 ≤ 2 ^ 64) :
    stackAt sp0 ((hookStack + 528) + 416) =
      memRegion (sp0 - BitVec.ofNat 64 (hookStack + 944)) 944 ∗ stackAt sp0 hookStack :=
  signalMessageNew_stackAt_split_bottom' sp0 ((hookStack + 528) + 416) hookStack 944 (by omega) hbnd

theorem new_dealloc_pq_and_epilogue_wpp_opt {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {hookStack : Nat} {sp0 : BitVec 64} {s0 : State}
    (hbnd : hookStack + 944 ≤ 2 ^ 64)
    (hst_entails : ∀ pqCap : BitVec 64,
      stackAt (sp0 - 416#64) (hookStack + 528) ∗
        newFrameRest sp0 ∗
        ((sp0 - 320#64) ↦₆₄ pqCap) ∗
        newSavedRegs sp0 s0 ⊢
      stackAt sp0 ((hookStack + 528) + 416))
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack)))
    (x : SignalMessageNewGhost) (pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hinv : OptCallInv oimg s)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (s0.readReg64 .lr)
      s
      (optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp ((hookStack + 528) + 416)))
      (PanicAllocPost s) := by
  have hsp_cancel : sp0 - 416#64 + 416#64 = sp0 := BitVec.sub_add_cancel sp0 416#64
  unfold optPqBuf
  by_cases hpq : x.pqRatchet.isEmpty = true
  · simp only [hpq, ↓reduceIte, sepConj_emp]
    refine SepWPp.pure_elim fun hpqCap => ?_
    subst hpqCap
    unfold newSavedRegs
    new_fetches_range b (Rust.withPanics ext) 0x5d8 0x5e0
    new_fetches_range b (Rust.withPanics ext) 0x60c 0x628
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0]
      have hst := hst_entails noneCap
      unfold newSavedRegs at hst
      refine Entails.trans ?_ (sepConj_mono_right hst)
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun hpq_pure => ?_
    rcases hpq_pure with ⟨hpqCap, hpq_pos, hpq_lt, hpqPtr_ne⟩
    subst hpqCap
    have hpqCap_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpqCap_ne : ¬(BitVec.ofNat 64 x.pqRatchet.length = 0xFFFFFFFFFFFFFFFF#64) := by
      intro h; rw [h] at hpqCap_toNat; simp at hpqCap_toNat; omega
    unfold newSavedRegs
    new_fetches_range b (Rust.withPanics ext) 0x5d8 0x608
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv0
    refine signalMessageNew_call_opt (x := (pqCopyPtr, x.pqRatchet.length, 1))
      (ret_pc := s0.readReg64 .lr)
      (F := memRegion (sp0 - (BitVec.ofNat 64 (hookStack + 944))) 944)
      hinv0 hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
      (by simp only [wp_norm, arm64_norm, *]) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hst := hst_entails (BitVec.ofNat 64 x.pqRatchet.length)
      unfold newSavedRegs at hst
      rw [stackAt_signalMessageNewGen_to_hook sp0 hookStack hbnd,
        sepConj_comm (memRegion (sp0 - (BitVec.ofNat 64 (hookStack + 944))) 944)] at hst
      have hmem_pq := pointsToBytes_entails_memRegion pqCopyPtr x.pqRatchet
      simp (config := { decide := true }) only [rustDeallocExternSpecWithStack, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      rw [← sepConj_assoc (stackAt sp0 hookStack)]
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_pq (sepConj_mono_left hst))))
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
    intro sf _ hpcf hrunf hspf hcsf
    rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f⟩
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, stackAt_signalMessageNewGen_to_hook sp0 hookStack hbnd]
      simp only [wp_norm, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)


end FnOffShieldDeallocPq

theorem new_dealloc_pq_and_epilogue_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (s0.readReg64 .lr)
      s
      (optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s) :=
  new_dealloc_pq_and_epilogue_wpp_opt (oimg := none) (hookStack := allocHookStack) (by decide)
    (fun c => newFrameRest_entails_stackAt sp0 c s0)
    (dealloc_opt_of_base hA (by fnoff_eq))
    x pqCap pqCopyPtr hpq_bound s trivial
    hpc hrun hsp hsp0 hsp0_align hsp_align hx20 htr

theorem new_dealloc_pq_and_epilogue_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (s0.readReg64 .lr)
      s
      (optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s) :=
  new_dealloc_pq_and_epilogue_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 pqCap
    pqCopyPtr hpq_bound s0 s hpc hrun hsp hsp0 hsp0_align hsp_align hx20 htr

/-! ## Combined Phase 3 (`+0x3dc..+0x628`) -/

theorem signalMessageNew_seg3_seq_wpp' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : TraceVRegsEq s s0)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr.1] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_seg3_seq_wp' {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hoom⟩⟩
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem five_words_entails_cells5 (sp0 w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp0 - 376#64) ↦₆₄ w0) ∗
      ((sp0 - 368#64) ↦₆₄ w1) ∗
      ((sp0 - 360#64) ↦₆₄ w2) ∗
      ((sp0 - 352#64) ↦₆₄ w3) ∗
      ((sp0 - 344#64) ↦₆₄ w4) ⊢
    cells (sp0 - 376#64) 5 := by
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 376#64 + 8#64 = sp0 - 368#64 by bv_lin,
    show sp0 - 368#64 + 8#64 = sp0 - 360#64 by bv_lin,
    show sp0 - 360#64 + 8#64 = sp0 - 352#64 by bv_lin,
    show sp0 - 352#64 + 8#64 = sp0 - 344#64 by bv_lin]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1)
      (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono (Entails.sepExists_intro w3)
          (Entails.sepExists_intro w4))))

theorem cells9_cells3_eq_cells12 (sp0 : BitVec 64) :
    cells (sp0 - 288#64) 9 ∗ cells (sp0 - 216#64) 3 = cells (sp0 - 288#64) 12 := by
  rw [← memRegion_cells' (sp0 - 288#64) 72 9, ← memRegion_cells' (sp0 - 216#64) 24 3,
    ← memRegion_split' (b := sp0 - 288#64) (b' := sp0 - 216#64) (n := 72) (k := 24)
      rfl (bv_sub_add_lit sp0 288 72).symm (by decide),
    memRegion_cells' (sp0 - 288#64) 96 12]

theorem entails_newFrameRest (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (w384 w380 w332 : BitVec 32)
    (w400 w376 w368 w360 w352 w328 : BitVec 64) :
    newUnusedPad sp0 ∗
      (((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ w400) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr)) ∗
      ((sp0 - 384#64) ↦₃₂ w384) ∗
      ((sp0 - 380#64) ↦₃₂ w380) ∗
      (((sp0 - 376#64) ↦₆₄ w376) ∗
       ((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr)) ∗
      ((sp0 - 332#64) ↦₃₂ w332) ∗
      ((sp0 - 328#64) ↦₆₄ w328) ∗
      memRegion (sp0 - 312#64) 24 ∗
      (cells (sp0 - 288#64) 9 ∗ cells (sp0 - 216#64) 3) ∗
      (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
      (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
      (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
      (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
      cells (sp0 - 176#64) 3 ∗
      memRegion (sp0 - 152#64) 16 ⊢
    newFrameRest sp0 := by
  unfold newFrameRest
  rw [cells9_cells3_eq_cells12 sp0]
  have hc3 := three_words_entails_cells3 (sp0 - 408#64) rkPtr w400 pqCopyPtr
  rw [bv_sub_add_lit sp0 408 8, show (sp0 - 408#64 + 16#64) = sp0 - 392#64 by bv_lin] at hc3
  have hc5 := five_words_entails_cells5 sp0 w376 w368 w360 w352 ctCopyPtr
  exact sepConj_mono_right
    (sepConj_mono hc3
      (sepConj_mono (Entails.sepExists_intro w384)
        (sepConj_mono (Entails.sepExists_intro w380)
          (sepConj_mono hc5
            (sepConj_mono (Entails.sepExists_intro w332)
              (sepConj_mono_left (Entails.sepExists_intro w328)))))))

theorem new_phase3_wpp_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hMac : ComputeMacOkExt img C A ext)
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool ∗
          stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s0) := by
  refine signalMessageNew_seg3_seq_wpp' htr
    (new_compute_mac_and_append_wpp_ext hMac x sp0 serPtr addrCap hct_bound hpq_bound s
      hF hsym hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  refine signalMessageNew_seg3_seq_wpp' htr1'
    (new_ct_clone_wpp_ext hA x sp0 serPtr (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine signalMessageNew_seg3_seq_wpp' htr2'
    (new_pq_clone_wpp_ext hA x sp0 serPtr (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound s2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wp'
    (new_addr_into_boxed_wp_ext x sp0 serPtr (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine signalMessageNew_seg3_seq_wp'
    (new_sret_stores_wp_ext x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine signalMessageNew_seg3_seq_wpp' htr5'
    (new_dealloc_rk_and_ct_wpp_ext hA x sp0 rkPtr ctCopyPtr pqCopyPtr hct_bound s5
      hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine signalMessageNew_seg3_seq_wpp' htr6'
    (new_dealloc_pq_and_epilogue_wpp_ext hA x sp0 pqCap pqCopyPtr hpq_bound s0 s6
      hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6')
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_phase3_wpp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hMac : ComputeMacOk img C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr signalMessageNewName + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool ∗
          stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s0) :=
  new_phase3_wpp_ext (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA) hMac x sp0 serPtr rkPtr
    ctCopyPtr pqCap pqCopyPtr addrCap verW32 hver haddrCap hct_bound hpq_bound s0 s hF hsym hpc
    hrun hsp hsp0 hsp0_align hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29 htr


theorem signalMessageNew_seg3_seq_wpp_inImage' {prog : Program} {mid ret : BitVec 64} {img : Obj.Image} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : TraceVRegsEq s s0) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → img.FrozenLoaded sm → sm.symtab = img.symtab → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr.1] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_seg3_seq_wp_inImage' {prog : Program} {mid ret : BitVec 64} {img : Obj.Image} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → img.FrozenLoaded sm → sm.symtab = img.symtab → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  rcases h1.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hoom⟩⟩
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim


theorem new_pq_clone_wpp_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1372#64
       else
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (if addrCap = noneCap then
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1384#64
       else
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX))
      (PanicAllocPost s) :=
  new_pq_clone_wpp_opt (oimg := some img) (hookStack := extHookStack) (by decide)
    (shim_opt_of_x hA (by fnoff_eq))
    (alloc_opt_of_x hA (by fnoff_eq))
    (memcpy_opt_of_x hA (by fnoff_eq))
    x sp0 serPtr serLen ctBoxPtr addrCap hpq_bound s ⟨hF, hsym⟩
    hpc hrun hsp hsp_align hx19 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_dealloc_pq_and_epilogue_wpp_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .lr)
      s
      (optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStackX)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp signalMessageNewStackX))
      (PanicAllocPost s) :=
  new_dealloc_pq_and_epilogue_wpp_opt (oimg := some img) (hookStack := extHookStack) (by decide)
    (fun c => newFrameRest_entails_stackAtX sp0 c s0)
    (dealloc_opt_of_x hA (by fnoff_eq))
    x pqCap pqCopyPtr hpq_bound s ⟨hF, hsym⟩
    hpc hrun hsp hsp0 hsp0_align hsp_align hx20 htr


theorem new_compute_mac_and_append_wpp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec C.F A)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
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
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1088#64)
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
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
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
    hrem8, memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [NewMacAndBoxesCallees.pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 60) hcl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl0
  refine signalMessageNew_call_placed
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
    hcl0 hMac (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ R' hm => by
      simpa only [computeMacSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
        arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    simp only [computeMacSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨by omega, ?_⟩
    exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [computeMacSpec, okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
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

theorem new_ct_clone_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1088#64)
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
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64)
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
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have ho898 := @oom_at_898_placed _ H h_panic2
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
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
      simp (config := { decide := true }) only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    have hsp_align1 : sf1.spAligned = true := by
      rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
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
      simp (config := { decide := true }) only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    have hsp_align2 : sf2.spAligned = true := by
      rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_63).base + 2200#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho898 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
        (F := ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
              A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align2)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp (config := { decide := true }) only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [framelessMemcpySpec, sepConj_assoc]
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

theorem new_pq_clone_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (x : SignalMessageNewGhost) (sp0 serPtr serLen ctBoxPtr addrCap : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 1372#64
       else
        (blkPl_63).base + 1132#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          boxU8Buf A (sm.readReg64 .x23) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_nil : x.pqRatchet = [] := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases had : addrCap = noneCap <;> simp_all [noneCap, arm64_norm]
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · unfold boxU8Buf
      simp only [hpq_nil, ↓reduceIte, sepConj_emp, List.length_nil, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hpq0
    have hpq_ne_nil : x.pqRatchet ≠ [] := by
      intro h; simp [h] at hpq_pos
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have ho858 := @oom_at_858_placed _ H h_panic
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp (config := { decide := true }) only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    have hsp_align1 : sf1.spAligned = true := by
      rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.pqRatchet.length, 1))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, arm64_norm] using hsp_align1)
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp (config := { decide := true }) only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    have hsp_align2 : sf2.spAligned = true := by
      rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_63).base + 2136#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho858 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
        (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
              A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align2)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp (config := { decide := true }) only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewMacAndBoxesCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [framelessMemcpySpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      have hsp_align3 : sf3.spAligned = true := by
        rw [State.spAligned, hsp3]; simpa [State.spAligned, arm64_norm] using hsp_align2
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases had : addrCap = noneCap <;> simp_all [noneCap, arm64_norm]
      · refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simpa [State.spAligned, arm64_norm] using hsp_align3,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      · unfold boxU8Buf
        have h23_eq : sf3.readReg64 (Reg.gpr 23#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hpq_ne_nil, ↓reduceIte, h23_eq, hsp2, hsp1, hsp, arm64_norm]
        refine Entails.pure_right ⟨hoom, by omega⟩ ?_
        exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_addr_into_boxed_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 serPtr serLen ctBoxPtr pqBoxPtr addrCap : BitVec 64)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc =
      (if addrCap = noneCap then
        (blkPl_63).base + 1384#64
       else
        (blkPl_63).base + 1176#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = serLen)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1400#64)
      s
      (optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse))
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = pqBoxPtr ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = ctBoxPtr ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = serLen ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          cells (sp0 - 216#64) 3 ∗
          optAddrBoxBuf A (sm.readReg64 .x0) (sm.readReg64 .x20) (x.addresses uuidTryParse))) := by
  have h216_8 : sp0 - 216#64 + 8#64 = sp0 - 208#64 := by bv_lin
  have h216_16 : sp0 - 216#64 + 16#64 = sp0 - 200#64 := by bv_lin
  cases had : x.addresses uuidTryParse with
  | none =>
    simp only [had, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at haddrCap
    subst haddrCap
    simp only [↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_none_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => ?_
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, sepConj_emp, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) noneCap w1 w0
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ hc3
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  | some ad =>
    have had_len := addresses_length had
    simp only [had, Option.isSome_some, ↓reduceIte] at haddrCap
    subst haddrCap
    have h36_ne : (36#64 = noneCap) = False := by decide
    simp only [h36_ne, ↓reduceIte] at hpc
    rw [signalMessageNew_optSerializeAddressesAt_some_eq A (sp0 - 216#64) had_len]
    refine SepWP.exists_elim fun addrPtr => ?_
    rw [h216_8, h216_16]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [optAddrBoxBuf, had_len, arm64_norm]
      have hc3 := three_words_entails_cells3 (sp0 - 216#64) 36#64 addrPtr 36#64
      rw [h216_8, h216_16] at hc3
      refine Entails.trans ?_ (sepConj_mono_left hc3)
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_sret_stores_wp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 serPtr ctBoxPtr pqBoxPtr addrBoxPtr addrBoxLen : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1400#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = addrBoxPtr)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = addrBoxLen)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = pqBoxPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = ctBoxPtr)
    (hx26 : s.readReg64 .x26 = serPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1452#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       boxU8Buf A pqBoxPtr x.pqRatchet ∗
       boxU8Buf A ctBoxPtr x.ciphertext ∗
       boxU8Buf A serPtr (x.model C.F uuidTryParse).serialized ∗
       optAddrBoxBuf A addrBoxPtr addrBoxLen (x.addresses uuidTryParse) ∗
       memRegion x.ret 120)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)))) := by
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_eq⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.senderRatchetKey.bytes)
  rw [hrk_eq x.senderRatchetKeyA, memRegion_sret_120 x.ret]
  simp only [cells, sepConj_emp, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      by simpa [State.spAligned, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [← sepExists_sepConj_right]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sret_cells_entails_signalMessageAt C.F A x serPtr ctBoxPtr pqBoxPtr
          addrBoxPtr addrBoxLen rk0 rk1 rk2 rk3 hrk_eq hct_bound hpq_bound))))))))

theorem new_dealloc_rk_and_ct_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1496#64)
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
  have hdealloc := new_dealloc_placed_ok h_dealloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63); clear h_dealloc
  have hrk_len : x.senderRatchetKey.serialize.length = 33 :=
    publicKey_serialize_length x.senderRatchetKey
  have hrk_ne : x.senderRatchetKey.serialize ≠ [] := by
    intro h; simp [h] at hrk_len
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
  apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
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
    apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
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

theorem new_dealloc_pq_and_epilogue_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hpc : s.pc = (blkPl_63).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s) := by
  have hdealloc := new_dealloc_placed_ok h_dealloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63); clear h_dealloc
  have hsp_cancel : sp0 - 416#64 + 416#64 = sp0 := BitVec.sub_add_cancel sp0 416#64
  unfold optPqBuf
  by_cases hpq : x.pqRatchet.isEmpty = true
  · simp only [hpq, ↓reduceIte, sepConj_emp]
    refine SepWPp.pure_elim fun hpqCap => ?_
    subst hpqCap
    unfold newSavedRegs
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0]
      have hst := newFrameRest_entails_stackAt sp0 noneCap s0
      unfold newSavedRegs at hst
      refine Entails.trans ?_ (sepConj_mono_right hst)
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun hpq_pure => ?_
    rcases hpq_pure with ⟨hpqCap, hpq_pos, hpq_lt, hpqPtr_ne⟩
    subst hpqCap
    have hpqCap_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpqCap_ne : ¬(BitVec.ofNat 64 x.pqRatchet.length = 0xFFFFFFFFFFFFFFFF#64) := by
      intro h; rw [h] at hpqCap_toNat; simp at hpqCap_toNat; omega
    unfold newSavedRegs
    apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (pqCopyPtr, x.pqRatchet.length, 1))
      (ret_pc := s0.readReg64 .lr)
      (F := memRegion (sp0 - (BitVec.ofNat 64 (allocHookStack + 944))) 944)
      hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
      (by simp only [wp_norm, arm64_norm, *]) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hst := newFrameRest_entails_stackAt sp0 (BitVec.ofNat 64 x.pqRatchet.length) s0
      unfold newSavedRegs at hst
      rw [stackAt_signalMessageNewGen_to_hook sp0 allocHookStack (by decide),
        sepConj_comm (memRegion (sp0 - (BitVec.ofNat 64 (allocHookStack + 944))) 944)] at hst
      have hmem_pq := pointsToBytes_entails_memRegion pqCopyPtr x.pqRatchet
      simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [← sepConj_assoc (stackAt sp0 allocHookStack)]
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_pq (sepConj_mono_left hst))))
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)
    intro sf hpcf hrunf hspf hcsf
    rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f⟩
    simp only [rustDeallocSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, stackAt_signalMessageNewGen_to_hook sp0 allocHookStack (by decide)]
      simp only [wp_norm, arm64_norm]
      exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

theorem new_phase3_wpp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (h_panic2 : H lsAllocHandleErrorSym = some Rust.panicked)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec C.F A)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool ∗
          stackAt s0.sp signalMessageNewStack))
      (PanicAllocPost s0) := by
  refine signalMessageNew_seg3_seq_wpp' htr
    (new_compute_mac_and_append_wpp_placed hMac x sp0 serPtr addrCap hct_bound hpq_bound s
      hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  refine signalMessageNew_seg3_seq_wpp' htr1'
    (new_ct_clone_wpp_placed h_shim h_alloc h_mc h_panic2 x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine signalMessageNew_seg3_seq_wpp' htr2'
    (new_pq_clone_wpp_placed h_shim h_alloc h_mc h_panic x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound s2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wp'
    (new_addr_into_boxed_wp_placed x sp0 serPtr (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine signalMessageNew_seg3_seq_wp'
    (new_sret_stores_wp_placed x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine signalMessageNew_seg3_seq_wpp' htr5'
    (new_dealloc_rk_and_ct_wpp_placed h_dealloc x sp0 rkPtr ctCopyPtr pqCopyPtr hct_bound s5
      hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine signalMessageNew_seg3_seq_wpp' htr6'
    (new_dealloc_pq_and_epilogue_wpp_placed h_dealloc x sp0 pqCap pqCopyPtr hpq_bound s0 s6
      hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6')
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

end CryptoVerification.LibsignalTripleRatchet
