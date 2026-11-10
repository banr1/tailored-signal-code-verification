/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.Repr
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import GeneratedLean.LibsignalSessionCode -- shake: keep

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 0. Call-site `subroutine_ok` and panic stub wrappers -/

theorem at_doReserve_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        bv% (2 ^ 64 +
          (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
          (ls_off% "libsignal_cli::stores::address_text")))
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "libsignal_cli::stores::address_text")
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")
    (by decide)]
  exact hRes

theorem at_decimal_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {decStk : Nat}
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "libsignal_cli::stores::decimal"))
      (decimalSpec A img decStk) :=
  sub_ok_at_of_fnAddr hDec addressTextName
    (ls_rel% "libsignal_cli::stores::address_text" "libsignal_cli::stores::decimal")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_lemma% fnOff "libsignal_cli::stores::decimal")])

theorem at_alloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hC.alloc_ok_at addressTextName
    (ls_rel% "libsignal_cli::stores::address_text" "__rustc::__rust_alloc")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_stub% "__rustc::__rust_alloc")])

theorem at_dealloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hC.dealloc_ok_at addressTextName
    (ls_rel% "libsignal_cli::stores::address_text" "__rustc::__rust_dealloc")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_stub% "__rustc::__rust_dealloc")])

theorem at_handleError_panic {img : Obj.Image}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
          "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_ext img.base ext addressTextName
    (ls_rel% "libsignal_cli::stores::address_text" "alloc::raw_vec::handle_error")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_stub% "alloc::raw_vec::handle_error")])

/-! ## 1. Pure model & arithmetic bounds -/

theorem utf8_dot : Cli.utf8 "." = [0x2e#8] := by decide +kernel

theorem device_zeroExtend32_toNat (d : BitVec 8) :
    (d.zeroExtend 32).toNat = d.toNat := by
  simp; omega

theorem decimalText_device_len_le_three :
    ∀ d : BitVec 8, (decimalText d.toNat).length ≤ 3 := by
  decide +kernel

theorem addressText_val_eq (g : AddrGhost) :
    addressText g.val =
      (g.name.bytes ++ [0x2e#8]) ++ decimalText (g.device.zeroExtend 32).toNat := by
  simp only [AddrGhost.val, addressText, utf8_dot, device_zeroExtend32_toNat]

theorem reserveCap1_bounds {len : Nat} (hlen : len < 2 ^ 32) :
    reserveCap len len 1 < 2 ^ 34 ∧
      len < reserveCap len len 1 ∧
      reserveCap len len 1 + 1 ≤ 2 ^ 63 := by
  unfold reserveCap
  omega

theorem reserveCap2_bounds {cap1 len decLen : Nat}
    (hcap1 : cap1 < 2 ^ 34) (hlen : len < 2 ^ 32) (hdec : decLen ≤ 3) :
    reserveCap cap1 (len + 1) decLen < 2 ^ 35 ∧
      len + 1 + decLen ≤ reserveCap cap1 (len + 1) decLen ∧
      reserveCap cap1 (len + 1) decLen + 1 ≤ 2 ^ 63 := by
  unfold reserveCap
  omega

theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## 2. Stack bounds & frame decomposition (`sub sp, sp, #0x70`) -/

/-- Any `stackAt sp stk` separately conjoined with `memRegion ret 24` has `stk ≤ 2 ^ 64`. -/
theorem stk_le_two_pow_64 {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (h : m ⊨ memRegion ret 24 ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  by_cases h0 : stk = 0
  · omega
  · have hdisj := (IsBlock.memRegion ret 24).disjoint
      (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) (by decide) (by omega) h
    have hlt : (ret - (sp - BitVec.ofNat 64 stk)).toNat < 2 ^ 64 := BitVec.isLt _
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

theorem spAligned_sub112 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 112#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  simp only [beq_iff_eq] at hsp0 ⊢
  have hmod0 : s0.sp.toNat % 16 = 0 := by
    have h1 : (s0.sp &&& 15#64).toNat = 0 := congrArg BitVec.toNat hsp0
    rw [BitVec.toNat_and] at h1
    change s0.sp.toNat &&& (2 ^ 4 - 1) = 0 at h1
    rw [Nat.and_two_pow_sub_one_eq_mod _ 4] at h1
    exact h1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (s0.sp - 112#64).toNat &&& (2 ^ 4 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4, BitVec.toNat_sub]
  change ((2 ^ 64 - 112 + s0.sp.toNat) % 2 ^ 64) % 16 = 0
  omega

/-- Saved callee-saved registers & FP/LR in `[sp' + 48 .. sp' + 112)`. -/
def addrCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 48#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp' + 56#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp' + 64#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp' + 72#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp' + 80#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp' + 88#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp' + 96#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp' + 104#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_sub_le (sp : BitVec 64) {k n : Nat} (hle : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n =
      memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  have h1 := ProofLib.stackAt_split_bottom sp k (n - k) (by omega)
  rw [show k + (n - k) = n by omega] at h1
  exact h1

theorem stackAt_frame112_split (sp : BitVec 64) {subStk stk : Nat}
    (hstk : 112 + subStk ≤ stk) (hle64 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
      stackAt (sp - 112#64) subStk ∗
      memRegion (sp - 112#64) 24 ∗
      memRegion (sp - 112#64 + 24#64) 24 ∗
      memRegion (sp - 112#64 + 48#64) 64 := by
  have htop := stackAt_sub_le sp (k := subStk + 112) (n := stk) (by omega) hle64
  have hcells := ProofLib.stackAt_split_cells sp subStk 14 (by omega)
  change stackAt sp (subStk + 112) =
    stackAt (sp - 112#64) subStk ∗ cells (sp - 112#64) 14 at hcells
  rw [← ProofLib.memRegion_cells (sp - 112#64) 14 (by decide)] at hcells
  change stackAt sp (subStk + 112) =
    stackAt (sp - 112#64) subStk ∗ memRegion (sp - 112#64) 112 at hcells
  have hm1 := ProofLib.memRegion_split (sp - 112#64) 24 88 (by decide)
  have hm2 : memRegion (sp - 112#64 + 24#64) 88 =
      memRegion (sp - 112#64 + 24#64) 24 ∗ memRegion (sp - 112#64 + 48#64) 64 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp - 112#64 + 24#64) 24 64 (by decide)
  rw [htop, hcells, hm1, hm2]

theorem memRegion64_cells (sp' : BitVec 64) :
    memRegion (sp' + 48#64) 64 ⊢
      ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64,
      ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
      ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
        ((sp' + 48#64) ↦₆₄ w29) ∗ ((sp' + 56#64) ↦₆₄ w30) ∗
        ((sp' + 64#64) ↦₆₄ w24) ∗ ((sp' + 72#64) ↦₆₄ w23) ∗
        ((sp' + 80#64) ↦₆₄ w22) ∗ ((sp' + 88#64) ↦₆₄ w21) ∗
        ((sp' + 96#64) ↦₆₄ w20) ∗ ((sp' + 104#64) ↦₆₄ w19) := by
  have hs1 := ProofLib.memRegion_split (sp' + 48#64) 8 56 (by decide)
  have hs2 := ProofLib.memRegion_split (sp' + 56#64) 8 48 (by decide)
  have hs3 := ProofLib.memRegion_split (sp' + 64#64) 8 40 (by decide)
  have hs4 := ProofLib.memRegion_split (sp' + 72#64) 8 32 (by decide)
  have hs5 := ProofLib.memRegion_split (sp' + 80#64) 8 24 (by decide)
  have hs6 := ProofLib.memRegion_split (sp' + 88#64) 8 16 (by decide)
  have hs7 := ProofLib.memRegion_split (sp' + 96#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem addrCalleeSavedAt_entails_memRegion64 (sp' : BitVec 64) (s0 : State) :
    addrCalleeSavedAt sp' s0 ⊢ memRegion (sp' + 48#64) 64 := by
  unfold addrCalleeSavedAt
  have hs1 := ProofLib.memRegion_split (sp' + 48#64) 8 56 (by decide)
  have hs2 := ProofLib.memRegion_split (sp' + 56#64) 8 48 (by decide)
  have hs3 := ProofLib.memRegion_split (sp' + 64#64) 8 40 (by decide)
  have hs4 := ProofLib.memRegion_split (sp' + 72#64) 8 32 (by decide)
  have hs5 := ProofLib.memRegion_split (sp' + 80#64) 8 24 (by decide)
  have hs6 := ProofLib.memRegion_split (sp' + 88#64) 8 16 (by decide)
  have hs7 := ProofLib.memRegion_split (sp' + 96#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  exact sepConj_mono (pointsTo64_entails_memRegion (sp' + 48#64) _)
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 56#64) _)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 64#64) _)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 72#64) _)
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 80#64) _)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 88#64) _)
              (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) _)
                (pointsTo64_entails_memRegion (sp' + 104#64) _)))))))

theorem memRegion24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  have hs1 := ProofLib.memRegion_split a 8 16 (by decide)
  have hs2 := ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2
  rw [hs1, hs2, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem cells24_entails_memRegion (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [show (24 : Nat) = 8 + (8 + 8) by decide,
    ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (pointsTo64_entails_memRegion (a + 16#64) w2))

/-! ## 3. `protocolAddressAt`, `vecU8At`, 128-bit move, and drop helpers -/

theorem pointsTo64_pair_eq_128 (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  rw [h0, h1]

theorem protocolAddressAt_open (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.name.cap) ∗
      ((a + 8#64) ↦₆₄ g.name.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      ((a + 24#64) ↦₈ g.device) ∗
      (vecU8BufRest A g.name.cap g.name.ptr g.name.bytes ∗ memRegion (a + 25#64) 7) := by
  unfold protocolAddressAt vecGhostAt vecU8At vecHeader
  change (vecU8At A a g.name.cap g.name.ptr g.name.bytes) ∗ ((a + 24#64) ↦₈ g.device) ∗
      memRegion (a + 25#64) 7 ⊢ _
  rw [vecU8At_eq_header_buf]
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (vecU8Buf_entails_slice_rest A g.name.cap g.name.ptr g.name.bytes))) ?_
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

theorem protocolAddressAt_close (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    (a ↦₆₄ g.name.cap) ∗
      ((a + 8#64) ↦₆₄ g.name.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      ((a + 24#64) ↦₈ g.device) ∗
      (vecU8BufRest A g.name.cap g.name.ptr g.name.bytes ∗ memRegion (a + 25#64) 7) ⊢
      protocolAddressAt A g a := by
  change _ ⊢ vecU8At A a g.name.cap g.name.ptr g.name.bytes ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 25#64) 7
  rw [vecU8At_eq_header_buf]
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_right (slice_rest_entails_vecU8Buf A g.name.cap g.name.ptr g.name.bytes)))
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

theorem vecU8At_zero_init (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8At A v 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem vecU8At_pos_init (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8At A v (BitVec.ofNat 64 bs.length) p' bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8At vecHeader
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

theorem vecU8At_open_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A v cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      (∃∗ b0 : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b0)) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1)) := by
  have hne0 : cap ≠ 0 := by intro h; subst h; simp at hlt
  unfold vecU8At vecHeader
  simp only [hne0, ↓reduceIte]
  rw [sepConj_assoc, sepConj_assoc, sepConj_pure_left_comm]
  rw [sepConj_pure_left_comm ((v + 8#64) ↦₆₄ ptr)]
  rw [sepConj_pure_left_comm (v ↦₆₄ cap)]
  refine Entails.pure_left fun ⟨_, h63, hptr⟩ => ?_
  have hsplit : memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      (∃∗ b0 : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b0)) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1)) := by
    rw [show cap.toNat - bs.length = 1 + (cap.toNat - (bs.length + 1)) by omega,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 bs.length) 1 (cap.toNat - (bs.length + 1))
        (by omega),
      ProofLib.memRegion_one, BitVec.add_assoc]
    have hadd : BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs.length + 1) := by
      rw [← BitVec.ofNat_add]
    rw [hadd]
  rw [hsplit, pure_true_emp ⟨h63, hptr⟩, emp_sepConj]
  apply entails_of_eq
  ac_rfl

theorem vecU8At_close_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (b : BitVec 8) (hlt : bs.length < cap.toNat) (h63 : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + 1)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + 1)) (cap.toNat - (bs.length + 1)) ⊢
      vecU8At A v cap ptr (bs ++ [b]) := by
  have hne0 : cap ≠ 0 := by intro h; subst h; simp at hlt
  have hlen : (bs ++ [b]).length = bs.length + 1 := List.length_append
  have hbytes : (ptr ↦ₛ (bs ++ [b])) =
      (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b) := by
    rw [pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  unfold vecU8At vecHeader
  simp only [hne0, hlen, ↓reduceIte]
  rw [hbytes]
  have hp : (bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by omega, h63, hptr⟩
  rw [hp, pure_true]
  apply entails_of_eq
  ac_rfl

theorem vecU8At_open_slice (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (m : Nat) (hle : bs.length + m ≤ cap.toNat) (hm : 0 < m) :
    vecU8At A v cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) m ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + m)) (cap.toNat - (bs.length + m)) := by
  have hne0 : cap ≠ 0 := by intro h; subst h; simp at hle; omega
  unfold vecU8At vecHeader
  simp only [hne0, ↓reduceIte]
  rw [sepConj_assoc, sepConj_assoc, sepConj_pure_left_comm]
  rw [sepConj_pure_left_comm ((v + 8#64) ↦₆₄ ptr)]
  rw [sepConj_pure_left_comm (v ↦₆₄ cap)]
  refine Entails.pure_left fun ⟨_, h63, hptr⟩ => ?_
  have hsplit : memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion (ptr + BitVec.ofNat 64 bs.length) m ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + m)) (cap.toNat - (bs.length + m)) := by
    rw [show cap.toNat - bs.length = m + (cap.toNat - (bs.length + m)) by omega,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 bs.length) m (cap.toNat - (bs.length + m))
        (by omega),
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hsplit, pure_true_emp ⟨h63, hptr⟩, emp_sepConj]
  apply entails_of_eq
  ac_rfl

theorem vecU8At_close_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs extra : List (BitVec 8))
    (hle : bs.length + extra.length ≤ cap.toNat) (h63 : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0)
    (hm : 0 < extra.length) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length + extra.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ extra) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + extra.length))
        (cap.toNat - (bs.length + extra.length)) ⊢
      vecU8At A v cap ptr (bs ++ extra) := by
  have hne0 : cap ≠ 0 := by
    intro h
    subst h
    change bs.length + extra.length ≤ 0 at hle
    omega
  have hlen : (bs ++ extra).length = bs.length + extra.length := List.length_append
  unfold vecU8At vecHeader
  simp only [hne0, hlen, ↓reduceIte]
  rw [pointsToBytes_append]
  have hp : (bs.length + extra.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨hle, h63, hptr⟩
  rw [hp, pure_true]
  apply entails_of_eq
  ac_rfl

theorem vecU8_dec_unpack (A : RustAlloc) (d : BitVec 64) (dec : List (BitVec 8)) :
    vecU8 A d dec ⊢
      ∃∗ dCap : BitVec 64, ∃∗ dPtr : BitVec 64,
        ⌜dec.length ≤ dCap.toNat ∧ dCap.toNat < 2 ^ 63 ∧ dPtr ≠ 0⌝ ∗
        (d ↦₆₄ dCap) ∗ ((d + 8#64) ↦₆₄ dPtr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
        (dPtr ↦ₛ dec) ∗ vecU8BufRest A dCap dPtr dec := by
  unfold vecU8
  refine Entails.sepExists_mono fun dCap => Entails.sepExists_mono fun dPtr => ?_
  rw [vecU8At_eq_header_buf]
  refine Entails.trans
    (sepConj_mono_right (vecU8Buf_entails_slice_rest A dCap dPtr dec)) ?_
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

/-- When `dCap ≠ 0`, `dPtr ↦ₛ dec ∗ vecU8BufRest A dCap dPtr dec` entails the raw live block
`A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat` needed by `__rust_dealloc(dPtr, dCap, 1)`. -/
theorem dec_buf_to_dealloc (A : RustAlloc) (dCap dPtr : BitVec 64) (dec : List (BitVec 8))
    (hle : dec.length ≤ dCap.toNat) (h63 : dCap.toNat < 2 ^ 63) (hne0 : dCap ≠ 0) :
    (dPtr ↦ₛ dec) ∗ vecU8BufRest A dCap dPtr dec ⊢
      A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat := by
  unfold vecU8BufRest
  simp only [hne0, ↓reduceIte]
  rw [show (dPtr ↦ₛ dec) ∗ (⌜dec.length ≤ dCap.toNat ∧ dCap.toNat < 2 ^ 63 ∧ dPtr ≠ 0⌝ ∗
        (A.live dPtr dCap.toNat 1 ∗ memRegion (dPtr + BitVec.ofNat 64 dec.length) (dCap.toNat - dec.length))) =
      ⌜dec.length ≤ dCap.toNat ∧ dCap.toNat < 2 ^ 63 ∧ dPtr ≠ 0⌝ ∗
        ((dPtr ↦ₛ dec) ∗ (A.live dPtr dCap.toNat 1 ∗ memRegion (dPtr + BitVec.ofNat 64 dec.length) (dCap.toNat - dec.length))) by ac_rfl]
  refine Entails.pure_left fun _ => ?_
  have hmem : memRegion dPtr dCap.toNat =
      memRegion dPtr dec.length ∗
      memRegion (dPtr + BitVec.ofNat 64 dec.length) (dCap.toNat - dec.length) := by
    conv => lhs; rw [show dCap.toNat = dec.length + (dCap.toNat - dec.length) by omega]
    exact ProofLib.memRegion_split dPtr dec.length (dCap.toNat - dec.length) (by omega)
  rw [hmem]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      ((IsBlock.pointsToBytes dPtr dec).entails_memRegion)))
  apply entails_of_eq
  ac_rfl

/-- Move `[src .. src + 16)` (`c`, `p`) and write `totalLen` to `[dst + 16]` via `ldr q0` + `str q0`
to form `vecU8 A dst bs` while keeping `[src .. src + 24)` as `memRegion src 24`. -/
theorem vecU8_from_moved_header (A : RustAlloc) (dst c p : BitVec 64) (bs : List (BitVec 8)) :
    (dst ↦₆₄ c) ∗ ((dst + 8#64) ↦₆₄ p) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A c p bs ⊢ vecU8 A dst bs := by
  unfold vecU8
  refine Entails.trans ?_ (Entails.sepExists_intro c)
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  rw [vecU8At_eq_header_buf]
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

end CryptoVerification.SignalSession.Cli.AddressText.Helpers
