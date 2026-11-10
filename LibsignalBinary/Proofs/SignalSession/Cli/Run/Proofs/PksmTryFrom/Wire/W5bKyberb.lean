/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyber
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup

/-!
# `PreKeySignalMessage::try_from`: Kyber Error Allocation, Panic Tails, and Mismatched-Field Error

Proves `.rodata` error-string allocation helpers (`freshString_entails_pksmErrE`), OOM
panic tails (`+0xa74`, `+0xa80`), the Kyber buffer deallocation step (`+0xa1c → +0xa24`),
and the 68-byte mismatched-Kyber error branch (`kyber_half_err_wpE`, `+0x6c8 → +0xa24`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp
open CryptoVerification.SignalSession.Cli

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.call_noPanic_tryFromX := @Wire.SepWPp.call_noPanic_tryFrom

open Lean Meta Elab Tactic in
local elab "pksm_fetches " b:term:max H:term:max hfn:ident
    k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat
    (← `(ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
    "pksm_fetches"
  let offLit := Syntax.mkNumLit (toString off)
  evalTactic (← `(tactic|
    responder_wire_fetches_from $b $H $hfn $offLit $k0 $len))

/-! ## Local BitVec Normalizers -/

private theorem bv_sub_add_lit_k (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_lit_k (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit_k bv_sub_sub_lit_k BitVec.toNat_zero
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_55X bv_add_neg_56X bv_add_neg_64X bv_add_neg_72X
  bv_add_neg_80X bv_add_neg_87X bv_add_neg_88X bv_add_neg_96X bv_add_neg_104X
  bv_add_neg_112X bv_add_neg_128X bv_add_neg_136X bv_add_neg_152X bv_add_neg_160X
  bv_add_neg_168X bv_add_neg_176X bv_add_neg_184X bv_add_neg_186X bv_add_neg_191X
  bv_add_neg_192X bv_add_neg_196X bv_add_neg_200X bv_add_neg_216X bv_add_neg_512X
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8
  (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem L1_PksmWire_W5bKyberb : True := trivial

/-! ## 1. Callee Wrappers, ADRP Normalization, `.rodata` Helpers, & `freshString_entails_pksmErrE` -/

theorem shim_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% preKeyTryFromName))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hA (name := preKeyTryFromName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% preKeyTryFromName))

theorem alloc_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% preKeyTryFromName))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hA (name := preKeyTryFromName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% preKeyTryFromName))

theorem panic_at_prekey_handle_errorX {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (contractProg b ext).externAt?
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (name := preKeyTryFromName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName))

theorem adrp_prekey_1844 {b : BitVec 64} {H : String → Option (State → State)}
    (halign : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr preKeyTryFromName + 1844#64) &&&
      bv% (2 ^ 64 - 4096)) =
    b + bv% (page% (ls_off% preKeyTryFromName + 1844)) := by
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
    BitVec.add_assoc, adrp_page_of_aligned halign]
  rfl

theorem adrp_prekey_2476 {b : BitVec 64} {H : String → Option (State → State)}
    (halign : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr preKeyTryFromName + 2476#64) &&&
      bv% (2 ^ 64 - 4096)) =
    b + bv% (page% (ls_off% preKeyTryFromName + 2476)) := by
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
    BitVec.add_assoc, adrp_page_of_aligned halign]
  rfl

theorem rodata_ro8_at {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (off : Nat) (hin : inLiRoData libsignalSessionImage off 8 = true := by decide +kernel)
    {m : Memory} (hro : img.RoDataLoaded m) :
    m.RO (img.base + BitVec.ofNat 64 off) 8 := by
  simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hin
  obtain ⟨⟨secOff, secLen⟩, hsec, hle1, hle2, hlt⟩ := hin
  have hsec_len : secLen < 2 ^ 32 := by
    have hall : ∀ p ∈ libsignalSessionImage.roData, p.2 < 2 ^ 32 := by decide +kernel
    exact hall (secOff, secLen) hsec
  have hsec_ro := ProofLib.ObjectLoad.rodata_ro himg rfl hsec hsec_len m hro
  intro a ha
  unfold Arm64.InRegion at ha
  apply hsec_ro a
  unfold Arm64.InRegion
  have hk : (a - (img.base + BitVec.ofNat 64 off)).toNat < 8 := ha
  have heq : a - (img.base + BitVec.ofNat 64 secOff) =
      (a - (img.base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 (off - secOff) := by
    have h1 : BitVec.ofNat 64 off = BitVec.ofNat 64 secOff + BitVec.ofNat 64 (off - secOff) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le hle1]
    rw [h1]; bv_omega
  rw [heq, BitVec.toNat_add_of_lt]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem stackAt_skipFieldStackX_ext (sp' : BitVec 64) :
    stackAt sp' (Prost.skipFieldStackX 100) =
      memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - extHookStack) ∗ stackAt sp' extHookStack :=
  stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)

theorem ule_64_vb_eq_true {vb : BitVec 8} (hvb_ge : 0x40 ≤ vb.toNat) :
    (64#64).ule (vb.zeroExtend 64) = true := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_true (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

theorem freshBuf_entails_vecU8 (A : RustAlloc) (v ptr : BitVec 64) (n : Nat)
    (hn_pos : 0 < n) (hn_lt : n < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr n 1 ∗ memRegion ptr n ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A v bs := by
  rw [ProofLib.memRegion_eq_exists_bytes ptr n (by omega)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  refine Entails.trans
    (Q := ⌜bs.length = n⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.live ptr n 1 ∗ (ptr ↦ₛ bs)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Entails.pure_left fun hlen => ?_
  subst hlen
  refine Entails.sepExists_right bs ?_
  dsimp only [vecU8]
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) (Entails.sepExists_right ptr ?_)
  have hcap_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have := congrArg BitVec.toNat h0
    rw [hcap_nat, hz] at this
    omega
  dsimp only [vecU8At, vecHeader]
  simp only [hcap_ne, ↓reduceIte, hcap_nat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [pure_true_emp ⟨Nat.le_refl _, hn_lt, hptr⟩, emp_sepConj]
  apply entails_of_eq; ac_rfl

/-- (`ErrAt.pksm0c_errCells_invalidMessage_preKey_words`): keeps the freshly allocated
`n`-byte `String` (`A.live ptr n 1 ∗ memRegion ptr n`) inside `speAt` as `vecU8 A (sret + 16) bs`,
absorbing only read-only `.rodata` frame `Pro` into `anyHeap`. -/
theorem freshString_entails_pksmErrE (A : RustAlloc) (sret ptr w5 w6 : BitVec 64) (n : Nat)
    (Pro : SepProp) (hn_pos : 0 < n) (hn_lt : n < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hw5 : w5.truncate 8 = 3#8) :
    (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
      ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ ((sret + 24#64) ↦₆₄ ptr) ∗
      ((sret + 32#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗
      memRegion (sret + 56#64) 192 ∗
      A.live ptr n 1 ∗ memRegion ptr n ∗ Pro ⊢
      pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap := by
  have hvec := freshBuf_entails_vecU8 A (sret + 16#64) ptr n hn_pos hn_lt hptr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
  refine Entails.trans
    (Q := (((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ ((sret + 24#64) ↦₆₄ ptr) ∗
        ((sret + 32#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.live ptr n 1 ∗ memRegion ptr n) ∗
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
        ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗ memRegion (sret + 56#64) 192) ∗
      Pro)
    (by apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono hvec (sepConj_mono_right (entails_anyHeap Pro))) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗ vecU8 A (sret + 16#64) bs ∗
        ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗ memRegion (sret + 56#64) 192) ∗
      anyHeap)
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left (pksm0c_errCells_invalidMessage_preKey_words A [] sret w5 w6 bs hw5)

theorem bf_low8_eq_3 (w : BitVec 64) :
    (w &&& bv% (2 ^ 64 - 256) ||| 3#64).truncate 8 = 3#8 := by
  bv_bits

theorem memRegion68_unpack (p : BitVec 64) :
    memRegion p 68 ⊢
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (p + 48#64) ↦₆₄ w6) ∗ (∃∗ w7 : BitVec 64, (p + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 32, (p + 64#64) ↦₃₂ w8) := by
  rw [show (68 : Nat) = 48 + (8 + (8 + 4)) by decide,
    Prost.memRegion_split p 48 20 (by decide),
    Prost.memRegion_split (p + 48#64) 8 12 (by decide),
    Prost.memRegion_split (p + 48#64 + 8#64) 8 4 (by decide),
    memRegion48_words6 p,
    ProofLib.memRegion_eight (p + 48#64),
    ProofLib.memRegion_eight (p + 48#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (memRegion_four_entails (p + 64#64)))))))))

theorem memRegion68_pack (p w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (w8 : BitVec 32) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
      ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
      ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₃₂ w8) ⊢ memRegion p 68 := by
  rw [show (68 : Nat) = 48 + (8 + (8 + 4)) by decide,
    Prost.memRegion_split p 48 20 (by decide),
    Prost.memRegion_split (p + 48#64) 8 12 (by decide),
    Prost.memRegion_split (p + 48#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (Q := ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
        ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5)) ∗
      ((p + 48#64) ↦₆₄ w6) ∗ ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₃₂ w8))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono (words6_entails_memRegion48 p w0 w1 w2 w3 w4 w5)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 48#64) w6)
      (sepConj_mono (pointsTo64_entails_memRegion (p + 56#64) w7)
        (pointsTo32_entails_memRegion (p + 64#64) w8)))

theorem memRegion54_unpack (p : BitVec 64) :
    memRegion p 54 =
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      memRegion (p + 48#64) 6 := by
  rw [show (54 : Nat) = 48 + 6 by decide,
    Prost.memRegion_split p 48 6 (by decide),
    memRegion48_words6 p]
  simp only [sepConj_assoc]

theorem memRegion54_pack (p w0 w1 w2 w3 w4 w46 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
      ((p + 32#64) ↦₆₄ w4) ∗ memRegion (p + 40#64) 6 ∗ ((p + 46#64) ↦₆₄ w46) ⊢
      memRegion p 54 := by
  rw [show (54 : Nat) = 8 + (8 + (8 + (8 + (8 + (6 + 8))))) by decide,
    Prost.memRegion_split p 8 46 (by decide),
    Prost.memRegion_split (p + 8#64) 8 38 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64) 8 30 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64) 8 22 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64) 8 14 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 6 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion p w0)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (p + 16#64) w2)
        (sepConj_mono (pointsTo64_entails_memRegion (p + 24#64) w3)
          (sepConj_mono (pointsTo64_entails_memRegion (p + 32#64) w4)
            (sepConj_mono_right (pointsTo64_entails_memRegion (p + 46#64) w46))))))

theorem shift_window_40_to_46 (p w40 : BitVec 64) :
    ((p + 40#64) ↦₆₄ w40) ∗ memRegion (p + 48#64) 6 ⊢
      memRegion (p + 40#64) 6 ∗ (∃∗ w46 : BitVec 64, (p + 46#64) ↦₆₄ w46) := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (p + 40#64) w40)) ?_
  have hsplit : memRegion (p + 40#64) 8 ∗ memRegion (p + 48#64) 6 =
      memRegion (p + 40#64) 6 ∗ (∃∗ w46 : BitVec 64, (p + 46#64) ↦₆₄ w46) := by
    rw [show p + 48#64 = p + 40#64 + BitVec.ofNat 64 8 by bv_omega,
      ← Prost.memRegion_split (p + 40#64) 8 6 (by decide),
      show (8 + 6 : Nat) = 6 + 8 by decide,
      Prost.memRegion_split (p + 40#64) 6 8 (by decide),
      ProofLib.memRegion_eight (p + 40#64 + BitVec.ofNat 64 6),
      show p + 40#64 + BitVec.ofNat 64 6 = p + 46#64 by bv_omega]
  exact entails_of_eq hsplit

theorem cap_sub1_add2_hi_of_pos_lt {cap : BitVec 64} (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (cap - bv% (2 ^ 64 - 1)).ult (cap - 1#64) = false := by
  rw [BitVec.ult_eq_decide]
  exact decide_eq_false (by bv_omega)

/-! ## 2. Panic Tails (`kyber_a74_panic_wp`, `kyber_a80_panic_wp`) & Dealloc (`kyber_a1c_to_a24_wp`) -/

/-- Panic tail at `+0xa74` (`2676`): `mov w0, #1; mov w1, #68; bl handle_error`. -/
theorem kyber_a74_panic_wp {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' target_pc : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : KyberExitA74State img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2676#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext) target_pc s P Q (tryFromQp s0) := by
  rcases hst with ⟨_hsp_eq, _hsp, hF, hsym, hallocF, htr⟩
  have hpan := panic_at_prekey_handle_errorX (b := img.base) (ext := ext)
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 2676 12; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpan hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ _ => ?_
  refine SepWPp.panic (by simp [hrun, arm64_norm])
    (by simpa [arm64_norm] using hpan)
    fun _ hm => ?_
  have hφ : allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                (entry + 2688#64)).setPC
            (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                  (entry + 2688#64)).setPC
              (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))).trace :=
    ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
     by simpa [Rust.panicked, arm64_norm] using htr⟩
  have hent : P ⊢ ⌜allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                (entry + 2688#64)).setPC
            (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                  (entry + 2688#64)).setPC
              (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))).trace⌝ ∗ anyHeap := by
    rw [pure_true_emp hφ, emp_sepConj]; exact entails_anyHeap P
  exact Satisfies.mono (sepConj_mono_left hent) hm

/-- Panic tail at `+0xa80` (`2688`): `mov w0, #1; mov w1, #54; bl handle_error`. -/
theorem kyber_a80_panic_wp {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' target_pc : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : KyberExitA80State img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2688#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext) target_pc s P Q (tryFromQp s0) := by
  rcases hst with ⟨_hsp_eq, _hsp, hF, hsym, hallocF, htr⟩
  have hpan := panic_at_prekey_handle_errorX (b := img.base) (ext := ext)
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 2688 12; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpan hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ _ => ?_
  refine SepWPp.panic (by simp [hrun, arm64_norm])
    (by simpa [arm64_norm] using hpan)
    fun _ hm => ?_
  have hφ : allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                (entry + 2700#64)).setPC
            (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                  (entry + 2700#64)).setPC
              (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))).trace :=
    ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
     by simpa [Rust.panicked, arm64_norm] using htr⟩
  have hent : P ⊢ ⌜allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                (entry + 2700#64)).setPC
            (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                  (entry + 2700#64)).setPC
              (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)))).trace⌝ ∗ anyHeap := by
    rw [pure_true_emp hφ, emp_sepConj]; exact entails_anyHeap P
  exact Satisfies.mono (sepConj_mono_left hent) hm

theorem sepConj_rot3_kyber (P1 P2 P3 F : SepProp) :
    (P1 ∗ P2 ∗ P3) ∗ F = P3 ∗ P1 ∗ P2 ∗ F := by ac_rfl

/-- Step `+0xa1c .. +0xa20 → +0xa24` (`2588 → 2596`): deallocates `kyberPtr` (`kyberCap > 0`)
and transitions from `KyberExitA1cState` at `+0xa1c` (`2588`) to `KyberExitA24State` at `+0xa24` (`2596`). -/
theorem kyber_a1c_to_a24_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : KyberExitA1cState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2588#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64) s
      (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24State img s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hpos, hlt, _hne,
    hx0, hx1, hx29, hx26, hx23, hx22, hx21, hx20, hx19⟩
  have hdealloc := dealloc_ok_at_prekeyX hA; clear hA
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 2588 8; clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_skipFieldStackX_ext sp'
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX (kyberPtr, kyberCap.toNat, 1) hdealloc
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2596#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
      stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = kyberPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = kyberCap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk kyberCap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hdealloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, _, hx29_2, _⟩
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  refine SepWP.done hpc2 hrun2 fun hF3 hsym3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hF3, hsym3,
        by simp [htr2, htr, arm64_norm]⟩,
      by simp [hx29_2, hx29, arm64_norm],
      by simp [hx26_2, hx26, arm64_norm],
      by simp [hx23_2, hx23, arm64_norm],
      by simp [hx22_2, hx22, arm64_norm],
      by simp [hx21_2, hx21, arm64_norm],
      by simp [hx20_2, hx20, arm64_norm],
      by simp [hx19_2, hx19, arm64_norm]⟩,
    by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl⟩

/-! ## 3. `kyber_err_alloc68_head_wpE`, `kyber_half_err_wpE`, & `pksmParse` Bridge -/

/-- Pure `pksmParse` corollary (`(kpkOpt.isSome != kyberOpt.isSome) = true`):
when `Pksm.decodeProto body = some m` has mismatched `kyberPreKeyId` / `kyberCiphertext`
presence, `Pksm.pksmParse (vb :: body) = none`. -/
theorem pksmParse_eq_none_of_kyber_half {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (hhalf : (m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true) :
    Pksm.pksmParse (vb :: body) = none :=
  pksmParse_kyberBad hd (kyberOk_false_of_half (bne_iff_ne.mp hhalf))

/-- Shared error-allocation head `+0x720 .. +0x780` (`1824 .. 1920`) :
calls `__rust_no_alloc_shim_is_unstable_v2` and `__rust_alloc(68, 1)`, panics via
`handle_error` (`tryFromQp s0`) if `x0 = 0`, otherwise copies the 68-byte `.rodata` error string
into the heap buffer, writes `pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)` keeping
the 68-byte `String` inside `speAt` as `vecU8`, and reaches `+0x780` (`1920`) with
`pstate = addsPState64 (kyberCap - 1#64) 2#64`. -/
theorem kyber_err_alloc68_head_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1824#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1920#64) s
      (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        sf.pstate = addsPState64 (kyberCap - 1#64) 2#64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hshim := shim_ok_at_prekeyX hA
  have halloc := alloc_ok_at_prekeyX hA
  have hpan := panic_at_prekey_handle_errorX (b := img.base) (ext := ext)
  clear hA
  let H := Rust.withPanics ext
  have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
  pksm_fetches img.base H hfn 1824 96
  pksm_fetches img.base H hfn 2676 12; clear hfn
  have hadrp := adrp_prekey_1844 (H := H) (ProofLib.ObjectLoad.base_aligned_of_loads himg)
  dsimp only [contractProg, tripleRatchetProgAtExt] at hshim halloc hpan hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_skipFieldStackX_ext sp'
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFromX () hshim
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 1828#64) (by simp [arm64_norm])
    (T := stackAt sp' extHookStack)
    (φ := True)
    (by simp [session2ShimSpecX, hsp_eq, arm64_norm])
    trivial
    (by rw [hstack]; sep_focus)
    ?_
  clear hshim
  intro s1 hpc1 hrun1 hsp1 hsp1_align hF1' hsym1' hcs1
  dsimp only [session2ShimSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  have hsp1_eq : s1.sp = sp' := by tryFromPost_sp [hsp1, hsp_eq]
  refine SepWPp.of_sepWP_frozen hF1' hsym1'
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) fun hF2 hsym2 => ?_
  have hlay68 : LayoutOk 68 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine SepWPp.call_noPanic_tryFromX (68, 1) halloc
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by tryFromPost_sp_align hsp1_align) hF2 hsym2
    (ret_pc := entry + 1840#64) (by simp [arm64_norm])
    (T := A.pool ∗ stackAt sp' extHookStack)
    (φ := (68#64 : BitVec 64).toNat = 68 ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk 68 1)
    (by simp [rustAllocSpecWithStack, hsp1_eq, arm64_norm])
    ⟨rfl, rfl, hlay68⟩
    (by simp only [hsp_eq, arm64_norm]; sep_focus)
    ?_
  clear halloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2' hsym2' hcs2
  dsimp only [rustAllocSpecWithStack]
  rw [sepConj_rot3_kyber]
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp1_eq]
  by_cases hoom : s2.readReg64 .x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.of_sepWP_frozen hF2' hsym2'
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun _ _ => ?_
    refine SepWPp.panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr1, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
    have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_left (memRegion68_unpack (s2.readReg64 .x0)))) ?_
    rw [memRegion248_split_err sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun s0_6 => SepWPp.exists_pre fun s0_5 =>
      SepWPp.exists_pre fun s0_4 => SepWPp.exists_pre fun s0_3 =>
      SepWPp.exists_pre fun s0_2 => SepWPp.exists_pre fun s0_1 =>
      SepWPp.exists_pre fun s0_0 =>
      SepWPp.exists_pre fun w8 => SepWPp.exists_pre fun w7 =>
      SepWPp.exists_pre fun w6 => SepWPp.exists_pre fun w5 =>
      SepWPp.exists_pre fun w4 => SepWPp.exists_pre fun w3 =>
      SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 =>
      SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_end hF2' hsym2' ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848))) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 8)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 16)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 24)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 32)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 40)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 48)) (by decide +kernel) hF2'.roData) rfl ?_
    refine SepWP.rodata64_intro (rodata_ro8_at himg (num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848) + 56)) (by decide +kernel) hF2'.roData) rfl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
    refine ⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hF3, hsym3,
        by simp [htr2, htr1, htr, arm64_norm]⟩,
      by simp [arm64_norm],
      by simp [hx29_2, hx29_1, hx29, arm64_norm],
      by simp [hx28_2, hx28_1, hx28, arm64_norm],
      by simp [hx26_2, hx26_1, hx26, arm64_norm],
      by simp [hx25_2, hx25_1, hx25, arm64_norm],
      by simp [hx23_2, hx23_1, hx23, arm64_norm],
      by simp [hx22_2, hx22_1, hx22, arm64_norm],
      by simp [hx21_2, hx21_1, hx21, arm64_norm],
      by simp [hx20_2, hx20_1, hx20, arm64_norm],
      by simp [hx19_2, hx19_1, hx19, arm64_norm], ?_⟩
    let rOff := num% (ls_xref% (ls_off% preKeyTryFromName + 1844) (ls_off% preKeyTryFromName + 1848))
    have hpack68 := memRegion68_pack (s2.readReg64 .x0)
      (s2.mem.read64 (img.base + BitVec.ofNat 64 rOff))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 48)))
      (s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 56)))
      0x746e6573#32
    have herr := freshString_entails_pksmErrE A sret (s2.readReg64 .x0)
      (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 68
      (((img.base + BitVec.ofNat 64 rOff) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 8)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 16)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 24)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 32)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 40)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 48)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 48))) ∗
        ((img.base + BitVec.ofNat 64 (rOff + 56)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 56))))
      (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
    have herr' :
        (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
          ((sret + 16#64) ↦₆₄ 68#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
          ((sret + 32#64) ↦₆₄ 68#64) ∗
          ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
          ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
          A.live (s2.readReg64 .x0) 68 1 ∗
          (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
            ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
            ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
            ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
            ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
            ((s2.readReg64 .x0 + 40#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40))) ∗
            ((s2.readReg64 .x0 + 48#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 48))) ∗
            ((s2.readReg64 .x0 + 56#64) ↦₆₄ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 56))) ∗
            ((s2.readReg64 .x0 + 64#64) ↦₃₂ 0x746e6573#32)) ∗
          (((img.base + BitVec.ofNat 64 rOff) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 rOff)) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 8)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 8))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 16)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 16))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 24)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 24))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 32)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 32))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 40)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 40))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 48)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 48))) ∗
            ((img.base + BitVec.ofNat 64 (rOff + 56)) ↦₆₄ᵣ s2.mem.read64 (img.base + BitVec.ofNat 64 (rOff + 56)))) ⊢
          pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpack68))))))))))
        herr
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) herr')
        (by apply entails_of_eq; ac_rfl))
    dsimp only [rOff]
    simp only [hstack, hsp1_eq, errTag, speWord, arm64_norm]
    apply entails_of_eq; ac_rfl

/-- (``+0x6c8 → +0xa24` / `+0xa74`, dec `1736 → 2596``):
When `kpkTag = 1#32` (`m.kyberPreKeyId = some kpkId`) and `m.kyberCiphertext = none`, or
`kpkTag = 0#32` (`m.kyberPreKeyId = none`) and `m.kyberCiphertext = some kyberCt`,
branches from `+0x6c8` (`1736`) to `+0x720` (`1824`), allocates the 68-byte error string,
writes `pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)` (keeping the 68-byte
`String` inside `speAt` as `vecU8`), deallocates `kyberPtr` via `+0xa1c` (`KyberExitA1cState`)
when `kyberCap > 0`, and reaches `+0xa24` (`2596`) in `KyberExitA24State`. -/
theorem kyber_half_err_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {kpkTag : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32)
    (hhalf : (kpkOpt.isSome != kyberOpt.isSome) = true)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 kpkTag 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64) s
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24State img s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  subst htag
  cases kpkOpt with
  | some _kpkId =>
    cases kyberOpt with
    | some _ => simp at hhalf
    | none =>
      dsimp only [optVecU8Buf]
      refine SepWPp.pure_pre fun hcap => ?_
      subst hcap
      rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
      let H := Rust.withPanics ext
      have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
          num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
        (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      pksm_fetches img.base H hfn 1736 12; clear hfn
      have h1 : SepWPp (contractProg img.base ext)
          ((contractProg img.base ext).fnAddr preKeyTryFromName + 1824#64) s
          (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueState img s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = noneCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
          (tryFromQp s0) := by
        dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
        examples_hide_fetches
        refine SepWPp.of_sepWP_end hF hsym ?_
        wp_steps
        refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        exact ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          Entails.refl _⟩
      refine SepWPp.bind h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine SepWPp.mono_pre hent1 ?_
      refine SepWPp.bind
        (kyber_err_alloc68_head_wpE himg hA hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, _hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      rcases hst2 with ⟨hsp2_eq, hsp2, hF2, hsym2, htr2⟩
      have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
          num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
        (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      pksm_fetches img.base H hfn 1920 4; clear hfn
      dsimp only [contractProg, tripleRatchetProgAtExt] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
      examples_hide_fetches
      refine SepWPp.of_sepWP_end hF2 hsym2 ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
      exact ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hF3, hsym3,
            by simp [htr2, arm64_norm]⟩,
          by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
          by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
          by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
          by simp [hx19_2, arm64_norm]⟩, hent2⟩
  | none =>
    cases kyberOpt with
    | none => simp at hhalf
    | some kyberCt =>
      have hcap_lt :
          optVecU8Buf A kyberCap kyberPtr kyberLen (some kyberCt) ⊢
            ⌜kyberCap.toNat < 2 ^ 63⌝ ∗
              ∃∗ active : Bool, deallocSlot A kyberCap kyberPtr active := by
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨_, hlt, _⟩ => ?_
        have hlt' : kyberCap.toNat < 2 ^ 63 := hlt
        rw [pure_true_emp hlt', emp_sepConj]
        refine Entails.trans ?_ (optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen (some kyberCt))
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        rw [pure_true_emp hlen, emp_sepConj, pure_true_emp ⟨‹_›, hlt, ‹_›⟩, emp_sepConj]
        exact Entails.refl _
      refine SepWPp.mono_pre (sepConj_mono_left hcap_lt) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun active => ?_
      refine SepWPp.pure_pre fun hky_lt => ?_
      have hky_eq := cap_add1_eq_of_lt hky_lt
      rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
      let H := Rust.withPanics ext
      have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
          num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
        (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      pksm_fetches img.base H hfn 1736 4
      pksm_fetches img.base H hfn 1816 8; clear hfn
      have h1 : SepWPp (contractProg img.base ext)
          ((contractProg img.base ext).fnAddr preKeyTryFromName + 1824#64) s
          (deallocSlot A kyberCap kyberPtr active ∗
            memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueState img s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = kyberCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
              deallocSlot A kyberCap kyberPtr active))
          (tryFromQp s0) := by
        dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
        examples_hide_fetches
        refine SepWPp.of_sepWP_end hF hsym ?_
        wp_steps
        refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hF1, hsym1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          by apply entails_of_eq; ac_rfl⟩
      refine SepWPp.bind h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine SepWPp.mono_pre hent1 ?_
      refine SepWPp.bind_frame_tryFrom
        (kyber_err_alloc68_head_wpE himg hA hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      refine SepWPp.mono_pre (P' := deallocSlot A kyberCap kyberPtr active ∗
          (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
        (Entails.trans (sepConj_mono_left hent2) (by apply entails_of_eq; ac_rfl)) ?_
      cases active with
      | false =>
        have hdealloc : deallocSlot A kyberCap kyberPtr false = ⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ := rfl
        rw [hdealloc]
        refine SepWPp.pure_pre fun hcap0 => ?_
        rcases hst2 with ⟨hsp2_eq, hsp2, hF2, hsym2, htr2⟩
        have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
            num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
          (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
        pksm_fetches img.base H hfn 1920 4; clear hfn
        dsimp only [contractProg, tripleRatchetProgAtExt] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
        examples_hide_fetches
        rcases hcap0 with rfl | rfl
        all_goals
          refine SepWPp.of_sepWP_end hF2 hsym2 ?_
          wp_steps
          refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
          exact ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hF3, hsym3,
                by simp [htr2, arm64_norm]⟩,
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            by apply entails_of_eq; ac_rfl⟩
      | true =>
        have hdealloc : deallocSlot A kyberCap kyberPtr true =
            (⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
              A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) := rfl
        rw [hdealloc]
        simp only [sepConj_assoc]
        refine SepWPp.pure_pre fun ⟨hpos, hlt, hne_ptr⟩ => ?_
        have hhi := cap_sub1_add2_hi_of_pos_lt hpos hlt
        rcases hst2 with ⟨hsp2_eq, hsp2, hF2, hsym2, htr2⟩
        have hfn : libsignalSessionCode.fnOff preKeyTryFromName =
            num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
          (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
        pksm_fetches img.base H hfn 1920 16; clear hfn
        have h3 : SepWPp (contractProg img.base ext)
            ((contractProg img.base ext).fnAddr preKeyTryFromName + 2588#64) s2
            (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
              pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
              A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
            (fun s3 P3 =>
              KyberExitA1cState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
              (P3 ⊢ (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
                  A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
                (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap)))
            (tryFromQp s0) := by
          dsimp only [contractProg, tripleRatchetProgAtExt] at hpc2 ⊢
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
          examples_hide_fetches
          refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + 1924#64) ?_
          wp_steps
          refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF2' hsym2' => ?_
          refine SepWPp.of_sepWP_end hF2' hsym2' ?_
          wp_steps
          refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
          refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hF3, hsym3,
                by simp [htr2, arm64_norm]⟩,
              hpos, hlt, hne_ptr,
              by simp [arm64_norm], by simp [arm64_norm],
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            by apply entails_of_eq; ac_rfl⟩
        refine SepWPp.bind h3 ?_; clear h3
        rintro s3 P3 hpc3 hrun3 ⟨hst3, hent3⟩
        refine SepWPp.mono_pre hent3 ?_
        refine SepWPp.frame_tryFrom (kyber_a1c_to_a24_wp hA hst3 hpc3 hrun3)
          fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
        refine Entails.trans (sepConj_mono_left hentf) ?_
        apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
