/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.Accept
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Owned-Error Rejecting Contract for `Pqxdh::accept` (`0x23920`)

Strengthens the rejecting branch (`Model.acceptKeys P inp = none`) of `Pqxdh::accept` so the
104-byte `Result<HandshakeKeys, SignalProtocolError>` output slot exposes `speWordsAt` together
with `pqxdhAcceptErrPayloadAt` (retaining the 28-byte heap `String` buffer on tag-24
`InvalidMessage` or witnessing tag-10 `InvalidKeyAgreement`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open Model

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3dd44
  libsignalSessionCode_fnOff_0x23920
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-- Owned heap payload of the `SignalProtocolError` returned by `pqxdhAccept` when
`Model.acceptKeys P inp = none`:
- `isStr = true`: tag 24 (`InvalidMessage`, `0x8000000000000018#64`) with heap `String` buffer at
  `(cap = w2, ptr = w3, len = w4)`,
- `isStr = false`: tag 10 (`InvalidKeyAgreement`, `0x800000000000000a#64`), plain payload. -/
def pqxdhAcceptErrPayloadAt (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) : SepProp :=
  ∃∗ isStr : Bool,
    if isStr then
      ⌜errTag = 0x8000000000000018#64⌝ ∗
      ∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = w4 ∧ bs.length ≤ w2.toNat ∧ w2.toNat < 2 ^ 63 ∧ w3 ≠ 0#64⌝ ∗
        (if w2 = 0#64 then emp
         else A.live w3 w2.toNat 1 ∗ (w3 ↦ₛ bs) ∗
           memRegion (w3 + BitVec.ofNat 64 bs.length) (w2.toNat - bs.length))
    else ⌜errTag = 0x800000000000000a#64⌝

/-- Owned-payload refinement of `pqxdhAcceptErrStrong2At` for the 104-byte
`Result<HandshakeKeys, SignalProtocolError>` sret slot `outPtr` of `Pqxdh::accept`. -/
def pqxdhAcceptErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗
  memRegion (outPtr + 4#64) 4 ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 48

/-- `pqxdhAcceptOptFieldsSpec` restricted to `Model.acceptKeys P g.inp = none` and strengthened
to expose `pqxdhAcceptErrOwnedAt A g.outPtr`. -/
def pqxdhAcceptErrOwnedInnerSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost where
  pre := fun (g : AcceptFieldsCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      Model.acceptKeys P g.inp = none⌝ ∗
    pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
    memRegion g.outPtr 104 ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s.sp pqxdhEntryStack ∗
    A.pool
  post := fun (g : AcceptFieldsCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
    (pqxdhAcceptErrOwnedAt A g.outPtr ∗ anyHeap) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗
    stackAt s0.sp pqxdhEntryStack ∗
    A.pool
  onPanic := rustPanicOnOom img

def pqxdhAcceptErrOwnedSpec (P : Primitives) (A : RustAlloc) (img : Obj.Image) :
    Spec AcceptFieldsCallGhost :=
  (pqxdhAcceptErrOwnedInnerSpec P A img).inImage img

/-! ## Separation-logic merge helpers -/

private theorem outPtr_tail64_to_spe_tail (outPtr : BitVec 64) (b40 : BitVec 8) :
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗ memRegion (outPtr + 56#64) 48 := by
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]
    exact Entails.sepExists_right b40 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hb40) ?_
  have hm64 :
      memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63 =
        (∃∗ w5 : BitVec 64, (outPtr + 40#64) ↦₆₄ w5) ∗
        (∃∗ w6 : BitVec 64, (outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 48 := by
    rw [← ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 1) (k := 63)
          (b' := outPtr + 41#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 8) (k := 56)
          (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 48)
          (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (outPtr + 40#64),
        ProofLib.memRegion_eight (outPtr + 48#64)]
  rw [hm64]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))

private theorem outPtr_err104_owned_merge (A : RustAlloc) (outPtr errTag w2 w3 w4 : BitVec 64)
    (b40 : BitVec 8) (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))))))) =
      (outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗
        ((((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) ∗
          (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
            ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
            pqxdhAcceptErrPayloadAt A errTag w2 w3 w4))) := by ac_rfl
  rw [hrearr]
  unfold pqxdhAcceptErrOwnedAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (outPtr_tail64_to_spe_tail outPtr b40)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem pqxdhAcceptErrPayloadAt_tag10_intro (A : RustAlloc) (w2 w3 w4 : BitVec 64) :
    emp ⊢ pqxdhAcceptErrPayloadAt A 0x800000000000000a#64 w2 w3 w4 := by
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← sepConj_emp ⌜True⌝, pure_sepConj_of_true trivial emp]
  exact Entails.refl _

private theorem outPtr_err104_owned_tag10_merge (A : RustAlloc) (outPtr w2 w3 w4 : BitVec 64)
    (b40 : BitVec 8) :
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ 0x800000000000000a#64) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  rw [← emp_sepConj ((outPtr ↦₃₂ 1#32) ∗ _)]
  exact Entails.trans
    (sepConj_mono_left (pqxdhAcceptErrPayloadAt_tag10_intro A w2 w3 w4))
    (outPtr_err104_owned_merge A outPtr 0x800000000000000a#64 w2 w3 w4 b40 (by decide))

private theorem err28_payload_intro (A : RustAlloc) (ptr u2 u3 : BitVec 64) (hptr : ptr ≠ 0#64) :
    memRegion ptr 12 ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) ∗ A.live ptr 28 1 ⊢
      pqxdhAcceptErrPayloadAt A 0x8000000000000018#64 28#64 ptr 28#64 := by
  have hm12 : memRegion ptr 12 =
      (∃∗ q0 : BitVec 64, ptr ↦₆₄ q0) ∗ (∃∗ q1 : BitVec 32, (ptr + 8#64) ↦₃₂ q1) := by
    rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 4)
          (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight ptr, memRegion_four (ptr + 8#64)]
  rw [hm12, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun q0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun q1 => ?_
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right true ?_
  simp only [↓reduceIte]
  rw [pure_sepConj_of_true trivial]
  let bs : List (BitVec 8) := unpack64 q0 ++ (unpack32 q1 ++ (unpack64 u2 ++ unpack64 u3))
  refine Entails.sepExists_right bs ?_
  have hbs_len : bs.length = 28 := by
    simp [bs, unpack64_length, unpack32_length]
  have hpure :
      BitVec.ofNat 64 bs.length = 28#64 ∧
      bs.length ≤ (28#64 : BitVec 64).toNat ∧
      (28#64 : BitVec 64).toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 := by
    rw [hbs_len]
    exact ⟨rfl, by decide, by decide, hptr⟩
  rw [pure_sepConj_of_true hpure]
  have h28_ne : (28#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [h28_ne, ↓reduceIte, hbs_len]
  have h28_nat : (28#64 : BitVec 64).toNat = 28 := rfl
  rw [h28_nat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  have hpts :
      (ptr ↦ₛ bs) =
        (ptr ↦₆₄ q0) ∗ ((ptr + 8#64) ↦₃₂ q1) ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) := by
    dsimp only [bs]
    rw [pointsToBytes_append, unpack64_length,
        pointsToBytes_append, unpack32_length,
        pointsToBytes_append, unpack64_length,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [hpts]
  exact Entails.of_eq (by ac_rfl)

/-! ## Rejecting `Pqxdh::accept` proof (`trTrapProgAt`) -/

set_option maxHeartbeats 1200000 in
theorem pqxdhAccept_err_owned_base_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks)
    (hag : PqxdhCalculateAgreementOk_trap P A img C absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptErrOwnedSpec P A img) := by
  have hb := base_aligned_of_loads himg
  have hA := hH.alloc
  unfold pqxdhAcceptErrOwnedSpec
  refine subroutine_ok_inImage_rodata4 (rodata_0x7c604 himg) (rodata_0x7c267 himg)
    (rodata_0x7ff6a himg) (rodata_0x81028 himg) ?_
  unfold pqxdhAcceptErrOwnedInnerSpec rustPanicOnOom
  have hfn : libsignalSessionCode.fnOff pqxdhAcceptSym = 0x23920 :=
    libsignalSessionCode_fnOff_0x23920
  have hcanon := subroutine_ok_rel_pqxdh_trap (ecPubKeyIsCanonical_call_ok_trap (C := C) hWF hH)
    libsignalSessionCode_fnOff_0x3dd44 hfn (k := 107556) (by decide)
  have hag' := subroutine_ok_rel_pqxdh_trap hag libsignalSessionCode_fnOff_0x3e6e0 hfn
    (k := 110016) (by decide)
  have hshim := pqxdh_shim_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    (name := pqxdhAcceptSym)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := pqxdh_alloc_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    hA (name := pqxdhAcceptSym)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := pqxdh_dealloc_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    hA (name := pqxdhAcceptSym)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x23920))
    (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := pqxdh_memcpy_region_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    (name := pqxdhAcceptSym)
    (k := num% (ls_off% "memcpy" - 0x23920))
    (by rw [hfn, (ls_stub% "memcpy")])
  have hpan_rawvec := pqxdh_panic_at_raw_vec_handle_error_trap (b := img.base) (C := C)
    (absHooks := absHooks) (name := pqxdhAcceptSym)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x23920))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hadrp_fa8_1 : (((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) + bv% (ls_str% "incoming base key is invalid" - 0x23000)) =
      img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_1 hb
  have hadrp_fa8_2 : (((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym +
    220#64 &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_str% "incoming base key is invalid") - 0x23000) +
      bv% ((ls_str% "incoming base key is invalid") % 4096)) =
      img.base + bv% (ls_str% "incoming base key is invalid") := by
    rw [Program.fnAddr_rebase, hfn]; exact accept_adrp_55604_2 hb
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.E2E.Pqxdh.pqxdhAccept
    img.base (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x23920 1728
  dsimp only [trTrapProgAt]
    at hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec hadrp_fa8_1 hadrp_fa8_2 ⊢
  clear himg hag hA hH hfn hb
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C absHooks))).fnAddr
      pqxdhAcceptSym = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C absHooks))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨inp, argPtr, pqskPtr, ctSlicePtr, ctBufPtr, outPtr⟩
  dsimp only at *
  subst ‹s0.readReg64 (.gpr 0#5) = argPtr› ‹s0.readReg64 (.gpr 8#5) = outPtr›
  have hacc_pre : Model.acceptKeys P inp = none := ‹Model.acceptKeys P inp = none›
  have hws : WellSizedAcceptKeysInput inp := ‹WellSizedAcceptKeysInput inp›
  rcases hws with ⟨hikBSk, _hikBPk, hspkBSk, _hspkBPk, _hopk_sz, hpqSk, _hpqPk, hikAPk, hekAPk,
    hkemCt⟩
  rw (occs := .pos [1]) [stackAt_pqxdh_accept_top s0.sp]
  refine SepWPp.fold (Entails.of_eq (pqsk_region_phaseA_split s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells4_sub4944_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  refine SepWPp.fold (Entails.of_eq (cells10_sub80_eq s0.sp)) (by sep_focus) ?_
  sep_elim_exists'
  have hF0 : FrozenRo img s0.mem := ‹FrozenRo img s0.mem›
  unfold pqxdhAcceptOptFieldsAt
  refine SepWPp.of_sepWP_frozen hF0 (mid := entry + 52#64) ?_
  wp_steps
  wp_call hcanon ⟨s0.readReg64 (.gpr 0#5) + 160#64, inp.hdr.ekAPk⟩
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1; try simp only [arm64_norm] at hF1
  cases hcanon_b : P.isCanonical inp.hdr.ekAPk
  · have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = false := hcanon_b
    simp only [hcanon_ec, Bool.false_eq_true, ↓reduceIte] at *
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP (mid := entry + 216#64) ?_
    wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call halloc (28, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc0 htr0 => ?_) (fun halloc0 halign0 htr0 => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
        (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (incoming_alloc_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold
        (Entails.of_eq (rodata_incoming_split1
          (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_
      apply SepWPp.of_sepWP_ret
      wp_simp_pre_fast [hadrp_fa8_1, hadrp_fa8_2, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_1_to_2
          (img.base + bv% (ls_str% "incoming base key is invalid"))))
        (by sep_focus) ?_
      wp_steps
      refine SepWP.fold
        (Entails.of_eq (rodata_incoming_split2
          (img.base + bv% (ls_str% "incoming base key is invalid"))).symm)
        (by sep_focus) ?_
      refine SepWP.fold (incoming_overlap_prep _ _ _) (by sep_focus) ?_
      sep_elim_exists'
      wp_steps
      refine SepWP.fold (err28_payload_intro A _ _ _ halloc0) (by sep_focus) ?_
      refine SepWP.fold
        (outPtr_err104_owned_merge A (s0.readReg64 (.gpr 8#5)) 0x8000000000000018#64
          28#64 _ 28#64 _ (by decide))
        (by sep_focus) ?_
      refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
      refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (pqsk_region_phaseA_merge s0.sp _) (by sep_focus) ?_
      refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
      clear hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec
      simp only [sepConj_assoc, *]
      wp_done
  · obtain ⟨ss, hss, _, _⟩ := kyberDecaps_some_and_fitBv8_eq hWF hpqSk hkemCt
    have hcanon_ec : P.isCanonicalEC inp.hdr.ekAPk = true := hcanon_b
    simp only [hcanon_ec, ↓reduceIte] at hpost
    rw [subStack_to_alloc s0.sp]
    refine SepWPp.of_sepWP_frozen hF1 (mid := entry + 72#64) ?_
    wp_steps; wp_call hshim (); wp_steps
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call halloc (192, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2; try simp only [arm64_norm] at hF2
    refine SepWPp.split_alloc (sp' := s0.sp - 4944#64) (by wp_norm_lhs)
      (fun halloc192 htr192 => ?_) (fun halloc192 halign192 htr192 => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x23920)) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.fold (Entails.of_eq (memRegion_192_init_split _)) (by sep_focus) ?_
      sep_elim_exists'
      refine SepWPp.fold (Entails.of_eq (alloc_to_calc_stack s0.sp)) (by sep_focus) ?_
      refine SepWPp.of_sepWP_frozen hF2 (mid := entry + 110016#64) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (pointsTo64_4_allOnes_eq_F_X25519 _)) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF3; try simp only [arm64_norm] at hF3
      refine SepWPp_call_hag hWF hag' hF3 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
        (s0.readReg64 (.gpr 0#5) + 128#64) inp.hdr.ikAPk (by wp_norm_lhs) (by wp_norm_lhs)
        hsp_align (by wp_norm_lhs) (ret_pc := entry + 120#64) (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hikAPk⟩
        (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
        (fun hdh1 sf1 hi1 u2_1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
        (fun hdh1 sf1 dh1_ptr hpc1 hrun1 hsp1 hcs1 htr1 hF4 => ?_)
      · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
          (by sep_focus) ?_
        sep_elim_exists'
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.fold (vec_err_dh1_merge _) (by sep_focus) ?_
        apply SepWPp.of_sepWP_ret
        wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
        refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
        refine SepWP.fold
          (outPtr_err104_owned_tag10_merge A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
        refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
        clear hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec
        simp only [sepConj_assoc, *]
        wp_done
      · have hdh1_len : (P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 32 := hWF.x25519_len _ _
        have hdh1_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)).length = 32 := by
          simp [bytesToBv8, hdh1_len]
        have hpfx1_len : (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk).length = 64 := by
          simp [F_X25519, hdh1_len]
        dsimp only [CalleeSavedPreserved, Reg.fp] at hcs1
        rcases hcs1 with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28,
          hcs29⟩
        simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
        refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
        refine SepWPp.of_sepWP_frozen hF4 (mid := entry + 110016#64) ?_
        wp_steps
        wp_call hmemcpy ⟨_, dh1_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ikAPk)⟩
        wp_steps
        refine SepWP.fold (hdh1_bv_len ▸ pointsToBytes_entails_memRegion dh1_ptr _)
          (by sep_focus) ?_
        wp_call hdealloc (dh1_ptr, 32, 1); wp_steps
        refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh1_ptr 32#64)
          (by sep_focus) ?_
        refine SepWP.fold
          (Entails.of_eq (pointsToBytes_append_at _ F_X25519
            (P.x25519 inp.spkBSk inp.hdr.ikAPk) 32 (by decide)))
          (by sep_focus) ?_
        refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
        · simp only [arm64_norm, *]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF5; try simp only [arm64_norm] at hF5
        refine SepWPp_call_hag hWF hag' hF5 (s0.readReg64 (.gpr 0#5) + 32#64) inp.ikBSk
          (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
          (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := entry + 304#64)
          (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hikBSk, hekAPk⟩
          (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
          (fun hdh2 sf2 hi2 u2_2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
          (fun hdh2 sf2 dh2_ptr hpc2 hrun2 hsp2 hcs2 htr2 hF6 => ?_)
        · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
            (by sep_focus) ?_
          sep_elim_exists'
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.fold (vec_err_dh2_merge _ hpfx1_len) (by sep_focus) ?_
          apply SepWPp.of_sepWP_ret
          wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
          refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
          refine SepWP.fold
            (outPtr_err104_owned_tag10_merge A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
            (by sep_focus) ?_
          refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
          refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm) (by sep_focus) ?_
          clear hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec
          simp only [sepConj_assoc, *]
          wp_done
        · have hdh2_len : (P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
          have hdh2_bv_len : (bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)).length = 32 := by
            simp [bytesToBv8, hdh2_len]
          have hpfx2_len :
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                P.x25519 inp.ikBSk inp.hdr.ekAPk).length = 96 := by
            simp [F_X25519, hdh1_len, hdh2_len]
          dsimp only [CalleeSavedPreserved, Reg.fp] at hcs2
          rcases hcs2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
            hcs2_27, hcs2_28, hcs2_29⟩
          simp only [arm64_norm]
            at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28
               hcs2_29
          refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
          refine SepWPp.of_sepWP_frozen hF6 (mid := entry + 110016#64) ?_
          wp_steps
          wp_call hmemcpy ⟨_, dh2_ptr, bytesToBv8 (P.x25519 inp.ikBSk inp.hdr.ekAPk)⟩
          wp_steps
          refine SepWP.fold (hdh2_bv_len ▸ pointsToBytes_entails_memRegion dh2_ptr _)
            (by sep_focus) ?_
          wp_call hdealloc (dh2_ptr, 32, 1); wp_steps
          refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh2_ptr 32#64)
            (by sep_focus) ?_
          refine SepWP.fold
            (Entails.of_eq (pointsToBytes_append_at _
              (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk)
              (P.x25519 inp.ikBSk inp.hdr.ekAPk) 64
              (by simp only [bytesToBv8, List.length_map, hpfx1_len])))
            (by sep_focus) ?_
          refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
          · simp only [arm64_norm, *]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF7; try simp only [arm64_norm] at hF7
          refine SepWPp_call_hag hWF hag' hF7 (s0.readReg64 (.gpr 0#5) + 96#64) inp.spkBSk
            (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
            (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := entry + 404#64)
            (by wp_norm_lhs) (by wp_norm_lhs)
            ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hspkBSk, hekAPk⟩
            (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
            (fun hdh3 sf3 hi3 u2_3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
            (fun hdh3 sf3 dh3_ptr hpc3 hrun3 hsp3 hcs3 htr3 hF8 => ?_)
          · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
              (by sep_focus) ?_
            sep_elim_exists'
            refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
            refine SepWPp.fold (vec_err_dh3_merge _ hpfx2_len) (by sep_focus) ?_
            apply SepWPp.of_sepWP_ret
            wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
            refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
            refine SepWP.fold
              (outPtr_err104_owned_tag10_merge A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
              (by sep_focus) ?_
            refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
            refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
            · simp only [arm64_norm, *]
            refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
              (by sep_focus) ?_
            clear hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec
            simp only [sepConj_assoc, *]
            wp_done
          · have hdh3_len : (P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 32 := hWF.x25519_len _ _
            have hdh3_bv_len : (bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)).length = 32 := by
              simp [bytesToBv8, hdh3_len]
            have hpfx3_len :
                (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                  P.x25519 inp.ikBSk inp.hdr.ekAPk ++
                  P.x25519 inp.spkBSk inp.hdr.ekAPk).length = 128 := by
              simp [F_X25519, hdh1_len, hdh2_len, hdh3_len]
            dsimp only [CalleeSavedPreserved, Reg.fp] at hcs3
            rcases hcs3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25,
              hcs3_26, hcs3_27, hcs3_28, hcs3_29⟩
            simp only [arm64_norm]
              at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28
                 hcs3_29
            cases hopk_eq : inp.opkBSk? with
            | none =>
              have hacc_some :=
                acceptKeys_eq_some_of_opk_none P inp ss ‹inp.trustedPeer = true›
                  ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                  ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hss
              rw [hacc_pre] at hacc_some
              cases hacc_some
            | some opkSk =>
              have hopkSk : opkSk.length = 32 := _hopk_sz opkSk hopk_eq
              simp only [↓reduceIte]
              refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
              refine SepWPp.of_sepWP_frozen hF8 (mid := entry + 110016#64) ?_
              wp_steps
              wp_call hmemcpy ⟨_, dh3_ptr, bytesToBv8 (P.x25519 inp.spkBSk inp.hdr.ekAPk)⟩
              wp_steps
              refine SepWP.fold (hdh3_bv_len ▸ pointsToBytes_entails_memRegion dh3_ptr _)
                (by sep_focus) ?_
              wp_call hdealloc (dh3_ptr, 32, 1)
              refine SepWP.fold (alloc_to_alloc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              wp_steps
              refine SepWP.fold (cells3_sub4912_to_memRegion24 s0.sp 0#64 dh3_ptr 32#64)
                (by sep_focus) ?_
              refine SepWP.fold
                (Entails.of_eq (pointsToBytes_append_at _
                  (F_X25519 ++ P.x25519 inp.spkBSk inp.hdr.ikAPk ++
                    P.x25519 inp.ikBSk inp.hdr.ekAPk)
                  (P.x25519 inp.spkBSk inp.hdr.ekAPk) 96
                  (by simp only [bytesToBv8, List.length_map, hpfx2_len])))
                (by sep_focus) ?_
              refine SepWP.fold (alloc_to_calc_stack_of_eq s0.sp _ ?_) (by sep_focus) ?_
              · simp only [arm64_norm, *]
              apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
              intro hF8_1; try simp only [arm64_norm] at hF8_1
              refine SepWPp_call_hag hWF hag' hF8_1 (s0.readReg64 (.gpr 0#5) + 265#64) opkSk
                (s0.readReg64 (.gpr 0#5) + 160#64) inp.hdr.ekAPk (by wp_norm_lhs)
                (by wp_norm_lhs) hsp_align (by wp_norm_lhs) (ret_pc := entry + 720#64)
                (by wp_norm_lhs) (by wp_norm_lhs)
                ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hopkSk, hekAPk⟩
                (by sep_focus) (allowPanic_hag (by wp_norm_lhs))
                (fun hdh4 sf4 hi4 u2_4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
                (fun hdh4 sf4 dh4_ptr hpc4 hrun4 hsp4 hcs4 htr4 hF8_2 => ?_)
              · dsimp only [CalleeSavedPreserved, Reg.fp] at hcs4
                rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25,
                  hcs4_26, hcs4_27, hcs4_28, hcs4_29⟩
                simp only [arm64_norm]
                  at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28
                     hcs4_29
                refine SepWPp.fold (Entails.of_eq (outPtr_err104_split (s0.readReg64 (.gpr 8#5))))
                  (by sep_focus) ?_
                sep_elim_exists'
                refine SepWPp.fold (Entails.of_eq (calc_to_alloc_stack s0.sp)) (by sep_focus) ?_
                refine SepWPp.fold (vec_err_dh4_merge _ hpfx3_len) (by sep_focus) ?_
                apply SepWPp.of_sepWP_ret
                wp_steps; wp_call hdealloc (_, 192, 1); wp_steps
                refine SepWP.fold emp_entails_anyHeap (by sep_focus) ?_
                refine SepWP.fold
                  (outPtr_err104_owned_tag10_merge A (s0.readReg64 (.gpr 8#5)) _ _ _ _)
                  (by sep_focus) ?_
                refine SepWP.fold (cells_sub4944_4_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (pqsk_region_phaseA_cells_merge s0.sp _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (cells_sub80_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
                refine SepWP.fold (subStack_to_alloc_of_eq s0.sp _ ?_) (by sep_focus) ?_
                · simp only [arm64_norm, *]
                refine SepWP.fold (Entails.of_eq (stackAt_pqxdh_accept_top s0.sp).symm)
                  (by sep_focus) ?_
                clear hcanon hag' hshim halloc hdealloc hmemcpy hpan_rawvec
                simp only [sepConj_assoc, *]
                wp_done
              · have hacc_some :=
                  acceptKeys_eq_some_of_opk_some P inp opkSk ss ‹inp.trustedPeer = true›
                    ‹inp.replayOk = true› hikAPk hekAPk hcanon_b hdh1 hdh2 hdh3
                    ‹inp.hdr.opkId?.isSome = inp.opkBSk?.isSome› hopk_eq hdh4 hss
                rw [hacc_pre] at hacc_some
                cases hacc_some

end CryptoVerification.E2E.Pqxdh.ResponderCore
