/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

theorem logOff_eq (img : Obj.Image) :
    logOff img = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
  rfl

/-!
# `<SignalMessage>::try_from` Post-Loop `ratchet_key = Some(rk)` Head (`+0x3b0 .. +0x4c4`)

Proves `post_rk_some_head_wp` and its relocatable `[LibsignalPlacement]` counterpart
`post_rk_some_head_wp_placed` (Block `85`), unpacking wire headers, dropping the scratch
`SignalProtocolError`, and calling `PublicKey::deserialize` into `sp' + 176`.
-/

/-- The part of `vecU8Buf A cap ptr bs` besides `(ptr ↦ₛ bs)`. -/
def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Buf_entails_slice_rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold vecU8Buf vecU8BufRest
  refine Entails.pure_left fun h => ?_
  have hle := h.1
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := by simp at hle; exact hle
    subst hbs
    simp only [pure_true_emp h, emp_sepConj, pointsToBytes_nil]
    exact Entails.refl _
  · simp only [pure_true_emp h, emp_sepConj, hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl

theorem slice_rest_entails_vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ⊢ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf vecU8BufRest
  rw [sepConj_left_comm (ptr ↦ₛ bs)]
  refine Entails.pure_left fun h => ?_
  have hle := h.1
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := by simp at hle; exact hle
    subst hbs
    rw [pure_true_emp h, emp_sepConj, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · rw [pure_true_emp h, emp_sepConj]
    simp only [hcap, ↓reduceIte]
    apply entails_of_eq; ac_rfl

theorem base_aligned {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    (img.base &&& 0xfff#64) = 0#64 := by
  have hal := ProofLib.ObjectLoad.Loads.aligned h
  unfold Obj.pageSize at hal
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xfff#64 : BitVec 64).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact hal

theorem memRegion48_split33_15 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 48 =
      memRegion (sp' + 176#64) 33 ∗ memRegion (sp' + 209#64) 15 := by
  have hs := memRegion_split (sp' + 176#64) 33 15 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs
  exact hs

theorem spe40_of_rk_ct (sp' rkPtr rkLen ctCap ctPtr ctLen : BitVec 64) :
    ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen ⊢
      memRegion (sp' + 184#64) 40 := by
  have hs1 := memRegion_split (sp' + 184#64) 8 32 (by decide)
  have hs2 := memRegion_split (sp' + 184#64 + 8#64) 8 24 (by decide)
  rw [hs1, hs2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion (sp' + 184#64) rkPtr)
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 192#64) rkLen)
      (vecHeader_entails_memRegion24 (sp' + 200#64) ctCap ctPtr ctLen))

theorem wireTail64_entails_memRegion64 (sp' pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64)
    (cTag cVal pcTag pcVal : BitVec 32) :
    vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
      vecHeader (sp' + 248#64) adCap adPtr adLen ∗
      ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
      ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ⊢
      memRegion (sp' + 224#64) 64 := by
  have hc8 : ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ⊢ memRegion (sp' + 272#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 272#64) cTag cVal
  have hpc8 : ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ⊢ memRegion (sp' + 280#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair_entails_memRegion8 (sp' + 280#64) pcTag pcVal
  have hs1 := memRegion_split (sp' + 224#64) 24 40 (by decide)
  have hs2 := memRegion_split (sp' + 224#64 + 24#64) 24 16 (by decide)
  have hs3 := memRegion_split (sp' + 224#64 + 24#64 + 24#64) 8 8 (by decide)
  rw [hs1, hs2, hs3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [← sepConj_assoc ((sp' + 272#64) ↦₃₂ cTag)]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 224#64) pqCap pqPtr pqLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 248#64) adCap adPtr adLen)
      (sepConj_mono hc8 hpc8))

/-- Step `+0x3b0..+0x4c4` (`944..1220`) when `res = some m'` and `m'.ratchetKey = some rk`:
loads all wire headers, spills fields to stack, calls `drop_in_place<SPE>` (`+0x4ac`),
and calls `PublicKey::deserialize` (`+0x4c0`) into `sp' + 176`. -/
theorem post_rk_some_head_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    {s0 s : State}
    {sp' x19 x20 x21 x23 w16 w32 w40 w72 w80 w88 w96
      rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w28 w48 w60 w64 cTag cVal pcTag pcVal : BitVec 32}
    (rk : List (BitVec 8))
    (hst : LoopExitState img s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x4c4#64) s
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        sf.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x4c4#64 ∧
        sf.status = .Running ∧
        sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
        sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = adCap ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 rk.length ∧
        sf.readReg64 .x25 = pqCap ∧ sf.readReg64 .x26 = rkPtr ∧
        sf.readReg64 .x27 = ctCap ∧ sf.readReg64 .x28 = ctPtr ∧
        (Pf ⊢ ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
          ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
          memRegion (sp' + 209#64) 15 ∗
          memRegion (sp' + 224#64) 64 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hF, hsym, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx20 : s.readReg64 .x20 = x20 := hregs.x20_eq
  have hx21 : s.readReg64 .x21 = x21 := hregs.x21_eq
  have hx23 : s.readReg64 .x23 = x23 := hregs.x23_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hcallSpe := dropSpe_ok_sub hDropSpe
  clear hDropSpe
  have hcallDeser : subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
      ((deserializeFullSpec img.base).inImage img) :=
    deserializeFull_ok_at_tripleRatchet (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") (k := num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) (by decide)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (vecU8Buf_entails_slice_rest A rkCap rkPtr rk)))))))))))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre (P' :=
      ⌜rk.length ≤ rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre (fun ⟨hrk_le, hrk_lt, _⟩ => ?_)
  have hrk_add2 := cap_add2_ne_of_lt hrk_lt
  have hrk_add1 := cap_add1_eq_of_lt hrk_lt
  have hstackSpe := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  tryFrom_fetches2 img.base C ctl abs 944 24
  tryFrom_fetches2 img.base C ctl abs 1060 8
  tryFrom_fetches2 img.base C ctl abs 1120 100
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.mono_pre (P' :=
      ((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
      ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
      ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
      ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
      ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
      ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
      ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
      ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
      ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
      ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
      logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.refl _) ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hspe40 := spe40_of_rk_ct sp' rkPtr (BitVec.ofNat 64 rk.length) ctCap ctPtr ctLen
  have htail64 := wireTail64_entails_memRegion64 sp' pqCap pqPtr pqLen adCap adPtr adLen
    cTag cVal pcTag pcVal
  have hspe_eq : speAt A [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine SepWPp.mono_pre (P' :=
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗
      (((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen) ∗
      (vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
      ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
      logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      apply entails_of_eq
      simp only [arm64_norm]
      ac_rfl) ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono hspe40 (sepConj_mono_left htail64))) ?_
  refine SepWPp.call_noPanic_tryFrom (⟨sp' + 176#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hF1 hsym1
    (ret_pc := entry + bv% (1200)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 176#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64)
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    rfl
    (by rw [hspe_eq, hstackSpe, hsp_eq]; sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropSpeSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 rk.length := by simp [hx24_cs, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = rkPtr := by simp [hx26_cs, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, arm64_norm]
  have hrk_len_lt : rk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrk_le hrk_lt
  have hrk_toNat : (BitVec.ofNat 64 rk.length).toNat = rk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  have h48_split := memRegion48_split33_15 sp'
  have hlog := logOff_eq img
  refine SepWPp.call_noPanic_tryFrom (rkPtr, rk, sp' + 176#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hF3 hsym3
    (ret_pc := entry + bv% (1220)) (by simp [arm64_norm])
    (T := (rkPtr ↦ₛ rk) ∗ memRegion (sp' + 176#64) 33 ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
    (φ := rkPtr = rkPtr ∧ (BitVec.ofNat 64 rk.length).toNat = rk.length ∧
      sp' + 176#64 = sp' + 176#64 ∧ rk.length < 2 ^ 63 ∧ (img.base &&& 0xfff#64) = 0#64)
    (by simp [deserializeFullSpec, arm64_norm])
    ⟨rfl, hrk_toNat, rfl, hrk_len_lt, hb⟩
    (by rw [h48_split, hlog]; sep_focus)
    ?_
  clear hcallDeser
  intro s4 hpc4 hrun4 hsp4 hsp4_align hF4 hsym4 hcs4
  dsimp only [deserializeFullSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr4 => ?_)
  rcases hcs4 with ⟨hx19_4cs, hx20_4cs, hx21_4cs, hx22_4cs, hx23_4cs, hx24_4cs, hx25_4cs, hx26_4cs, hx27_4cs, hx28_4cs, _⟩
  refine SepWPp.of_sepWP_end hF4 hsym4 ?_
  refine SepWP.done (by simp [hpc4, arm64_norm]) hrun4 ?_
  intro _ _
  refine ⟨PostEpilogueState.of_steps hF4 hsym4 (by simp [hsp4, hsp2_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr4, htr2_eq, arm64_norm]),
    by simp [hpc4, arm64_norm], hrun4,
    by simp [hx19_4cs, hx19_2, arm64_norm],
    by simp [hx20_4cs, hx20_2, arm64_norm],
    by simp [hx21_4cs, hx21_2, arm64_norm],
    by simp [hx22_4cs, hx22_2, arm64_norm],
    by simp [hx23_4cs, hx23_2, arm64_norm],
    by simp [hx24_4cs, hx24_2, arm64_norm],
    by simp [hx25_4cs, hx25_2, arm64_norm],
    by simp [hx26_4cs, hx26_2, arm64_norm],
    by simp [hx27_4cs, hx27_2, arm64_norm],
    by simp [hx28_4cs, hx28_2, arm64_norm],
    ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A rkCap rkPtr rk
  rw [← hlog]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepack)))))))))))))))
  apply entails_of_eq
  simp only [hstackSpe, hsp_eq, arm64_norm]
  ac_rfl

theorem tryFrom_eq_of_gt9 {bs : List (BitVec 8)} (hgt9 : 9 < bs.length)
    (hge3 : ¬ ((bs.headD 0#8) >>> 4) < 3#8) (hle4 : ¬ 4#8 < ((bs.headD 0#8) >>> 4)) :
    SignalMessage.tryFrom protoSignalCodec bs =
      match decode ((bs.take (bs.length - 8)).drop 1) with
      | none => .error .invalidProtobufEncoding
      | some p =>
        match p.ratchetKey with
        | none => .error .invalidProtobufEncoding
        | some rk =>
          match PublicKey.deserialize rk with
          | .error e => .error e
          | .ok senderRatchetKey =>
            match p.counter with
            | none => .error .invalidProtobufEncoding
            | some counter =>
              match p.ciphertext with
              | none => .error .invalidProtobufEncoding
              | some ciphertext =>
                .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey, counter,
                      previousCounter := p.previousCounter.getD 0#32, ciphertext,
                      pqRatchet := p.pqRatchet.getD [], addresses := p.addresses,
                      serialized := bs } := by
  have hnotlt : ¬ bs.length < 8 + 1 := by omega
  have hv3 : ¬ ((bs.headD 0) >>> 4) < preKyberVersion := hge3
  have hv4 : ¬ currentVersion < ((bs.headD 0) >>> 4) := hle4
  have hcodec : protoSignalCodec.decode = LibsignalProtoCodec.decode := rfl
  unfold SignalMessage.tryFrom
  have hmac : macLength = 8 := rfl
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    hmac, hnotlt, hv3, hv4, ↓reduceIte, hcodec]
  cases LibsignalProtoCodec.decode ((bs.take (bs.length - 8)).drop 1) with
  | none => rfl
  | some p =>
    dsimp only
    cases p.ratchetKey with
    | none => rfl
    | some rk =>
      dsimp only
      cases PublicKey.deserialize rk with
      | error e => rfl
      | ok pk =>
        dsimp only
        cases p.counter with
        | none => rfl
        | some cnt =>
          dsimp only
          cases p.ciphertext <;> rfl

theorem msg_bounds_of_decode {bs : List (BitVec 8)} {m' : ProtoSignalMessage}
    {ct : List (BitVec 8)}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hct : m'.ciphertext = some ct) :
    macLength + 1 ≤ bs.length ∧ bs.length < 2 ^ 40 ∧
      ct.length < 2 ^ 40 ∧ (m'.pqRatchet.getD []).length < 2 ^ 40 ∧
      (∀ ad, m'.addresses = some ad → ad.length < 2 ^ 40) := by
  have hfields := decode_field_lengths hdec
  rcases hfields with ⟨_, hct_le, hpq_le, had_le⟩
  have hsub_le : ((bs.take (bs.length - 8)).drop 1).length ≤ bs.length := by
    simp only [List.length_drop, List.length_take]
    omega
  rw [hct, Option.getD_some] at hct_le
  have hmac : macLength = 8 := rfl
  refine ⟨by omega, by omega, by omega, by omega, fun ad had => ?_⟩
  rw [had, Option.getD_some] at had_le
  omega

def spUnused104 (sp' : BitVec 64) : SepProp :=
  memRegion (sp' + 113#64) 7 ∗ memRegion (sp' + 126#64) 2 ∗
    memRegion (sp' + 135#64) 1 ∗ memRegion (sp' + 160#64) 16

theorem sevenBytesHeadAt_entails_memRegion7 (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    sevenBytesHeadAt a b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion a 7 := by
  dsimp only [sevenBytesHeadAt]
  have hs1 := memRegion_split a 4 3 (by decide)
  have hs2 := memRegion_split (a + 4#64) 1 2 (by decide)
  have hs3 := memRegion_split (a + 4#64 + 1#64) 1 1 (by decide)
  rw [hs1, hs2, hs3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion a _)
    (sepConj_mono (pointsTo8_entails_memRegion (a + 4#64) b4)
      (sepConj_mono (pointsTo8_entails_memRegion (a + 5#64) b5)
        (pointsTo8_entails_memRegion (a + 6#64) b6)))

theorem memRegion72_104_pack (sp' w104 w136 w144 w152 : BitVec 64)
    (w120 : BitVec 32) (w124 : BitVec 16) (b112 c0 c1 c2 c3 c4 c5 c6 : BitVec 8) :
    spUnused104 sp' ∗
      ((sp' + 104#64) ↦₆₄ w104) ∗ ((sp' + 112#64) ↦₈ b112) ∗
      ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
      sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
      vecHeader (sp' + 136#64) w136 w144 w152 ⊢
      memRegion (sp' + 104#64) 72 := by
  have hs1 := memRegion_split (sp' + 104#64) 8 64 (by decide)
  have hs2 := memRegion_split (sp' + 104#64 + 8#64) 1 63 (by decide)
  have hs3 := memRegion_split (sp' + 104#64 + 8#64 + 1#64) 7 56 (by decide)
  have hs4 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64) 4 52 (by decide)
  have hs5 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 50 (by decide)
  have hs6 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64) 2 48 (by decide)
  have hs7 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64 + 2#64) 7 41 (by decide)
  have hs8 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64 + 2#64 + 7#64) 1 40 (by decide)
  have hs9 := memRegion_split (sp' + 104#64 + 8#64 + 1#64 + 7#64 + 4#64 + 2#64 + 2#64 + 7#64 + 1#64) 24 16 (by decide)
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [spUnused104]
  refine Entails.trans (Q := ((sp' + 104#64) ↦₆₄ w104) ∗ ((sp' + 112#64) ↦₈ b112) ∗
      memRegion (sp' + 113#64) 7 ∗ ((sp' + 120#64) ↦₃₂ w120) ∗
      ((sp' + 124#64) ↦₁₆ w124) ∗ memRegion (sp' + 126#64) 2 ∗
      sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
      memRegion (sp' + 135#64) 1 ∗ vecHeader (sp' + 136#64) w136 w144 w152 ∗
      memRegion (sp' + 160#64) 16)
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion (sp' + 104#64) w104)
    (sepConj_mono (pointsTo8_entails_memRegion (sp' + 112#64) b112)
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 120#64) w120)
        (sepConj_mono (pointsTo16_entails_memRegion (sp' + 124#64) w124)
          (sepConj_mono_right (sepConj_mono
            (sevenBytesHeadAt_entails_memRegion7 (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6)
            (sepConj_mono_right (sepConj_mono_left
              (vecHeader_entails_memRegion24 (sp' + 136#64) w136 w144 w152)))))))))

theorem post_memRegion_two_entails (a : BitVec 64) :
    memRegion a 2 ⊢ ∃∗ w : BitVec 16, a ↦₁₆ w := by
  rw [memRegion_eq_exists_bytes a 2 (by decide)]
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try simp at hlen
  have heq : (a ↦₁₆ (b1 ++ b0)) = (a ↦ₛ [b0, b1]) := by
    rw [pointsTo16_eq_pointsToBytes, unpack16_append2]
  rw [ ← heq ]
  exact Entails.sepExists_intro (b1 ++ b0)

theorem post_memRegion_seven_entails (a : BitVec 64) :
    memRegion a 7 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
        sevenBytesHeadAt a c0 c1 c2 c3 c4 c5 c6 := by
  have hs1 := memRegion_split a 4 3 (by decide)
  have hs2 := memRegion_split (a + 4#64) 1 2 (by decide)
  have hs3 := memRegion_split (a + 4#64 + 1#64) 1 1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3
  rw [hs1, hs2, hs3]
  refine Entails.trans
    (sepConj_mono (memRegion_four_entails a)
      (sepConj_mono (post_memRegion_one_entails (a + 4#64))
        (sepConj_mono (post_memRegion_one_entails (a + 5#64))
          (post_memRegion_one_entails (a + 6#64))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c6 => ?_
  have hw0 : w0 = w0.extractLsb' 24 8 ++ w0.extractLsb' 16 8 ++
      w0.extractLsb' 8 8 ++ w0.extractLsb' 0 8 := by bv_kernel
  refine Entails.trans ?_ (Entails.sepExists_intro (w0.extractLsb' 0 8))
  refine Entails.trans ?_ (Entails.sepExists_intro (w0.extractLsb' 8 8))
  refine Entails.trans ?_ (Entails.sepExists_intro (w0.extractLsb' 16 8))
  refine Entails.trans ?_ (Entails.sepExists_intro (w0.extractLsb' 24 8))
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  dsimp only [sevenBytesHeadAt]
  rw [ ← hw0 ]
  exact Entails.refl _

theorem memRegion24_entails_vecHeader (a : BitVec 64) :
    memRegion a 24 ⊢ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      vecHeader a w0 w1 w2 := by
  have hs1 := memRegion_split a 8 16 (by decide)
  have hs2 := memRegion_split (a + 8#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2
  rw [hs1, hs2, memRegion_eight a, memRegion_eight (a + 8#64), memRegion_eight (a + 16#64)]
  dsimp only [vecHeader]
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion72_104_unpack (sp' : BitVec 64) :
    memRegion (sp' + 104#64) 72 ⊢
      ∃∗ w104 : BitVec 64, ∃∗ b112 : BitVec 8,
      ∃∗ w120 : BitVec 32, ∃∗ w124 : BitVec 16,
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
      ∃∗ w136 : BitVec 64, ∃∗ w144 : BitVec 64, ∃∗ w152 : BitVec 64,
        spUnused104 sp' ∗
        ((sp' + 104#64) ↦₆₄ w104) ∗ ((sp' + 112#64) ↦₈ b112) ∗
        ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
        sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
        vecHeader (sp' + 136#64) w136 w144 w152 := by
  have hs1 := memRegion_split (sp' + 104#64) 8 64 (by decide)
  have hs2 := memRegion_split (sp' + 112#64) 1 63 (by decide)
  have hs3 := memRegion_split (sp' + 113#64) 7 56 (by decide)
  have hs4 := memRegion_split (sp' + 120#64) 4 52 (by decide)
  have hs5 := memRegion_split (sp' + 124#64) 2 50 (by decide)
  have hs6 := memRegion_split (sp' + 126#64) 2 48 (by decide)
  have hs7 := memRegion_split (sp' + 128#64) 7 41 (by decide)
  have hs8 := memRegion_split (sp' + 135#64) 1 40 (by decide)
  have hs9 := memRegion_split (sp' + 136#64) 24 16 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, memRegion_eight (sp' + 104#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (post_memRegion_one_entails (sp' + 112#64))
      (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 120#64))
        (sepConj_mono (post_memRegion_two_entails (sp' + 124#64))
          (sepConj_mono_right (sepConj_mono (post_memRegion_seven_entails (sp' + 128#64))
            (sepConj_mono_right (sepConj_mono_left
              (memRegion24_entails_vecHeader (sp' + 136#64))))))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w104 => Entails.sepExists_elim fun b112 =>
    Entails.sepExists_elim fun w120 => Entails.sepExists_elim fun w124 =>
    Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => Entails.sepExists_elim fun w136 =>
    Entails.sepExists_elim fun w144 => Entails.sepExists_elim fun w152 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w104)
  refine Entails.trans ?_ (Entails.sepExists_intro b112)
  refine Entails.trans ?_ (Entails.sepExists_intro w120)
  refine Entails.trans ?_ (Entails.sepExists_intro w124)
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  refine Entails.trans ?_ (Entails.sepExists_intro w136)
  refine Entails.trans ?_ (Entails.sepExists_intro w144)
  refine Entails.trans ?_ (Entails.sepExists_intro w152)
  dsimp only [spUnused104]
  apply entails_of_eq; ac_rfl

def spUnused0 (sp' : BitVec 64) : SepProp :=
  memRegion sp' 12 ∗ memRegion (sp' + 24#64) 4 ∗ memRegion (sp' + 56#64) 4

theorem memRegion104_0_pack (sp' : BitVec 64)
    (w12 w28 w48 w52 w60 w64 w68 : BitVec 32)
    (w16 w32 w40 w72 w80 w88 w96 : BitVec 64) :
    spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ w16) ∗
      ((sp' + 28#64) ↦₃₂ w28) ∗ ((sp' + 32#64) ↦₆₄ w32) ∗
      ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₃₂ w48) ∗
      ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
      ((sp' + 64#64) ↦₃₂ w64) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ⊢
      memRegion sp' 104 := by
  have hs1 := memRegion_split sp' 12 92 (by decide)
  have hs2 := memRegion_split (sp' + 12#64) 4 88 (by decide)
  have hs3 := memRegion_split (sp' + 16#64) 8 80 (by decide)
  have hs4 := memRegion_split (sp' + 24#64) 4 76 (by decide)
  have hs5 := memRegion_split (sp' + 28#64) 4 72 (by decide)
  have hs6 := memRegion_split (sp' + 32#64) 8 64 (by decide)
  have hs7 := memRegion_split (sp' + 40#64) 8 56 (by decide)
  have hs8 := memRegion_split (sp' + 48#64) 4 52 (by decide)
  have hs9 := memRegion_split (sp' + 52#64) 4 48 (by decide)
  have hs10 := memRegion_split (sp' + 56#64) 4 44 (by decide)
  have hs11 := memRegion_split (sp' + 60#64) 4 40 (by decide)
  have hs12 := memRegion_split (sp' + 64#64) 4 36 (by decide)
  have hs13 := memRegion_split (sp' + 68#64) 4 32 (by decide)
  have hs14 := memRegion_split (sp' + 72#64) 8 24 (by decide)
  have hs15 := memRegion_split (sp' + 80#64) 8 16 (by decide)
  have hs16 := memRegion_split (sp' + 88#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 12#64) w12)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 16#64) w16)
        (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 28#64) w28)
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 32#64) w32)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 40#64) w40)
              (sepConj_mono (pointsTo32_entails_memRegion (sp' + 48#64) w48)
                (sepConj_mono (pointsTo32_entails_memRegion (sp' + 52#64) w52)
                  (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion (sp' + 60#64) w60)
                    (sepConj_mono (pointsTo32_entails_memRegion (sp' + 64#64) w64)
                      (sepConj_mono (pointsTo32_entails_memRegion (sp' + 68#64) w68)
                        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 72#64) w72)
                          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 80#64) w80)
                            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 88#64) w88)
                              (pointsTo64_entails_memRegion (sp' + 96#64) w96)))))))))))))))))
  dsimp only [spUnused0]
  apply entails_of_eq; ac_rfl

theorem memRegion104_0_unpack (sp' : BitVec 64) :
    memRegion sp' 104 ⊢
      ∃∗ w12 : BitVec 32, ∃∗ w16 : BitVec 64, ∃∗ w28 : BitVec 32,
      ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 32,
      ∃∗ w52 : BitVec 32, ∃∗ w60 : BitVec 32, ∃∗ w64 : BitVec 32,
      ∃∗ w68 : BitVec 32, ∃∗ w72 : BitVec 64, ∃∗ w80 : BitVec 64,
      ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64,
        spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ w16) ∗
        ((sp' + 28#64) ↦₃₂ w28) ∗ ((sp' + 32#64) ↦₆₄ w32) ∗
        ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₃₂ w48) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
        ((sp' + 64#64) ↦₃₂ w64) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) := by
  have hs1 := memRegion_split sp' 12 92 (by decide)
  have hs2 := memRegion_split (sp' + 12#64) 4 88 (by decide)
  have hs3 := memRegion_split (sp' + 16#64) 8 80 (by decide)
  have hs4 := memRegion_split (sp' + 24#64) 4 76 (by decide)
  have hs5 := memRegion_split (sp' + 28#64) 4 72 (by decide)
  have hs6 := memRegion_split (sp' + 32#64) 8 64 (by decide)
  have hs7 := memRegion_split (sp' + 40#64) 8 56 (by decide)
  have hs8 := memRegion_split (sp' + 48#64) 4 52 (by decide)
  have hs9 := memRegion_split (sp' + 52#64) 4 48 (by decide)
  have hs10 := memRegion_split (sp' + 56#64) 4 44 (by decide)
  have hs11 := memRegion_split (sp' + 60#64) 4 40 (by decide)
  have hs12 := memRegion_split (sp' + 64#64) 4 36 (by decide)
  have hs13 := memRegion_split (sp' + 68#64) 4 32 (by decide)
  have hs14 := memRegion_split (sp' + 72#64) 8 24 (by decide)
  have hs15 := memRegion_split (sp' + 80#64) 8 16 (by decide)
  have hs16 := memRegion_split (sp' + 88#64) 8 8 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16]
  rw [memRegion_eight (sp' + 16#64), memRegion_eight (sp' + 32#64), memRegion_eight (sp' + 40#64),
    memRegion_eight (sp' + 72#64), memRegion_eight (sp' + 80#64), memRegion_eight (sp' + 88#64),
    memRegion_eight (sp' + 96#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 12#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 28#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 48#64))
          (sepConj_mono (memRegion_four_entails (sp' + 52#64))
            (sepConj_mono_right (sepConj_mono (memRegion_four_entails (sp' + 60#64))
              (sepConj_mono (memRegion_four_entails (sp' + 64#64))
                (sepConj_mono_left (memRegion_four_entails (sp' + 68#64))))))))))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w12 => Entails.sepExists_elim fun w16 =>
    Entails.sepExists_elim fun w28 => Entails.sepExists_elim fun w32 =>
    Entails.sepExists_elim fun w40 => Entails.sepExists_elim fun w48 =>
    Entails.sepExists_elim fun w52 => Entails.sepExists_elim fun w60 =>
    Entails.sepExists_elim fun w64 => Entails.sepExists_elim fun w68 =>
    Entails.sepExists_elim fun w72 => Entails.sepExists_elim fun w80 =>
    Entails.sepExists_elim fun w88 => Entails.sepExists_elim fun w96 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w12)
  refine Entails.trans ?_ (Entails.sepExists_intro w16)
  refine Entails.trans ?_ (Entails.sepExists_intro w28)
  refine Entails.trans ?_ (Entails.sepExists_intro w32)
  refine Entails.trans ?_ (Entails.sepExists_intro w40)
  refine Entails.trans ?_ (Entails.sepExists_intro w48)
  refine Entails.trans ?_ (Entails.sepExists_intro w52)
  refine Entails.trans ?_ (Entails.sepExists_intro w60)
  refine Entails.trans ?_ (Entails.sepExists_intro w64)
  refine Entails.trans ?_ (Entails.sepExists_intro w68)
  refine Entails.trans ?_ (Entails.sepExists_intro w72)
  refine Entails.trans ?_ (Entails.sepExists_intro w80)
  refine Entails.trans ?_ (Entails.sepExists_intro w88)
  refine Entails.trans ?_ (Entails.sepExists_intro w96)
  dsimp only [spUnused0]
  apply entails_of_eq; ac_rfl

theorem pcVal_if_eq_getD {opt : Option (BitVec 32)} {pcTag pcVal : BitVec 32}
    (h : optU32TagVal pcTag pcVal opt) :
    (if (pcTag &&& 1#32) != 0#32 then pcVal else 0#32) = opt.getD 0#32 := by
  cases opt with
  | none => rcases h with rfl; rfl
  | some v => rcases h with ⟨rfl, rfl⟩; rfl

/-! ## Relocatable `[LibsignalPlacement]` `post_rk_some_head_wp_placed` (Block `85`) -/

theorem post_rk_some_head_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A H)
    {s0 s : State}
    {sp' x19 x20 x21 x23 w16 w32 w40 w72 w80 w88 w96
      rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w28 w48 w60 w64 cTag cVal pcTag pcVal : BitVec 32}
    (rk : List (BitVec 8))
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 0x3b0#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x4c4#64) s
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 0x4c4#64 ∧
        sf.status = .Running ∧
        sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
        sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = adCap ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 rk.length ∧
        sf.readReg64 .x25 = pqCap ∧ sf.readReg64 .x26 = rkPtr ∧
        sf.readReg64 .x27 = ctCap ∧ sf.readReg64 .x28 = ctPtr ∧
        (Pf ⊢ ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
          ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
          memRegion (sp' + 209#64) 15 ∗
          memRegion (sp' + 224#64) 64 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx20 : s.readReg64 .x20 = x20 := hregs.x20_eq
  have hx21 : s.readReg64 .x21 = x21 := hregs.x21_eq
  have hx23 : s.readReg64 .x23 = x23 := hregs.x23_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hcallSpe := hDropSpe
  clear hDropSpe
  have hcallDeser := deserializeFull_ok_at_placed H
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (vecU8Buf_entails_slice_rest A rkCap rkPtr rk)))))))))))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre (P' :=
      ⌜rk.length ≤ rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre (fun ⟨hrk_le, hrk_lt, _⟩ => ?_)
  have hrk_add2 := cap_add2_ne_of_lt hrk_lt
  have hrk_add1 := cap_add1_eq_of_lt hrk_lt
  have hstackSpe := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  refine SepWPp.mono_pre (P' :=
      ((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
      ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
      ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
      ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
      ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
      ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
      ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
      ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
      ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
      ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
      logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.refl _) ?_
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hspe40 := spe40_of_rk_ct sp' rkPtr (BitVec.ofNat 64 rk.length) ctCap ctPtr ctLen
  have htail64 := wireTail64_entails_memRegion64 sp' pqCap pqPtr pqLen adCap adPtr adLen
    cTag cVal pcTag pcVal
  have hspe_eq : speAt A [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine SepWPp.mono_pre (P' :=
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗
      (((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen) ∗
      (vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
      ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A rkCap rkPtr rk ∗
      logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      apply entails_of_eq
      simp only [arm64_norm]
      ac_rfl) ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono hspe40 (sepConj_mono_left htail64))) ?_
  refine SepWPp.call_noPanic_tryFrom_placed (⟨sp' + 176#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1200)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 176#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64)
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    rfl
    (by rw [hspe_eq, hstackSpe, hsp_eq]; sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 rk.length := by simp [hx24_cs, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = rkPtr := by simp [hx26_cs, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, arm64_norm]
  have hrk_len_lt : rk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrk_le hrk_lt
  have hrk_toNat : (BitVec.ofNat 64 rk.length).toNat = rk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).ρ deserializeName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  have h48_split := memRegion48_split33_15 sp'
  refine SepWPp.call_noPanic_tryFrom_placed (rkPtr, rk, sp' + 176#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hcl3
    (ret_pc := (blkPl_85).base + bv% (1220)) (by simp [arm64_norm])
    (T := (rkPtr ↦ₛ rk) ∗ memRegion (sp' + 176#64) 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    (φ := rkPtr = rkPtr ∧ (BitVec.ofNat 64 rk.length).toNat = rk.length ∧
      sp' + 176#64 = sp' + 176#64 ∧ rk.length < 2 ^ 63)
    (by simp [deserializeFullPlacedSpec, arm64_norm])
    ⟨rfl, hrk_toNat, rfl, hrk_len_lt⟩
    (by rw [h48_split, logOff_tryFromPlacedImg]; sep_focus)
    ?_
  clear hcallDeser
  intro s4 hpc4 hrun4 hsp4 hsp4_align hcl4 hcs4
  dsimp only [deserializeFullPlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr4 => ?_)
  rcases hcs4 with ⟨hx19_4cs, hx20_4cs, hx21_4cs, hx22_4cs, hx23_4cs, hx24_4cs, hx25_4cs, hx26_4cs, hx27_4cs, hx28_4cs, _⟩
  refine SepWPp.of_sepWP_end_placed hcl4 ?_
  refine SepWP.done (by simp [hpc4, arm64_norm]) hrun4 ?_
  intro _
  refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by simp [hsp4, hsp2_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr4, htr2_eq, arm64_norm]),
    by simp [hpc4, arm64_norm], hrun4,
    by simp [hx19_4cs, hx19_2, arm64_norm],
    by simp [hx20_4cs, hx20_2, arm64_norm],
    by simp [hx21_4cs, hx21_2, arm64_norm],
    by simp [hx22_4cs, hx22_2, arm64_norm],
    by simp [hx23_4cs, hx23_2, arm64_norm],
    by simp [hx24_4cs, hx24_2, arm64_norm],
    by simp [hx25_4cs, hx25_2, arm64_norm],
    by simp [hx26_4cs, hx26_2, arm64_norm],
    by simp [hx27_4cs, hx27_2, arm64_norm],
    by simp [hx28_4cs, hx28_2, arm64_norm],
    ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A rkCap rkPtr rk
  rw [← logOff_tryFromPlacedImg]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepack)))))))))))))))
  apply entails_of_eq
  simp only [hstackSpe, hsp_eq, arm64_norm]
  ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Wire
