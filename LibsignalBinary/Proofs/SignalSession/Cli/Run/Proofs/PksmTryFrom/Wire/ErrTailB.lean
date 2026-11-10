/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Missing-Field and Key-Deserialization Error Tails

Proves word-level and exact-`pksmErrE` error entry blocks (`+0x5e0`, `+0x61c`, `+0x66c`,
`+0x678`, `+0x7a8` → `+0x504`) for missing required protobuf fields and `base_key`
`PublicKey::deserialize` errors.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.call_noPanic_tryFrom := @Wire.SepWPp.call_noPanic_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private theorem etb_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

private gen_decodes libsignalSessionCode_tree etbDecB [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1504) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1588),
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1644) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1668),
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1960) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1972)]

local macro "etb_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.etbDecB $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## 1. Word-Level Entry Blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8`) -/

/-- `+0x678 .. +0x680` (`1656` → `+0x7b8` → `+0x504`): `SpkNoneTailState` entry
(`mov x8, #-1; str x27, [x19, #8]; b +0x7b8`), then `tail_7b8_wpX`. -/
theorem entry_678_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 w1 x27v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7b8_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etb_prekey_fetches img.base H 1656 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1976#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret + 8#64) ↦₆₄ x27v))
    (by apply entails_of_eq; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (hnext msgAct ikAct bkAct kyAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x66c .. +0x674` (`1644` → `+0x7d0` → `+0x504`): `MsgNoneTailState` entry
(`mov x8, #-1; stp x8, x27, [x19]; b +0x7d0`), then `tail_7d0_wpX` (msg slot is `None`). -/
theorem entry_66c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 w1 x27v ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7d0_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etb_prekey_fetches img.base H 1644 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2000#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (hnext ikAct bkAct kyAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x5e0 .. +0x600` (`1504` → `+0x604` → `+0x504`): `BkNoneTailState` entry
(`stp x9 (= -1), x27, [x19]`), frees the kyber slot inline (`x28 = kyCap`, `x25 = kyPtr`;
`sub #1; cmn #3; b.hi +0x604`, else `bl __rust_dealloc` returning to `+0x604`), then
`tail_604_wpX` (ik, msg). -/
theorem entry_5e0_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 w1 x27v kyCap kyPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyAct ikAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_604_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    etb_prekey_fetches img.base H 1504 20
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    rcases hcap with rfl | rfl
    all_goals
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1540#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
        (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
      exact SepWPp.frame_tryFrom
        (hnext ikAct msgAct
          (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]))
        fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hcall := etb_dealloc_ok_at_prekey hC.alloc
    etb_prekey_fetches img.base H 1504 36
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
    refine SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.call_noPanic_tryFrom (kyPtr, kyCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + 1540#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := kyPtr = kyPtr ∧ kyCap.toNat = kyCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk kyCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A msgCap msgPtr msgAct ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext ikAct msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx23_cs, hx23, arm64_norm]) (by simp [hx26_cs, hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x61c .. +0x634` (`1564` → `+0x638` → `+0x504`): `IkNoneTailState` entry
(`ldr x1, [sp, #0x58]; stp x8 (= -1), x27, [x19]`), frees the bk slot inline
(`[sp' + 88] = bkCap`, `[sp' + 80] = bkPtr`; `cbz`, so `bkCap ≠ noneCap`), then `tail_638_wpX`
(kyber, msg). -/
theorem entry_61c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 w1 x27v bkCap bkPtr kyCap kyPtr msgCap msgPtr : BitVec 64}
    (bkAct kyAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_638_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    etb_prekey_fetches img.base H 1564 16
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1592#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext kyAct msgAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hcall := etb_dealloc_ok_at_prekey hC.alloc
    etb_prekey_fetches img.base H 1564 28
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
    refine SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.call_noPanic_tryFrom (bkPtr, bkCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + 1592#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := bkPtr = bkPtr ∧ bkCap.toNat = bkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk bkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, hx26_cs, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext kyAct msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm])
        (by simp [hx26_cs, hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x7a8 .. +0x7b4` (`1960` → `+0x7b8` → `+0x504`): `DeserErrTailState` entry
(`and x10, x10, #0xff; orr x8, x8, x10; stp x9, x8, [x19, #8]; mov x8, #-1`), then
`tail_7b8_wpX`. -/
theorem entry_7a8_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 w1 w2 x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
        ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7b8_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etb_prekey_fetches img.base H 1960 16
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1976#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret + 8#64) ↦₆₄ x9v) ∗ ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64)))))
    (by apply entails_of_eq; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (hnext msgAct ikAct bkAct kyAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

/-! ## 2. Exact `pksmErrE` Payload Relation (`speWordsOf`) & Entry Theorems (`*_wpE`) -/

/-- Register-level `SignalProtocolError` payload invariant at `+0x7a8` (`entry_7a8_wpE`), where
`and x10, x10, #0xff; orr x8, x8, x10; stp x9, x8, [x19, #8]` stores tag word `x9` at `sret + 8`
and payload word `x8 ||| (x10 &&& 255#64)` at `sret + 16`:
- `.noKeyTypeIdentifier`: `x9 = speWord 7` (`x10` is untouched on `disc = 0` at `+0x5c0`);
- `.badKeyType t`: `x9 = speWord 8` and low byte `(x8 ||| (x10 &&& 255#64)).truncate 8 = t`;
- `.badKeyLength n`: `x9 = speWord 9` and `(x8 ||| (x10 &&& 255#64)) = BitVec.ofNat 64 n`;
- `.invalidKeyAgreement`: `x9 = speWord 10`. -/
def speWordsOf (e : SignalProtocolError) (x9v x8v x10v : BitVec 64) : Prop :=
  match e with
  | .noKeyTypeIdentifier => x9v = speWord 7
  | .badKeyType t => x9v = speWord 8 ∧ (x8v ||| (x10v &&& 255#64)).truncate 8 = t
  | .badKeyLength n => x9v = speWord 9 ∧ (x8v ||| (x10v &&& 255#64)) = BitVec.ofNat 64 n
  | .invalidKeyAgreement => x9v = speWord 10
  | _ => False

theorem etb_speWordsOf_noKeyType (x8v x10v : BitVec 64) :
    speWordsOf .noKeyTypeIdentifier (speWord 7) x8v x10v := rfl

theorem etb_speWordsOf_badKeyType (t : BitVec 8) :
    speWordsOf (.badKeyType t) (speWord 8) 0#64 (t.zeroExtend 64) :=
  ⟨rfl, by bv_bits⟩

theorem etb_speWordsOf_badKeyLength (n : Nat) :
    speWordsOf (.badKeyLength n) (speWord 9)
      (BitVec.ofNat 64 n &&& (-256#64)) (BitVec.ofNat 64 n) :=
  ⟨rfl, by bv_bits⟩

theorem etb_speWordsOf_invalidKeyAgreement (x8v x10v : BitVec 64) :
    speWordsOf .invalidKeyAgreement (speWord 10) x8v x10v := rfl

private theorem etb_memRegion248_words2 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    sepExists_sepConj_left]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

private theorem etb_memRegion248_words3 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          memRegion (sret + 24#64) 224 := by
  rw [etb_memRegion248_words2 sret, show (232 : Nat) = 8 + 224 by decide,
    Prost.memRegion_split (sret + 16#64) 8 224 (by decide),
    ProofLib.memRegion_eight (sret + 16#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

/-- Packs the three words written at `sret .. sret + 24` by `+0x7a8 .. +0x7bc` plus trailing
`memRegion (sret + 24) 224` into exact `pksmErrE A fn sret e`. -/
theorem etb_speWordsOf_entails_pksmErrE (A : RustAlloc) (fn : List (BitVec 8))
    (sret x9v x8v x10v : BitVec 64) (e : SignalProtocolError)
    (hw : speWordsOf e x9v x8v x10v) :
    (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
      ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
      pksmErrE A fn sret e := by
  cases e with
  | noKeyTypeIdentifier =>
    subst hw
    have hm : ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
        memRegion (sret + 16#64) 232 := by
      rw [show (232 : Nat) = 8 + 224 by decide,
        Prost.memRegion_split (sret + 16#64) 8 224 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion (sret + 16#64) _)
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right hm))
      (errCells_noKeyType A fn sret)
  | badKeyType t =>
    obtain ⟨rfl, ht⟩ := hw
    exact pksm0c_errCells_badKeyType_word A fn sret (x8v ||| (x10v &&& 255#64)) t ht
  | badKeyLength n =>
    obtain ⟨rfl, hn⟩ := hw
    rw [hn]
    exact errCells_badKeyLength A fn sret n
  | invalidKeyAgreement =>
    subst hw
    have hm : ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224 ⊢
        memRegion (sret + 16#64) 232 := by
      rw [show (232 : Nat) = 8 + 224 by decide,
        Prost.memRegion_split (sret + 16#64) 8 224 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion (sret + 16#64) _)
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right hm))
      (errCells_invalidKeyAgreement A fn sret)
  | _ => exact False.elim hw

/-- (``+0x678 → +0x504``): `SpkNoneTailState` entry with `x27 = speWord 2`,
producing exact `pksmErrE A [] sret .invalidProtobufEncoding` in `ErrTailQ`. -/
theorem entry_678_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = speWord 2) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (memRegion sret 248 ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A [] sret .invalidProtobufEncoding ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etb_memRegion248_words2 sret]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => ?_
  refine SepWPp.mono_pre
    (P' := (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      (memRegion (sret + 16#64) 232 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etb_sepWPp_mono_post
    (entry_678_wpX hC msgAct ikAct bkAct kyAct hst hpc hrun hx19 hx27 hx26 hx23 hx28 hx25
      hmsg hik hbk)
    fun _ _ h => etb_errTailQ_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗ memRegion (sret + 16#64) 232) ∗
      (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (errCells_invalidProtobufEncoding A [] sret))

/-- (``+0x66c → +0x504``): `MsgNoneTailState` entry with `x27 = speWord 2`,
producing exact `pksmErrE A [] sret .invalidProtobufEncoding` in `ErrTailQ`. -/
theorem entry_66c_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = speWord 2) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (memRegion sret 248 ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A [] sret .invalidProtobufEncoding ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etb_memRegion248_words2 sret]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => ?_
  refine SepWPp.mono_pre
    (P' := (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      (memRegion (sret + 16#64) 232 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etb_sepWPp_mono_post
    (entry_66c_wpX hC ikAct bkAct kyAct hst hpc hrun hx19 hx27 hx23 hx28 hx25 hik hbk)
    fun _ _ h => etb_errTailQ_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗ memRegion (sret + 16#64) 232) ∗
      (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (errCells_invalidProtobufEncoding A [] sret))

/-- (``+0x5e0 → +0x504``): `BkNoneTailState` entry with `x27 = speWord 2`,
producing exact `pksmErrE A [] sret .invalidProtobufEncoding` in `ErrTailQ`. -/
theorem entry_5e0_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret kyCap kyPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyAct ikAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = speWord 2)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗ memRegion sret 248 ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A [] sret .invalidProtobufEncoding ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etb_memRegion248_words2 sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => ?_
  refine SepWPp.mono_pre
    (P' := deallocSlot A kyCap kyPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ (memRegion (sret + 16#64) 232 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etb_sepWPp_mono_post
    (entry_5e0_wpX hC kyAct ikAct msgAct hst hpc hrun hx19 hx27 hx28 hx25 hx23 hx26)
    fun _ _ h => etb_errTailQ_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗ memRegion (sret + 16#64) 232) ∗
      (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (errCells_invalidProtobufEncoding A [] sret))

/-- (``+0x61c → +0x504``): `IkNoneTailState` entry with `x27 = speWord 2`,
producing exact `pksmErrE A [] sret .invalidProtobufEncoding` in `ErrTailQ`. -/
theorem entry_61c_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret bkCap bkPtr kyCap kyPtr msgCap msgPtr : BitVec 64}
    (bkAct kyAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = speWord 2)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗ memRegion sret 248 ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A [] sret .invalidProtobufEncoding ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etb_memRegion248_words2 sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => ?_
  refine SepWPp.mono_pre
    (P' := deallocSlot A bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
      stackAt sp' (Prost.skipFieldStackX 100) ∗ (memRegion (sret + 16#64) 232 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etb_sepWPp_mono_post
    (entry_61c_wpX hC bkAct kyAct msgAct hst hpc hrun hx19 hx27 hx28 hx25 hx26 hbk)
    fun _ _ h => etb_errTailQ_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 2) ∗ memRegion (sret + 16#64) 232) ∗
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (errCells_invalidProtobufEncoding A [] sret))

/-- (``+0x7a8 → +0x504``): `DeserErrTailState` entry with exact `SignalProtocolError`
`e` matching `speWordsOf e x9v x8v x10v` (`NoKeyTypeIdentifier` / `BadKeyType` / `BadKeyLength` /
`InvalidKeyAgreement`), producing exact `pksmErrE A [] sret e` in `ErrTailQ`. -/
theorem entry_7a8_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    {e : SignalProtocolError} (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hw : speWordsOf e x9v x8v x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (memRegion sret 248 ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A [] sret e ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etb_memRegion248_words3 sret]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  refine SepWPp.mono_pre
    (P' := (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      (memRegion (sret + 24#64) 224 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etb_sepWPp_mono_post
    (entry_7a8_wpX hC msgAct ikAct bkAct kyAct hst hpc hrun hx19 hx8 hx9 hx10 hx26 hx23 hx28 hx25
      hmsg hik hbk)
    fun _ _ h => etb_errTailQ_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
        ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224) ∗
      (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (etb_speWordsOf_entails_pksmErrE A [] sret x9v x8v x10v e hw))

/-- Absorbs any heap/rodata residue `R_heap` alongside `pksmErrE A fn sret e` into
`pksmErrE A fn sret e ∗ anyHeap` (for final epilogue close). -/
theorem etb_pksmErrE_absorb_heap (A : RustAlloc) (fn : List (BitVec 8)) (sret : BitVec 64)
    (e : SignalProtocolError) (R_heap F_epi : SepProp) :
    pksmErrE A fn sret e ∗ R_heap ∗ F_epi ⊢
      (pksmErrE A fn sret e ∗ anyHeap) ∗ F_epi := by
  rw [← sepConj_assoc]
  exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap R_heap))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
