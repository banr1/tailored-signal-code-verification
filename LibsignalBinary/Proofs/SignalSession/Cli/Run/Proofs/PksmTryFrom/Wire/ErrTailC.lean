/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6States
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6Exits
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBB
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Pack, `IdentityKey`, and `SignalMessage` Error/Dealloc Tails

Proves the `+0x970..+0xa58` `Option<Vec<u8>>` and Kyber `Box<[u8]>` deallocation chains, the
`+0xa68` `try_clone_from_ref` OOM panic branch, and the exact-`pksmErrE` error entries at
`+0x978` (`IdentityKey::try_from`) and `+0x9f0` (`SignalMessage::try_from`).
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

private gen_decodes libsignalSessionCode_tree etcDec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2416) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2456),
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2544) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2652),
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2664) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2676)]

local macro "etc_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.etcDec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem etc_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem etc_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem etc_bv_add_sub_lit (x a b : BitVec 64) : x + a - b = x + (a - b) := by bv_omega
private theorem etc_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by
  bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit etc_bv_sub_add_lit' etc_bv_sub_sub_lit etc_bv_add_sub_lit etc_bv_add_neg_160
  BitVec.toNat_zero cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## 1. Shared Dealloc Chain (`+0xa24 .. +0xa58` → `+0x80c` / `+0x504`) -/

/-- `+0xa4c .. +0xa58` (`2636` → `+0x80c` / `+0x504`): frees the bk slot
`deallocSlot A bkCap bkPtr bkAct` (`ldr x1, [sp, #0x58]` = `bkCap`, `cbz x1, +0x504`;
`ldr x0, [sp, #0x50]` = `bkPtr`, `b +0x80c`), so `bkCap ≠ noneCap`; via `tail_80c_wpX`. -/
theorem tail_a4c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State} {sp' sret bkCap bkPtr : BitVec 64}
    (bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2636#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    etc_prekey_fetches img.base H 2636 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_end hF hsym ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact ⟨PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
      (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hnext := @tail_80c_wpX img A ext hC s0
    etc_prekey_fetches img.base H 2636 16
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0xa38 .. +0xa48` (`2616` → `+0xa4c` → `+0x504`): frees the ik slot
`deallocSlot A ikCap ikPtr ikAct` (`x23 = ikCap`, `[sp' + 104] = ikPtr`; `cbz`, so
`ikCap ≠ noneCap`), then chains into `tail_a4c_wpX`. -/
theorem tail_a38_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret ikCap ikPtr bkCap bkPtr : BitVec 64} (ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2616#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_a4c_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : ikCap = 0#64 := hcap.resolve_left hik
    etc_prekey_fetches img.base H 2616 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2636#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext bkAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A ikCap ikPtr true =
        (⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
          A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : ikCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hcall := etb_dealloc_ok_at_prekey hC.alloc
    etc_prekey_fetches img.base H 2616 20
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
    refine SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.call_noPanic_tryFrom (ikPtr, ikCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + 2636#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk ikCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, _, _, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext bkAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
/-- `+0xa28 .. +0xa34` (`2600` → `+0xa38` → `+0x504`): frees the active msg buffer
(`ldr x0, [sp, #0x60]` = `msgPtr`, `x1 = x26 = msgCap`), then chains into `tail_a38_wpX`. -/
theorem tail_a28_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2600#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hpos : 0 < msgCap.toNat) (hlt : msgCap.toNat < 2 ^ 63)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_a38_wpX img A ext hC s0
  let H := Rust.withPanics ext
  have hcall := etb_dealloc_ok_at_prekey hC.alloc
  etc_prekey_fetches img.base H 2600 16
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFrom (msgPtr, msgCap.toNat, 1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2616#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt s.sp extHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
      LayoutOk msgCap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, _, _, _, _⟩
  refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (hnext ikAct bkAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
        by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
      (by simp [hx23_cs, hx23, arm64_norm]) hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0xa24` (`2596` → `+0xa28` / `+0xa38` → `+0x504`): `cbz x26, +0xa38` on the msg slot
`deallocSlot A msgCap msgPtr msgAct` (`x26 = msgCap`, `[sp' + 96] = msgPtr`, so
`msgCap ≠ noneCap`), then `tail_a28_wpX` / `tail_a38_wpX`. -/
theorem tail_a24_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (msgAct ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases msgAct with
  | false =>
    have hnext := @tail_a38_wpX img A ext hC s0
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    etc_prekey_fetches img.base H 2596 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext ikAct bkAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hnext := @tail_a28_wpX img A ext hC s0
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    etc_prekey_fetches img.base H 2596 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      fun hF1 hsym1 => ?_
    exact hnext ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 2. Pack Ok Exit (`+0x970`) -/

/-- `+0x970 .. +0x974` (`2416` → `+0xa28` / `+0xa38` → `+0x504`): the Pack Ok exit
(`PackOkState`). `cbnz x26, +0xa28; b +0xa38` frees the msg / ik / bk `Option<Vec<u8>>` slots of
the L6b frame (`deallocSlot`, `≠ noneCap`), leaving the four spill cells. -/
theorem deallocChain_970_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (msgAct ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PackOkState img s0 sp' sret ikCap msgCap s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2416#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ deallocSlot A ikCap ikPtr ikAct ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx19, hx26, hx23⟩
  refine SepWPp.pure_pre fun ⟨hmsg, hik, hbk⟩ => ?_
  refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by apply entails_of_eq; ac_rfl) ?_
  let H := Rust.withPanics ext
  cases msgAct with
  | false =>
    have hnext := @tail_a38_wpX img A ext hC s0
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    etc_prekey_fetches img.base H 2416 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext ikAct bkAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hnext := @tail_a28_wpX img A ext hC s0
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    etc_prekey_fetches img.base H 2416 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      fun hF1 hsym1 => ?_
    exact hnext ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 3. Kyber `Box<[u8]>` Slot and Exact-Err Copy Helpers -/

/-- Ownership of the Kyber `Box<[u8]>` slot `(x28, x25) = (ptr, len)` at the Kyber-box error
entries: active (`len > 0`, live `u8` block) or inactive (`ptr = 0` or `len = 0`). -/
def boxSlot (A : RustAlloc) (ptr len : BitVec 64) (act : Bool) : SepProp :=
  if act then
    ⌜0 < len.toNat ∧ len.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ A.live ptr len.toNat 1 ∗
      memRegion ptr len.toNat
  else ⌜ptr = 0#64 ∨ len = 0#64⌝

/-- An absent Kyber box (`ptr = 0`) is an inactive `boxSlot`. -/
theorem boxSlot_of_null (A : RustAlloc) (len : BitVec 64) :
    SepProp.emp ⊢ boxSlot A 0#64 len false := by
  show SepProp.emp ⊢ ⌜(0#64 : BitVec 64) = 0#64 ∨ len = 0#64⌝
  exact Entails.pure_right_only (Or.inl rfl) (Entails.refl _)

/-- A `boxSlot` with `ptr = 0` owns no heap. -/
theorem boxSlot_null_elim (A : RustAlloc) (len : BitVec 64) (act : Bool) :
    boxSlot A 0#64 len act ⊢ SepProp.emp := by
  cases act with
  | false =>
    show ⌜(0#64 : BitVec 64) = 0#64 ∨ len = 0#64⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  | true =>
    show (⌜0 < len.toNat ∧ len.toNat < 2 ^ 63 ∧ (0#64 : BitVec 64) ≠ 0#64⌝ ∗
      A.live 0#64 len.toNat 1 ∗ memRegion 0#64 len.toNat) ⊢ SepProp.emp
    exact Entails.pure_left fun ⟨_, _, h⟩ => absurd rfl h

/-- Bridge from upstream `boxU8Buf` to `boxSlot`. -/
theorem boxU8Buf_entails_boxSlot (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf A ptr bs ⊢ boxSlot A ptr (BitVec.ofNat 64 bs.length) (!bs.isEmpty) := by
  cases bs with
  | nil =>
    unfold boxU8Buf
    rw [ite_eq_left rfl]
    refine Entails.pure_left fun _ => ?_
    show SepProp.emp ⊢ ⌜ptr = 0#64 ∨ BitVec.ofNat 64 0 = 0#64⌝
    exact Entails.pure_right_only (Or.inr rfl) (Entails.refl _)
  | cons b bs' =>
    unfold boxU8Buf
    rw [ite_eq_right (List.cons_ne_nil _ _)]
    refine Entails.pure_left fun ⟨hptr, hlt⟩ => ?_
    have hlen : (BitVec.ofNat 64 (b :: bs').length).toNat = (b :: bs').length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))
    show (A.live ptr (b :: bs').length 1 ∗ (ptr ↦ₛ (b :: bs'))) ⊢
      (⌜0 < (BitVec.ofNat 64 (b :: bs').length).toNat ∧
          (BitVec.ofNat 64 (b :: bs').length).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr (BitVec.ofNat 64 (b :: bs').length).toNat 1 ∗
        memRegion ptr (BitVec.ofNat 64 (b :: bs').length).toNat)
    rw [hlen]
    exact Entails.pure_right ⟨Nat.succ_pos _, hlt, hptr⟩
      (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: bs')))

/-- Weakening the frame of an `ErrTailQ` postcondition along `F ∗ G ⊢ H`. -/
theorem ErrTailQ.frame_entails {img : Obj.Image} {s0 sf : State} {sp' sret : BitVec 64}
    {F G H Pf : SepProp} (h : ErrTailQ img s0 sp' sret F sf Pf) (hent : F ∗ G ⊢ H) :
    ErrTailQ img s0 sp' sret H sf (Pf ∗ G) :=
  ⟨h.1, h.2.1, Entails.trans (sepConj_mono_left h.2.2) hent⟩

/-! ## 4. Kyber-Box Free (`+0x990`, `+0xa0c`, `+0xa10` → `+0xa24`) -/

/-- `+0xa10 .. +0xa20` (`2576` → `+0xa24` → `+0x504`): `cbz x25, +0xa24`, else
`__rust_dealloc(x28, x25, 1)` returning to `+0xa24`; `x28 = kbPtr ≠ 0`, `x25 = kbLen`. -/
theorem tail_a10_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2576#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hkb : kbPtr ≠ 0#64)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_a24_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases boxAct with
  | false =>
    have hbox : boxSlot A kbPtr kbLen false = ⌜kbPtr = 0#64 ∨ kbLen = 0#64⌝ := rfl
    rw [hbox]
    refine SepWPp.pure_pre fun hz => ?_
    obtain rfl : kbLen = 0#64 := hz.resolve_left hkb
    etc_prekey_fetches img.base H 2576 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hnext msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  | true =>
    have hbox : boxSlot A kbPtr kbLen true =
        (⌜0 < kbLen.toNat ∧ kbLen.toNat < 2 ^ 63 ∧ kbPtr ≠ 0#64⌝ ∗
          A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat) := rfl
    rw [hbox]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : kbLen ≠ 0#64 := by rintro rfl; simp at hpos
    have hcall := etb_dealloc_ok_at_prekey hC.alloc
    etc_prekey_fetches img.base H 2576 20
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
    refine SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.call_noPanic_tryFrom (kbPtr, kbLen.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + 2596#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat ∗
        stackAt s.sp extHookStack)
      (φ := kbPtr = kbPtr ∧ kbLen.toNat = kbLen.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk kbLen.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _⟩
    refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact hnext msgAct ikAct bkAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
        by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
      (by simp [hx26_cs, hx26, arm64_norm]) (by simp [hx23_cs, hx23, arm64_norm]) hmsg hik hbk

/-- `+0x990 .. +0x994` (`2448` → `+0xa10` / `+0xa24` → `+0x504`): `cbnz x28, +0xa10; b +0xa24`
on the Kyber box (`x28 = kbPtr`), then `tail_a10_wpX` / `tail_a24_wpX`. -/
theorem tail_990_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2448#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  by_cases hz : kbPtr = 0#64
  · subst hz
    have hnext := @tail_a24_wpX img A ext hC s0
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    etc_prekey_fetches img.base H 2448 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hnext msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · have hnext := @tail_a10_wpX img A ext hC s0
    etc_prekey_fetches img.base H 2448 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2576#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      fun hF1 hsym1 => ?_
    exact hnext boxAct msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

/-- `+0xa0c` (`2572` → `+0xa10` / `+0xa24` → `+0x504`): `cbz x28, +0xa24` on the Kyber box
(`x28 = kbPtr`), then `tail_a10_wpX` / `tail_a24_wpX`. -/
theorem tail_a0c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2572#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  by_cases hz : kbPtr = 0#64
  · subst hz
    have hnext := @tail_a24_wpX img A ext hC s0
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    etc_prekey_fetches img.base H 2572 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hnext msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · have hnext := @tail_a10_wpX img A ext hC s0
    etc_prekey_fetches img.base H 2572 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2576#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      fun hF1 hsym1 => ?_
    exact hnext boxAct msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

/-! ## 5. Clone Alloc-Fail Panic (`+0xa68`) -/

/-- `+0xa68 .. +0xa70` (`2664`): `mov w0, #1; mov x1, x20; bl handle_alloc_error` (PAN, after
`__rust_alloc` returned `0` at `+0x8bc`). Any `P` / `Q`; the panic satisfies `tryFromQp s0`. -/
theorem pan_a68_wpX {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : CloneAllocFail img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2664#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext) ret s P Q (tryFromQp s0) := by
  rcases hst with ⟨_, _, hF, hsym, hallocF, htr⟩
  have hpan := panic_at_prekey_handle_alloc_errorX (b := img.base) (ext := ext)
  let H := Rust.withPanics ext
  etc_prekey_fetches img.base H 2664 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpan hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ _ => ?_
  refine SepWPp.panic (by simp [hrun, arm64_norm]) (by simpa [arm64_norm] using hpan)
    fun _ hm => allowPanic_panicked
      ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
        by simpa [Rust.panicked, arm64_norm] using htr⟩ hm

/-! ## 6. Kyber-Box Exact-Err Entries (`+0x978`, `+0x9f0`) -/

private theorem etc_memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

private theorem etc_memRegion248_words7 (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [ProofLib.memRegion_split r 8 240 (by decide),
    ProofLib.memRegion_split (r + 8#64) 24 216 (by decide),
    ProofLib.memRegion_split (r + 8#64 + 24#64) 24 192 (by decide),
    ProofLib.memRegion_eight r,
    etc_memRegion24_words3 (r + 8#64),
    etc_memRegion24_words3 (r + 8#64 + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem etc_words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) w2)
        (pointsTo64_entails_memRegion (a + 24#64) w3)))

private theorem etc_words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      etc_words4_entails_memRegion32 (a + 8#64) w1 w2 w3 w4)

private theorem etc_ikErr_speDetached_intro {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (w2 w3 w4 w5 : BitVec 64) :
    SepProp.emp ⊢
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 w2 w3 w4 w5 e := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show SepProp.emp ⊢ ⌜speWord 7 = speWord 7⌝
    exact Entails.pure_right_only rfl (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 8 = speWord 8 ∧ (t.zeroExtend 64).truncate 8 = t⌝
    exact Entails.pure_right_only ⟨rfl, by bv_bits⟩ (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 9 = speWord 9 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n⌝
    exact Entails.pure_right_only ⟨rfl, rfl⟩ (Entails.refl _)

private theorem etc_ikErr_speDetached_elim {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (d0 d1 d2 d3 d4 d5 : BitVec 64) :
    pksm0c_speDetached A fn d0 d1 d2 d3 d4 d5 e ⊢ SepProp.emp := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show ⌜d0 = speWord 7⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 8 ∧ d1.truncate 8 = t⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 9 ∧ d1 = BitVec.ofNat 64 n⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _

/-- General 48-byte error copy (`+0x978 .. +0x98c`, `2424` → `+0x990` → `+0x504`)**:
writes `[sret] := errTag`, `[sret + 8] := x8 (= w0)`, `[sret + 16 .. + 40] := [sp' + 144 .. + 168]`
(`w1 .. w4`), and `[sret + 48] := [x29 - 0xa0] (= [sp' + 352] = w5)`, packs `pksmErrE A fn sret e`
through `ErrAt.errCopy48_entails_pksmErrE`, and chains into `tail_990_wpX`. -/
theorem e_978_copy48_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : IdentErrState img s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = w0)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗
        ((sp' + 168#64) ↦₆₄ w4) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
        pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 352#64) 8 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, hx29, hx28, hx25, hx26, hx23, hx19⟩
  have hnext := @tail_990_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etc_prekey_fetches img.base H 2424 24
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [etc_memRegion248_words7 sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2448#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre (P' := (boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ w0) ∗ ((sret + 16#64) ↦₆₄ w1) ∗
          ((sret + 24#64) ↦₆₄ w2) ∗ ((sret + 32#64) ↦₆₄ w3) ∗ ((sret + 40#64) ↦₆₄ w4) ∗
          ((sret + 48#64) ↦₆₄ w5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e) ∗
        (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗
          ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
        ((sp' + 352#64) ↦₆₄ w5)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  have hm32 := etc_words4_entails_memRegion32 (sp' + 144#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm32
  exact SepWPp.frame_tryFrom
    (hnext boxAct msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => h.frame_entails (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A fn sret w0 w1 w2 w3 w4 w5 e)
        (sepConj_mono hm32
          (pointsTo64_entails_memRegion (sp' + 352#64) w5))))
      (by apply entails_of_eq; ac_rfl))

private theorem etc_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

/-- (``+0x978 .. +0x98c`, `2424` → `+0x990` → `+0x504``): `IdentErrState` entry (`IdentityKey::try_from` returned `Err e` with
`PublicKey.deserialize ik = .error e`), consuming `x8 = (ikErrWords e).1`,
`(sp' + 144) ↦₆₄ (ikErrWords e).2`, `memRegion (sp' + 152) 24`, and `speAt A fn (sp' + 312) e`
from `IdentKey.preKey_ident_err_830_to_978_wpE`, packing exact `pksmErrE A fn sret e` through
`e_978_copy48_wpE` (`ErrAt.errCopy48_entails_pksmErrE`), and restoring
`memRegion (sp' + 144) 32 ∗ memRegion (sp' + 312) 48`. -/
theorem e_978_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hik_err : PublicKey.deserialize ik = .error e)
    (hst : IdentErrState img s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = (ikErrWords e).1)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
        speAt A fn (sp' + 312#64) e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 312#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etc_memRegion24_words3 (sp' + 152#64)]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_speAt_detach A fn (sp' + 312#64) e)))) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun d0 => SepWPp.exists_pre fun d1 => SepWPp.exists_pre fun d2 =>
    SepWPp.exists_pre fun d3 => SepWPp.exists_pre fun d4 => SepWPp.exists_pre fun w5 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u2 => SepWPp.exists_pre fun u1 => ?_
  have hdet :
      pksm0c_speDetached A fn d0 d1 d2 d3 d4 w5 e ⊢
        pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e :=
    Entails.trans (etc_ikErr_speDetached_elim hik_err d0 d1 d2 d3 d4 w5)
      (etc_ikErr_speDetached_intro hik_err u1 u2 u3 w5)
  have hm40 := etc_words5_entails_memRegion40 (sp' + 312#64) d0 d1 d2 d3 d4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm40
  refine SepWPp.mono_pre
    (P' := ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
      ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e ∗
      memRegion sret 248 ∗
      boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ (memRegion (sp' + 312#64) 40 ∗ R))
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ d0) ∗ ((sp' + 320#64) ↦₆₄ d1) ∗ ((sp' + 328#64) ↦₆₄ d2) ∗
            ((sp' + 336#64) ↦₆₄ d3) ∗ ((sp' + 344#64) ↦₆₄ d4)) ∗
          pksm0c_speDetached A fn d0 d1 d2 d3 d4 w5 e ∗
          (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
            ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
            memRegion sret 248 ∗
            boxSlot A kbPtr kbLen boxAct ∗
            deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hm40 (sepConj_mono_left hdet)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine etc_sepWPp_mono_post
    (e_978_copy48_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hx8 hmsg hik hbk)
    fun _ _ h => etb_errTailQ_mono h ?_
  have h48 : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48]
  apply entails_of_eq; ac_rfl

/-- (``+0x9f0 .. +0xa08`, `2544` → `+0xa0c` → `+0x504``): `SigMsgErrState` entry (`SignalMessage::try_from` returned `Err e`). Detaches
`speAt A fn (sp' + 176) e` via `ErrAt.pksm0c_speAt_detach`, writes `[sret] := errTag` and copies
the 48-byte error payload `sp' + 176 .. 224` into `sret + 8 .. 56`, packs exact
`pksmErrE A fn sret e` through `ErrAt.errCopy48_entails_pksmErrE`, restores
`memRegion (sp' + 176) 48`, and chains into `tail_a0c_wpX`. -/
theorem e_9f0_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : SigMsgErrState img s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (speAt A fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hF, hsym, htr⟩, _, hx28, hx25, hx26, hx23, hx19⟩
  have hnext := @tail_a0c_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etc_prekey_fetches img.base H 2544 28
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rw [etc_memRegion248_words7 sret]
  refine SepWPp.mono_pre (sepConj_mono_left (pksm0c_speAt_detach A fn (sp' + 176#64) e)) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun u0 => SepWPp.exists_pre fun u1 => SepWPp.exists_pre fun u2 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u4 => SepWPp.exists_pre fun u5 => ?_
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2572#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  have hm48 := pksm0c_words6_entails_memRegion48 (sp' + 176#64) u0 u1 u2 u3 u4 u5
  unfold pksm0c_speWords6At at hm48
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm48
  refine SepWPp.mono_pre (P' := (boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ u0) ∗ ((sret + 16#64) ↦₆₄ u1) ∗
          ((sret + 24#64) ↦₆₄ u2) ∗ ((sret + 32#64) ↦₆₄ u3) ∗ ((sret + 40#64) ↦₆₄ u4) ∗
          ((sret + 48#64) ↦₆₄ u5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A fn u0 u1 u2 u3 u4 u5 e) ∗
        (((sp' + 176#64) ↦₆₄ u0) ∗ ((sp' + 184#64) ↦₆₄ u1) ∗ ((sp' + 192#64) ↦₆₄ u2) ∗
          ((sp' + 200#64) ↦₆₄ u3) ∗ ((sp' + 208#64) ↦₆₄ u4) ∗ ((sp' + 216#64) ↦₆₄ u5))))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (hnext boxAct msgAct ikAct bkAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => h.frame_entails (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A fn sret u0 u1 u2 u3 u4 u5 e) hm48))
      (by apply entails_of_eq; ac_rfl))

/-- Word-copy error companion (`SigMsg.preKey_sigMsg_err_878_to_9f0_wpX` shape)**:
takes the 6 copied words `ew0 .. ew5` at `sp' + 176 .. 216` together with the universal
2-word packer `hpack`, packs `speAt A fn (sp' + 176) e`, and invokes `e_9f0_wpE`. -/
theorem e_9f0_words2_wpE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A fn b e)
    (hst : SigMsgErrState img s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  have hm32 : ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      memRegion (sp' + 192#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      etc_words4_entails_memRegion32 (sp' + 192#64) ew2 ew3 ew4 ew5
  have hspe : ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
      ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      speAt A fn (sp' + 176#64) e := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hpack (sp' + 176#64)
  refine SepWPp.mono_pre
    (P' := speAt A fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
      boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by
      refine Entails.trans
        (Q := (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
            ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
            ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5)) ∗
          (memRegion sret 248 ∗
            boxSlot A kbPtr kbLen boxAct ∗
            deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; ac_rfl) ?_
      exact sepConj_mono_left hspe) ?_
  exact e_9f0_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hmsg hik hbk

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
