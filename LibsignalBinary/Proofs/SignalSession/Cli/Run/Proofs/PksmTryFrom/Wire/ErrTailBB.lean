/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Shared Post-Loop and Presence Deallocation Chains

Proves the shared post-loop `Option<Vec<u8>>` deallocation chains (`+0x604..+0x668` and
`+0x7b8..+0x814` → `+0x504`) into `ErrTailQ`.
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

private gen_decodes libsignalSessionCode_tree etbDecBB [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1540) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1640),
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1976) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 2068)]

local macro "etb_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.etbDecBB $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-- Discharges `__rust_dealloc` relative to `preKeyTryFromName` on `contractProg img.base ext`
directly from `hC.alloc : AllocHooksW img A ext`. -/
theorem etb_dealloc_ok_at_prekey {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (halloc : AllocHooksW img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr halloc.dealloc preKeyTryFromName
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))
    (by
      rw [(ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")]
      simp only [arm64_norm])

/-! ## 1. Common Postcondition -/

/-- Postcondition of every dealloc-chain leaf: at `+0x504` (`1284`) with
`PostEpilogueState`, `x19 = sret`, and the remaining frame `F`. -/
abbrev ErrTailQ (img : Obj.Image) (s0 : State) (sp' sret : BitVec 64) (F : SepProp) :
    State → SepProp → Prop :=
  fun sf Pf => PostEpilogueState img s0 sp' sf ∧ sf.readReg64 .x19 = sret ∧ (Pf ⊢ F)

/-- Framing `G` onto an `ErrTailQ` postcondition (for `SepWPp.frame_tryFrom`). -/
theorem ErrTailQ.frame_eq {img : Obj.Image} {s0 sf : State} {sp' sret : BitVec 64}
    {F G H Pf : SepProp} (h : ErrTailQ img s0 sp' sret F sf Pf) (heq : F ∗ G = H) :
    ErrTailQ img s0 sp' sret H sf (Pf ∗ G) :=
  ⟨h.1, h.2.1, heq ▸ sepConj_mono_left h.2.2⟩

/-- Strengthening an `ErrTailQ` target frame via `F ⊢ F'`. -/
theorem etb_errTailQ_mono {img : Obj.Image} {s0 sf : State} {sp' sret : BitVec 64}
    {F F' Pf : SepProp} (h : ErrTailQ img s0 sp' sret F sf Pf) (hF : F ⊢ F') :
    ErrTailQ img s0 sp' sret F' sf Pf :=
  ⟨h.1, h.2.1, Entails.trans h.2.2 hF⟩

/-! ## 2. Shared Dealloc Chain (`+0x7b8 .. +0x814` → `+0x504`) -/

/-- `+0x80c .. +0x814` (`2060 .. 2068` → `+0x504`): `mov w2, #1; bl __rust_dealloc; b +0x504`,
freeing an active `(x0 = ptr, x1 = cap)` `u8` buffer. Shared by `+0x668`, `+0x804`, `+0xa58`. -/
theorem tail_80c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State} {sp' sret ptr cap : BitVec 64} {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2060#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := etb_dealloc_ok_at_prekey hC.alloc
  let H := Rust.withPanics ext
  etb_prekey_fetches img.base H 2060 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFrom (ptr, cap.toNat, 1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 2068#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk cap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  have hx19_2 : s2.readReg64 .x19 = sret := by simp [hcs2.1, hx19, arm64_norm]
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
  refine ⟨PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), by simp [hx19_2, arm64_norm], ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl

/-- `+0x7f8 .. +0x814` (`2040` → `+0x504`): frees the kyber slot `deallocSlot A kyCap kyPtr kyAct`
(`x28 = kyCap`, `x25 = kyPtr`; `sub #1; cmn #3; b.hi` skips `cap ∈ {0, noneCap}`). -/
theorem tail_7f8_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State} {sp' sret kyCap kyPtr : BitVec 64}
    (kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2040#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    etb_prekey_fetches img.base H 2040 12
    dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    rcases hcap with rfl | rfl
    all_goals
      refine SepWPp.of_sepWP_end hF hsym ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      exact ⟨PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @tail_80c_wpX img A ext hC s0
    etb_prekey_fetches img.base H 2040 20
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hnext
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt

/-- `+0x7e4 .. +0x7f4` (`2020` → `+0x7f8` → `+0x504`): frees the bk slot
`deallocSlot A bkCap bkPtr bkAct` (`[sp' + 88] = bkCap`, `[sp' + 80] = bkPtr`; `cbz`, so
`bkCap ≠ noneCap`), then chains into `tail_7f8_wpX`. -/
theorem tail_7e4_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret bkCap bkPtr kyCap kyPtr : BitVec 64} (bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2020#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7f8_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    etb_prekey_fetches img.base H 2020 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2040#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext kyAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]))
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
    etb_prekey_fetches img.base H 2020 20
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
      (ret_pc := entry + 2040#64) (by simp [arm64_norm])
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
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, _, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x7d0 .. +0x7e0` (`2000` → `+0x7e4` → `+0x504`): frees the ik slot
`deallocSlot A ikCap ikPtr ikAct` (`x23 = ikCap`, `[sp' + 104] = ikPtr`; `cbz`, so
`ikCap ≠ noneCap`), then chains into `tail_7e4_wpX`. -/
theorem tail_7d0_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64} (ikAct bkAct kyAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 2000#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7e4_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : ikCap = 0#64 := hcap.resolve_left hik
    etb_prekey_fetches img.base H 2000 4
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2020#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext bkAct kyAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hbk)
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
    etb_prekey_fetches img.base H 2000 20
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
      (ret_pc := entry + 2020#64) (by simp [arm64_norm])
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
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, _, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext bkAct kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x7b8 .. +0x7cc` (`1976` → `+0x7d0` → `+0x504`): `ldr x0, [sp, #0x60]; str x8, [x19]`
(`x8 = errTag`, writes the Err tag word), then frees the msg slot
`deallocSlot A msgCap msgPtr msgAct` (`x26 = msgCap`, `[sp' + 96] = msgPtr`; `cbz`, so
`msgCap ≠ noneCap`), then chains into `tail_7d0_wpX`. -/
theorem tail_7b8_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret w0 msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1976#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = errTag) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @tail_7d0_wpX img A ext hC s0
  let H := Rust.withPanics ext
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    etb_prekey_fetches img.base H 1976 12
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
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext ikAct bkAct kyAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hcall := etb_dealloc_ok_at_prekey hC.alloc
    etb_prekey_fetches img.base H 1976 24
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
      (ret_pc := entry + 2000#64) (by simp [arm64_norm])
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
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, hx25_cs, _, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext ikAct bkAct kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx23_cs, hx23, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-! ## 3. Presence-Error Dealloc Chain (`+0x604 .. +0x668` → `+0x80c` / `+0x504`) -/

/-- `+0x654 .. +0x668` (`1620` → `+0x80c` / `+0x504`): frees the msg slot
`deallocSlot A msgCap msgPtr msgAct` (`x26 = msgCap`, `[sp' + 96] = msgPtr`;
`sub #1; cmn #3; b.hi +0x504` skips `cap ∈ {0, noneCap}`), via `tail_80c_wpX`. -/
theorem tail_654_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State} {sp' sret msgCap msgPtr : BitVec 64}
    (msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1620#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    etb_prekey_fetches img.base H 1620 12
    dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    rcases hcap with rfl | rfl
    all_goals
      refine SepWPp.of_sepWP_end hF hsym ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      exact ⟨PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @tail_80c_wpX img A ext hC s0
    etb_prekey_fetches img.base H 1620 24
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗ ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-- `+0x64c .. +0x650` (`1612` → `+0x654` → `+0x504`): `mov w2, #1; bl __rust_dealloc` freeing an
active `(x0 = ptr, x1 = cap)` `u8` buffer, then `tail_654_wpX` (msg slot). -/
theorem tail_64c_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret ptr cap msgCap msgPtr : BitVec 64} (msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1612#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := etb_dealloc_ok_at_prekey hC.alloc
  have hnext := @tail_654_wpX img A ext hC s0
  let H := Rust.withPanics ext
  etb_prekey_fetches img.base H 1612 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_noPanic_tryFrom (ptr, cap.toNat, 1) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + 1620#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk cap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, hx26_cs, _, _, _⟩
  refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  exact hnext msgAct
    ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2, by simp [htr2, htr, arm64_norm]⟩
    hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm]) (by simp [hx26_cs, hx26, arm64_norm])

/-- `+0x638 .. +0x648` (`1592` → `+0x64c` / `+0x654` → `+0x504`): frees the kyber slot
`deallocSlot A kyCap kyPtr kyAct` (`x28 = kyCap`, `x25 = kyPtr`; `cmn #3; b.hi`), then the msg
slot. -/
theorem tail_638_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret kyCap kyPtr msgCap msgPtr : BitVec 64} (kyAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1592#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    have hnext := @tail_654_wpX img A ext hC s0
    etb_prekey_fetches img.base H 1592 12
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    rcases hcap with rfl | rfl
    all_goals
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1620#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      exact hnext msgAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx26, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @tail_64c_wpX img A ext hC s0
    etb_prekey_fetches img.base H 1592 20
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1612#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hnext msgAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt

/-- `+0x604 .. +0x618` (`1540` → `+0x64c` / `+0x654` → `+0x504`): frees the ik slot
`deallocSlot A ikCap ikPtr ikAct` (`x23 = ikCap`, `[sp' + 104] = ikPtr`; `cmn #3; b.hi`), then the
msg slot. -/
theorem tail_604_wpX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : PksmCallees img A ext) {s0 s : State}
    {sp' sret ikCap ikPtr msgCap msgPtr : BitVec 64} (ikAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1540#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQ img s0 sp' sret (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  let H := Rust.withPanics ext
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    have hnext := @tail_654_wpX img A ext hC s0
    etb_prekey_fetches img.base H 1540 12
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    rcases hcap with rfl | rfl
    all_goals
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1620#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr))
        (by apply entails_of_eq; ac_rfl) ?_
      exact SepWPp.frame_tryFrom
        (hnext msgAct
          (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx26, arm64_norm]))
        fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A ikCap ikPtr true =
        (⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
          A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @tail_64c_wpX img A ext hC s0
    etb_prekey_fetches img.base H 1540 24
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + 1612#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre (P' := (A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (hnext msgAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
