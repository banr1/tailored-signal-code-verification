/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyB
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: Unknown-Tag `skip_field` Arm and Key-Check Error Stubs

Symbolic execution of the `prost::encoding::skip_field` caller wrapper, the unknown-tag
arm (`+0x2d8..+0x2e8`, `+0x364..+0x368`), and the protobuf key-validation error stubs
(`+0x154..+0x16c`, `+0x308..+0x33c`) on `contractProg img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_SkipArm : True := trivial

/-! ## 2. Callee Offset Wrapper: `skipField_ok_atX` -/

/-- Caller-relative `subroutine_ok` for `prost::encoding::skip_field::<&mut &[u8]> [local#1]`
from `preKeyTryFromName`. -/
theorem skipField_ok_atX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.SkipFieldOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((Prost.skipFieldSpecX A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) =
      (contractProg img.base ext).fnAddr skipFieldName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

abbrev skipField_ok_subPK := @skipField_ok_atX

/-! ## 3. (`+0x2d8..+0x2e8`, `+0x364..+0x368`): Unknown-Tag `skip_field` Branch -/

/-- Error stub `+0x364..+0x368` (`mov x24, x0; b +0x460`) for `skip_field` failure. -/
theorem skipFieldErrPK_364_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {n : Nat} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x364#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx0_ne : s.readReg64 .x0 ≠ 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        decodeErrorAtStackLen A (s.readReg64 .x0) n ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 868 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 868#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
    by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hF1, hsym1, by simpa [arm64_norm] using htr⟩, ?_⟩
  simp only [arm64_norm]
  exact preKeyLoopExitMem_err_intro A sp' ptr bs (s.readReg64 (Reg.gpr 0#5)) hx0_ne n mErr

set_option maxHeartbeats 800000 in
/-- Unknown-tag (`skip_field`) branch `+0x2d8..+0x2e8` and error stub `+0x364..+0x368`:
calls `skip_field(wt, tag, sp' + 440, 100)`, jumping to `+0x0e4` on `some rest` or setting
`x24 := x0` at `+0x364` and jumping to `+0x460` on `none`. -/
theorem mergeSkipField_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hskip : Prost.SkipFieldOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2d8#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  have hcall := skipField_ok_atX hskip
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 728 20
  preKeyTryFrom_fetches img.base H 868 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 728#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_tryFromX ⟨wt, tag, 100, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (740)) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ sliceCursorAt (sp' + 296#64) ptr bs ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 2 ^ 32 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 2 ^ 32 ∧ bs.length < 2 ^ 63)
    (by simp only [Prost.skipFieldSpecX, hsp_eq, h0, h1, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide, by omega⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  dsimp only [Prost.skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (228)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine SepWPp.mono_pre ?_
      (hcont rest _ hs
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr))
    apply entails_of_eq
    simp only [hsp_eq, arm64_norm]
    ac_rfl
  | none =>
    dsimp only
    have hres := hnone hs
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine SepWPp.of_sepWP_end hF2 hsym2 ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [arm64_norm]
    refine Entails.trans ?_
      (preKeyLoopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 m)
    apply entails_of_eq
    simp only [hsp_eq, arm64_norm]
    ac_rfl
/-! ## 4. Key-Check Error Rows (`+0x154..+0x16c`, `+0x308..+0x33c`) -/

/-- Key-check error stub `+0x308..+0x310` (`add x8, x27, #2; stur x24, [x29, #-0x38]; b +0x324`):
constructs `Kind::InvalidTag` (`0x8000000000000004`) when `key >> 32 ≠ 0` and jumps to
`decodeErrorFromPK_tail_wpX` (`+0x324..+0x334` → `+0x460`). -/
theorem decodeErrorInvalidTagPK_308_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr w0 w1 : BitVec 64}
    {bs rest : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x308#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ w0) ∗
        ((sp' + 456#64) ↦₆₄ w1) ∗
        memRegion (sp' + 464#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have herr := @decodeErrorFromPK_tail_wpX img A ext hFrom s0
  preKeyTryFrom_fetches img.base H 776 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at herr hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 776#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h27 : s.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := hregs.x27
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre ?_
    (herr (w0 := w0) (mErr := mErr)
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1
      (by simpa [arm64_norm] using htr)
      (by simp only [KindNoHeap, arm64_norm]))
  refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 (s.readReg64 (Reg.gpr 24#5)) bs rest mErr)
  apply entails_of_eq
  ac_rfl

/-- Key-check error stub `+0x314..+0x31c` (`mov x8, #0x8000000000000003; stur x0, [x29, #-0x38]; b +0x324`):
constructs `Kind::InvalidWireType` (`0x8000000000000003`) when `wt ≥ 6` and jumps to
`decodeErrorFromPK_tail_wpX` (`+0x324..+0x334` → `+0x460`). -/
theorem decodeErrorInvalidWireTypePK_314_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr w0 w1 : BitVec 64}
    {bs rest : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x314#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ w0) ∗
        ((sp' + 456#64) ↦₆₄ w1) ∗
        memRegion (sp' + 464#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have herr := @decodeErrorFromPK_tail_wpX img A ext hFrom s0
  preKeyTryFrom_fetches img.base H 788 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at herr hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 788#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre ?_
    (herr (w0 := w0) (mErr := mErr)
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1
      (by simpa [arm64_norm] using htr)
      (by simp only [KindNoHeap, arm64_norm]))
  refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 (s.readReg64 (Reg.gpr 0#5)) bs rest mErr)
  apply entails_of_eq
  ac_rfl

/-- Key-check error stub `+0x320..+0x334` (`add x8, x27, #3` falling into `+0x324`):
constructs `Kind::InvalidTag(0)` (`0x8000000000000005`) when `tag = 0` and falls through to
`decodeErrorFromPK_tail_wpX` (`+0x324..+0x334` → `+0x460`). -/
theorem decodeErrorInvalidTagZeroPK_320_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr w0 : BitVec 64}
    {bs rest : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x320#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ w0) ∗
        memRegion (sp' + 456#64) 56 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have herr := @decodeErrorFromPK_tail_wpX img A ext hFrom s0
  preKeyTryFrom_fetches img.base H 800 4
  dsimp only [contractProg, tripleRatchetProgAtExt] at herr hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 800#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h27 : s.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := hregs.x27
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre ?_
    (herr (w0 := w0) (mErr := mErr)
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1
      (by simpa [arm64_norm] using htr)
      (by simp only [KindNoHeap, arm64_norm]))
  refine Entails.trans
    (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 296#64) ptr bs rest)) ?_
  apply entails_of_eq
  simp only [arm64_norm]

/-- L1/Key-check error stub `+0x338..+0x33c` (`ldur x24, [x29, #-0x38]; b +0x460`):
loads the `DecodeError` pointer `e` from `[sp' + 456]` into `x24` and jumps to `+0x460`. -/
theorem decodeVarintSliceErrPK_338_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr e : BitVec 64}
    {bs : List (BitVec 8)} {n : Nat} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x338#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (he_ne : e ≠ 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 8 ∗
        ((sp' + 456#64) ↦₆₄ e) ∗
        memRegion (sp' + 464#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        decodeErrorAtStackLen A e n ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 824 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 824#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
    by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hF1, hsym1, by simpa [arm64_norm] using htr⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (preKeyLoopExitMem_err_intro A sp' ptr bs e he_ne n mErr)
  rw [memRegion64_split8_448 sp']
  simp only [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (pointsTo64_456_memRegion48_entails_memRegion56 sp' e)

set_option maxHeartbeats 800000 in
/-- Key validation `+0x154..+0x164` and error rows `+0x308..+0x334`:
validates `key` in `x24` (`key < 2^32`, `key % 8 < 6`), advancing to `+0x168` (`lsr w1, w24, #3`)
with `x0 = wt.toNat` and `x24 = key` on `key.toNat < 2^32` and `WireType.ofNat? (key.toNat % 8) = some wt`,
or jumping through `+0x308`/`+0x314` → `+0x324` (`decodeErrorFromPK_tail_wpX`) to `+0x460` on error. -/
theorem decodeKeyCheckPK_154_to_168_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (wt : WireType) (s1 : State),
      key.toNat < 2 ^ 32 →
      WireType.ofNat? (key.toNat % 8) = some wt →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x168#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x24 = key →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have herr := @decodeErrorFromPK_tail_wpX img A ext hFrom s0
  preKeyTryFrom_fetches img.base H 340 20
  preKeyTryFrom_fetches img.base H 776 24
  dsimp only [contractProg, tripleRatchetProgAtExt] at herr hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 340#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h24 : s.readReg64 (Reg.gpr 24#5) = key := hx24
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h27 : s.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := hregs.x27
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by
      unfold decodeKey
      rw [hdv]
      simp only [hkey32, ↓reduceIte]
    have hres := hnone hdk
    subst hres
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    rw [memRegion64_split_448_456_464 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre ?_
      (herr (w0 := w0) (mErr := m)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1
        (by simpa [arm64_norm] using htr)
        (by simp only [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 key bs rest m)
    apply entails_of_eq
    ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey
        rw [hdv]
        simp only [hkey32, ↓reduceIte, hwt]
      have hres := hnone hdk
      subst hres
      have hge6 : 6 ≤ key.toNat % 8 := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      rw [memRegion64_split_448_456_464 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine SepWPp.mono_pre ?_
        (herr (w0 := w0) (mErr := m)
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1
          (by simpa [arm64_norm] using htr)
          (by simp only [KindNoHeap, arm64_norm]))
      refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 (key &&& 7#64) bs rest m)
      apply entails_of_eq
      ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (360)) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      have hand7_eq := key_and7_eq_wt key hwt
      exact hcont wt _ hkey_lt hwt
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1
        (by simpa [arm64_norm] using htr)
        (by simp only [arm64_norm]; exact hand7_eq)
        (by simp only [arm64_norm]; exact h24)

/-- Full key validation `+0x154..+0x16c` and error rows `+0x308..+0x334`:
validates `key` in `x24` (`key < 2^32`, `key % 8 < 6`, `tag = key / 8 ≥ 1`), advancing to `+0x170`
with `x0 = wt.toNat` and `x1 = tag` on `some ((tag, wt), rest)`, or jumping through
`+0x308`/`+0x314`/`+0x320` → `+0x324` (`decodeErrorFromPK_tail_wpX`) to `+0x460` on `none`. -/
theorem decodeKeyCheckPK_154_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (tag : Nat) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) :=
  decodeKeyPK_tail_cpsX hFrom hdv hpc hrun hregs hsp hF hsym htr hx24 hcont hnone

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
