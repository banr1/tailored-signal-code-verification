/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup

/-!
# `PreKeySignalMessage::try_from`: Loop-Decode Error Tail (`+0x460 → +0x504 → ret`)

Proves `cleanup_47c_wpX`, the error-specialized epilogue `epilogue_504_err_wpE`, and the full
loop-decode error path (`+0x460`, `x24 ≠ 0`), freeing any active `Option<Vec<u8>>` field buffers,
dropping `DecodeError`, and writing `pksmErrE A [] sret .invalidProtobufEncoding`.
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
open CryptoVerification.LibsignalTripleRatchet.Prost hiding memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev SepWPp.call_noPanic_tryFrom := @Wire.SepWPp.call_noPanic_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private gen_decodes libsignalSessionCode_tree et2Dec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1120) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1188)]

local macro "et2_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.et2Dec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem et2_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem et2_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem et2_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem et2_bv_add_neg_120 (x : BitVec 64) : x + bv% (2 ^ 64 - 120) = x - 120#64 := by bv_omega
private theorem et2_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem et2_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem et2_bv_add_neg_144 (x : BitVec 64) : x + bv% (2 ^ 64 - 144) = x - 144#64 := by bv_omega
private theorem et2_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem et2_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem et2_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem et2_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem et2_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem et2_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem et2_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit et2_bv_sub_add_lit' et2_bv_sub_sub_lit BitVec.toNat_zero
  et2_bv_add_neg_112 et2_bv_add_neg_120 et2_bv_add_neg_128 et2_bv_add_neg_136 et2_bv_add_neg_144
  et2_bv_add_neg_152 et2_bv_add_neg_160 et2_bv_add_neg_168 et2_bv_add_neg_176 et2_bv_add_neg_184
  et2_bv_add_neg_192 et2_bv_add_neg_200

set_option maxHeartbeats 800000 in
/-- (``+0x47c .. +0x4a0` / `1148 .. 1184` → `+0x4a4` / `1188` → `+0x504` / `1284``): frees `deallocSlot A kyberCap kyberPtr kyberAct` (`x28 = kyberCap`, `x25 = kyberPtr`, saving
`x0 = bkPtr` in `x20` and `x1 = bkCap` in `x22` across `__rust_dealloc`), then chains into
`cleanup_4a4_wpX`. -/
theorem cleanup_47c_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret x24 w0 w1 kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyberAct bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1148#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx28 : s.readReg64 .x28 = kyberCap) (hx25 : s.readReg64 .x25 = kyberPtr)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A kyberCap kyberPtr kyberAct ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @cleanup_4a4_wpX img A ext halloc hDropErr s0
  clear hDropErr
  let H := Rust.withPanics ext
  cases kyberAct with
  | false =>
    have hdealloc : deallocSlot A kyberCap kyberPtr false = ⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    et2_prekey_fetches img.base H 1148 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1148#64 at hpc
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (1188)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext bkAct ikAct msgAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A kyberCap kyberPtr true =
        (⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
          A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := et_dealloc_ok_at_prekey halloc
    et2_prekey_fetches img.base H 1148 40
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1148#64 at hpc
    change subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) _ at hcall
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.call_noPanic_tryFrom (kyberPtr, kyberCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + bv% (1180)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := kyberPtr = kyberPtr ∧ kyberCap.toNat = kyberCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk kyberCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = bkPtr := by simp [hx20_cs, arm64_norm]
    have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = msgPtr := by simp [hx21_cs, hx21, arm64_norm]
    have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = bkCap := by simp [hx22_cs, arm64_norm]
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = ikCap := by simp [hx23_cs, hx23, arm64_norm]
    have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 (Reg.gpr 26#5) = msgCap := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := by
      simp [hx27_cs, hx27, arm64_norm]
    refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (1188)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine SepWPp.mono_pre (P' := deallocSlot A bkCap bkPtr bkAct ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact hnext bkAct ikAct msgAct
      (PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm])
      (by simp [hx27_2, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hx23_2, arm64_norm]) (by simp [hx26_2, arm64_norm]) (by simp [hx21_2, arm64_norm])

/-! ## 4. Full Loop-Decode Error Tail (`+0x460 → +0x504` and `+0x460 → ret`) -/

abbrev PreKeyTryFromRawGhost := CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost

/-- Shared epilogue (`+0x504 .. +0x520` → `ret`) of `PreKeySignalMessage::try_from` on
`contractProg img.base ext` specialized to `x : PreKeyTryFromRawGhost`. -/
theorem epilogue_504_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : PreKeyTryFromRawGhost} {s0 s : State} {R : SepProp}
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        R ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        sf.trace = s0.trace ∧
        (Pf ⊢ R ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) :=
  epilogue_504_raw_wpX hst hpc hrun

/-- Error-specialized epilogue (`+0x504 .. +0x520` → `ret`) with exact
`R = pksmErrE A fn x.ret e ∗ anyHeap`. -/
theorem epilogue_504_err_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : PreKeyTryFromRawGhost} {s0 s : State}
    (fn : List (BitVec 8)) (e : SignalProtocolError)
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A fn x.ret e ∗ anyHeap) ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        sf.trace = s0.trace ∧
        (Pf ⊢ (pksmErrE A fn x.ret e ∗ anyHeap) ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) :=
  epilogue_504_wpX hst hpc hrun

set_option maxHeartbeats 1200000 in
/-- Loop-decode error path (`+0x460 .. +0x500` → `+0x504` when `x24 ≠ 0`):
loads the 4 `Option<Vec<u8>>` headers of `mErr : ProtoPreKeySignalMessage` from `sp' + 312..408`, spills
`ikPtr` to `sp' + 104`, frees any active buffers among `kyberCiphertext`, `baseKey`, `identityKey`,
`message`, drops `decodeErrorAt A x24`, writes `pksmErrE A [] sret .invalidProtobufEncoding ∗ anyHeap`,
and repacks `memRegion sp' 296` and `memRegion (sp' + 312) 128`. -/
theorem preKey_loopErr_460_to_504_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 x24 : BitVec 64} {vb : BitVec 8}
    (hst : PreKeyLoopExitState img s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (wirePreKeyOf A (sp' + 312#64) mErr ∗
        decodeErrorAt A x24 ∗
        memRegion sp' 296 ∗
        memRegion sret 248 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 296 ∗ memRegion (sp' + 312#64) 128 ∗
          (pksmErrE A [] sret .invalidProtobufEncoding ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hF, hsym, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx29 : s.readReg64 .x29 = sp' + 512#64 := hregs.x29
  have hx19 : s.readReg64 .x19 = sret := hregs.x19
  have hx27 : s.readReg64 .x27 = 0x8000000000000002#64 := hregs.x27
  have hnext := @cleanup_47c_wpX img A ext halloc hDropErr s0
  clear hDropErr
  unfold wirePreKeyOf
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun g => ?_
  unfold wirePreKeyAt
  have hent_wire :
      optVecU8At A g.kyberCt (sp' + 312#64) mErr.kyberCiphertext ∗
      optVecU8At A g.baseKey (sp' + 312#64 + 0x18#64) mErr.baseKey ∗
      optVecU8At A g.identityKey (sp' + 312#64 + 0x30#64) mErr.identityKey ∗
      optVecU8At A g.message (sp' + 312#64 + 0x48#64) mErr.message ∗
      Prost.optU32At (sp' + 312#64 + 0x60#64) mErr.registrationId ∗
      Prost.optU32At (sp' + 312#64 + 0x68#64) mErr.preKeyId ∗
      Prost.optU32At (sp' + 312#64 + 0x70#64) mErr.signedPreKeyId ∗
      Prost.optU32At (sp' + 312#64 + 0x78#64) mErr.kyberPreKeyId ⊢
      (∃∗ kyberCap, ∃∗ kyberPtr, ∃∗ kyberLen, ∃∗ kyberAct,
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗ deallocSlot A kyberCap kyberPtr kyberAct) ∗
      (∃∗ bkCap, ∃∗ bkPtr, ∃∗ bkLen, ∃∗ bkAct,
        vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗ deallocSlot A bkCap bkPtr bkAct) ∗
      (∃∗ ikCap, ∃∗ ikPtr, ∃∗ ikLen, ∃∗ ikAct,
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗ deallocSlot A ikCap ikPtr ikAct) ∗
      (∃∗ msgCap, ∃∗ msgPtr, ∃∗ msgLen, ∃∗ msgAct,
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗ deallocSlot A msgCap msgPtr msgAct) ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
      memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (optVecU8At_entails_header_dealloc A g.kyberCt (sp' + 312#64) mErr.kyberCiphertext)
      (sepConj_mono (optVecU8At_entails_header_dealloc A g.baseKey (sp' + 336#64) mErr.baseKey)
        (sepConj_mono (optVecU8At_entails_header_dealloc A g.identityKey (sp' + 360#64) mErr.identityKey)
          (sepConj_mono (optVecU8At_entails_header_dealloc A g.message (sp' + 384#64) mErr.message)
            (sepConj_mono (optU32At_entails_memRegion8 (sp' + 408#64) mErr.registrationId)
              (sepConj_mono (optU32At_entails_memRegion8 (sp' + 416#64) mErr.preKeyId)
                (sepConj_mono (optU32At_entails_memRegion8 (sp' + 424#64) mErr.signedPreKeyId)
                  (optU32At_entails_memRegion8 (sp' + 432#64) mErr.kyberPreKeyId)))))))
  rw (occs := .pos [1]) [memRegion296_split104 sp']
  refine SepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion248_split16 sret))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
    SepWPp.exists_pre fun w104 =>
    SepWPp.exists_pre fun msgCap => SepWPp.exists_pre fun msgPtr =>
    SepWPp.exists_pre fun msgLen => SepWPp.exists_pre fun msgAct =>
    SepWPp.exists_pre fun ikCap => SepWPp.exists_pre fun ikPtr =>
    SepWPp.exists_pre fun ikLen => SepWPp.exists_pre fun ikAct =>
    SepWPp.exists_pre fun bkCap => SepWPp.exists_pre fun bkPtr =>
    SepWPp.exists_pre fun bkLen => SepWPp.exists_pre fun bkAct =>
    SepWPp.exists_pre fun kyberCap => SepWPp.exists_pre fun kyberPtr =>
    SepWPp.exists_pre fun kyberLen => SepWPp.exists_pre fun kyberAct => ?_
  have hvh :
      vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen =
        ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∧
      vecHeader (sp' + 336#64) bkCap bkPtr bkLen =
        ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∧
      vecHeader (sp' + 360#64) ikCap ikPtr ikLen =
        ((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∧
      vecHeader (sp' + 384#64) msgCap msgPtr msgLen =
        ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]
  simp only [sepConj_assoc]
  let H := Rust.withPanics ext
  et2_prekey_fetches img.base H 1120 28
  dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (1148)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  set F_hdr := memRegion sp' 104 ∗ memRegion (sp' + 112#64) 184 ∗
    vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
    vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗
    vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
    vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
    memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
    memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sret + 16#64) 232
  refine SepWPp.mono_pre (P' := (deallocSlot A kyberCap kyberPtr kyberAct ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A msgCap msgPtr msgAct ∗
      decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ F_hdr)
    (by
      dsimp only [F_hdr]
      apply entails_of_eq
      rw [hvh1, hvh2, hvh3, hvh4]
      ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (hnext kyberAct bkAct ikAct msgAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hm296 := memRegion296_repack104 sp' ikPtr
  have hm128 := wirePreKeyHeaders_entails_memRegion128 sp' kyberCap kyberPtr kyberLen
    bkCap bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen
  have herr : (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
      memRegion (sret + 16#64) 232 ⊢ pksmErrE A [] sret .invalidProtobufEncoding ∗ anyHeap := by
    have hc : (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
        memRegion (sret + 16#64) 232 ⊢ pksmErrE A [] sret .invalidProtobufEncoding :=
      errCells_invalidProtobufEncoding A [] sret
    exact Entails.trans hc
      (Entails.trans (Entails.of_eq (sepConj_emp _).symm) (sepConj_mono_right (entails_anyHeap emp)))
  dsimp only [F_hdr]
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono hm296
        (sepConj_mono hm128
          (sepConj_mono herr (Entails.refl (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))))
      (by apply entails_of_eq; ac_rfl))
  apply entails_of_eq; ac_rfl

/-- Full loop-decode error tail (`+0x460` / `1120` → `+0x504` / `1284` → `s0.readReg64 .x30`)
chaining `preKey_loopErr_460_to_504_wpE` into `epilogue_504_err_wpE`. -/
theorem preKey_loopErr_460_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {x : PreKeyTryFromRawGhost} {s0 s : State} {vb : BitVec 8} {x24 : BitVec 64}
    (hst : PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (contractProg img.base ext)
      (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) mErr ∗
        decodeErrorAt A x24 ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        sf.trace = s0.trace ∧
        (Pf ⊢ (pksmErrE A [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
          (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  have hsub := stackAt_preKeyTryFromSubStack_skipField sp'
  set F_epi := memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
    memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗
    memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗
    (x.ptr ↦ₛ x.bytes) ∗ logOff img
  refine SepWPp.mono_pre (P' :=
      (wirePreKeyOf A (sp' + 312#64) mErr ∗
        decodeErrorAt A x24 ∗
        memRegion sp' 296 ∗
        memRegion x.ret 248 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ F_epi)
    (by
      dsimp only [F_epi]
      rw [hsub]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (preKey_loopErr_460_to_504_wpE halloc hDropErr hst hpc hrun hx24 hx24_ne mErr) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  refine SepWPp.mono_pre (P' :=
      stackAt sp' preKeyTryFromSubStack ∗
        memRegion sp' 296 ∗
        memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗
        preKeyCalleeSavedAt sp' s0 ∗
        (pksmErrE A [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
    (by
      dsimp only [F_epi]
      rw [hsub, ← memRegion152_repack_16_128_8 sp']
      apply entails_of_eq; ac_rfl) ?_
  exact epilogue_504_err_wpE [] .invalidProtobufEncoding hst1 hpc1 hrun1

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
