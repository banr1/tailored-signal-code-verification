/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- shake: keep
public import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Shared Epilogue and Loop-Error Deallocation Chain

Stack/frame splitting lemmas, shared epilogue `epilogue_504_raw_wpX` (`+0x504..+0x520 → ret`),
and loop-error `Option<Vec<u8>>` deallocation and `DecodeError` drop steps (`+0x4a4..+0x500 → +0x504`).
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
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.call_noPanic_tryFrom := @Wire.SepWPp.call_noPanic_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private gen_decodes libsignalSessionCode_tree etDec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1120) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1316)]

local macro "et_prekey_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.etDec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Local kernel-checked BitVec normalizers -/

private theorem et_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem et_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem et_bv_add_neg_8 (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem et_bv_add_neg_16 (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem et_bv_add_neg_24 (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem et_bv_add_neg_32 (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem et_bv_add_neg_40 (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem et_bv_add_neg_48 (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem et_bv_add_neg_56 (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem et_bv_add_neg_64 (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem et_bv_add_neg_72 (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem et_bv_add_neg_80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem et_bv_add_neg_88 (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem et_bv_add_neg_96 (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem et_bv_add_neg_104 (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem et_bv_add_neg_112 (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem et_bv_add_neg_128 (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem et_bv_add_neg_136 (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem et_bv_add_neg_152 (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem et_bv_add_neg_160 (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem et_bv_add_neg_168 (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem et_bv_add_neg_176 (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem et_bv_add_neg_184 (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem et_bv_add_neg_192 (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem et_bv_add_neg_200 (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem et_bv_add_neg_512 (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit et_bv_sub_add_lit' et_bv_sub_sub_lit BitVec.toNat_zero
  et_bv_add_neg_8 et_bv_add_neg_16 et_bv_add_neg_24 et_bv_add_neg_32 et_bv_add_neg_40
  et_bv_add_neg_48 et_bv_add_neg_56 et_bv_add_neg_64 et_bv_add_neg_72 et_bv_add_neg_80
  et_bv_add_neg_88 et_bv_add_neg_96 et_bv_add_neg_104 et_bv_add_neg_112 et_bv_add_neg_128
  et_bv_add_neg_136 et_bv_add_neg_152 et_bv_add_neg_160 et_bv_add_neg_168 et_bv_add_neg_176
  et_bv_add_neg_184 et_bv_add_neg_192 et_bv_add_neg_200 et_bv_add_neg_512

/-! ## 1. Callee Wrapper, Stack-Split Helpers, and Region Packing Helpers -/

/-- `core::ptr::drop_glue::<prost::error::DecodeError> [local#1]` at the `preKeyTryFromName`
call offset on `contractProg img.base ext` (native `Prost.dropDecodeErrorSpecX A`). -/
theorem dropDecodeError_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.DropDecodeErrorOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]" -
          ls_off% preKeyTryFromName) % 2 ^ 64))
      ((Prost.dropDecodeErrorSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") (by decide)]
  exact h

theorem stackAt_skipFieldStackW_dropDecodeError (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - Prost.dropDecodeErrorStackX) ∗
        stackAt sp Prost.dropDecodeErrorStackX :=
  stackAt_sub_split sp Prost.dropDecodeErrorStackX (Prost.skipFieldStackX 100) (by decide) (by decide)

theorem stackAt_skipFieldStackX_ext (sp : BitVec 64) :
    stackAt sp (Prost.skipFieldStackX 100) =
      memRegion (sp - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - extHookStack) ∗ stackAt sp extHookStack :=
  stackAt_sub_split sp extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)

theorem stackAt_preKeyTryFromSubStack_skipField (sp : BitVec 64) :
    stackAt sp preKeyTryFromSubStack =
      memRegion (sp - BitVec.ofNat 64 preKeyTryFromSubStack)
        (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
        stackAt sp (Prost.skipFieldStackX 100) :=
  stackAt_sub_split sp (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide)

theorem memRegion248_split16 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret, ProofLib.memRegion_eight (sret + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion296_split104 (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 104 ∗ (∃∗ w104 : BitVec 64, (sp' + 104#64) ↦₆₄ w104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 104 + (8 + 184) by decide,
    Prost.memRegion_split sp' 104 192 (by decide),
    Prost.memRegion_split (sp' + 104#64) 8 184 (by decide),
    ProofLib.memRegion_eight (sp' + 104#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion296_repack104 (sp' w104 : BitVec 64) :
    memRegion sp' 104 ∗ ((sp' + 104#64) ↦₆₄ w104) ∗ memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 104 + (8 + 184) by decide,
    Prost.memRegion_split sp' 104 192 (by decide),
    Prost.memRegion_split (sp' + 104#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) w104))

/-- Reassembling `memRegion (sp' + 312) 128` from the 4 `vecHeader`s and 4 `memRegion _ 8` slots
of `wirePreKeyAt`. -/
theorem wirePreKeyHeaders_entails_memRegion128 (sp' kyberCap kyberPtr kyberLen
    bkCap bkPtr bkLen ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64) :
    vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
      vecHeader (sp' + 336#64) bkCap bkPtr bkLen ∗
      vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
      vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
      memRegion (sp' + 408#64) 8 ∗ memRegion (sp' + 416#64) 8 ∗
      memRegion (sp' + 424#64) 8 ∗ memRegion (sp' + 432#64) 8 ⊢
      memRegion (sp' + 312#64) 128 := by
  rw [show (128 : Nat) = 24 + (24 + (24 + (24 + (8 + (8 + (8 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 312#64) 24 104 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64) 24 80 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64) 24 56 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64) 24 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr kyberLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 336#64) bkCap bkPtr bkLen)
      (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 360#64) ikCap ikPtr ikLen)
        (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 384#64) msgCap msgPtr msgLen)
          (Entails.refl _))))

theorem memRegion152_repack_16_128_8 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 128 ∗ memRegion (sp' + 440#64) 8 =
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 16 + (128 + 8) by decide,
    Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem et_stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) preKeyTryFromSubStack ∗
      memRegion (sp - 608#64) 296 ∗
      memRegion (sp - 608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

/-! ## 2. Shared Epilogue (`+0x504 .. +0x520` / `1284 .. 1312` → `s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
/-- Shared epilogue (`+0x504 .. +0x520` → `ret`) of `PreKeySignalMessage::try_from` on
`contractProg img.base ext`: restores `sp = s0.sp`, callee-saved registers `x19..x30`, and
packs the 608-byte frame + `stackAt (s0.sp - 608) preKeyTryFromSubStack` into
`stackAt s0.sp preKeyTryFromStack`. Parameterized over any payload `R : SepProp`. -/
theorem epilogue_504_raw_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ptr : BitVec 64} {bytes : List (BitVec 8)} {s0 s : State} {R : SepProp}
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
        R ∗ (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        sf.trace = s0.trace ∧
        (Pf ⊢ R ∗ (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hsp0 : s0.spAligned = true := by
    rw [State.spAligned, hsp_eq, beq_iff_eq] at hsp
    rw [State.spAligned, beq_iff_eq]
    generalize s0.sp = sp0 at hsp ⊢
    bv_bits
  let H := Rust.withPanics ext
  et_prekey_fetches img.base H 1284 32
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .x30) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  unfold preKeyCalleeSavedAt
  simp only [et_bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨by simp [arm64_norm], fun hv => ?_, by simp [htr, arm64_norm], ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], hv⟩
  · have hstk := et_stackAt_preKeyTryFrom_unsplit s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [et_bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    apply entails_of_eq; ac_rfl

/-! ## 3. Loop-Decode Error Deallocation Chain (`+0x47c .. +0x500 → +0x504`) -/

set_option maxHeartbeats 800000 in
/-- (``+0x4f4 .. +0x500` / `1268 .. 1280` → `+0x504` / `1284``): `mov x0, x24; bl drop_in_place<DecodeError>; mov x8, #-1; stp x8, x27, [x19]`. -/
theorem cleanup_4f4_drop_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret x24 w0 w1 : BitVec 64}
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1268#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcall := dropDecodeError_ok_at_prekeyX hDropErr
  clear hDropErr
  let H := Rust.withPanics ext
  et_prekey_fetches img.base H 1268 16
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1268#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]" -
        ls_off% preKeyTryFromName) % 2 ^ 64)) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hstack := stackAt_skipFieldStackW_dropDecodeError sp'
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]" -
      ls_off% preKeyTryFromName) % 2 ^ 64)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.call_noPanic_tryFrom x24 hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hF1 hsym1
    (ret_pc := entry + bv% (1276)) (by simp [arm64_norm])
    (T := decodeErrorAt A x24 ∗ A.pool ∗ stackAt s.sp Prost.dropDecodeErrorStackX)
    (φ := x24 = x24)
    (by simp [Prost.dropDecodeErrorSpecX, arm64_norm])
    rfl
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Prost.dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, hx27_cs, _⟩
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = sret := by simp [hx19_cs, hx19, arm64_norm]
  have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := by
    simp [hx27_cs, hx27, arm64_norm]
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, errTag, arm64_norm]
  ac_rfl

/-- Discharges `__rust_dealloc` relative to `preKeyTryFromName` on `contractProg img.base ext`
directly from `halloc : AllocHooksW img A ext` (`hC.alloc`). -/
theorem et_dealloc_ok_at_prekey {img : Obj.Image} {A : RustAlloc}
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

set_option maxHeartbeats 800000 in
/-- (``+0x4cc .. +0x4e4` / `1228 .. 1252` → `+0x4f4` / `1268` → `+0x504` / `1284``): frees `deallocSlot A msgCap msgPtr msgAct` (`x26 = msgCap`, `x21 = msgPtr`), then chains into
`cleanup_4f4_drop_wpX`. -/
theorem cleanup_4cc_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret x24 w0 w1 msgCap msgPtr : BitVec 64} (msgAct : Bool)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1228#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @cleanup_4f4_drop_wpX img A ext hDropErr s0
  clear hDropErr
  let H := Rust.withPanics ext
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    et_prekey_fetches img.base H 1228 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1228#64 at hpc
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (1268)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm]) (by simp [hx27, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := et_dealloc_ok_at_prekey halloc
    et_prekey_fetches img.base H 1228 28
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1228#64 at hpc
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
    refine SepWPp.call_noPanic_tryFrom (msgPtr, msgCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + bv% (1252)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk msgCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, _, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_cs, hx27, arm64_norm]
    refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (1268)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine SepWPp.mono_pre (P' := decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact hnext
      (PostEpilogueState.of_steps hF3 hsym3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm]) (by simp [hx27_2, arm64_norm])

set_option maxHeartbeats 800000 in
/-- (``+0x4b4 .. +0x4c8` / `1204 .. 1224` → `+0x4cc` / `1228` → `+0x504` / `1284``): frees `deallocSlot A ikCap ikPtr ikAct` (`x23 = ikCap`, `[sp' + 104] = ikPtr`), then chains into
`cleanup_4cc_wpX`. -/
theorem cleanup_4b4_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret x24 w0 w1 ikCap ikPtr msgCap msgPtr : BitVec 64} (ikAct msgAct : Bool)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1204#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hnext := @cleanup_4cc_wpX img A ext halloc hDropErr s0
  clear hDropErr
  let H := Rust.withPanics ext
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    et_prekey_fetches img.base H 1204 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1204#64 at hpc
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (1228)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext msgAct
        (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  | true =>
    have hdealloc : deallocSlot A ikCap ikPtr true =
        (⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
          A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := et_dealloc_ok_at_prekey halloc
    et_prekey_fetches img.base H 1204 24
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1204#64 at hpc
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
    refine SepWPp.call_noPanic_tryFrom (ikPtr, ikCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + bv% (1228)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk ikCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, hx21_cs, _, _, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx21_2 : s2.readReg64 .x21 = msgPtr := by simp [hx21_cs, hx21, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_cs, hx27, arm64_norm]
    refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx26_2 hx21_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- (``+0x4a4 .. +0x4b0` / `1188 .. 1200` → `+0x4b4` / `1204` → `+0x504` / `1284``): frees `deallocSlot A bkCap bkPtr bkAct` (`x1 = bkCap`, `x0 = bkPtr`), then chains into
`cleanup_4b4_wpX`. -/
theorem cleanup_4a4_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    {s0 s : State} {sp' sret x24 w0 w1 bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1188#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
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
  have hnext := @cleanup_4b4_wpX img A ext halloc hDropErr s0
  clear hDropErr
  let H := Rust.withPanics ext
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    et_prekey_fetches img.base H 1188 8
    dsimp only [contractProg, tripleRatchetProgAtExt] at hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1188#64 at hpc
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
    examples_hide_fetches
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (1204)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext ikAct msgAct
      (PostEpilogueState.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := et_dealloc_ok_at_prekey halloc
    et_prekey_fetches img.base H 1188 16
    dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    change SepWPp (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
    change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1188#64 at hpc
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
    refine SepWPp.call_noPanic_tryFrom (bkPtr, bkCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hF1 hsym1
      (ret_pc := entry + bv% (1204)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := s.readReg64 (Reg.gpr 0#5) = bkPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = bkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk bkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, hx21_cs, _, hx23_cs, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx21_2 : s2.readReg64 .x21 = msgPtr := by simp [hx21_cs, hx21, arm64_norm]
    have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, hx23, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_cs, hx27, arm64_norm]
    refine SepWPp.mono_pre (P' := deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact hnext ikAct msgAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hF2, hsym2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx23_2 hx26_2 hx21_2

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
