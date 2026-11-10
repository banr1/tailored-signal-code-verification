/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Post-Loop Presence Checks and Deallocation Bridges

Proves the `[LibsignalPlacement]` required-field presence checks (`+0x460..+0x5b4`) and
presence-failure `deallocSlot` bridges to `+0x5e0`, `+0x61c`, `+0x66c`, and `+0x678` on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## 1. Frozen Exit State Abbreviations (`[LibsignalPlacement]`) -/

abbrev BkNoneTailStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64)
    (spkTag : BitVec 32) (vb : BitVec 8) (sf : State) : Prop :=
  PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
    (spkTag.zeroExtend 64) vb sf

abbrev IkNoneTailStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr msgCap x24 : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr noneCap msgCap x24 vb sf

abbrev MsgNoneTailStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap x24 : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap noneCap x24 vb sf

abbrev SpkNoneTailStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap 0#64 vb sf

abbrev PresenceOkStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap 1#64 vb sf

/-! ## 2. (`+0x460 .. +0x5b4`): Presence Checks -/

theorem post_bk_none_to_5e0_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1504#64) s
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal))
      (fun sf Pf =>
        BkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ BkNoneTailMem A sp' kyberCap kyberPtr kyberLen bkPtr bkLen
          ikCap ikPtr ikLen msgCap msgPtr msgLen
          regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (optVecU8Buf_cap_add2_ne A kyberCap kyberPtr kyberLen kyberOpt))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hky_ne => ?_
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [h29, arm64_norm], by simp [arm64_norm], by simp [h27, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [h22, arm64_norm], by simp [h21, arm64_norm], by simp [h20, arm64_norm],
    by simp [h19, arm64_norm]⟩, ?_⟩
  dsimp only [BkNoneTailMem, vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

theorem post_bk_some_to_57c_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk : List (BitVec 8)}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
          (spkTag.zeroExtend 64) vb sf ∧
        bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧
        (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
            regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hcallSpe := hC.dropSpeX
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp')
      (sepConj_mono_right (sepConj_mono (optVecU8Buf_cap_add2_ne A kyberCap kyberPtr kyberLen kyberOpt)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_lt_len A bkCap bkPtr bk)))))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w16 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w24 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w32 => SepWPp.exists_pre fun w40 =>
    SepWPp.exists_pre fun w48 => SepWPp.exists_pre fun w52 =>
    SepWPp.exists_pre fun w56 => SepWPp.exists_pre fun w68 =>
    SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
    SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
    SepWPp.exists_pre fun w104 => ?_
  refine SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      ⌜bk.length ≤ bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
        ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hky_ne => SepWPp.pure_pre fun ⟨hbk_le, hbk_lt, _⟩ => ?_
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr kyberLen bkCap bkPtr (BitVec.ofNat 64 bk.length)
  have hhdr80 := post_headers_entails_memRegion80W sp' ikCap ikPtr ikLen msgCap msgPtr msgLen
    regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (P' := (speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗
      stackAt s.sp Getters.dropSpeStackX) ∗
      (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗
        memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
          (Prost.skipFieldStackX 100 - Getters.dropSpeStackX)))
    (by
      rw [hspe, hstackSpe, hsp_eq]; dsimp only [seg1SpillsAtW]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ bkCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ BitVec.ofNat 64 bk.length)) ∗
        (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool ∗ stackAt sp' Getters.dropSpeStackX ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
            (Prost.skipFieldStackX 100 - Getters.dropSpeStackX)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) (by apply entails_of_eq; ac_rfl)) ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded
    (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 1404#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen ikPtr ikLen msgPtr msgLen
        regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
      memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
      optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗
      memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl rfl ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_cs, h29, arm64_norm], by simp [hx28_cs, arm64_norm],
    by simp [hx27_cs, h27, arm64_norm], by simp [hx26_cs, arm64_norm],
    by simp [hx25_cs, arm64_norm], by simp [hx24_cs, arm64_norm],
    by simp [hx23_cs, arm64_norm], by simp [hx22_cs, h22, arm64_norm],
    by simp [hx21_cs, h21, arm64_norm], by simp [hx20_cs, h20, arm64_norm],
    by simp [hx19_cs, h19, arm64_norm]⟩, hbk_le, hbk_lt, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

theorem post_ik_none_to_61c_placed_wpW [LibsignalPlacement]
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1564#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

theorem post_ik_some_to_590_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1424#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hik_eq := cap_add1_eq_of_lt hik_lt
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded
    (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 1424#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

theorem post_msg_none_to_66c_placed_wpW [LibsignalPlacement]
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1644#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

theorem post_msg_some_to_5a4_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) (hmsg_lt : msgCap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1444#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded
    (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 1444#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

theorem post_spk_none_to_678_placed_wpW [LibsignalPlacement]
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1656#64) s
      (memRegion (sp' + 312#64) 48)
      (fun sf Pf =>
        SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine SepWPp.mono_pre (post_memRegion48_split8 (sp' + 312#64)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.exists_pre fun w312 => of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, Entails.refl _⟩

theorem post_spk_some_to_5b4_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1460#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hcallSpe := hC.dropSpeX
  have hstackSpe := stackAt_sub_split sp' Getters.dropSpeStackX (Prost.skipFieldStackX 100)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312 =>
    of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded
    (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 1460#64) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp Getters.dropSpeStackX)
    (F := memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
      (Prost.skipFieldStackX 100 - Getters.dropSpeStackX))
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [Getters.dropSpeSpecX, hsp_eq, arm64_norm]) rfl
    (by rw [hspe, hstackSpe, hsp_eq]; ac_rfl) ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [Getters.dropSpeSpecX]; rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 (SepWP.done hpc2 hrun2 fun hcl3 => ?_)
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    by simp [hx29_2, hx29, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [hx24_2, hx24, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

theorem post_seg1_xok_to_5b4_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {vb : BitVec 8} {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))} {bk ik msg : List (BitVec 8)}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1460#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        bkCap.toNat < 2 ^ 63 ∧ ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧
        (Pf ⊢ seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
            ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
            regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (vecU8Buf_cap_lt_len A ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_cap_lt_len A msgCap msgPtr msg)))))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜ik.length ≤ ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0⌝ ∗
      ⌜msg.length ≤ msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0⌝ ∗
      ((memRegion (sp' + 16#64) 96 ∗ vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        vecHeader (sp' + 360#64) ikCap ikPtr (BitVec.ofNat 64 ik.length) ∗
        vecHeader (sp' + 384#64) msgCap msgPtr (BitVec.ofNat 64 msg.length) ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ spkId) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun ⟨_, hik_lt, _⟩ => SepWPp.pure_pre fun ⟨_, hmsg_lt, _⟩ => ?_
  let tailF := seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
      ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
      regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg
  refine SepWPp.bind (Qm := fun s1 P1 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s1 ∧
      bkCap.toNat < 2 ^ 63 ∧
      (P1 ⊢ (seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
            ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
            regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
          memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        (Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg)))
    (SepWPp.frame_tryFrom (post_bk_some_to_57c_placed_wpW hC hst hpc hrun hx24)
      fun s1 P1 ⟨hst1, _, hbk_lt, hent1⟩ =>
        ⟨by simpa [PresenceOkStatePlaced, PresenceErrTailStatePlaced] using hst1, hbk_lt,
          sepConj_mono_left hent1⟩) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hbk_lt, hent1⟩
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF)
    (Entails.trans hent1 (by dsimp only [tailF]; apply entails_of_eq; ac_rfl)) ?_
  refine SepWPp.bind (Qm := fun s2 P2 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s2 ∧
      (P2 ⊢ (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF))
    (SepWPp.frame_tryFrom (post_ik_some_to_590_placed_wpW hC hst1 hpc1 hrun1 hik_lt)
      fun s2 P2 ⟨hst2, hent2⟩ => ⟨hst2, sepConj_mono_left hent2⟩) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, hent2⟩
  refine SepWPp.mono_pre hent2 ?_
  refine SepWPp.bind (Qm := fun s3 P3 =>
      PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
      (P3 ⊢ (memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ tailF))
    (SepWPp.frame_tryFrom (post_msg_some_to_5a4_placed_wpW hC hst2 hpc2 hrun2 hmsg_lt)
      fun s3 P3 ⟨hst3, hent3⟩ => ⟨hst3, sepConj_mono_left hent3⟩) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, hent3⟩
  refine SepWPp.mono_pre hent3 ?_
  refine SepWPp.frame_tryFrom (post_spk_some_to_5b4_placed_wpW hC hst3 hpc3 hrun3)
    fun sf Pf ⟨hst4, hent4⟩ => ⟨hst4, hbk_lt, hik_lt, hmsg_lt, ?_⟩
  refine Entails.trans (sepConj_mono_left hent4) ?_
  dsimp only [tailF]; apply entails_of_eq; ac_rfl

/-! ## 3. Dealloc-Slot Bridges (`[LibsignalPlacement]`) -/

theorem post_bk_none_full_to_5e0_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt ikOpt msgOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1504#64) s
      ((((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
          vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          optVecU8Buf A ikCap ikPtr ikLen ikOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        BkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ ∃∗ kyAct : Bool, ∃∗ ikAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A kyberCap kyberPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      (tryFromQp s0) := by
  refine SepWPp.frame_tryFrom (post_bk_none_to_5e0_placed_wpW hst hpc hrun hx24)
    fun sf Pf ⟨hbst, hent⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  dsimp only [BkNoneTailMem]
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  have hik := optVecU8Buf_entails_deallocSlot A ikCap ikPtr ikLen ikOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A msgCap msgPtr msgLen msgOpt
  refine Entails.trans (Q :=
      (∃∗ kyAct : Bool, deallocSlot A kyberCap kyberPtr kyAct) ∗
      (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗
      (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
    ?_ ?_
  · refine Entails.trans (Q :=
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        optVecU8Buf A ikCap ikPtr ikLen ikOpt ∗
        optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      (by apply entails_of_eq; ac_rfl)
      (sepConj_mono hky (sepConj_mono hik (sepConj_mono_left hmsg)))
  · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun msgAct =>
      Entails.sepExists_elim fun ikAct =>
      Entails.sepExists_elim fun kyAct => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
    refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
    refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
    apply entails_of_eq; ac_rfl

theorem post_ik_none_full_to_61c_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 bkCap bkPtr kyberCap kyberPtr kyberLen
      msgCap msgPtr msgLen x24 : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {kyberOpt msgOpt : Option (List (BitVec 8))}
    (hst : IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1564#64) s
      (memRegion (sp' + 312#64) 48 ∗
        (Wire.vecU8Buf A bkCap bkPtr bk ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ bkAct : Bool, ∃∗ kyAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_ik_none_to_61c_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hist, hent⟩ => ⟨hist, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A msgCap msgPtr msgLen msgOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hky (sepConj_mono_left hmsg)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  apply entails_of_eq; ac_rfl

theorem post_msg_none_full_to_66c_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 ikCap ikPtr bkCap bkPtr kyberCap kyberPtr kyberLen
      x24 : BitVec 64} {vb : BitVec 8}
    {ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1644#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hik_ne => SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_msg_none_to_66c_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hmst, hent⟩ => ⟨hmst, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

theorem post_spk_none_full_to_678_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 msgCap msgPtr ikCap ikPtr bkCap bkPtr
      kyberCap kyberPtr kyberLen : BitVec 64} {vb : BitVec 8}
    {msg ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1656#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A msgCap msgPtr msg)
        (sepConj_mono_right (sepConj_mono (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
          (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hmsg_ne =>
    SepWPp.pure_pre fun hik_ne =>
    SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_spk_none_to_678_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hsst, hent⟩ => ⟨hsst, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
