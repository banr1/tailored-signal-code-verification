/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Empty-Body and Loop-Entry Prologue Segments

Proves the `+0x0bc → +0x524 → +0x504` empty-body error path, `+0x0bc → +0x0f4` loop-entry
step, and `preKey_init_to_460_placed_wpW` on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open RunProofs.Pksm

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_entails := @Wire.SepWPp.bind_frame_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

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
attribute [local simp, local arm64_norm, local wp_norm]
  cond_eq_subs1_false_w40 cond_eq_len1
  cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

/-- First half of `x.bytes = [vb]` (`len = 1#64`) after `+0x0bc` under `[LibsignalPlacement]`:
steps `+0x0bc → +0x300 → +0x460..+0x474 → +0x4e8..+0x4ec → +0x524` (`1316`). -/
theorem prologue_bc_len1_to_524_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {sret sp' s104 kyberPtr bkPtr ikPtr msgPtr : BitVec 64} {s0 s3 : State}
    (hst : PostEpilogueStatePlaced s0 sp' s3)
    (hpc : s3.pc = (blkPl_111).base + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 1#64 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx19 : s3.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1316#64) s3
      (((sp' + 104#64) ↦₆₄ s104) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr))
      (fun s4 P4 =>
        (PostEpilogueStatePlaced s0 sp' s4 ∧
        s4.readReg64 .x29 = sp' + 512#64 ∧
        s4.readReg64 .x28 = noneCap ∧
        s4.readReg64 .x27 = 0x8000000000000002#64 ∧
        s4.readReg64 .x26 = noneCap ∧
        s4.readReg64 .x23 = noneCap ∧
        s4.readReg64 .x19 = sret ∧
        s4.readReg64 .x8 = msgPtr ∧
        s4.readReg64 .x1 = noneCap) ∧
        (P4 ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  dsimp only [noneCap]
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl4
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl4, by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [arm64_norm],
    by simp [hx27, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx19, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm]⟩, ?_⟩
  apply entails_of_eq; ac_rfl

private theorem plb_memRegion248_split16 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ ws8 : BitVec 64, ∃∗ ws0 : BitVec 64,
        (sret ↦₆₄ ws0) ∗ ((sret + 8#64) ↦₆₄ ws8) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 16 + 232 by decide,
    Prost.memRegion_split sret 16 232 (by decide)]
  refine Entails.trans (sepConj_mono_left (memRegion16_split8_8' sret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  exact Entails.refl _

/-- (``x.bytes = [vb]`, `len = 1#64`, second half `+0x524 → +0x504`, `[LibsignalPlacement]``): steps `+0x524..+0x550 → +0x5e0..+0x5f0 → +0x604..+0x60c → +0x654..+0x65c → +0x504` (`1284`),
writing `pksmErrE A [] sret .invalidProtobufEncoding`. -/
theorem prologue_524_len1_to_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {sret sp' s96 kyberPtr kyberLen bkPtr bkLen ikPtr ikLen msgPtr msgLen : BitVec 64}
    {u412 u420 u428 u436 : BitVec 32} {s0 s4 : State}
    (hst : PostEpilogueStatePlaced s0 sp' s4)
    (hpc : s4.pc = (blkPl_111).base + 1316#64)
    (hrun : s4.status = .Running)
    (hx29 : s4.readReg64 .x29 = sp' + 512#64)
    (hx28 : s4.readReg64 .x28 = noneCap)
    (hx27 : s4.readReg64 .x27 = 0x8000000000000002#64)
    (hx26 : s4.readReg64 .x26 = noneCap)
    (hx23 : s4.readReg64 .x23 = noneCap)
    (hx19 : s4.readReg64 .x19 = sret)
    (hx1 : s4.readReg64 .x1 = noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s4
      (memRegion sret 248 ∗
        ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ pksmErrE A [] sret .invalidProtobufEncoding ∗
          ((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ bkLen) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
          ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  dsimp only [noneCap] at hx28 hx26 hx23 hx1 ⊢
  refine SepWPp.mono_pre (sepConj_mono_left (plb_memRegion248_split16 sret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun ws8 => SepWPp.exists_pre fun ws0 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl5
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl5, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_invalidProtobufEncoding A [] sret
  unfold errTag speWord at herr
  change (sret ↦₆₄ 18446744073709551615#64) ∗
    ((sret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
    memRegion (sret + 16#64) 232 ⊢ _ at herr
  refine Entails.trans (Q := ((sret ↦₆₄ 18446744073709551615#64) ∗
      ((sret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
      memRegion (sret + 16#64) 232) ∗
      (((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
        ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left herr

abbrev preKey_entry_to_f90_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.preKey_entry_to_f90_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
