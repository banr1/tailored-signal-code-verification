/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Prologue
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridgePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedA
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Prologue and Early-Error Branches (`+0x000..+0x0f4`)

Proves the empty-slice, legacy/unrecognized-version, frame-initialization, empty-body, and
loop-entry prologue segments on `preKeyPlacedProg H`.
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

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

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

private theorem pl_spAligned_sub608_pl {s : State} (h : s.spAligned = true) :
    ((s.sp - 608#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned, beq_iff_eq] at h
  rw [beq_iff_eq]
  bv_bits

attribute [local simp, local arm64_norm, local wp_norm]
  cond_eq_subs1_false_w40 cond_eq_len1
  cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

/-- (``x.bytes = []`, `x1 = 0`, `[LibsignalPlacement]``): `cbz x1, +0x04c` at `+0x024` branches to
`+0x04c..+0x05c`, writing `Err(CiphertextMessageTooShort(0))` and jumping to `+0x504` (`1284`). -/
theorem prologue_nil_to_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State}
    (_hnil : x.bytes = [])
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx1 : s0.readReg64 .x1 = 0#64) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗
          pksmErrE A [] x.ret (.ciphertextMessageTooShort 0) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion248_split_8_8_8 x.ret)
      (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun ws16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨by simp_all [arm64_norm], ?_, hcl1, by simp_all [arm64_norm]⟩, ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608_pl hsp
  · unfold preKeyCalleeSavedAt
    simp only [bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    have herr := errCells_tooShort A [] x.ret 0
    unfold errTag speWord at herr
    change (x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
      ((x.ret + 16#64) ↦₆₄ 0#64) ∗
      memRegion (x.ret + 24#64) 224 ⊢ _ at herr
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left herr))
    apply entails_of_eq; ac_rfl

/-- When `x.bytes ≠ []` and `x.bytes.length < 2 ^ 32`, steps `+0x000..+0x024` (`10` insns, `40` bytes)
save callee-saved registers, take `cbz x1, +0x04c` as false, and stop at `+0x028` (`40`) before
`ldrb w22, [x0]`. -/
theorem prologue_entry_ne_nil_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 : State}
    (hne : x.bytes ≠ []) (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 40#64) s0
      (memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun s1 P1 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1 ∧
        s1.readReg64 .x0 = x.ptr ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        (P1 ⊢ preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  have hlen_ne : BitVec.ofNat 64 x.bytes.length ≠ 0#64 :=
    ofNat64_length_ne_zero_w40 hne hlt
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hlen_ne
  refine SepWPp.mono_pre (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨by simp_all [arm64_norm], ?_, hcl1, by simp_all [arm64_norm]⟩,
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608_pl hsp
  · unfold preKeyCalleeSavedAt
    simp only [bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    apply entails_of_eq; ac_rfl

/-- (``(vb >>> 4) < 3#8`, i.e. `vb < 0x30#8`, `[LibsignalPlacement]``): `+0x028..+0x048` → `+0x070..+0x07c` → `+0x504` (`1284`), writing
`pksmErrE A [] x.ret (.legacyCiphertextVersion (vb >>> 4))`. -/
theorem prologue_28_legacyVer_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    (hcons : x.bytes = vb :: body)
    (hlt3 : (vb >>> 4) < 3#8)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.legacyCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun bs16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl2
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_legacyVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 18446744073709551615#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- (``¬ (vb >>> 4) < 3#8` and `4#8 < (vb >>> 4)`, i.e. `0x4f#8 < vb`, `[LibsignalPlacement]``): `+0x028..+0x03c` → `+0x060..+0x07c` → `+0x504` (`1284`), writing
`pksmErrE A [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4))`. -/
theorem prologue_28_unrecognizedVer_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    (hcons : x.bytes = vb :: body)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hgt4 : 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun bs16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl2
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_unrecognizedVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 18446744073709551615#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- Case `¬ (vb >>> 4) < 3#8` and `¬ 4#8 < (vb >>> 4)` (`0x30#8 ≤ vb ≤ 0x4f#8`) under `[LibsignalPlacement]`:
`+0x028..+0x03c` → `+0x060..+0x064` → `+0x080` (`128`). -/
theorem prologue_28_validVer_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {s0 s1 : State}
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx1 : s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s1.readReg64 .x19 = x.ret)
    (hx29 : s1.readReg64 .x29 = s0.sp - 608#64 + 512#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 128#64) s1
      (x.ptr ↦₈ vb)
      (fun s2 P2 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s2 ∧
        s2.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        s2.readReg64 .x27 = 0x8000000000000002#64 ∧
        s2.readReg64 .x22 = vb.zeroExtend 64 ∧
        s2.readReg64 .x21 = x.ptr ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        (P2 ⊢ x.ptr ↦₈ vb))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl2
  exact ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx19, arm64_norm], by simp [hx1, arm64_norm], Entails.refl _⟩

/-- Steps `+0x080..+0x0b8` (`128` to `188`, `15` insns) under `[LibsignalPlacement]`:
initializes the slice cursor at `sp' + 296`, zeroes the 4 `Option<u32>` tags, sets the 4 `Vec<u8>`
capacities to `noneCap`, and writes `sp' + 296` to `sp' + 440`. -/
theorem prologue_80_init_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {sret sp' ptr len : BitVec 64} {vb : BitVec 8} {s0 s2 : State}
    (hst : PostEpilogueStatePlaced s0 sp' s2)
    (hpc : s2.pc = (blkPl_111).base + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = len) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 188#64) s2
      (memRegion (sp' + 296#64) 152)
      (fun s3 P3 =>
        PostEpilogueStatePlaced s0 sp' s3 ∧
        s3.pstate = subsPState64 len 1#64 ∧
        s3.readReg64 .x29 = sp' + 512#64 ∧
        s3.readReg64 .x27 = 0x8000000000000002#64 ∧
        s3.readReg64 .x22 = vb.zeroExtend 64 ∧
        s3.readReg64 .x21 = ptr ∧
        s3.readReg64 .x20 = len ∧
        s3.readReg64 .x19 = sret ∧
        s3.readReg64 .x8 = sp' + 296#64 ∧
        s3.readReg64 .x2 = len - 1#64 ∧
        (P3 ⊢ ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ (len - 1#64)) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine SepWPp.mono_pre (memRegion152_init_cells sp') ?_
  refine SepWPp.exists_pre fun w440 =>
    SepWPp.exists_pre fun w432 => SepWPp.exists_pre fun w424 =>
    SepWPp.exists_pre fun w416 => SepWPp.exists_pre fun w408 =>
    SepWPp.exists_pre fun w384 => SepWPp.exists_pre fun w360 =>
    SepWPp.exists_pre fun w336 => SepWPp.exists_pre fun w312 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl3
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl3, by simp [htr, arm64_norm]⟩, by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [arm64_norm], by simp [hx19, arm64_norm],
    by simp [arm64_norm], by simp [BitVec.sub_eq_add_neg, arm64_norm], ?_⟩
  unfold noneCap
  try simp only [arm64_norm]
  apply entails_of_eq; ac_rfl

abbrev prologue_to_c24_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.prologue_to_c24_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
