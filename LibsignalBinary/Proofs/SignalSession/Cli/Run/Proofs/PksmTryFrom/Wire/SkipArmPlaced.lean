/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArm
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Unknown-Tag `skip_field` Arm

Proves `skipFieldErrPK_364_placed_wpX` and `mergeSkipField_placed_cpsPK`
(`+0x2d8..+0x2e8` and error stub `+0x364..+0x368`) on `preKeyPlacedProg H`.
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
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs PreKeyLoopRegs.of_calleeSaved SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev call_tryFrom_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom_pk

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_72 bv_add_neg_216

theorem skipFieldErrPK_364_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr : BitVec 64} {bs : List (BitVec 8)} {n : Nat} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x364#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx0_ne : s.readReg64 .x0 ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        decodeErrorAtStackLen A (s.readReg64 .x0) n ∗ wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs none) (tryFromQp s0) := by
  change s.pc = (blkPl_111).base + 868#64 at hpc
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
    by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcl1, by simpa [arm64_norm] using htr⟩, ?_⟩
  simp only [arm64_norm]
  exact preKeyLoopExitMem_err_intro A sp' ptr bs (s.readReg64 (Reg.gpr 0#5)) hx0_ne n mErr

set_option maxHeartbeats 800000 in
theorem mergeSkipField_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.skipFieldSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x2d8#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  change s.pc = (blkPl_111).base + 728#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 1) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, tag, 100, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hskip
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 740#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ sliceCursorAt (sp' + 296#64) ptr bs ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 2 ^ 32 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 2 ^ 32 ∧ bs.length < 2 ^ 63)
    (by simp only [Prost.skipFieldSpecX, hsp_eq, h0, h1, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl,
      by decide, by omega⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [Prost.skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 228#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont rest _ hs (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3 (by simpa [arm64_norm] using htr2.trans htr))
    apply entails_of_eq; simp only [hsp_eq, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hs; subst hres; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [arm64_norm]
    refine Entails.trans ?_
      (preKeyLoopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 m)
    apply entails_of_eq; simp only [hsp_eq, arm64_norm]; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
