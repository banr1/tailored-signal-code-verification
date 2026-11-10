/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Loop-Decode Error Tail and Shared Epilogue

Proves the `LibsignalCodeRoLoaded`-preserving epilogue (`+0x504..+0x520 → ret`), the
`+0x47c..+0x500` loop-error deallocation chain, and the full `+0x460` loop-decode error tail
on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
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

@[local arm64_norm, local wp_norm]
private theorem etw_bv_add_neg_120 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 120) = sp' + 392#64 := by bv_omega
@[local arm64_norm, local wp_norm]
private theorem etw_bv_add_neg_144 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 144) = sp' + 368#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

private theorem etw_stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) preKeyTryFromSubStack ∗
      memRegion (sp - 608#64) 296 ∗
      memRegion (sp - 608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

/-! ## 1. Shared Epilogue (`+0x504 .. +0x520` → `s0.readReg64 .x30`) -/

theorem epilogue_504_placed_w_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 s : State} {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        R ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        (Pf ⊢ R ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hsp0 : s0.spAligned = true := by
    rw [State.spAligned, hsp_eq, beq_iff_eq] at hsp
    rw [State.spAligned, beq_iff_eq]
    generalize s0.sp = sp0 at hsp ⊢
    bv_bits
  unfold preKeyCalleeSavedAt
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, hcl1, by simp [htr, arm64_norm], ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · have hstk := etw_stackAt_preKeyTryFrom_unsplit s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    apply entails_of_eq; ac_rfl

theorem epilogue_504_err_placed_w_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 s : State}
    (fn : List (BitVec 8)) (e : SignalProtocolError)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A fn x.ret e ∗ anyHeap) ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        (Pf ⊢ (pksmErrE A fn x.ret e ∗ anyHeap) ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) :=
  epilogue_504_placed_w_wpX hst hpc hrun

/-! ## 2. Loop-Decode Error Deallocation Chain (`+0x47c .. +0x500 → +0x504`) -/

set_option maxHeartbeats 800000 in
theorem cleanup_4f4_drop_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State} {sp' sret x24 w0 w1 : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1268#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hstack := stackAt_skipFieldStackW_dropDecodeError sp'
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 4) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded x24 hDropErr
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 1276#64) (by simp [arm64_norm])
    (T := decodeErrorAt A x24 ∗ A.pool ∗ stackAt s.sp Prost.dropDecodeErrorStackX)
    (φ := x24 = x24)
    (by simp [Prost.dropDecodeErrorSpecX, arm64_norm])
    rfl (by rw [hstack, hsp_eq]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [Prost.dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, hx27_cs, _⟩
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = sret := by simp [hx19_cs, hx19, arm64_norm]
  have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := by
    simp [hx27_cs, hx27, arm64_norm]
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
  refine ⟨PreKeyPostState.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, errTag, arm64_norm]; ac_rfl

set_option maxHeartbeats 800000 in
theorem cleanup_4cc_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State} {sp' sret x24 w0 w1 msgCap msgPtr : BitVec 64} (msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1228#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    change SepWPp _ _ _ (⌜msgCap = noneCap ∨ msgCap = 0#64⌝ ∗ _) _ _
    refine SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1268#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact cleanup_4f4_drop_placed_wpX hDropErr
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm]) (by simp [hx27, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
      A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (msgPtr, msgCap.toNat, 1) hdeallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1252#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk msgCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, _, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_cs, hx27, arm64_norm]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1268#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
    refine SepWPp.mono_pre (P' := decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact cleanup_4f4_drop_placed_wpX hDropErr
      (PreKeyPostState.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm]) (by simp [hx27_2, arm64_norm])

set_option maxHeartbeats 800000 in
theorem cleanup_4b4_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State} {sp' sret x24 w0 w1 ikCap ikPtr msgCap msgPtr : BitVec 64} (ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1204#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    change SepWPp _ _ _ (⌜ikCap = noneCap ∨ ikCap = 0#64⌝ ∗ _) _ _
    refine SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1228#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (cleanup_4cc_placed_wpX hdeallocX hDropErr msgAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
        (by simp [hx27, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; ac_rfl
  | true =>
    change SepWPp _ _ _ ((⌜0 < ikCap.toNat ∧ ikCap.toNat < 2 ^ 63 ∧ ikPtr ≠ 0#64⌝ ∗
      A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ikCap.toNat, 1) hdeallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1228#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk ikCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
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
      (cleanup_4cc_placed_wpX hdeallocX hDropErr msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx26_2 hx21_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem cleanup_4a4_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State} {sp' sret x24 w0 w1 bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1188#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    change SepWPp _ _ _ (⌜bkCap = noneCap ∨ bkCap = 0#64⌝ ∗ _) _ _
    refine SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1204#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact cleanup_4b4_placed_wpX hdeallocX hDropErr ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
      A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (bkPtr, bkCap.toNat, 1) hdeallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1204#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := s.readReg64 (Reg.gpr 0#5) = bkPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = bkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk bkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
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
    exact cleanup_4b4_placed_wpX hdeallocX hDropErr ikAct msgAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 hx19_2 hx24_2 hx27_2 hx23_2 hx26_2 hx21_2

set_option maxHeartbeats 800000 in
theorem cleanup_47c_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State}
    {sp' sret x24 w0 w1 kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyberAct bkAct ikAct msgAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1148#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret) (hx24 : s.readReg64 .x24 = x24)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64)
    (hx28 : s.readReg64 .x28 = kyberCap) (hx25 : s.readReg64 .x25 = kyberPtr)
    (hx0 : s.readReg64 .x0 = bkPtr) (hx1 : s.readReg64 .x1 = bkCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) (hx21 : s.readReg64 .x21 = msgPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A kyberCap kyberPtr kyberAct ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyberAct with
  | false =>
    change SepWPp _ _ _ (⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ ∗ _) _ _
    refine SepWPp.pure_pre fun hcap => ?_
    have hslt := slt_one_of_false_cap hcap
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1188#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact cleanup_4a4_placed_wpX hdeallocX hDropErr bkAct ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]) (by simp [hx21, arm64_norm])
  | true =>
    change SepWPp _ _ _ ((⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
      A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) ∗ _) _ _
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    have hslt := cap_slt_one_of_pos hpos hlt
    have hstack := stackAt_skipFieldStackX_ext sp'
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (kyberPtr, kyberCap.toNat, 1) hdeallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1180#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := kyberPtr = kyberPtr ∧ kyberCap.toNat = kyberCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk kyberCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, _, hx26_cs, hx27_cs, _⟩
    have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = sret := by simp [hx19_cs, hx19, arm64_norm]
    have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = bkPtr := by simp [hx20_cs, arm64_norm]
    have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = msgPtr := by simp [hx21_cs, hx21, arm64_norm]
    have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = bkCap := by simp [hx22_cs, arm64_norm]
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = ikCap := by simp [hx23_cs, hx23, arm64_norm]
    have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 (Reg.gpr 26#5) = msgCap := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := by simp [hx27_cs, hx27, arm64_norm]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1188#64) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
    refine SepWPp.mono_pre (P' := deallocSlot A bkCap bkPtr bkAct ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗
        decodeErrorAt A x24 ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact cleanup_4a4_placed_wpX hdeallocX hDropErr bkAct ikAct msgAct
      (PreKeyPostState.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm])
      (by simp [hx27_2, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hx23_2, arm64_norm]) (by simp [hx26_2, arm64_norm]) (by simp [hx21_2, arm64_norm])

/-! ## 3. Full Loop-Decode Error Tail (`+0x460 → +0x504` and `+0x460 → ret`) -/

set_option maxHeartbeats 1200000 in
theorem preKey_loopErr_460_to_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {s0 s : State} {sp' sret len ptr0 x24 : BitVec 64} {vb : BitVec 8}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (wirePreKeyOf A (sp' + 312#64) mErr ∗
        decodeErrorAt A x24 ∗ memRegion sp' 296 ∗ memRegion sret 248 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 296 ∗ memRegion (sp' + 312#64) 128 ∗
          (pksmErrE A [] sret .invalidProtobufEncoding ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx29 : s.readReg64 .x29 = sp' + 512#64 := hregs.x29
  have hx19 : s.readReg64 .x19 = sret := hregs.x19
  have hx27 : s.readReg64 .x27 = 0x8000000000000002#64 := hregs.x27
  have hx24_beq : (x24 == 0#64) = false := beq_eq_false_iff_ne.mpr hx24_ne
  unfold wirePreKeyOf; simp only [sepExists_sepConj_left]
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
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (memRegion248_split16 sret))))) ?_
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
  rw [hvh1, hvh2, hvh3, hvh4]; simp only [sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1148#64) ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
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
    (by dsimp only [F_hdr]; apply entails_of_eq; rw [hvh1, hvh2, hvh3, hvh4]; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (cleanup_47c_placed_wpX hdeallocX hDropErr kyberAct bkAct ikAct msgAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
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
    have hc := errCells_invalidProtobufEncoding A [] sret
    exact Entails.trans hc
      (Entails.trans (Entails.of_eq (sepConj_emp _).symm) (sepConj_mono_right (entails_anyHeap emp)))
  dsimp only [F_hdr]
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono hm296 (sepConj_mono hm128
        (sepConj_mono herr (Entails.refl (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))))
      (by apply entails_of_eq; ac_rfl))
  apply entails_of_eq; ac_rfl

theorem preKey_loopErr_460_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdeallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack A extHookStack)))
    (hDropErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.dropDecodeErrorSpecX A)))
    {x : RunCompose.PksmGhost} {s0 s : State} {vb : BitVec 8} {x24 : BitVec 64}
    (hst : PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoPreKeySignalMessage) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) mErr ∗
        decodeErrorAt A x24 ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        (Pf ⊢ (pksmErrE A [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
          (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
          stackAt s0.sp preKeyTryFromStack))
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  have hsub := stackAt_preKeyTryFromSubStack_skipField sp'
  set F_epi := memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
    memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 440#64) 8 ∗
    memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0 ∗
    (x.ptr ↦ₛ x.bytes) ∗ lsLogOff
  refine SepWPp.mono_pre (P' :=
      (wirePreKeyOf A (sp' + 312#64) mErr ∗ decodeErrorAt A x24 ∗
        memRegion sp' 296 ∗ memRegion x.ret 248 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗ F_epi)
    (by dsimp only [F_epi]; rw [hsub]; apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (preKey_loopErr_460_to_504_placed_wpE hdeallocX hDropErr hst hpc hrun hx24 hx24_ne mErr) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
  refine SepWPp.mono_pre (P' :=
      stackAt sp' preKeyTryFromSubStack ∗ memRegion sp' 296 ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        preKeyCalleeSavedAt sp' s0 ∗
        (pksmErrE A [] x.ret .invalidProtobufEncoding ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
    (by dsimp only [F_epi]; rw [hsub, ← memRegion152_repack_16_128_8 sp']; apply entails_of_eq; ac_rfl) ?_
  exact epilogue_504_err_placed_w_wpE [] .invalidProtobufEncoding hst1 hpc1 hrun1

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
