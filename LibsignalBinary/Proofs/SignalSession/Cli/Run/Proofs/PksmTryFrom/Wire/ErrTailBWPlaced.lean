/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Post-Loop Deallocation Chains and Error Entry Blocks

Proves the post-loop deallocation chains (`+0x604..+0x668`, `+0x7b8..+0x814` → `+0x504`) and
error entry blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8`) on `preKeyPlacedProg H`.
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
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
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

/-! ## 1. Common Postcondition (`ErrTailQPlaced`) -/

/-- Postcondition of every dealloc-chain leaf under `[LibsignalPlacement]`: at `+0x504`
(`1284`) with `PostEpilogueStatePlaced`, `x19 = sret`, and the remaining frame `F`. -/
abbrev ErrTailQPlaced [LibsignalPlacement] (s0 : State) (sp' sret : BitVec 64) (F : SepProp) :
    State → SepProp → Prop :=
  fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧ sf.readReg64 .x19 = sret ∧ (Pf ⊢ F)

theorem ErrTailQPlaced.frame_eq [LibsignalPlacement] {s0 sf : State} {sp' sret : BitVec 64}
    {F G H0 Pf : SepProp} (h : ErrTailQPlaced s0 sp' sret F sf Pf) (heq : F ∗ G = H0) :
    ErrTailQPlaced s0 sp' sret H0 sf (Pf ∗ G) :=
  ⟨h.1, h.2.1, heq ▸ sepConj_mono_left h.2.2⟩

theorem etb_errTailQPlaced_mono [LibsignalPlacement] {s0 sf : State} {sp' sret : BitVec 64}
    {F F' Pf : SepProp} (h : ErrTailQPlaced s0 sp' sret F sf Pf) (hF : F ⊢ F') :
    ErrTailQPlaced s0 sp' sret F' sf Pf :=
  ⟨h.1, h.2.1, Entails.trans h.2.2 hF⟩

/-! ## 2. Shared Dealloc Chain (`+0x7b8 .. +0x814` → `+0x504`) -/

theorem tail_80c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State} {sp' sret ptr cap : BitVec 64} {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2060#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (ptr, cap.toNat, 1) hC.deallocX
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 2068#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk cap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  have hx19_2 : s2.readReg64 .x19 = sret := by simp [hcs2.1, hx19, arm64_norm]
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
  refine ⟨PreKeyPostState.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), by simp [hx19_2, arm64_norm], ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl

theorem tail_7f8_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State} {sp' sret kyCap kyPtr : BitVec 64}
    (kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2040#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
      exact ⟨PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_80c_placed_wpX hC
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt

theorem tail_7e4_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret bkCap bkPtr kyCap kyPtr : BitVec 64} (bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2020#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2040#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_7f8_placed_wpX hC kyAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
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
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (bkPtr, bkCap.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 2040#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := bkPtr = bkPtr ∧ bkCap.toNat = bkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk bkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, _, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_7f8_placed_wpX hC kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_7d0_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64} (ikAct bkAct kyAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2000#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : ikCap = 0#64 := hcap.resolve_left hik
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2020#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_7e4_placed_wpX hC bkAct kyAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
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
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ikCap.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 2020#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk ikCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
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
      (tail_7e4_placed_wpX hC bkAct kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_7b8_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1976#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = errTag) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2000#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sp' + 96#64) ↦₆₄ msgPtr)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_7d0_placed_wpX hC ikAct bkAct kyAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
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
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (msgPtr, msgCap.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 2000#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk msgCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
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
      (tail_7d0_placed_wpX hC ikAct bkAct kyAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx23_cs, hx23, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-! ## 3. Presence-Error Dealloc Chain (`+0x604 .. +0x668` → `+0x80c` / `+0x504`) -/

theorem tail_654_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State} {sp' sret msgCap msgPtr : BitVec 64}
    (msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1620#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
      exact ⟨PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗ ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_80c_placed_wpX hC
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_64c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret ptr cap msgCap msgPtr : BitVec 64} (msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1612#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (ptr, cap.toNat, 1) hC.deallocX
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 1620#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk cap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, hx26_cs, _, _, _⟩
  refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  exact tail_654_placed_wpX hC msgAct
    ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
    hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm]) (by simp [hx26_cs, hx26, arm64_norm])

theorem tail_638_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret kyCap kyPtr msgCap msgPtr : BitVec 64} (kyAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1592#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 1620#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
      exact tail_654_placed_wpX hC msgAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
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
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 1612#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_64c_placed_wpX hC msgAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt

theorem tail_604_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret ikCap ikPtr msgCap msgPtr : BitVec 64} (ikAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1540#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases ikAct with
  | false =>
    have hdealloc : deallocSlot A ikCap ikPtr false = ⌜ikCap = noneCap ∨ ikCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 1620#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr))
        (by apply entails_of_eq; ac_rfl) ?_
      exact SepWPp.frame_tryFrom
        (tail_654_placed_wpX hC msgAct
          (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
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
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 1612#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗ ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_64c_placed_wpX hC msgAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx26, arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

/-! ## 4. Word-Level Entry Blocks (`+0x5e0`, `+0x61c`, `+0x66c`, `+0x678`, `+0x7a8`) -/

theorem entry_678_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 w1 x27v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1656#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx26 : s.readReg64 .x26 = msgCap)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).base + 1976#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret + 8#64) ↦₆₄ x27v))
    (by apply entails_of_eq; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (tail_7b8_placed_wpX hC msgAct ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

theorem entry_66c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 w1 x27v ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1644#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).base + 2000#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (tail_7d0_placed_wpX hC ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

theorem entry_5e0_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 w1 x27v kyCap kyPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    (kyAct ikAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1504#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx23 : s.readReg64 .x23 = ikCap) (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A kyCap kyPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases kyAct with
  | false =>
    have hdealloc : deallocSlot A kyCap kyPtr false = ⌜kyCap = noneCap ∨ kyCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    rcases hcap with rfl | rfl
    all_goals
      refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
        (mid := (blkPl_111).base + 1540#64) ?_
      wp_steps
      refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
      refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A msgCap msgPtr msgAct ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
          ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
        (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
      exact SepWPp.frame_tryFrom
        (tail_604_placed_wpX hC ikAct msgAct
          (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
            (by simp [htr, arm64_norm]))
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm]))
        fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A kyCap kyPtr true =
        (⌜0 < kyCap.toNat ∧ kyCap.toNat < 2 ^ 63 ∧ kyPtr ≠ 0#64⌝ ∗
          A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (kyPtr, kyCap.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1540#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kyPtr kyCap.toNat 1 ∗ memRegion kyPtr kyCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := kyPtr = kyPtr ∧ kyCap.toNat = kyCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk kyCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ deallocSlot A msgCap msgPtr msgAct ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_604_placed_wpX hC ikAct msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx23_cs, hx23, arm64_norm]) (by simp [hx26_cs, hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem entry_61c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 w1 x27v bkCap bkPtr kyCap kyPtr msgCap msgPtr : BitVec 64}
    (bkAct kyAct msgAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1564#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases bkAct with
  | false =>
    have hdealloc : deallocSlot A bkCap bkPtr false = ⌜bkCap = noneCap ∨ bkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : bkCap = 0#64 := hcap.resolve_left hbk
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 1592#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ 0#64)))
      (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_638_placed_wpX hC kyAct msgAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (bkPtr, bkCap.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 1592#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        stackAt s.sp extHookStack)
      (φ := bkPtr = bkPtr ∧ bkCap.toNat = bkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk bkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, hx25_cs, hx26_cs, _, hx28_cs, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A kyCap kyPtr kyAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ A.pool ∗
        stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x27v) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, errTag, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_638_placed_wpX hC kyAct msgAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
        (by simp [hx28_cs, hx28, arm64_norm]) (by simp [hx25_cs, hx25, arm64_norm])
        (by simp [hx26_cs, hx26, arm64_norm]))
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem entry_7a8_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret w0 w1 w2 x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
        ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).base + 1976#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine SepWPp.mono_pre (P' := (deallocSlot A msgCap msgPtr msgAct ∗ (sret ↦₆₄ w0) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret + 8#64) ↦₆₄ x9v) ∗ ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64)))))
    (by apply entails_of_eq; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (tail_7b8_placed_wpX hC msgAct ikAct bkAct kyAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [errTag, arm64_norm]) (by simp [hx26, arm64_norm])
      (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

private theorem etbw_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

private theorem etbw_memRegion248_words2 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    sepExists_sepConj_left]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

private theorem etbw_memRegion248_words3 (sret : BitVec 64) :
    memRegion sret 248 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
          memRegion (sret + 24#64) 224 := by
  rw [etbw_memRegion248_words2 sret, show (232 : Nat) = 8 + 224 by decide,
    Prost.memRegion_split (sret + 16#64) 8 224 (by decide),
    ProofLib.memRegion_eight (sret + 16#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]

theorem entry_7a8_placed_wpE [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret x8v x9v x10v msgCap msgPtr ikCap ikPtr bkCap bkPtr kyCap kyPtr : BitVec 64}
    {e : SignalProtocolError} (msgAct ikAct bkAct kyAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1960#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = x9v) (hx10 : s.readReg64 .x10 = x10v)
    (hw : speWordsOf e x9v x8v x10v)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kyCap) (hx25 : s.readReg64 .x25 = kyPtr)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (memRegion sret 248 ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (pksmErrE A [] sret e ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etbw_memRegion248_words3 sret]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w2 => ?_
  refine SepWPp.mono_pre
    (P' := (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ ((sret + 16#64) ↦₆₄ w2) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyCap kyPtr kyAct ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      (memRegion (sret + 24#64) 224 ∗ R))
    (by apply entails_of_eq; ac_rfl) ?_
  refine etbw_sepWPp_mono_post
    (entry_7a8_placed_wpX hC msgAct ikAct bkAct kyAct hst hpc hrun hx19 hx8 hx9 hx10 hx26 hx23 hx28
      hx25 hmsg hik hbk)
    fun _ _ h => etb_errTailQPlaced_mono h ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ x9v) ∗
        ((sret + 16#64) ↦₆₄ (x8v ||| (x10v &&& 255#64))) ∗ memRegion (sret + 24#64) 224) ∗
      (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_left (etb_speWordsOf_entails_pksmErrE A [] sret x9v x8v x10v e hw))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
