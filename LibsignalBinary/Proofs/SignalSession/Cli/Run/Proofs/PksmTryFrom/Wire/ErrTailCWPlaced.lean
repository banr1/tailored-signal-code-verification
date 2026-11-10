/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6ExitsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Pack, `IdentityKey`, and `SignalMessage` Error/Dealloc Tails

Proves the `+0x970..+0xa58` deallocation chains, Kyber `Box<[u8]>` cleanup (`+0x990..+0xa20`),
`+0xa68` OOM panic branch, and `+0x978` / `+0x9f0` exact-`pksmErrE` error entries on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 Arm64.Obj ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoGames CryptoGames.Ratchet
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
private abbrev SepWPp.panic := @Wire.SepWPp.panic
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

private theorem etcw_bv_add_sub_lit (x a b : BitVec 64) : x + a - b = x + (a - b) := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit etcw_bv_add_sub_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
attribute [local simp] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

theorem ErrTailQPlaced.frame_entails [LibsignalPlacement] {s0 sf : State} {sp' sret : BitVec 64}
    {F G H0 Pf : SepProp} (h : ErrTailQPlaced s0 sp' sret F sf Pf) (hent : F ∗ G ⊢ H0) :
    ErrTailQPlaced s0 sp' sret H0 sf (Pf ∗ G) :=
  ⟨h.1, h.2.1, Entails.trans (sepConj_mono_left h.2.2) hent⟩

/-! ## 1. Shared Dealloc Chain (`+0xa24 .. +0xa58` → `+0x80c` / `+0x504`) -/

theorem tail_a4c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State} {sp' sret bkCap bkPtr : BitVec 64}
    (bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2636#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
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
    refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact ⟨PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
      (by simp [htr, arm64_norm]), by simp [hx19, arm64_norm], Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A bkCap bkPtr true =
        (⌜0 < bkCap.toNat ∧ bkCap.toNat < 2 ^ 63 ∧ bkPtr ≠ 0#64⌝ ∗
          A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : bkCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_80c_placed_wpX hC
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) hpos hlt)
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_a38_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret ikCap ikPtr bkCap bkPtr : BitVec 64} (ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2616#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
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
      (mid := (blkPl_111).base + 2636#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_a4c_placed_wpX hC bkAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm]) hbk)
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
      (ret_pc := (blkPl_111).base + 2636#64) (by simp [arm64_norm])
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
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, _, _, _, _⟩
    refine SepWPp.mono_pre (P' := (deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_a4c_placed_wpX hC bkAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
          by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm]) hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_a28_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2600#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hpos : 0 < msgCap.toNat) (hlt : msgCap.toNat < 2 ^ 63)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (msgPtr, msgCap.toNat, 1) hC.deallocX
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 2616#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt s.sp extHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk msgCap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, _, _, _, _⟩
  refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (tail_a38_placed_wpX hC ikAct bkAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
        by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
      (by simp [hx23_cs, hx23, arm64_norm]) hik hbk)
    fun sf Pf h => h.frame_eq (by ac_rfl)

theorem tail_a24_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (msgAct ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2596#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
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
      (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_a38_placed_wpX hC ikAct bkAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a28_placed_wpX hC ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 2. Pack Ok Exit (`+0x970`) -/

theorem deallocChain_970_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64} (msgAct ikAct bkAct : Bool)
    {R : SepProp}
    (hst : PackOkStatePlaced s0 sp' sret ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2416#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A msgCap msgPtr msgAct ∗ deallocSlot A ikCap ikPtr ikAct ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx19, hx26, hx23⟩
  refine SepWPp.pure_pre fun ⟨hmsg, hik, hbk⟩ => ?_
  refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by apply entails_of_eq; ac_rfl) ?_
  cases msgAct with
  | false =>
    have hdealloc : deallocSlot A msgCap msgPtr false = ⌜msgCap = noneCap ∨ msgCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre fun hcap => ?_
    obtain rfl : msgCap = 0#64 := hcap.resolve_left hmsg
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre (P' := (deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    exact SepWPp.frame_tryFrom
      (tail_a38_placed_wpX hC ikAct bkAct
        (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx23, arm64_norm]) hik hbk)
      fun sf Pf h => h.frame_eq (by ac_rfl)
  | true =>
    have hdealloc : deallocSlot A msgCap msgPtr true =
        (⌜0 < msgCap.toNat ∧ msgCap.toNat < 2 ^ 63 ∧ msgPtr ≠ 0#64⌝ ∗
          A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : msgCap ≠ 0#64 := by rintro rfl; simp at hpos
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a28_placed_wpX hC ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hpos hlt hik hbk

/-! ## 3. Kyber-Box Free (`+0x990`, `+0xa0c`, `+0xa10` → `+0xa24`) -/

theorem tail_a10_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2576#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hkb : kbPtr ≠ 0#64)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases boxAct with
  | false =>
    have hbox : boxSlot A kbPtr kbLen false = ⌜kbPtr = 0#64 ∨ kbLen = 0#64⌝ := rfl
    rw [hbox]
    refine SepWPp.pure_pre fun hz => ?_
    obtain rfl : kbLen = 0#64 := hz.resolve_left hkb
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  | true =>
    have hbox : boxSlot A kbPtr kbLen true =
        (⌜0 < kbLen.toNat ∧ kbLen.toNat < 2 ^ 63 ∧ kbPtr ≠ 0#64⌝ ∗
          A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat) := rfl
    rw [hbox]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hne : kbLen ≠ 0#64 := by rintro rfl; simp at hpos
    have hstack := stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    refine call_noPanic_pk keepsFrozenInv_codeRoLoaded (kbPtr, kbLen.toNat, 1) hC.deallocX
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_111).base + 2596#64) (by simp [arm64_norm])
      (T := A.pool ∗ A.live kbPtr kbLen.toNat 1 ∗ memRegion kbPtr kbLen.toNat ∗
        stackAt s.sp extHookStack)
      (φ := kbPtr = kbPtr ∧ kbLen.toNat = kbLen.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        LayoutOk kbLen.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    rcases hcs2 with ⟨hx19_cs, _, _, _, hx23_cs, _, _, hx26_cs, _, _, _⟩
    refine SepWPp.mono_pre (P' := deallocSlot A msgCap msgPtr msgAct ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2,
        by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 (by simp [hx19_cs, hx19, arm64_norm])
      (by simp [hx26_cs, hx26, arm64_norm]) (by simp [hx23_cs, hx23, arm64_norm]) hmsg hik hbk

theorem tail_990_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2448#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  by_cases hz : kbPtr = 0#64
  · subst hz
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2576#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a10_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

theorem tail_a0c_placed_wpX [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2572#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = sret)
    (hx26 : s.readReg64 .x26 = msgCap) (hx23 : s.readReg64 .x23 = ikCap)
    (hx28 : s.readReg64 .x28 = kbPtr) (hx25 : s.readReg64 .x25 = kbLen)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  by_cases hz : kbPtr = 0#64
  · subst hz
    refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left (boxSlot_null_elim A kbLen boxAct))
      (entails_of_eq (emp_sepConj _))) ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2596#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a24_placed_wpX hC msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm]) hmsg hik hbk
  · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 2576#64) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
    exact tail_a10_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hz hmsg hik hbk

/-! ## 4. Clone Alloc-Fail Panic (`+0xa68`) -/

theorem pan_a68_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    (h_panic : H lsAllocHandleErrorSym = some Rust.panicked)
    {s0 s : State} {sp' ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : CloneAllocFailPlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2664#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ret s P Q (tryFromQp s0) := by
  rcases hst with ⟨_, _, hcl, hallocF, htr⟩
  have hpan : (preKeyPlacedProg H).externAt? ((blkPl_111).ρ lsAllocHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem).trans h_panic
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsAllocHandleErrorSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ => ?_
  refine SepWPp.panic (by simp [hrun, arm64_norm]) (by simpa [arm64_norm] using hpan)
    fun _ hm => allowPanic_panicked
      ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
        by simpa [Rust.panicked, arm64_norm] using htr⟩ hm

/-! ## 5. Kyber-Box Exact-Err Entries (`+0x978`, `+0x9f0`) -/

private theorem etcw_memRegion24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

private theorem etcw_memRegion248_words7 (r : BitVec 64) :
    memRegion r 248 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗ memRegion (r + 56#64) 192 := by
  rw [ProofLib.memRegion_split r 8 240 (by decide),
    ProofLib.memRegion_split (r + 8#64) 24 216 (by decide),
    ProofLib.memRegion_split (r + 8#64 + 24#64) 24 192 (by decide),
    ProofLib.memRegion_eight r,
    etcw_memRegion24_words3 (r + 8#64),
    etcw_memRegion24_words3 (r + 8#64 + 24#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem etcw_words4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) w2)
        (pointsTo64_entails_memRegion (a + 24#64) w3)))

private theorem etcw_words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      etcw_words4_entails_memRegion32 (a + 8#64) w1 w2 w3 w4)

private theorem etcw_ikErr_speDetached_intro {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (w2 w3 w4 w5 : BitVec 64) :
    SepProp.emp ⊢
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 w2 w3 w4 w5 e := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show SepProp.emp ⊢ ⌜speWord 7 = speWord 7⌝
    exact Entails.pure_right_only rfl (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 8 = speWord 8 ∧ (t.zeroExtend 64).truncate 8 = t⌝
    exact Entails.pure_right_only ⟨rfl, by bv_bits⟩ (Entails.refl _)
  · show SepProp.emp ⊢ ⌜speWord 9 = speWord 9 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n⌝
    exact Entails.pure_right_only ⟨rfl, rfl⟩ (Entails.refl _)

private theorem etcw_ikErr_speDetached_elim {A : RustAlloc} {fn : List (BitVec 8)}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (hik : PublicKey.deserialize ik = .error e) (d0 d1 d2 d3 d4 d5 : BitVec 64) :
    pksm0c_speDetached A fn d0 d1 d2 d3 d4 d5 e ⊢ SepProp.emp := by
  rcases deserialize_error_cases hik with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · show ⌜d0 = speWord 7⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 8 ∧ d1.truncate 8 = t⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _
  · show ⌜d0 = speWord 9 ∧ d1 = BitVec.ofNat 64 n⌝ ⊢ SepProp.emp
    exact Entails.pure_left_only fun _ => Entails.refl _

theorem e_978_copy48_placed_wpE [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : IdentErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = w0)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗ ((sp' + 160#64) ↦₆₄ w3) ∗
        ((sp' + 168#64) ↦₆₄ w4) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
        pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 352#64) 8 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx25, hx26, hx23, hx19⟩
  rw [etcw_memRegion248_words7 sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).base + 2448#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine SepWPp.mono_pre (P' := (boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ w0) ∗ ((sret + 16#64) ↦₆₄ w1) ∗
          ((sret + 24#64) ↦₆₄ w2) ∗ ((sret + 32#64) ↦₆₄ w3) ∗ ((sret + 40#64) ↦₆₄ w4) ∗
          ((sret + 48#64) ↦₆₄ w5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A fn w0 w1 w2 w3 w4 w5 e) ∗
        (((sp' + 144#64) ↦₆₄ w1) ∗ ((sp' + 152#64) ↦₆₄ w2) ∗
          ((sp' + 160#64) ↦₆₄ w3) ∗ ((sp' + 168#64) ↦₆₄ w4)) ∗
        ((sp' + 352#64) ↦₆₄ w5)))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  have hm32 := etcw_words4_entails_memRegion32 (sp' + 144#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm32
  exact SepWPp.frame_tryFrom
    (tail_990_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => h.frame_entails (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A fn sret w0 w1 w2 w3 w4 w5 e)
        (sepConj_mono hm32
          (pointsTo64_entails_memRegion (sp' + 352#64) w5))))
      (by apply entails_of_eq; ac_rfl))

private theorem etcw_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Q' Qp : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, hQ, hv⟩ | hpan⟩
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ, hv⟩⟩
  · exact ⟨sf, hs, Or.inr hpan⟩

theorem e_978_placed_wpE [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ik : List (BitVec 8)} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hik_err : PublicKey.deserialize ik = .error e)
    (hst : IdentErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2424#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = (ikErrWords e).1)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ memRegion (sp' + 152#64) 24 ∗
        speAt A fn (sp' + 312#64) e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 312#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rw [etcw_memRegion24_words3 (sp' + 152#64)]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pksm0c_speAt_detach A fn (sp' + 312#64) e)))) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun d0 => SepWPp.exists_pre fun d1 => SepWPp.exists_pre fun d2 =>
    SepWPp.exists_pre fun d3 => SepWPp.exists_pre fun d4 => SepWPp.exists_pre fun w5 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u2 => SepWPp.exists_pre fun u1 => ?_
  have hdet :
      pksm0c_speDetached A fn d0 d1 d2 d3 d4 w5 e ⊢
        pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e :=
    Entails.trans (etcw_ikErr_speDetached_elim hik_err d0 d1 d2 d3 d4 w5)
      (etcw_ikErr_speDetached_intro hik_err u1 u2 u3 w5)
  have hm40 := etcw_words5_entails_memRegion40 (sp' + 312#64) d0 d1 d2 d3 d4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm40
  refine SepWPp.mono_pre
    (P' := ((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
      ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
      pksm0c_speDetached A fn (ikErrWords e).1 (ikErrWords e).2 u1 u2 u3 w5 e ∗
      memRegion sret 248 ∗
      boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ (memRegion (sp' + 312#64) 40 ∗ R))
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ d0) ∗ ((sp' + 320#64) ↦₆₄ d1) ∗ ((sp' + 328#64) ↦₆₄ d2) ∗
            ((sp' + 336#64) ↦₆₄ d3) ∗ ((sp' + 344#64) ↦₆₄ d4)) ∗
          pksm0c_speDetached A fn d0 d1 d2 d3 d4 w5 e ∗
          (((sp' + 144#64) ↦₆₄ (ikErrWords e).2) ∗ ((sp' + 152#64) ↦₆₄ u1) ∗
            ((sp' + 160#64) ↦₆₄ u2) ∗ ((sp' + 168#64) ↦₆₄ u3) ∗ ((sp' + 352#64) ↦₆₄ w5) ∗
            memRegion sret 248 ∗
            boxSlot A kbPtr kbLen boxAct ∗
            deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hm40 (sepConj_mono_left hdet)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine etcw_sepWPp_mono_post
    (e_978_copy48_placed_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hx8 hmsg hik hbk)
    fun _ _ h => etb_errTailQPlaced_mono h ?_
  have h48 : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48]
  apply entails_of_eq; ac_rfl

theorem e_9f0_placed_wpE [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hst : SigMsgErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (speAt A fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, _, hx28, hx25, hx26, hx23, hx19⟩
  rw [etcw_memRegion248_words7 sret]
  refine SepWPp.mono_pre (sepConj_mono_left (pksm0c_speAt_detach A fn (sp' + 176#64) e)) ?_
  simp only [pksm0c_speWords6At, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ => SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun _ =>
    SepWPp.exists_pre fun u0 => SepWPp.exists_pre fun u1 => SepWPp.exists_pre fun u2 =>
    SepWPp.exists_pre fun u3 => SepWPp.exists_pre fun u4 => SepWPp.exists_pre fun u5 => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).base + 2572#64) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have hm48 := pksm0c_words6_entails_memRegion48 (sp' + 176#64) u0 u1 u2 u3 u4 u5
  unfold pksm0c_speWords6At at hm48
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm48
  refine SepWPp.mono_pre (P' := (boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) ∗
      (((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ u0) ∗ ((sret + 16#64) ↦₆₄ u1) ∗
          ((sret + 24#64) ↦₆₄ u2) ∗ ((sret + 32#64) ↦₆₄ u3) ∗ ((sret + 40#64) ↦₆₄ u4) ∗
          ((sret + 48#64) ↦₆₄ u5) ∗ memRegion (sret + 56#64) 192 ∗
          pksm0c_speDetached A fn u0 u1 u2 u3 u4 u5 e) ∗
        (((sp' + 176#64) ↦₆₄ u0) ∗ ((sp' + 184#64) ↦₆₄ u1) ∗ ((sp' + 192#64) ↦₆₄ u2) ∗
          ((sp' + 200#64) ↦₆₄ u3) ∗ ((sp' + 208#64) ↦₆₄ u4) ∗ ((sp' + 216#64) ↦₆₄ u5))))
    (by apply entails_of_eq; simp only [errTag, arm64_norm]; ac_rfl) ?_
  exact SepWPp.frame_tryFrom
    (tail_a0c_placed_wpX hC boxAct msgAct ikAct bkAct
      (PreKeyPostState.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hx19, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) hmsg hik hbk)
    fun _ _ h => h.frame_entails (Entails.trans
      (sepConj_mono_right (sepConj_mono
        (errCopy48_entails_pksmErrE A fn sret u0 u1 u2 u3 u4 u5 e) hm48))
      (by apply entails_of_eq; ac_rfl))

theorem e_9f0_words2_placed_wpE [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H) (fn : List (BitVec 8)) {s0 s : State}
    {sp' sret kbPtr kbLen msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    {ew0 ew1 ew2 ew3 ew4 ew5 : BitVec 64} {e : SignalProtocolError}
    (boxAct msgAct ikAct bkAct : Bool) {R : SepProp}
    (hpack : ∀ b : BitVec 64,
      (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢ speAt A fn b e)
    (hst : SigMsgErrStatePlaced s0 sp' sret kbPtr kbLen ikCap msgCap s)
    (hpc : s.pc = (blkPl_111).base + 2544#64)
    (hrun : s.status = .Running)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion sret 248 ∗
        boxSlot A kbPtr kbLen boxAct ∗
        deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
      (ErrTailQPlaced s0 sp' sret (pksmErrE A fn sret e ∗ memRegion (sp' + 176#64) 48 ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
      (tryFromQp s0) := by
  have hm32 : ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      memRegion (sp' + 192#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      etcw_words4_entails_memRegion32 (sp' + 192#64) ew2 ew3 ew4 ew5
  have hspe : ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
      ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
      speAt A fn (sp' + 176#64) e := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hm32)) ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hpack (sp' + 176#64)
  refine SepWPp.mono_pre
    (P' := speAt A fn (sp' + 176#64) e ∗ memRegion sret 248 ∗
      boxSlot A kbPtr kbLen boxAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)
    (by
      refine Entails.trans
        (Q := (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
            ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
            ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5)) ∗
          (memRegion sret 248 ∗
            boxSlot A kbPtr kbLen boxAct ∗
            deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            deallocSlot A bkCap bkPtr bkAct ∗
            ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R))
        (by apply entails_of_eq; ac_rfl) ?_
      exact sepConj_mono_left hspe) ?_
  exact e_9f0_placed_wpE hC fn boxAct msgAct ikAct bkAct hst hpc hrun hmsg hik hbk

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
