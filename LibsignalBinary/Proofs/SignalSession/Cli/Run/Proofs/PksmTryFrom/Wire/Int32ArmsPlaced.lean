/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32Arms
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` `int32::merge` Field Arms

Proves the four `int32::merge` field arms (`pre_key_id`, `registration_id`, `signed_pre_key_id`,
`kyber_pre_key_id`) and `int32ArmPK_placed_cps` on `preKeyPlacedProg H`.
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
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs PreKeyLoopRegs.of_calleeSaved SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev call_tryFrom_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom_pk

@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_104 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 104) = sp' + 408#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_100 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 100) = sp' + 412#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_96 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 96) = sp' + 416#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_92 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 92) = sp' + 420#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_88 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 88) = sp' + 424#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_84 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 84) = sp' + 428#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_80 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 80) = sp' + 432#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_76 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 76) = sp' + 436#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_72 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_64 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ia_bv_add_neg_56 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 56) = sp' + 456#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero

/-! ## Tag 1 (`pre_key_id`, `+0x260..+0x27c` / `+0x3f0..+0x410`, `off = 0x68`) -/

set_option maxHeartbeats 800000 in
theorem initOptU32_preKeyId_placed_cpsX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x260#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (blkPl_111).base + 0x26c#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (optU32At (sp' + 416#64) (some v0) ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optU32At (sp' + 416#64) o ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 608#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 620#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 416#64 + 4#64 = sp' + 420#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 616#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 416#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 620#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl2 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 416#64) ↦₆₄ 1#64) =
        ((sp' + 416#64) ↦₃₂ 1#32) ∗ ((sp' + 420#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 416#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergePreKeyId_placed_cpsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x260#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with preKeyId := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_preKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 416#64) m.preKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest1 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_preKeyId_placed_cpsX (s0 := s0) hpc hrun hregs hsp hcl htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 620#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 420#64) v0))) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 420#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hint32
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 632#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 420#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 420#64 = sp' + 420#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_preKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64),
      ProofLib.memRegion_four (sp' + 420#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with preKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    rw [← wirePreKeyOf_update_preKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## Tag 5 (`registration_id`, `+0x280..+0x29c` / `+0x414..+0x434`, `off = 0x60`) -/

set_option maxHeartbeats 800000 in
theorem initOptU32_regId_placed_cpsX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x280#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (blkPl_111).base + 0x28c#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (optU32At (sp' + 408#64) (some v0) ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optU32At (sp' + 408#64) o ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 640#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 652#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 408#64 + 4#64 = sp' + 412#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 648#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 408#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 652#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl2 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 408#64) ↦₆₄ 1#64) =
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 408#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeRegId_placed_cpsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x280#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with registrationId := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_regId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 408#64) m.registrationId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest5 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_regId_placed_cpsX (s0 := s0) hpc hrun hregs hsp hcl htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 652#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 412#64) v0))) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 412#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hint32
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 664#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 412#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 412#64 = sp' + 412#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_regId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64),
      ProofLib.memRegion_four (sp' + 412#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with registrationId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    rw [← wirePreKeyOf_update_regId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## Tag 6 (`signed_pre_key_id`, `+0x1d0..+0x1ec` / `+0x384..+0x3a4`, `off = 0x70`) -/

set_option maxHeartbeats 800000 in
theorem initOptU32_signedPreKeyId_placed_cpsX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x1d0#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (blkPl_111).base + 0x1dc#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (optU32At (sp' + 424#64) (some v0) ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optU32At (sp' + 424#64) o ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 464#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 476#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 424#64 + 4#64 = sp' + 428#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 472#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 424#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 476#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl2 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 424#64) ↦₆₄ 1#64) =
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 424#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeSignedPreKeyId_placed_cpsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x1d0#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with signedPreKeyId := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_signedPreKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 424#64) m.signedPreKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest6 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_signedPreKeyId_placed_cpsX (s0 := s0) hpc hrun hregs hsp hcl htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 476#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 428#64) v0))) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 428#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hint32
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 488#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 428#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 428#64 = sp' + 428#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_signedPreKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64),
      ProofLib.memRegion_four (sp' + 428#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with signedPreKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    rw [← wirePreKeyOf_update_signedPreKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## Tag 7 (`kyber_pre_key_id`, `+0x2c8..+0x2d4` / `+0x0d4..+0x0e0` / `+0x3cc..+0x3ec`, `off = 0x78`) -/

set_option maxHeartbeats 800000 in
theorem initOptU32_kyberPreKeyId_placed_cpsX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x2c8#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (blkPl_111).base + 0x0d4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (optU32At (sp' + 432#64) (some v0) ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optU32At (sp' + 432#64) o ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 712#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 212#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 432#64 + 4#64 = sp' + 436#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 720#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 432#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 212#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl2 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 432#64) ↦₆₄ 1#64) =
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 432#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeKyberPreKeyId_placed_cpsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x2c8#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with kyberPreKeyId := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_kyberPreKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 432#64) m.kyberPreKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest7 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_kyberPreKeyId_placed_cpsX (s0 := s0) hpc hrun hregs hsp hcl htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 212#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 436#64) v0))) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 8) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 436#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hint32
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 224#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 436#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 436#64 = sp' + 436#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_kyberPreKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64),
      ProofLib.memRegion_four (sp' + 436#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with kyberPreKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    rw [← wirePreKeyOf_update_kyberPreKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

theorem int32ArmPK_placed_cps (f : Int32FieldPK) [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + f.entryOff)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) (f.set m v))
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  cases f with
  | preKeyId => exact mergePreKeyId_placed_cpsX hPush hint32 hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  | registrationId => exact mergeRegId_placed_cpsX hPush hint32 hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  | signedPreKeyId => exact mergeSignedPreKeyId_placed_cpsX hPush hint32 hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  | kyberPreKeyId => exact mergeKyberPreKeyId_placed_cpsX hPush hint32 hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
