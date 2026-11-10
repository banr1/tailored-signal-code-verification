/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArms
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` `bytes::merge` Arms and `DecodeError::push` Tail

Proves the four `bytes::merge` field arms (`kyber_ciphertext`, `base_key`, `identity_key`,
`message`) and the shared `DecodeError::push` error tail (`+0x458..+0x45c → +0x460`) on
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
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
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
private abbrev of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev call_tryFrom_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom_pk

@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_216 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 216) = sp' + 296#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_200 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 200) = sp' + 312#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_176 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 176) = sp' + 336#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_152 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 152) = sp' + 360#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_128 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 128) = sp' + 384#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_72 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem pl_ba_bv_add_neg_64 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero

/-! ## Shared `DecodeError::push` tail (`+0x458..+0x45c` → `+0x460`) -/

set_option maxHeartbeats 800000 in
/-- Shared `DecodeError::push` tail at `+0x458..+0x45c` → `+0x460` on `preKeyPlacedProg H`. -/
theorem decodeErrorPushPK_tail_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr err : BitVec 64} {n : Nat}
    {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x458#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 448#64)
    (herr : err ≠ 0#64)
    (hn : n < 2 ^ 32) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ err) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        decodeErrorAtStackLen A err n ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  change s.pc = (blkPl_111).base + 1112#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (Prost.skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 257) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    (sp' + 448#64, err, n) hPush
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1116#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 448#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 2 ^ 32)
    (by simp only [decodeErrorPushExternSpecWithStack, hsp_eq, hx0, arm64_norm])
    ⟨herr, hn⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]; rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre (fun err' => SepWPp.pure_pre (fun herr' =>
    of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_))
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
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 448#64) err')) ?_
  refine Entails.trans ?_ (preKeyLoopExitMem_err_intro A sp' ptr bs err' herr' (n + 1) mErr)
  apply entails_of_eq; simp only [hstack, hsp_eq, memRegion64_split8_448 sp', arm64_norm]; ac_rfl

/-! ## Tag 8 (`kyber_ciphertext`, `+0x238..+0x25c` / `+0x36c..+0x380` → `+0x3e0..+0x3ec`, `off = 0x00`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_kyberCt_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x238#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (blkPl_111).base + 0x24c#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A (sp' + 312#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A pin (sp' + 312#64) u ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 568#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 312#64 320#64 328#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 588#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 312#64 320#64 328#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 312#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 588#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 312#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeKyberCiphertext_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x238#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with kyberCiphertext := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_kyberCt A g sp' m]
  let F_msg := optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_kyberCt_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 588#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 312#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 600#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 312#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 312#64 = sp' + 312#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
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
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with kyberCiphertext := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 2 (`base_key`, `+0x190..+0x1b4` / `+0x3a8..+0x3c8`, `off = 0x18`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_baseKey_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x190#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (blkPl_111).base + 0x1a4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A (sp' + 336#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A pin (sp' + 336#64) u ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 400#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 336#64 344#64 352#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 420#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 336#64 344#64 352#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 336#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 420#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 336#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeBaseKey_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x190#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with baseKey := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_baseKey A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_baseKey_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 420#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 336#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 432#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 336#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 336#64 = sp' + 336#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
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
    have hmsg := vecU8At_baseKey_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with baseKey := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg := vecU8At_baseKey_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 3 (`identity_key`, `+0x2a0..+0x2c4` / `+0x340..+0x360`, `off = 0x30`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_identityKey_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x2a0#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (blkPl_111).base + 0x2b4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A (sp' + 360#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A pin (sp' + 360#64) u ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 672#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 360#64 368#64 376#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 692#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 360#64 368#64 376#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 360#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 692#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 360#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeIdentityKey_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x2a0#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with identityKey := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_identityKey A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_identityKey_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 692#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 360#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 704#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 360#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 360#64 = sp' + 360#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
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
    have hmsg := vecU8At_identityKey_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with identityKey := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg := vecU8At_identityKey_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 4 (`message`, `+0x200..+0x224` / `+0x438..+0x454`, `off = 0x48`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_message_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x200#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (blkPl_111).base + 0x214#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A (sp' + 384#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A pin (sp' + 384#64) u ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 512#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 384#64 392#64 400#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 532#64) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 384#64 392#64 400#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 384#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 532#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 384#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeMessage_placed_cpsPK [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x200#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with message := some v })
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_message A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.message (sp' + 384#64) m.message ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_message_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  change s1.pc = (blkPl_111).base + 532#64 at hpc1
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) fun hcl2 => ?_
  refine call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    ⟨wt, sp' + 384#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 544#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 384#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 384#64 = sp' + 384#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20,
       by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
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
    have hmsg := vecU8At_message_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 =>
      of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (n := 0) (mErr := { m with message := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg := vecU8At_message_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Parametric `bytesArmPK_placed_cps` (`off ∈ {0x00, 0x18, 0x30, 0x48}`) -/

theorem bytesArmPK_placed_cps (f : BytesArmFieldPK) [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + f.entryOff)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) (f.set m v))
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  cases f
  · exact mergeKyberCiphertext_placed_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeBaseKey_placed_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeIdentityKey_placed_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeMessage_placed_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
