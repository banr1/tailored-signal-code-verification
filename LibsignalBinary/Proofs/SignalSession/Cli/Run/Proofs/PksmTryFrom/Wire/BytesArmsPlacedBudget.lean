/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` `bytes::merge` Arms and `DecodeError::push` Tail

Allocation-budget (`RustCliAllocBudget M`) proofs of the four `bytes::merge` field arms and
the shared `DecodeError::push` error tail on `preKeyPlacedProg H` over
`SigTryFromLoopBoundedEnv rem caps` and `wirePreKeyLoopCapsOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlacedBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalProtoCodec
  (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost bytesMergeStackX
   decodeVarintSliceStackX optVecU8At skipFieldStackX sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp cmn_one_ne_of_lt entails_of_eq optVecU8At_none_split optVecU8At_some_unfold
   pointsTo64_emptyVec_eq_vecU8At setWidth8_ofNat64 stackAt_sub_split vecU8At_fold_of_pure)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (keepsFrozenInv_codeRoLoaded preKeyPlacedProg)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
  (BytesArmFieldPK PreKeyLoopRegs memRegion64_split8_448
   vecU8At_baseKey_entails_wirePreKeyOf vecU8At_identityKey_entails_wirePreKeyOf
   vecU8At_kyberCt_entails_wirePreKeyOf vecU8At_message_entails_wirePreKeyOf
   wirePreKeyAt_split_baseKey wirePreKeyAt_split_identityKey
   wirePreKeyAt_split_kyberCt wirePreKeyAt_split_message
   wirePreKeyU32s)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (decodeErrorPushPK_tail_placed_wpX decodeErrorPushPK_tail_placed_wpX_caps
   optFieldCapMatch_pksm_init preKeyLoopExitPostPlaced preKeyLoopExitPostPlaced_bytesStep
   sepWP_done_sync_pool_111 sepWP_seg_111
   vecU8At_baseKey_entails_wirePreKeyLoopCapsOf
   vecU8At_identityKey_entails_wirePreKeyLoopCapsOf
   vecU8At_kyberCt_entails_wirePreKeyLoopCapsOf
   vecU8At_message_entails_wirePreKeyLoopCapsOf
   wirePreKeyLoopCapsOf)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bmPreBoundBudget bytesMergeEventsCore bytesMergeRawSpecGen bytesMergeRawSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (bmExactPostVec bmNextCap bytesMergeExactRawSpecX decodeErrorPushBoundedSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromField SigTryFromLoopBoundedEnv
   bmNextCap_lt_two_pow_63 fitsEnv_sigLoop_bytesMerge fitsEnv_sigLoop_bytesTail
   mergeBytes_progress noPanicQp sepWPp_call_noPanic_placed sepWPp_mono_post)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (decodeErrorPushPK_tail_placed_wpX decodeErrorPushPK_tail_placed_wpX_caps)

/-- Maps the 4 `BytesArmFieldPK` selectors onto `SigTryFromField` (`(.rk, .ct, .pq, .ad)`). -/
def bytesArmToSigField (f : BytesArmFieldPK) : SigTryFromField :=
  BytesArmFieldPK.casesOn (motive := fun _ => SigTryFromField) f .rk .ct .pq .ad

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

private theorem ba_bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem ba_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem pl_ba_bv_add_neg_216 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 216) = sp' + 296#64 := by bv_omega
private theorem pl_ba_bv_add_neg_200 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 200) = sp' + 312#64 := by bv_omega
private theorem pl_ba_bv_add_neg_176 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 176) = sp' + 336#64 := by bv_omega
private theorem pl_ba_bv_add_neg_152 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 152) = sp' + 360#64 := by bv_omega
private theorem pl_ba_bv_add_neg_128 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 128) = sp' + 384#64 := by bv_omega
private theorem pl_ba_bv_add_neg_72 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
private theorem pl_ba_bv_add_neg_64 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  pl_ba_bv_add_neg_216 pl_ba_bv_add_neg_200 pl_ba_bv_add_neg_176 pl_ba_bv_add_neg_152
  pl_ba_bv_add_neg_128 pl_ba_bv_add_neg_72 pl_ba_bv_add_neg_64
attribute [local arm64_norm, local wp_norm]
  ba_bv_sub_add_lit ba_bv_sub_sub_lit BitVec.toNat_zero

/-! ## Tag 8 (`kyber_ciphertext`, `+0x238..+0x25c` / `+0x36c..+0x380` → `+0x3e0..+0x3ec`, `off = 0x00`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_kyberCt_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
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
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A.repAlloc (sp' + 312#64) cap0 vecPtr0 v0 ∗ A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A.repAlloc pin (sp' + 312#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 568#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 312#64 320#64 328#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 588#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 312#64 320#64 328#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 312#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 588#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 312#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeKyberCiphertext_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + 0x238#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (evs₁ : List AllocEvent) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .rk < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .rk)) bs →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .rk (bmNextCap (caps.get .rk) v.length))) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64)
            (caps.set .rk (bmNextCap (caps.get .rk) v.length))
            { m with kyberCiphertext := some v })
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .rk (bmNextCap (caps.get .rk) v.length))
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  unfold wirePreKeyLoopCapsOf
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_pre fun g => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hc => ?_
  rw [wirePreKeyAt_split_kyberCt A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A.repAlloc g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A.repAlloc g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_kyberCt_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 hcap0_init
  change s1.pc = (blkPl_111).base + 588#64 at hpc1
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_pksm_init hc.1 hlen hcap0_init
  let x_arg : BytesMergeGhost :=
    ⟨wt, (sp' + 312#64), cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .rk hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 600#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 312#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (sp' + 312#64) = (sp' + 312#64) ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, hcap0_ok, hfit_bm⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [bytesMergeExactRawSpecX, bmExactPostVec, x_arg]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    have hevs₁ : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .rk)) bs := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      rwa [hcap0_bv] at hevs
    have hprog : rest.length + v.length + 1 ≤ rem := by
      have := mergeBytes_progress hm; omega
    have hnext_lt : bmNextCap (caps.get .rk) v.length < 2 ^ 63 := by
      dsimp only [SigTryFromCaps.get]
      rw [← hcap0_nat]
      exact bmNextCap_lt_two_pow_63 hcap0_ok (by omega) (by omega) hm
    have hfit_tail : FitsEnv M lim (M.stepEvents evs st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .rk (bmNextCap (caps.get .rk) v.length))) :=
      fitsEnv_sigLoop_bytesTail .rk hm hmax hprog hcap_lt hevs₁ hfit
    refine sepWPp_mono_post
      (fun _ _ => preKeyLoopExitPostPlaced_bytesStep .rk hm hmax hprog hcap_lt hevs₁) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨_hcap'_ok, hcap'_eq⟩ => ?_
    rw [hcap0_nat] at hcap'_eq
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs₁ hfit_tail
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyLoopCapsOf A.repAlloc g sp' cap' ptr' caps m v hc hcap'_eq hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm; subst hres
    have hevs_err : evs = rustAllocEvents 72 8 := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      simp only [bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_err
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with kyberCiphertext := some v0 }) hfit
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyOf A.repAlloc g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

/-! ## Tag 2 (`base_key`, `+0x190..+0x1b4` / `+0x3a8..+0x3c8`, `off = 0x18`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_baseKey_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
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
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A.repAlloc (sp' + 336#64) cap0 vecPtr0 v0 ∗ A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A.repAlloc pin (sp' + 336#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 400#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 336#64 344#64 352#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 420#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 336#64 344#64 352#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 336#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 420#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 336#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeBaseKey_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + 0x190#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (evs₁ : List AllocEvent) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .ct < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ct)) bs →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .ct (bmNextCap (caps.get .ct) v.length))) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64)
            (caps.set .ct (bmNextCap (caps.get .ct) v.length))
            { m with baseKey := some v })
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .ct (bmNextCap (caps.get .ct) v.length))
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  unfold wirePreKeyLoopCapsOf
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_pre fun g => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hc => ?_
  rw [wirePreKeyAt_split_baseKey A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A.repAlloc g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A.repAlloc g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.baseKey (sp' + 336#64) m.baseKey ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_baseKey_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 hcap0_init
  change s1.pc = (blkPl_111).base + 420#64 at hpc1
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_pksm_init hc.2.1 hlen hcap0_init
  let x_arg : BytesMergeGhost :=
    ⟨wt, (sp' + 336#64), cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .ct hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 432#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 336#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (sp' + 336#64) = (sp' + 336#64) ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, hcap0_ok, hfit_bm⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [bytesMergeExactRawSpecX, bmExactPostVec, x_arg]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    have hevs₁ : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ct)) bs := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      rwa [hcap0_bv] at hevs
    have hprog : rest.length + v.length + 1 ≤ rem := by
      have := mergeBytes_progress hm; omega
    have hnext_lt : bmNextCap (caps.get .ct) v.length < 2 ^ 63 := by
      dsimp only [SigTryFromCaps.get]
      rw [← hcap0_nat]
      exact bmNextCap_lt_two_pow_63 hcap0_ok (by omega) (by omega) hm
    have hfit_tail : FitsEnv M lim (M.stepEvents evs st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .ct (bmNextCap (caps.get .ct) v.length))) :=
      fitsEnv_sigLoop_bytesTail .ct hm hmax hprog hcap_lt hevs₁ hfit
    refine sepWPp_mono_post
      (fun _ _ => preKeyLoopExitPostPlaced_bytesStep .ct hm hmax hprog hcap_lt hevs₁) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨_hcap'_ok, hcap'_eq⟩ => ?_
    rw [hcap0_nat] at hcap'_eq
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs₁ hfit_tail
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_baseKey_entails_wirePreKeyLoopCapsOf A.repAlloc g sp' cap' ptr' caps m v hc hcap'_eq hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm; subst hres
    have hevs_err : evs = rustAllocEvents 72 8 := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      simp only [bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_err
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with baseKey := some v0 }) hfit
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_baseKey_entails_wirePreKeyOf A.repAlloc g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

/-! ## Tag 3 (`identity_key`, `+0x2a0..+0x2c4` / `+0x340..+0x360`, `off = 0x30`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_identityKey_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
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
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A.repAlloc (sp' + 360#64) cap0 vecPtr0 v0 ∗ A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A.repAlloc pin (sp' + 360#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 672#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 360#64 368#64 376#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 692#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 360#64 368#64 376#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 360#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 692#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 360#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeIdentityKey_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + 0x2a0#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (evs₁ : List AllocEvent) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .pq < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .pq)) bs →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .pq (bmNextCap (caps.get .pq) v.length))) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64)
            (caps.set .pq (bmNextCap (caps.get .pq) v.length))
            { m with identityKey := some v })
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .pq (bmNextCap (caps.get .pq) v.length))
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  unfold wirePreKeyLoopCapsOf
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_pre fun g => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hc => ?_
  rw [wirePreKeyAt_split_identityKey A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A.repAlloc g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A.repAlloc g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.identityKey (sp' + 360#64) m.identityKey ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_identityKey_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 hcap0_init
  change s1.pc = (blkPl_111).base + 692#64 at hpc1
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_pksm_init hc.2.2.1 hlen hcap0_init
  let x_arg : BytesMergeGhost :=
    ⟨wt, (sp' + 360#64), cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .pq hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 704#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 360#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (sp' + 360#64) = (sp' + 360#64) ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, hcap0_ok, hfit_bm⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [bytesMergeExactRawSpecX, bmExactPostVec, x_arg]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    have hevs₁ : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .pq)) bs := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      rwa [hcap0_bv] at hevs
    have hprog : rest.length + v.length + 1 ≤ rem := by
      have := mergeBytes_progress hm; omega
    have hnext_lt : bmNextCap (caps.get .pq) v.length < 2 ^ 63 := by
      dsimp only [SigTryFromCaps.get]
      rw [← hcap0_nat]
      exact bmNextCap_lt_two_pow_63 hcap0_ok (by omega) (by omega) hm
    have hfit_tail : FitsEnv M lim (M.stepEvents evs st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .pq (bmNextCap (caps.get .pq) v.length))) :=
      fitsEnv_sigLoop_bytesTail .pq hm hmax hprog hcap_lt hevs₁ hfit
    refine sepWPp_mono_post
      (fun _ _ => preKeyLoopExitPostPlaced_bytesStep .pq hm hmax hprog hcap_lt hevs₁) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨_hcap'_ok, hcap'_eq⟩ => ?_
    rw [hcap0_nat] at hcap'_eq
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs₁ hfit_tail
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_identityKey_entails_wirePreKeyLoopCapsOf A.repAlloc g sp' cap' ptr' caps m v hc hcap'_eq hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm; subst hres
    have hevs_err : evs = rustAllocEvents 72 8 := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      simp only [bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_err
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with identityKey := some v0 }) hfit
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_identityKey_entails_wirePreKeyOf A.repAlloc g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

/-! ## Tag 4 (`message`, `+0x200..+0x224` / `+0x438..+0x454`, `off = 0x48`) -/

set_option maxHeartbeats 800000 in
theorem initOptVecU8_message_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
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
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (vecU8At A.repAlloc (sp' + 384#64) cap0 vecPtr0 v0 ∗ A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (optVecU8At A.repAlloc pin (sp' + 384#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 512#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 384#64 392#64 400#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 532#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 384#64 392#64 400#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 384#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 532#64) ?_
    apply sepWP_seg_111; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr rfl)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 384#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeMessage_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + 0x200#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (evs₁ : List AllocEvent) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .ad < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ad)) bs →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .ad (bmNextCap (caps.get .ad) v.length))) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64)
            (caps.set .ad (bmNextCap (caps.get .ad) v.length))
            { m with message := some v })
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .ad (bmNextCap (caps.get .ad) v.length))
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  unfold wirePreKeyLoopCapsOf
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_pre fun g => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hc => ?_
  rw [wirePreKeyAt_split_message A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A.repAlloc g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A.repAlloc g.identityKey (sp' + 360#64) m.identityKey ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.message (sp' + 384#64) m.message ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_message_placed_cpsPK hpc hrun hregs hsp hcl htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 hcap0_init
  change s1.pc = (blkPl_111).base + 532#64 at hpc1
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_pksm_init hc.2.2.2 hlen hcap0_init
  let x_arg : BytesMergeGhost :=
    ⟨wt, (sp' + 384#64), cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .ad hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := lsmpl.base 7) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hbytes
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_111).base + 544#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 384#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (sp' + 384#64) = (sp' + 384#64) ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, hcap0_ok, hfit_bm⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x27, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  dsimp only [bytesMergeExactRawSpecX, bmExactPostVec, x_arg]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  rw [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    have hevs₁ : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ad)) bs := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      rwa [hcap0_bv] at hevs
    have hprog : rest.length + v.length + 1 ≤ rem := by
      have := mergeBytes_progress hm; omega
    have hnext_lt : bmNextCap (caps.get .ad) v.length < 2 ^ 63 := by
      dsimp only [SigTryFromCaps.get]
      rw [← hcap0_nat]
      exact bmNextCap_lt_two_pow_63 hcap0_ok (by omega) (by omega) hm
    have hfit_tail : FitsEnv M lim (M.stepEvents evs st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set .ad (bmNextCap (caps.get .ad) v.length))) :=
      fitsEnv_sigLoop_bytesTail .ad hm hmax hprog hcap_lt hevs₁ hfit
    refine sepWPp_mono_post
      (fun _ _ => preKeyLoopExitPostPlaced_bytesStep .ad hm hmax hprog hcap_lt hevs₁) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨_hcap'_ok, hcap'_eq⟩ => ?_
    rw [hcap0_nat] at hcap'_eq
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 228#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs₁ hfit_tail
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_message_entails_wirePreKeyLoopCapsOf A.repAlloc g sp' cap' ptr' caps m v hc hcap'_eq hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm; subst hres
    have hevs_err : evs = rustAllocEvents 72 8 := by
      rw [BytesMergeEnv] at hevs
      dsimp only [x_arg] at hevs
      simp only [bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_err
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl3 (mid := (blkPl_111).base + 1112#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (decodeErrorPushPK_tail_placed_wpX hPush (s0 := s0) (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with message := some v0 }) hfit
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_message_entails_wirePreKeyOf A.repAlloc g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

/-! ## Parametric `bytesArmPK_placed_cps` (`off ∈ {0x00, 0x18, 0x30, 0x48}`) -/

theorem bytesArmPK_placed_cps (f : BytesArmFieldPK) [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + f.entryOff)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (evs₁ : List AllocEvent) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get (bytesArmToSigField f) < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get (bytesArmToSigField f))) bs →
      FitsEnv M lim (M.stepEvents evs₁ st)
        (SigTryFromLoopBoundedEnv rest.length
          (caps.set (bytesArmToSigField f) (bmNextCap (caps.get (bytesArmToSigField f)) v.length))) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64)
            (caps.set (bytesArmToSigField f) (bmNextCap (caps.get (bytesArmToSigField f)) v.length)) (f.set m v))
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set (bytesArmToSigField f) (bmNextCap (caps.get (bytesArmToSigField f)) v.length))
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  cases f
  · exact mergeKyberCiphertext_placed_cpsPK hPush hbytes hfit hmax hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeBaseKey_placed_cpsPK hPush hbytes hfit hmax hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeIdentityKey_placed_cpsPK hPush hbytes hfit hmax hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone
  · exact mergeMessage_placed_cpsPK hPush hbytes hfit hmax hpc hrun hregs hx0 hsp hcl htr hlen hcont hnone

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlacedBudget
