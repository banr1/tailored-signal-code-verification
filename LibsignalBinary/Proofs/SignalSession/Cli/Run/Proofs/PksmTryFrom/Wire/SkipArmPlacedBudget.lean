/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlaced
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Unknown-Tag `skip_field` Arm

Allocation-budget (`RustCliAllocBudget M`) proofs of `skipFieldErrPK_364_placed_wpX` and
`mergeSkipField_placed_cpsPK` (`+0x2d8..+0x2e8`, `+0x364..+0x368`) on `preKeyPlacedProg H`
over `SigTryFromLoopBoundedEnv` and `wirePreKeyLoopCapsOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlacedBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost decodeErrorHookStackX decodeVarintSliceStackX skipFieldStackX
   sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp entails_of_eq setWidth32_ofNat64 setWidth8_ofNat64)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (bv_add_neg_72 bv_add_neg_216 keepsFrozenInv_codeRoLoaded preKeyPlacedProg)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
  (PreKeyLoopRegs)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (decodeErrorAtStackLen_mk_eq preKeyLoopExitMem_err_loopCaps_intro
   preKeyLoopExitPostPlaced sepWP_done_sync_pool_111 sepWP_seg_111
   wirePreKeyLoopCapsOf wirePreKeyLoopCapsOf_mk_eq)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (SkipFieldEnv skipFieldEventsCore skipFieldSpecGen skipFieldSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromErrTailEnv SigTryFromLoopBoundedEnv
   fitsEnv_sigLoop_errTail noPanicQp
   sepWPp_call_noPanic_placed sepWPp_end_noPanic_placed)

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

private theorem sk_bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem sk_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  sk_bv_sub_add_lit sk_bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_72 bv_add_neg_216

theorem skipFieldErrPK_364_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr : BitVec 64} {bs : List (BitVec 8)} {n : Nat} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x364#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx0_ne : s.readReg64 .x0 ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) n ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps mErr)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs none)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 868#64 at hpc
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
    by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcl1, by simpa [arm64_norm] using htr⟩, [], .done .nil, ?_⟩
  simp only [M.stepEvents_nil, arm64_norm]
  refine Entails.trans ?_
    (preKeyLoopExitMem_err_loopCaps_intro (A.atState lim st _) sp' ptr bs
      (s.readReg64 (Reg.gpr 0#5)) hx0_ne n caps mErr)
  simp only [RustCliAllocBudget.atState, wirePreKeyLoopCapsOf_mk_eq, decodeErrorAtStackLen_mk_eq]
  apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem mergeSkipField_placed_cpsPK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withLsCodeRoLoaded lsmpl (skipFieldSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
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
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 728#64 at hpc
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  let x_arg : SkipFieldGhost := ⟨wt, tag, 100, sp' + 440#64, sp' + 296#64, ptr, bs⟩
  have hfit_skip : FitsEnv M lim st (SkipFieldEnv x_arg) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_skipField) hfit
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 1) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hskip
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 740#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ sliceCursorAt (sp' + 296#64) ptr bs ∗
      stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 2 ^ 32 ∧
      sp' + 512#64 - 72#64 = sp' + 440#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 2 ^ 32 ∧ bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (SkipFieldEnv x_arg))
    (by
      have hstack : skipFieldStackX 100 = 80 + (9696 + extHookStack * 2) := by
        simp only [skipFieldStackX, decodeVarintSliceStackX, decodeErrorHookStackX]; omega
      simp only [skipFieldSpecX, skipFieldSpecGen, decodeErrorHookStackX, hstack,
        x_arg, hsp_eq, h0, h1, arm64_norm]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl,
      by decide, by omega, hfit_skip⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [skipFieldSpecX, skipFieldSpecGen, x_arg]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hevs => ?_
  have hstack : 9696 + (80 + 2 * extHookStack) = skipFieldStackX 100 := by
    simp only [skipFieldStackX, decodeVarintSliceStackX, decodeErrorHookStackX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    have hevs_nil : evs = [] := by
      rw [hevs]; unfold skipFieldEventsCore; simp only [hs]
    subst hevs_nil
    simp only [M.stepEvents_nil, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 228#64) ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont rest _ hs (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3 (by simpa [arm64_norm] using htr2.trans htr))
    apply entails_of_eq
    simp only [decodeErrorHookStackX, hsp_eq, arm64_norm]; rw [hstack]; sep_ac_rfl
  | none =>
    have hres := hnone hs; subst hres
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_111; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
      by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done (SigTryFromErrTailEnv.of_skipField hevs), ?_⟩
    simp only [arm64_norm]
    refine Entails.trans ?_
      (preKeyLoopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
        sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 caps m)
    simp only [RustCliAllocBudget.atState, wirePreKeyLoopCapsOf_mk_eq, decodeErrorAtStackLen_mk_eq]
    apply entails_of_eq
    simp only [decodeErrorHookStackX, hsp_eq, arm64_norm]; rw [hstack]; sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlacedBudget
