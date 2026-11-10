/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Inner `bytes::merge` & `skip_field` Steps for `Chunked.KeysSampled::merge` (Block `304`)

Proves the budget-threaded inner `skip_field`, `tag = 3` (`ek`), and `tag = 4` (`dk`) step lemmas
of `Unchunked.HeaderSent` inside `Chunked.KeysSampled::merge` on Block `304`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetSteps

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix SkipFieldGhost
   pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr
  (headerSentPBAt optHeaderSentPBAt unchunked4At)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Auth
  (WppPost mergeBytes_length optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedInl10CalleeSaved ChunkedKeysSampledMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedInlBelowStack
   chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails
   chunkedInlBelow_skipField97 chunkedInlBelow_skipField97_entails
   chunkedKeysSampledMerge_fnOff chunkedKeysSampledPBAt codecWireTypeToProto
   memRegion_48_cells1_160 unchunked4CapAt_entails_chunkedKeysSampledPBAt unchunked4CapAt_mono
   vecU8At_entails_rustBytesVecAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_304 blkPl_304)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split
   SpqrMergeIterEnv SpqrMergeLoopEnv decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedKeysSampledMergeEnv chunkedKeysSampledMergeSpec keysSampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
  (chunkedKeysSampledErrFrame chunkedKeysSampledUcLoopPre
   chunkedKeysSampled_uc_field_push_exit_placed chunkedKeysSampled_uc_push_exit_placed
   unchunked4CapAt_eq unchunked4CapAt_eq_dk
   vecU8At_entails_vecU8CapAt vecU8CapAt vecU8CapAt_entails_vecU8' vecU8CapAt_mono')
open scoped LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedKeysSampledMerge_fnOff

/-! ## 1. Reusable `BytesMerge3Env` → `SpqrMergeLoopEnv` Combinators -/

theorem fitsEnv_bytesMerge3_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x_bm : BytesMergeGhost} {f₀ f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hf : f₀ + max 1 (2 * x_bm.bs.length) ≤ f_tot)
    (hlen : x_bm.bs.length ≤ maxLen)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (BytesMerge3Env x_bm) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st)
      (SpqrMergeLoopEnv (max 1 (2 * x_bm.bs.length)) maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_bytesHead hlen (Nat.le_refl _) hrem

theorem bytesMergeErr_to_spqr {x_bm : BytesMergeGhost} {maxLen polyCapBound : Nat}
    {evs : List AllocEvent} (hm : mergeBytes x_bm.wt x_bm.bs = none)
    (hb : BytesMerge3Env x_bm evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs :=
  .bytesMergeErr x_bm.wt x_bm.valCap x_bm.bs hm hb

theorem bytesMergeOk_to_spqr {x_bm : BytesMergeGhost} {v rest' : List (BitVec 8)}
    {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hm : mergeBytes x_bm.wt x_bm.bs = some (v, rest'))
    (hlen : x_bm.bs.length ≤ maxLen)
    (hb : BytesMerge3Env x_bm evs) :
    SpqrMergeLoopEnv (2 * v.length + 1) maxLen polyCapBound evs := by
  simpa only [Nat.zero_add] using SpqrMergeLoopEnv.bytesSingle (fuel := 0) hm hlen hb

/-! ## 2. Placed Inner `bytes::merge` (Tags 3 & 4) and `skip_field` Steps for Block `304` -/

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_304).base

theorem chunkedKeysSampled_uc_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.HeaderSent} {sendingHdr : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysSampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Chunked.KeysSampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_304).base + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysSampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with ek := v } sendingHdr x.bs rest' (keysSampledPolyCapBound x))
        (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_304).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysSampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingHdr x.bs rest (keysSampledPolyCapBound x))
      (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedKeysSampled_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingHdr := sendingHdr }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [chunkedKeysSampledUcLoopPre, spqrPoolAt, unchunked4CapAt_eq, vecU8CapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap1
    apply SepWP.exists_elim; intro ptr1
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr, cap1, ptr1, uc.ek, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 416#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawBudgetSpec, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap1,
        fitsEnv_bytesMerge3_of_spqr (x_bm := x_bm) (by dsimp only [x_bm]; omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes iwt rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply sepWPpLscro_of_vm (mid := entry + 984#64)
      (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_b
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_b
      wp_focus_pure; intro hsm0
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (vecU8At_entails_rustBytesVecAt A.repAlloc x.msgPtr cap1 ptr1 uc.ek) (by sep_focus)
      apply SepWP.fold (vecU8CapAt_entails_vecU8' A.repAlloc (x.msgPtr + 0x18#64) rest.length uc.dk) (by sep_focus)
      apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A.repAlloc (x.msgPtr + 0x30#64) rest.length uc.auth) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
          (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
          hevs (bytesMergeErr_to_spqr (x_bm := x_bm) hmb hevs_b))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply sepWPpLscro_of_vm (mid := entry + 1068#64)
      by_vm_steps
        (conv => arg 4; rw [memRegion_48_cells1_160 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedKeysSampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (keysSampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingHdr := sendingHdr } x.bs)
          (by dsimp only [chunkedKeysSampledErrFrame, chunkedKeysSampledPBAt,
                optHeaderSentPBAt, headerSentPBAt, unchunked4At];
              sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
      have hmb_len := mergeBytes_len_bound hmb
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_vecU8CapAt A.repAlloc x.msgPtr cap1' ptr1' rest'.length v hcap1') (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono' A.repAlloc (x.msgPtr + 0x18#64) uc.dk hrest'_le) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * (x.bs.length - rest'.length)) (by omega)
            hevs (bytesMergeOk_to_spqr (x_bm := x_bm) hmb hrest_le hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedKeysSampledUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc with ek := v } sendingHdr x.bs rest' (keysSampledPolyCapBound x))
          (by dsimp only [chunkedKeysSampledUcLoopPre]; rw [unchunked4CapAt_eq];
              sep_entail)
        exact hcont v rest' _ hmb
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedKeysSampled_uc_tag4_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.HeaderSent} {sendingHdr : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysSampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Chunked.KeysSampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_304).base + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysSampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with dk := v } sendingHdr x.bs rest' (keysSampledPolyCapBound x))
        (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_304).base + 564#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysSampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingHdr x.bs rest (keysSampledPolyCapBound x))
      (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedKeysSampled_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingHdr := sendingHdr }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [chunkedKeysSampledUcLoopPre, spqrPoolAt, unchunked4CapAt_eq_dk, vecU8CapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap2
    apply SepWP.exists_elim; intro ptr2
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, uc.dk, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 576#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawBudgetSpec, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap2,
        fitsEnv_bytesMerge3_of_spqr (x_bm := x_bm) (by dsimp only [x_bm]; omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes iwt rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply sepWPpLscro_of_vm (mid := entry + 912#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_b
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_entails_vecU8' A.repAlloc x.msgPtr rest.length uc.ek) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_rustBytesVecAt A.repAlloc (x.msgPtr + 0x18#64) cap2 ptr2 uc.dk) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A.repAlloc (x.msgPtr + 0x30#64) rest.length uc.auth) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (bytesMergeErr_to_spqr (x_bm := x_bm) hmb hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 1068#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedKeysSampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (keysSampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingHdr := sendingHdr } x.bs)
          (by dsimp only [chunkedKeysSampledErrFrame, chunkedKeysSampledPBAt,
                optHeaderSentPBAt, headerSentPBAt, unchunked4At];
              sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
      have hmb_len := mergeBytes_len_bound hmb
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        apply SepWP.exists_elim; intro cap2'
        apply SepWP.exists_elim; intro ptr2'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap2'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono' A.repAlloc x.msgPtr uc.ek hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) cap2' ptr2' rest'.length v hcap2') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * (x.bs.length - rest'.length)) (by omega)
            hevs (bytesMergeOk_to_spqr (x_bm := x_bm) hmb hrest_le hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedKeysSampledUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc with dk := v } sendingHdr x.bs rest' (keysSampledPolyCapBound x))
          (by dsimp only [chunkedKeysSampledUcLoopPre]; rw [unchunked4CapAt_eq];
              sep_entail)
        exact hcont v rest' _ hmb
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedKeysSampled_uc_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hSkipCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.HeaderSent} {sendingHdr : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysSampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Chunked.KeysSampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_304).base + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysSampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          uc sendingHdr x.bs rest' (keysSampledPolyCapBound x))
        (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_304).base + 584#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysSampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingHdr x.bs rest (keysSampledPolyCapBound x))
      (WppPost (chunkedKeysSampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩
  have hpush_exit := @chunkedKeysSampled_uc_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, sendingHdr := sendingHdr }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [chunkedKeysSampledUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField97 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 596#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx1],
        htag_lt,
        by simp only [arm64_norm, wp_norm, hx19],
        by simp only [arm64_norm, wp_norm],
        by decide,
        hrest_lt,
        fitsEnv_skipField_of_spqr (by omega) hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
    | none =>
      have hnone := hnone_of_sf hsf
      apply sepWPpLscro_of_vm (mid := entry + 776#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (unchunked4CapAt_entails_chunkedKeysSampledPBAt A.repAlloc x.msgPtr rest.length uc sendingHdr) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (skipFieldEnv_to_spqr hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            memRegion (s0.sp - 128#64) 48 ∗
            chunkedKeysSampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (keysSampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, sendingHdr := sendingHdr } x.bs)
          (by dsimp only [chunkedKeysSampledErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (unchunked4CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth uc.ek uc.dk hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest'.length))
            hevs (skipFieldEnv_eq_nil_of_some hsf hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedKeysSampledUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            uc sendingHdr x.bs rest' (keysSampledPolyCapBound x))
          (by dsimp only [chunkedKeysSampledUcLoopPre]; sep_entail)
        exact hcont rest' _ hsf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetSteps
