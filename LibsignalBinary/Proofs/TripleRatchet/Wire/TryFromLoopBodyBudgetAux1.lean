/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Loop Body: Varint, Key & Skip-Field

Relocatable `[LibsignalPlacement]` CPS proofs for `decode_varint_slow`, `decode_varint_slice`,
inlined `decode_varint` + `decode_key`, and the `skip_field` branch on Block `85` under
`TryFromLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux1

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSession (ProtoSignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeKey skipField)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 extHookStack LibsignalCodeRoLoaded KindNoHeap varintSlowName)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost VarintSlicePre varintSliceResultAt sliceCursorAt sliceCursorAfter
   decodeVarintSliceStackX skipFieldStackX decodeVarintSliceName skipFieldName
   wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedProg LoopRegs
   wireSignalMessageLoopOf
   decodeVarint_suffix decodeVarint_cons_of_le skipField_suffix
   pointsToBytes_split_last stackAt_sub_split
   memRegion48_split8 memRegion48_split24 memRegion48_split_296_304_312
   pointsTo64_zero_split32 pointsTo64_one_split32 pointsTo64_pair_entails_memRegion16
   scratch24_ok_entails_memRegion48 scratch24_err_entails_memRegion48
   signExtend64_bit63_eq_false_iff signExtend64_bit63_eq_true_iff
   signExtend64_eq_zeroExtend64_of_le signExtend32_bit31_eq_false_iff
   signExtend32_bit31_eq_true_iff
   key_lsr32_ne_zero_of_ge key_lsr32_eq_zero_of_lt
   sliceCursorAfter_entails_memRegion decodeKey_err_entails
   key_and7_ule6_of_ge key_and7_ule6_of_lt
   key_tag32_zeroExtend64_eq key_tag32_eq_zero_of_lt1 key_tag32_ne_zero_of_ge1
   key_and7_eq_wt setWidth8_ofNat64 setWidth32_ofNat64 entails_of_eq)
open CryptoVerification.LibsignalTripleRatchet.Wire.TryFromLoopStateSimp
  (sp_setPC_pre sp_setMem_setPC_pre
   readReg64_setPC_pre readReg64_setMem_setPC_pre
   readReg32_setPC_pre readReg32_setMem_setPC_pre
   readReg_setPC_pre readReg_setMem_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents decodeVarintSlowBudgetSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpecGen decodeVarintSliceSpecX
   SkipFieldEnv skipFieldEventsCore skipFieldSpecGen skipFieldSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DecodeVarintSliceOkWPlaced SkipFieldOkWPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromErrTailEnv SigTryFromLoopBoundedEnv fitsEnv_sigLoop_errTail
   wireSignalMessageLoopCapsOf wireSignalMessageLoopCapsOf_entails_loopOf
   wireSignalMessageLoopCapsOf_entails_of wireSignalMessageLoopCapsOf_mono
   loopExitMem_err_loopCaps_intro
   noPanicQp sepWPp_end_noPanic_placed sepWPp_call_noPanic_placed
   loopExitPostPlaced sepWP_seg_85 sepWP_done_sync_pool_85
   decodeErrorFrom_tail_wp_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre
  sp_setMem_setPC_pre
  readReg64_setPC_pre
  readReg64_setMem_setPC_pre
  readReg32_setPC_pre
  readReg32_setMem_setPC_pre
  readReg_setPC_pre
  readReg_setMem_setPC_pre

/-! ## `decode_varint_slow` and `decode_varint_slice` branches -/

theorem decodeVarintSlow_tail_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hS : TripleRatchetHooksWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x284#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  have hcall := hS.decodeVarintSlow
  have hfit_slow : FitsEnv M lim st (DecodeVarintSlowEnv bs) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeVarintSlow) hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold sliceCursorAt
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ varintSlowName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (sp' + 288#64, sp' + 160#64, ptr, bs, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 652#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ ((sp' + 160#64) ↦₆₄ ptr) ∗
      ((sp' + 160#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      stackAt sp' (64 + 2 * extHookStack))
    (φ := bs.length < 2 ^ 64 ∧ FitsEnv M lim st (DecodeVarintSlowEnv bs))
    (by
      simp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack,
        hsp_eq, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨by omega, hfit_slow⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack]
  have hvs := decodeVarint_eq_varintSlow bs
  rw [hvs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hevs_nil : evs = [] := by
      rw [DecodeVarintSlowEnv, decodeVarintSlowEvents, hvs, hd] at hevs
      exact hevs
    subst hevs_nil
    simp only [M.stepEvents_nil, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 336#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp only [arm64_norm]))
    apply entails_of_eq
    unfold sliceCursorAfter
    simp only [hstack, hsp_eq, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only [Option.map]
    rw [hnone hd, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_1, hx1_ne⟩ => ?_
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done (SigTryFromErrTailEnv.of_decodeVarintSlow hevs), ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 160#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length))
      (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left hpair)
        (loopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
          sp' ptr bs (s2.readReg64 (Reg.gpr 1#5)) hx1_ne 0 bs.length caps m))
    dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [hstack, hsp_eq, arm64_norm]
    sep_ac_rfl

theorem decodeVarintSlice_tail_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x11c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  have hcall := hvarint
  have hfit_slice : FitsEnv M lim st (DecodeVarintSliceEnv bs) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_decodeVarintSlice) hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := hx28
  have h27 : s.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := hx27
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  unfold sliceCursorAt
  simp only [hstack, memRegion48_split24 sp', sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeVarintSliceName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (⟨sp' + 296#64, ptr, bs⟩, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 292#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 296#64) 24 ∗ (ptr ↦ₛ bs) ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := bs.length < 2 ^ 63 ∧ VarintSlicePre bs ∧ FitsEnv M lim st (DecodeVarintSliceEnv bs))
    (by
      simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen,
        hsp_eq, h1, h2, hx2_nat, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨hlen, hpre_slice, hfit_slice⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
  have h28_2 : s2.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := by
    simpa [arm64_norm, h28] using hcs2.2.2.2.2.2.2.2.2.2.1
  have h27_2 : s2.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := by
    simpa [arm64_norm, h27] using hcs2.2.2.2.2.2.2.2.2.1
  dsimp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv :
        BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
          BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (sp' + 296#64)]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hevs_nil : evs = [] := by
      rw [DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] at hevs
      exact hevs
    subst hevs_nil
    simp only [M.stepEvents_nil]
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 336#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    wp_if hcc
    · exfalso
      rw [← hrest] at hcc
      exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine sepWP_done_sync_pool_85 A lim st fun _ hcl3 => ?_
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd
          (by simp only [arm64_norm])
          (by simp only [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
           by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
           by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
           by simpa [arm64_norm] using hregs2.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcl3
          (by simpa [arm64_norm] using htr2.trans htr)
          (by simp only [arm64_norm]))
      have hscr := scratch24_ok_entails_memRegion48 sp' key
        (BitVec.ofNat 64 (bs.length - rest.length))
      unfold sliceCursorAfter
      simp only [← hrest, hsub_bv]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq
      simp only [hstack, hsp_eq, arm64_norm]
      sep_ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [hnone hd, pointsTo64_one_split32 (sp' + 296#64), sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    refine SepWPp.exists_pre fun e => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun he_ne => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done (SigTryFromErrTailEnv.of_decodeVarintSlice hevs), ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 160#64) ptr
      (BitVec.ofNat 64 bs.length)
    have hscr := scratch24_err_entails_memRegion48 sp' e
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans
        (sepConj_mono hpair
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
        (loopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
          sp' ptr bs e he_ne 0 bs.length caps m))
    dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [hstack, hsp_eq, arm64_norm]
    sep_ac_rfl

/-! ## Multi-byte and inlined `decodeVarint` + `decodeKey` -/

theorem decodeVarintMulti_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x108#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hne : bs ≠ [])
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  have hslice := @decodeVarintSlice_tail_cps_placed _ M A lim st rem caps H hvarint s0
  have hslow := @decodeVarintSlow_tail_cps_placed _ M A lim st rem caps H hS s0
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]
      omega
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 284#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
      (hslice hfit
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simpa [arm64_norm] using hx28)
        (by simpa [arm64_norm] using hx27)
        (by simpa [arm64_norm] using hx1)
        (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        hlen
        (Or.inl hlen11)
        hcont hnone)
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]
      omega
    have hlast_addr :
        ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]
        exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]
      bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 284#64) ?_
      apply sepWP_seg_85; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (hslice hfit
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simpa [arm64_norm] using hx28)
          (by simpa [arm64_norm] using hx27)
          (by simpa [arm64_norm] using hx1)
          (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          hlen
          (Or.inr ⟨hne, hlast⟩)
          hcont hnone)
      apply entails_of_eq
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr,
        show ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 bs.length - 1#64 by bv_omega]
      sep_ac_rfl
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 644#64) ?_
      apply sepWP_seg_85; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (hslow hfit
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          hlen hcont hnone)
      apply entails_of_eq
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr,
        show ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 bs.length - 1#64 by bv_omega]
      sep_ac_rfl

theorem decodeVarint_inlined_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr (b0 :: bs1) rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
        (noPanicQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
      (noPanicQp s0) := by
  have hmulti := @decodeVarintMulti_cps_placed _ M A lim st rem caps H hS hvarint s0
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := hx28
  have h27 : s.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := hx27
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 :
        BitVec.ofNat 64 (bs1.length + 1) - 1#64 =
          BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]
      bv_omega
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 336#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (by simp only [hse, arm64_norm]))
    apply entails_of_eq
    unfold sliceCursorAfter
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm]
    sep_ac_rfl
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 264#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hmulti hfit
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simpa [arm64_norm] using hx28)
        (by simpa [arm64_norm] using hx27)
        (by simp only [arm64_norm])
        (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (List.cons_ne_nil b0 bs1)
        hlen hcont hnone)
    apply entails_of_eq
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [arm64_norm]
    sep_ac_rfl

theorem decodeKey_tail_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hS : TripleRatchetHooksWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (blkPl_85).base + 0x150#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_85).base + 0x16c#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  have herr := @decodeErrorFrom_tail_wp_placed _ M A lim st rem caps H hS s0
  have h24 : s.readReg64 (Reg.gpr 24#5) = key := hx24
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h26 : s.readReg64 (Reg.gpr 26#5) = 0x8000000000000002#64 := hregs.x26
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by
      unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have hres := hnone hdk
    subst hres
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    rw [memRegion48_split_296_304_312 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (herr (w0 := w0) (mErr := m) hfit
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (by simp only [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (wireSignalMessageLoopCapsOf_entails_loopOf (A.atState lim st _) (sp' + 176#64)
              bs.length caps m))))))))
        (decodeKey_err_entails (A.atState lim st _) sp' ptr w0 key bs rest bs.length m))
    dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq; sep_ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hres := hnone hdk
      subst hres
      have hge6 : 6 ≤ key.toNat % 8 := by
        match hk : key.toNat % 8 with
        | 0 | 1 | 2 | 3 | 4 | 5 => simp [WireType.ofNat?, hk] at hwt
        | n + 6 => omega
      have hbcs := key_and7_ule6_of_ge key hge6
      rw [memRegion48_split_296_304_312 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
      apply sepWP_seg_85; intro _m_strip
      wp_steps
      refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
      refine SepWPp.mono_pre ?_
        (herr (w0 := w0) (mErr := m) hfit
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          (by simp only [KindNoHeap, arm64_norm]))
      refine Entails.trans ?_
        (Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (wireSignalMessageLoopCapsOf_entails_loopOf (A.atState lim st _) (sp' + 176#64)
                bs.length caps m))))))))
          (decodeKey_err_entails (A.atState lim st _) sp' ptr w0 (key &&& 7#64) bs rest bs.length m))
      dsimp only [RustCliAllocBudget.atState]
      apply entails_of_eq; sep_ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := by
        match hk : key.toNat % 8 with
        | 0 | 1 | 2 | 3 | 4 | 5 => omega
        | n + 6 => simp [WireType.ofNat?, hk] at hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hres := hnone hdk
        subst hres
        have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_pre fun w0 => ?_
        refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
        apply sepWP_seg_85; intro _m_strip
        wp_steps
        refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
        refine SepWPp.mono_pre ?_
          (herr (w0 := w0) (mErr := m) hfit
            (by simp only [arm64_norm])
            (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
             by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
             by simpa [arm64_norm] using hregs.x19_eq⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcl1
            (by simpa [arm64_norm] using htr)
            (by simp only [KindNoHeap, arm64_norm]))
        refine Entails.trans
          (sepConj_mono_right
            (sepConj_mono (sliceCursorAfter_entails_memRegion (sp' + 160#64) ptr bs rest)
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right
                  (wireSignalMessageLoopCapsOf_entails_of A.repAlloc (sp' + 176#64) bs.length caps m))))))) ?_
        apply entails_of_eq
        simp only [arm64_norm]
        sep_ac_rfl
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 364#64) ?_
        apply sepWP_seg_85; intro _m_strip
        wp_steps
        refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        refine SepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
          (hcont (key.toNat / 8) wt _ hdk
            (by simp only [arm64_norm])
            (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
             by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
             by simpa [arm64_norm] using hregs.x19_eq⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcl1
            (by simpa [arm64_norm] using htr)
            (by simpa only [arm64_norm] using hand7_eq)
            (by simpa only [arm64_norm] using htag_eq))

theorem decodeKey_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (blkPl_85).base + 0x16c#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr (b0 :: bs1) rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
        (noPanicQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
      (noPanicQp s0) := by
  refine decodeVarint_inlined_cps_placed hS hvarint hfit hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1 =>
      decodeKey_tail_cps_placed hS hfit hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk)
        hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

/-! ## `skip_field` branch -/

theorem mergeSkipField_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} (hskip : SkipFieldOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_85).base + 0x0d0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) rest.length caps m)
        (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  have hcall := hskip
  let g_skip : SkipFieldGhost := ⟨wt, tag, 100, sp' + 288#64, sp' + 160#64, ptr, bs⟩
  have hfit_skip : FitsEnv M lim st (SkipFieldEnv g_skip) :=
    fitsEnv_sigLoop_errTail (fun _ => SigTryFromErrTailEnv.of_skipField) hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ skipFieldName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st (g_skip, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 220#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ sliceCursorAt (sp' + 160#64) ptr bs ∗
      stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 2 ^ 32 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 2 ^ 32 ∧ bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (SkipFieldEnv g_skip))
    (by
      dsimp only [g_skip]
      simp only [skipFieldSpecX, skipFieldSpecGen, skipFieldStackX, hsp_eq, h0, h1, arm64_norm]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide,
      hlen, hfit_skip⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  dsimp only [skipFieldSpecX, skipFieldSpecGen, g_skip]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    have hevs_nil : evs = [] := by
      rw [SkipFieldEnv, skipFieldEventsCore] at hevs
      dsimp only at hevs
      rw [hs] at hevs
      exact hevs
    subst hevs_nil
    simp only [M.stepEvents_nil, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 224#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont rest _ hs
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3
        (by simpa [arm64_norm] using htr2.trans htr))
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (wireSignalMessageLoopCapsOf_mono A.repAlloc (sp' + 176#64) m hrest_le))))))
    apply entails_of_eq
    simp only [skipFieldStackX, hsp_eq, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hs
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine sepWPp_end_noPanic_placed hcl2 ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
      evs, .done (SigTryFromErrTailEnv.of_skipField hevs), ?_⟩
    simp only [arm64_norm]
    refine Entails.trans ?_
      (loopExitMem_err_loopCaps_intro (A.atState lim (M.stepEvents evs st) _)
        sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 bs.length caps m)
    dsimp only [RustCliAllocBudget.atState]
    apply entails_of_eq
    simp only [skipFieldStackX, hsp_eq, arm64_norm]
    sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux1
