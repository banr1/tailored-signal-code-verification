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
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Loop Body: Tags 4, 5 & Dispatch

Relocatable `[LibsignalPlacement]` CPS proofs for the `bytes::merge` branches (`ciphertext` tag 4,
`pq_ratchet` tag 5) and tag dispatch (`+0x16c..+0x1c4`) on Block `85` under `TryFromLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux3

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSession (ProtoSignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalProtoCodec
  (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 LibsignalCodeRoLoaded decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost BytesMergeCapOk
   optVecU8At optU32At sliceCursorAt sliceCursorAfter
   decodeErrorHookStackX decodeVarintSliceStackX bytesMergeStackX skipFieldStackX
   bytesMergeName wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedProg LoopRegs
   wireSignalMessageAt_split_rk wireSignalMessageAt_split_ct wireSignalMessageAt_split_pq
   optVecU8At_none_split pointsTo64_emptyVec_eq_vecU8At
   optVecU8At_some_unfold cmn_one_ne_of_lt vecU8At_fold_of_pure
   vecU8At_rk_entails_wireSignalMessageOf
   vecU8At_ct_entails_wireSignalMessageOf
   vecU8At_pq_entails_wireSignalMessageOf
   mergeBytes_suffix tag_ge7_conds
   stackAt_sub_split memRegion48_split8 setWidth8_ofNat64 entails_of_eq)
open CryptoVerification.LibsignalTripleRatchet.Wire.TryFromLoopStateSimp
  (sp_setPC_pre sp_setMem_setPC_pre
   readReg64_setPC_pre readReg64_setMem_setPC_pre
   readReg32_setPC_pre readReg32_setMem_setPC_pre
   readReg_setPC_pre readReg_setMem_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore bmPreBoundBudget bytesMergeRawSpecGen bytesMergeRawSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced BytesMergeOkWPlaced
   bmNextCap bmExactPostVec bytesMergeExactRawSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromLoopBoundedEnv
   fitsEnv_sigLoop_bytesMerge optFieldCapMatch_init bmNextCap_lt_two_pow_63 mergeBytes_progress
   wireSignalMessageLoopCapsOf
   vecU8At_rk_entails_wireSignalMessageLoopCapsOf
   vecU8At_ct_entails_wireSignalMessageLoopCapsOf
   vecU8At_pq_entails_wireSignalMessageLoopCapsOf
   noPanicQp sepWPp_call_noPanic_placed sepWPp_mono_post
   loopExitPostPlaced loopExitPostPlaced_bytesStep
   sepWP_seg_85 sepWP_done_sync_pool_85 decodeErrorPush_tail_wp_placed)

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

/-! ## `ciphertext` (tag 4) and `pq_ratchet` (tag 5) `bytes::merge` branches -/

theorem initOptVecU8_ct_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x214#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x228#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A.repAlloc (sp' + 200#64) cap0 ptr0 v0 ∗
          A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A.repAlloc pin (sp' + 200#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 200#64 208#64 216#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 552#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 200#64 208#64 216#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 200#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 552#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 200#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

theorem mergeCiphertext_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_85).base + 0x214#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest evs₁ : List _) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .ct < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ct)) bs →
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
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) rest.length
            (caps.set .ct (bmNextCap (caps.get .ct) v.length))
            { m with ciphertext := some v })
        (loopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .ct (bmNextCap (caps.get .ct) v.length))
          s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  unfold wireSignalMessageLoopCapsOf
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun g => SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
  rw [wireSignalMessageAt_split_ct A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A.repAlloc g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A.repAlloc g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.ct (sp' + 200#64) m.ciphertext ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_ct_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hc_ct := hc.ct
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_init (cap0 := cap0) hc_ct hg.ct
      (by revert hc_ct hcap0; generalize m.ciphertext = x; cases x <;> intro h _ <;> exact h)
  have hcall := hbytes
  let x_arg : BytesMergeGhost :=
    ⟨wt, sp' + 200#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .ct hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 564#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 200#64) cap0 ptr0 v0 ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 24#64 = sp' + 200#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hcap0_ok, hfit_bm⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
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
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hprog := mergeBytes_progress hm
    have hevs_core : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .ct)) bs := by
      rw [BytesMergeEnv] at hevs; dsimp only at hevs; rwa [hcap0_bv] at hevs
    refine sepWPp_mono_post
      (fun _ _ => loopExitPostPlaced_bytesStep .ct (rem' := rest.length) hm hmax (by omega) hcap_lt hevs_core) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hcap', hcap_eq⟩ => ?_
    have hcap_eq' : cap'.toNat = bmNextCap caps.ct v.length := by rwa [hcap0_nat] at hcap_eq
    have hnext_lt : bmNextCap caps.ct v.length < 2 ^ 63 :=
      hcap0_nat ▸ bmNextCap_lt_two_pow_63 hcap0_ok (hcap0_nat ▸ hcap_lt) hlen hm
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs_core
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_ct_entails_wireSignalMessageLoopCapsOf A.repAlloc g sp' cap' ptr'
      rest.length caps m v (hg.mono hrest_le) hc hcap' hcap_eq' hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    have hevs_eq : evs = rustAllocEvents 72 8 := by
      simp [BytesMergeEnv, bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_eq
    have herr := @decodeErrorPush_tail_wp_placed _ M A lim st rem caps H hS s0
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with ciphertext := some v0 }) hfit
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_ct_entails_wireSignalMessageOf A.repAlloc g sp' cap0 ptr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

theorem initOptVecU8_pq_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x25c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x270#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A.repAlloc (sp' + 224#64) cap0 ptr0 v0 ∗
          A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A.repAlloc pin (sp' + 224#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 224#64 232#64 240#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 624#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 224#64 232#64 240#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 224#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 624#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 224#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

theorem mergePqRatchet_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_85).base + 0x25c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest evs₁ : List _) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .pq < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .pq)) bs →
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
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) rest.length
            (caps.set .pq (bmNextCap (caps.get .pq) v.length))
            { m with pqRatchet := some v })
        (loopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .pq (bmNextCap (caps.get .pq) v.length))
          s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  unfold wireSignalMessageLoopCapsOf
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun g => SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
  rw [wireSignalMessageAt_split_pq A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A.repAlloc g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A.repAlloc g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.pq (sp' + 224#64) m.pqRatchet ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_pq_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hc_pq := hc.pq
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_init (cap0 := cap0) hc_pq hg.pq
      (by revert hc_pq hcap0; generalize m.pqRatchet = x; cases x <;> intro h _ <;> exact h)
  have hcall := hbytes
  let x_arg : BytesMergeGhost :=
    ⟨wt, sp' + 224#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .pq hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 636#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 224#64) cap0 ptr0 v0 ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 48#64 = sp' + 224#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hcap0_ok, hfit_bm⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
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
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hprog := mergeBytes_progress hm
    have hevs_core : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .pq)) bs := by
      rw [BytesMergeEnv] at hevs; dsimp only at hevs; rwa [hcap0_bv] at hevs
    refine sepWPp_mono_post
      (fun _ _ => loopExitPostPlaced_bytesStep .pq (rem' := rest.length) hm hmax (by omega) hcap_lt hevs_core) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hcap', hcap_eq⟩ => ?_
    have hcap_eq' : cap'.toNat = bmNextCap caps.pq v.length := by rwa [hcap0_nat] at hcap_eq
    have hnext_lt : bmNextCap caps.pq v.length < 2 ^ 63 :=
      hcap0_nat ▸ bmNextCap_lt_two_pow_63 hcap0_ok (hcap0_nat ▸ hcap_lt) hlen hm
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs_core
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_pq_entails_wireSignalMessageLoopCapsOf A.repAlloc g sp' cap' ptr'
      rest.length caps m v (hg.mono hrest_le) hc hcap' hcap_eq' hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    have hevs_eq : evs = rustAllocEvents 72 8 := by
      simp [BytesMergeEnv, bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_eq
    have herr := @decodeErrorPush_tail_wp_placed _ M A lim st rem caps H hS s0
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with pqRatchet := some v0 }) hfit
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_pq_entails_wireSignalMessageOf A.repAlloc g sp' cap0 ptr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

theorem initOptVecU8_rk_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x1ec#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x200#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A.repAlloc (sp' + 176#64) cap0 ptr0 v0 ∗
          A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A.repAlloc pin (sp' + 176#64) u ∗ A.pool lim st s ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A.repAlloc pin sp' 176#64 184#64 192#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 => ?_
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 512#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' 176#64 184#64 192#64]
    apply entails_of_eq; sep_ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A.repAlloc pin (sp' + 176#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre fun hp => ?_
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 512#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ rfl
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A.repAlloc pin (sp' + 176#64) v0 hp]
    apply entails_of_eq; sep_ac_rfl

theorem mergeRatchetKey_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_85).base + 0x1ec#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest evs₁ : List _) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      caps.get .rk < 2 ^ 63 →
      evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .rk)) bs →
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
          A.pool lim (M.stepEvents evs₁ st) s1 ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) rest.length
            (caps.set .rk (bmNextCap (caps.get .rk) v.length))
            { m with ratchetKey := some v })
        (loopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length
          (caps.set .rk (bmNextCap (caps.get .rk) v.length))
          s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  unfold wireSignalMessageLoopCapsOf
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre fun g => SepWPp.pure_pre fun ⟨hg, hc⟩ => ?_
  rw [wireSignalMessageAt_split_rk A.repAlloc g sp' m]
  let F_msg := optVecU8At A.repAlloc g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A.repAlloc g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A.repAlloc g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A.repAlloc g.rk (sp' + 176#64) m.ratchetKey ∗ A.pool lim st s ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; sep_ac_rfl) ?_
  refine initOptVecU8_rk_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hc_rk := hc.rk
  obtain ⟨hcap0_ok, hcap0_bv, hcap0_nat, hcap_lt⟩ :=
    optFieldCapMatch_init (cap0 := cap0) hc_rk hg.rk
      (by revert hc_rk hcap0; generalize m.ratchetKey = x; cases x <;> intro h _ <;> exact h)
  have hcall := hbytes
  let x_arg : BytesMergeGhost :=
    ⟨wt, sp' + 176#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv x_arg) :=
    fitsEnv_sigLoop_bytesMerge .rk hcap0_bv hcap_lt hmax hfit
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl2 => ?_
  refine sepWPp_call_noPanic_placed A lim st (x_arg, st) hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 524#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A.repAlloc (sp' + 176#64) cap0 ptr0 v0 ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length ∧ FitsEnv M lim st (BytesMergeEnv x_arg))
    (by
      simp only [bytesMergeExactRawSpecX, bytesMergeRawSpecX, bytesMergeRawSpecGen, bmPreBoundBudget,
        bytesMergeStackX, decodeVarintSliceStackX, x_arg, hsp_eq, h0, arm64_norm, true_and]
      sep_ac_rfl)
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, hlen, hcap0_ok, hfit_bm⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
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
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hprog := mergeBytes_progress hm
    have hevs_core : evs = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get .rk)) bs := by
      rw [BytesMergeEnv] at hevs; dsimp only at hevs; rwa [hcap0_bv] at hevs
    refine sepWPp_mono_post
      (fun _ _ => loopExitPostPlaced_bytesStep .rk (rem' := rest.length) hm hmax (by omega) hcap_lt hevs_core) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun cap' => SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hcap', hcap_eq⟩ => ?_
    have hcap_eq' : cap'.toNat = bmNextCap caps.rk v.length := by rwa [hcap0_nat] at hcap_eq
    have hnext_lt : bmNextCap caps.rk v.length < 2 ^ 63 :=
      hcap0_nat ▸ bmNextCap_lt_two_pow_63 hcap0_ok (hcap0_nat ▸ hcap_lt) hlen hm
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents evs st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (hcont v rest evs _ hm hcap_lt hevs_core
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_rk_entails_wireSignalMessageLoopCapsOf A.repAlloc g sp' cap' ptr'
      rest.length caps m v (hg.mono hrest_le) hc hcap' hcap_eq' hnext_lt
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    have hevs_eq : evs = rustAllocEvents 72 8 := by
      simp [BytesMergeEnv, bytesMergeEventsCore, hm] at hevs
      exact hevs
    subst hevs_eq
    have herr := @decodeErrorPush_tail_wp_placed _ M A lim st rem caps H hS s0
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => ?_
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    apply sepWP_seg_85; intro _m_strip2
    wp_steps
    refine sepWP_done_sync_pool_85 A lim (M.stepEvents (rustAllocEvents 72 8) st) fun _ hcl4 => ?_
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5))
        (mErr := { m with ratchetKey := some v0 }) hfit
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne)
    have hmsg := vecU8At_rk_entails_wireSignalMessageOf A.repAlloc g sp' cap0 ptr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right hmsg))))))))
    apply entails_of_eq
    simp only [bytesMergeStackX, decodeVarintSliceStackX, hstack, hsp_eq, F_msg, arm64_norm]
    sep_ac_rfl

/-! ## Tag dispatch (`+0x16c..+0x1c4`) -/

private theorem dispatch_tag_ge7_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64} {n : ℕ}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x16c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (n + 7))
    (htag_lt : n + 7 < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h7 : 7 ≤ n + 7 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x0d0#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 (n + 7) →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s (A.pool lim st s ∗ F) Q Qp := by
  have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 7) := hx1
  obtain ⟨hc1, hc2, hc3, hc3_ne, hc4, hc5, hc6, hc6_ne⟩ := tag_ge7_conds (n + 7) (by omega) htag_lt
  cases hgt : BitVec.slt 3#32 ((BitVec.ofNat 64 (n + 7)).setWidth 32)
  · refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 208#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h7 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 208#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h7 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr

theorem dispatch_tag_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64} {tag : ℕ}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x16c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x1ec#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x23c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x18c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h4 : tag = 4 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x214#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h5 : tag = 5 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x25c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h6 : tag = 6 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x1c4#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h7 : 7 ≤ tag → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x0d0#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 (A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s (A.pool lim st s ∗ F) Q Qp := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 492#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h1 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 572#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h2 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 396#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h3 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 532#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h4 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 604#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h5 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 6#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 452#64) ?_
    apply sepWP_seg_85; intro _m_strip
    wp_steps
    refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
    exact h6 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · exact dispatch_tag_ge7_cps_placed hpc hrun hregs hx1 htag_lt hsp hcl htr h7

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux3
