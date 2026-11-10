/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux1
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux2
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux3
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Decode Loop Induction

Relocatable `[LibsignalPlacement]` field-merge dispatch, cursor advance, empty-slice exit, and
fuel-inductive protobuf decode loop theorems (`decodeLoop_e0_wp_placed`, `decodeLoop_f0_wp_placed`)
on Block `85` under `TryFromLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSession (ProtoSignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey mergeField decodeLoop emptyProtoSignalMessage recursionLimit)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter skipFieldStackX wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedProg LoopRegs
   sliceCursorAfter_eq_take_cursorAt loopExitMem_ok_intro
   cons_len_bv64_ne_zero decodeKey_suffix mergeUint32_suffix skipField_suffix
   mergeField_suffix entails_of_eq)
open CryptoVerification.LibsignalTripleRatchet.Wire.TryFromLoopStateSimp
  (sp_setPC_pre sp_setMem_setPC_pre
   readReg64_setPC_pre readReg64_setMem_setPC_pre
   readReg32_setPC_pre readReg32_setMem_setPC_pre
   readReg_setPC_pre readReg_setMem_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DecodeVarintSliceOkWPlaced Int32MergeOkWPlaced
   SkipFieldOkWPlaced BytesMergeOkWPlaced bmNextCap)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromLoopBoundedEnv TryFromLoopEnv
   mergeBytes_progress
   fitsEnv_sigLoop_bytesTail fitsEnv_sigLoop_skipStep fitsEnv_sigLoop_mono_rem
   wireSignalMessageLoopCapsOf wireSignalMessageLoopCapsOf_mono
   wireSignalMessageLoopCapsOf_entails_of wireSignalMessageOf_emptyMsg_entails_loopCapsOf
   noPanicQp sepWPp_frame_noPanic sepWPp_end_noPanic_placed sepWPp_mono_post
   loopExitPostPlaced loopExitPostPlaced_mono_rem loopExitPostPlaced_skipStep
   loopExitPostPlaced_append_prefix
   sepWP_seg_85 sepWP_done_sync_pool_85)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux1
  (decodeKey_cps_placed mergeSkipField_cps_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux2
  (mergePrevCounter_cps_placed mergeCounter_cps_placed mergeAddresses_cps_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudgetAux3
  (mergeCiphertext_cps_placed mergePqRatchet_cps_placed mergeRatchetKey_cps_placed
   dispatch_tag_cps_placed)

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

/-! ## Field merge dispatch and cursor advance -/

theorem mergeField_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hbs_lt : bs.length < rem)
    (hpc : s.pc = (blkPl_85).base + 0x16c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : ProtoSignalMessage) (rest : List (BitVec 8))
      (caps' : SigTryFromCaps) (evs₁ : List AllocEvent) (s1 : State),
      mergeField m tag wt bs = some (m', rest) →
      FitsEnv M lim (M.stepEvents evs₁ st) (SigTryFromLoopBoundedEnv rest.length caps') →
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
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) rest.length caps' m')
        (loopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length caps'
          s0 sp' x19 x20 x21 x23 ptr bs res)
        (noPanicQp s0))
    (hnone : mergeField m tag wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  let F_body := sliceCursorAt (sp' + 160#64) ptr bs ∗
    ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
    memRegion (sp' + 296#64) 48 ∗
    stackAt sp' (skipFieldStackX 100) ∗
    wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m
  refine SepWPp.mono_pre (P' := A.pool lim st s ∗ F_body)
    (by apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl) ?_
  refine dispatch_tag_cps_placed hpc hrun hregs hx1 htag_ge htag_lt hsp hcl htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcl1 htr1 => ?_)
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergeRatchetKey_cps_placed hS hbytes hfit (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest evs₁ s2 hm hcap_lt hevs₁ =>
          hcont { m with ratchetKey := some v } rest
            (caps.set .rk (bmNextCap (caps.get .rk) v.length)) evs₁ s2
            (by simp [mergeField, hm])
            (fitsEnv_sigLoop_bytesTail .rk hm (by omega)
              (by have := mergeBytes_progress hm; omega) hcap_lt hevs₁ hfit))
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergeCounter_cps_placed hS hint32 hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
          obtain ⟨k, _, hrest_eq⟩ := mergeUint32_suffix hm
          have hrest_lt : rest.length < rem := by simp [hrest_eq]; omega
          have hfit' : FitsEnv M lim (M.stepEvents [] st)
              (SigTryFromLoopBoundedEnv rest.length caps) := by
            rw [M.stepEvents_nil]; exact fitsEnv_sigLoop_skipStep hrest_lt hfit
          have hc2 := hcont { m with counter := some v } rest caps [] s2
            (by simp [mergeField, hm]) hfit' hpc2 hrun2 hregs2 hsp2 hcl2 htr2
          rw [M.stepEvents_nil] at hc2
          exact sepWPp_mono_post (fun _ _ => loopExitPostPlaced_skipStep hrest_lt) hc2)
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergePrevCounter_cps_placed hS hint32 hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
          obtain ⟨k, _, hrest_eq⟩ := mergeUint32_suffix hm
          have hrest_lt : rest.length < rem := by simp [hrest_eq]; omega
          have hfit' : FitsEnv M lim (M.stepEvents [] st)
              (SigTryFromLoopBoundedEnv rest.length caps) := by
            rw [M.stepEvents_nil]; exact fitsEnv_sigLoop_skipStep hrest_lt hfit
          have hc2 := hcont { m with previousCounter := some v } rest caps [] s2
            (by simp [mergeField, hm]) hfit' hpc2 hrun2 hregs2 hsp2 hcl2 htr2
          rw [M.stepEvents_nil] at hc2
          exact sepWPp_mono_post (fun _ _ => loopExitPostPlaced_skipStep hrest_lt) hc2)
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergeCiphertext_cps_placed hS hbytes hfit (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest evs₁ s2 hm hcap_lt hevs₁ =>
          hcont { m with ciphertext := some v } rest
            (caps.set .ct (bmNextCap (caps.get .ct) v.length)) evs₁ s2
            (by simp [mergeField, hm])
            (fitsEnv_sigLoop_bytesTail .ct hm (by omega)
              (by have := mergeBytes_progress hm; omega) hcap_lt hevs₁ hfit))
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergePqRatchet_cps_placed hS hbytes hfit (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest evs₁ s2 hm hcap_lt hevs₁ =>
          hcont { m with pqRatchet := some v } rest
            (caps.set .pq (bmNextCap (caps.get .pq) v.length)) evs₁ s2
            (by simp [mergeField, hm])
            (fitsEnv_sigLoop_bytesTail .pq hm (by omega)
              (by have := mergeBytes_progress hm; omega) hcap_lt hevs₁ hfit))
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · subst htag
    refine SepWPp.mono_pre ?_
      (mergeAddresses_cps_placed hS hbytes hfit (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0)
        hsp1 hcl1 htr1 hlen
        (fun v rest evs₁ s2 hm hcap_lt hevs₁ =>
          hcont { m with addresses := some v } rest
            (caps.set .ad (bmNextCap (caps.get .ad) v.length)) evs₁ s2
            (by simp [mergeField, hm])
            (fitsEnv_sigLoop_bytesTail .ad hm (by omega)
              (by have := mergeBytes_progress hm; omega) hcap_lt hevs₁ hfit))
        (fun hm => hnone (by simp [mergeField, hm])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    refine SepWPp.mono_pre ?_
      (mergeSkipField_cps_placed hskip hfit hpc1 hrun1 hregs1
        (hx0_1.trans hx0) hx1_1 htag_lt hsp1 hcl1 htr1 hlen
        (fun rest s2 hs hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
          obtain ⟨k, _, hrest_eq⟩ := skipField_suffix hs
          have hrest_lt : rest.length < rem := by simp [hrest_eq]; omega
          have hfit' : FitsEnv M lim (M.stepEvents [] st)
              (SigTryFromLoopBoundedEnv rest.length caps) := by
            rw [M.stepEvents_nil]; exact fitsEnv_sigLoop_skipStep hrest_lt hfit
          have hc2 := hcont m rest caps [] s2
            (by simp [mergeField, recursionLimit, hs]) hfit' hpc2 hrun2 hregs2 hsp2 hcl2 htr2
          rw [M.stepEvents_nil] at hc2
          exact sepWPp_mono_post (fun _ _ => loopExitPostPlaced_skipStep hrest_lt) hc2)
        (fun hs => hnone (by simp [mergeField, recursionLimit, hs])))
    apply entails_of_eq; dsimp only [F_body]; sep_ac_rfl

theorem advance_cursor_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {res : Option ProtoSignalMessage} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest res)
      (noPanicQp s0)) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗ R)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 160#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 160#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepWPp_frame_noPanic h (fun _ _ hqm => loopExitPostPlaced_append_prefix hkl hqm)

/-! ## Loop header checks and fuel induction -/

theorem loopExitEmpty_298_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x298#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hres : res = some m) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr bs res)
      (noPanicQp s0) := by
  subst hres
  refine sepWPp_end_noPanic_placed hcl ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
    by simpa [arm64_norm] using hregs.x19_eq⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcl1,
    by simpa [arm64_norm] using htr⟩, [], .done .nil, ?_⟩
  simp only [M.stepEvents_nil, arm64_norm]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (wireSignalMessageLoopCapsOf_entails_of A.repAlloc (sp' + 176#64) bs.length caps m)))))) ?_
  refine Entails.trans ?_
    (loopExitMem_ok_intro (A.atState lim st _) sp' ptr bs m)
  dsimp only [RustCliAllocBudget.atState]
  apply entails_of_eq; sep_ac_rfl

theorem loopCheck_e0_empty_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0e0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hres : res = some m) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr [] ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) ([] : List (BitVec 8)).length caps m)
      (loopExitPostPlaced A lim st rem caps s0 sp' x19 x20 x21 x23 ptr [] res)
      (noPanicQp s0) := by
  have hexit := @loopExitEmpty_298_wp_placed _ M A lim st rem caps H s0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 664#64) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre ?_
    (hexit (sp' := sp') (x19 := x19) (x20 := x20) (x21 := x21) (x23 := x23)
      (ptr := ptr) (bs := []) (m := m) (res := res)
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcl1 htr hres)
  unfold sliceCursorAt
  apply entails_of_eq; sep_ac_rfl

theorem loopCheck_e0_cons_cps_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x0e0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x0f0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x28 = sp' + 160#64 →
      s1.readReg64 .x27 = sp' + 168#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ A.pool lim st s ∗ F) Q Qp := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 240#64) ?_
  apply sepWP_seg_85; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_85 A lim st fun _ hcl1 => ?_
  refine SepWPp.mono_pre ?_
    (hcont _
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcl1 htr)
  unfold sliceCursorAt
  apply entails_of_eq; sep_ac_rfl

theorem decodeLoop_f0_step_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {caps : SigTryFromCaps}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage}
    (ih : ∀ {st : M.σ} {caps : SigTryFromCaps} {s : State} {ptr : BitVec 64}
      {bs : List (BitVec 8)} {m : ProtoSignalMessage},
      FitsEnv M lim st (SigTryFromLoopBoundedEnv bs.length caps) →
      s.pc = (blkPl_85).base + 0x0e0#64 →
      s.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s
        (sliceCursorAt (sp' + 160#64) ptr bs ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st bs.length caps
          s0 sp' x19 x20 x21 x23 ptr bs (decodeLoop fuel m bs))
        (noPanicQp s0))
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv (b0 :: bs1).length caps))
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m)
      (loopExitPostPlaced A lim st (b0 :: bs1).length caps
        s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1)
        (decodeLoop (fuel + 1) m (b0 :: bs1)))
      (noPanicQp s0) := by
  refine decodeKey_cps_placed hS hvarint hfit
    hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [decodeLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine advance_cursor_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (wireSignalMessageLoopCapsOf_mono A.repAlloc (sp' + 176#64)
        (m := rest1.length) (n := (b0 :: bs1).length) m (by omega))))))) ?_
  refine mergeField_cps_placed hS hint32 hskip hbytes hfit (by omega)
    hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt hsp1 hcl1 htr1 (by omega)
    (fun m' rest2 caps' evs₁ s2 hmf hfit2 hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => ?_)
    (fun hmf_none => by simp [decodeLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := mergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  refine advance_cursor_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : decodeLoop (fuel + 1) m (b0 :: bs1) = decodeLoop fuel m' rest2 := by
    simp [decodeLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hfit2 hpc2 hrun2 hregs2 hsp2 hcl2 htr2 (by omega) (by omega)

theorem decodeLoop_e0_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 : State} {sp' x19 x20 x21 x23 : BitVec 64} :
    ∀ (fuel : ℕ) {st : M.σ} {caps : SigTryFromCaps} {s : State} {ptr : BitVec 64}
      {bs : List (BitVec 8)} {m : ProtoSignalMessage},
      FitsEnv M lim st (SigTryFromLoopBoundedEnv bs.length caps) →
      s.pc = (blkPl_85).base + 0x0e0#64 →
      s.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s
        (sliceCursorAt (sp' + 160#64) ptr bs ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) bs.length caps m)
        (loopExitPostPlaced A lim st bs.length caps
          s0 sp' x19 x20 x21 x23 ptr bs (decodeLoop fuel m bs))
        (noPanicQp s0)
  | 0, _, _, s, ptr, bs, m, _, hpc, hrun, hregs, hsp, hcl, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopCheck_e0_empty_wp_placed hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, st, caps, s, ptr, bs, m, hfit, hpc, hrun, hregs, hsp, hcl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheck_e0_empty_wp_placed hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 =>
      let F_tail := memRegion (sp' + 296#64) 48 ∗
        stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopCapsOf A.repAlloc (sp' + 176#64) (b0 :: bs1).length caps m
      refine SepWPp.mono_pre
        (P' := sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ A.pool lim st s ∗ F_tail)
        (by apply entails_of_eq; dsimp only [F_tail]; sep_ac_rfl) ?_
      refine loopCheck_e0_cons_cps_placed hpc hrun hregs hsp hcl htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx28_1 hx27_1 hx2_1 hsp1 hcl1 htr1
      refine SepWPp.mono_pre ?_
        (decodeLoop_f0_step_wp_placed hS hvarint hint32 hskip hbytes
          (decodeLoop_e0_wp_placed hS hvarint hint32 hskip hbytes fuel)
          hfit hpc1 hrun1 hregs1 hx28_1 hx27_1 hx2_1 hsp1 hcl1 htr1 hfuel hlen)
      apply entails_of_eq; dsimp only [F_tail]; sep_ac_rfl

theorem decodeLoop_f0_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage}
    (hfit : FitsEnv M lim st (TryFromLoopEnv (2 * (fuel + 1) + 2) maxLen))
    (hmax : (b0 :: bs1).length ≤ maxLen)
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hm : m = emptyProtoSignalMessage := by rfl) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A.repAlloc (sp' + 176#64) m)
      (loopExitPostPlaced A lim st maxLen SigTryFromCaps.zero
        s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1)
        (decodeLoop (fuel + 1) m (b0 :: bs1)))
      (noPanicQp s0) := by
  subst hm
  refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (wireSignalMessageOf_emptyMsg_entails_loopCapsOf A.repAlloc
        (sp' + 176#64) (b0 :: bs1).length)))))) ?_
  exact sepWPp_mono_post (fun _ _ => loopExitPostPlaced_mono_rem hmax)
    (decodeLoop_f0_step_wp_placed hS hvarint hint32 hskip hbytes
      (decodeLoop_e0_wp_placed hS hvarint hint32 hskip hbytes fuel)
      (fitsEnv_sigLoop_mono_rem hmax hfit)
      hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hfuel hlen)

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudget
