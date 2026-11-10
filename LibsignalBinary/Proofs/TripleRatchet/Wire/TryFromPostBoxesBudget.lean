/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Post-Loop Box Conversion & Packing for `<SignalMessage>::try_from`

Defines capacity- and slice-indexed allocator event envelopes (`IntoBoxedCapEnv`, `PostCtBoxesEnv`,
`PostClonePackEnv`) and proves relocatable `[LibsignalPlacement]` budget-threaded post-loop
box-conversion and `SignalMessage` packing lemmas on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession
  (SignalMessage SignalProtocolError)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (VecArg TryCloneSliceCall boxU8Buf
   blkPC_85 blkPl_85 blkLib_eq_85 withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr
  (speAt signalMessageResultAt speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropSpeName DropSpeGhost dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (skipFieldStackX)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg PostEpilogueStatePlaced
   vecU8Buf vecU8Buf_zero vecU8Buf_dealloc vecU8At_eq_header_buf optVecU8Buf
   optVecU8Buf_pq_to_vecU8Buf post_memRegion48_split24 vecHeader_memRegion24_entails_48
   optBoxU8Pending memRegion104_unpack_x19 msgResultAt_ok_intro
   pkBytesOf pkLayoutAt pkRestAt sevenBytesHeadAt sevenBytesTailAt sevenBytesHeadAt_eq_tailAt
   slt_noneCap_one cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero cap_add1_eq_of_lt
   pure_true_emp stackAt_sub_split entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (intoBoxedSliceName tryCloneFromRefName intoBoxedSliceStackX tryCloneFromRefStackX
   intoBoxedSliceEvents IntoBoxedSliceEnv intoBoxedSliceSpecWithStack intoBoxedSliceSpecX
   tryCloneFromRefEvents TryCloneFromRefEnv tryCloneFromRefSpecWithStack tryCloneFromRefSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DropSpeOkWPlaced IntoBoxedSliceOkPlaced TryCloneFromRefOkPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
  (blk85_noSvc0 postNoPanicQp wpp_sync_pre wpp_frame_noPanic
   wpp_of_sepWP_end_noPanic_placed cleanup_698_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget (wpp_call_s)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm]
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

local macro "wp_steps_sync_boxes85 " mid:term : tactic => `(tactic| (
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_85).rebase (blkPl_85).base (hooksException _))
    blkLib_eq_85 blk85_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done
    (by first | wp_norm_lhs | simp [arm64_norm])
    (by wp_norm_lhs) fun _m_real _hnsp => ?_
  first
    | refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
    | refine ProofLib.SepWP.transport_atStatePool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
))

/-! ## Allocator event envelopes for box conversion and cloning -/

/-- Capacity-and-slice allocator event list of `<Vec<u8>>::into_boxed_slice`
(`intoBoxedSliceEvents x = intoBoxedCapEvents x.cap x.bytes`). -/
def intoBoxedCapEvents (cap : BitVec 64) (bs : List (BitVec 8)) : List AllocEvent :=
  if cap.toNat ≤ bs.length then []
  else if bs = [] then rustDeallocEvents cap.toNat 1
  else rustReallocEvents cap.toNat bs.length 1

/-- Capacity-and-slice allocator event envelope of `<Vec<u8>>::into_boxed_slice`. -/
def IntoBoxedCapEnv (cap : BitVec 64) (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = intoBoxedCapEvents cap bs

/-- Optional-slice allocator event envelope for `m'.addresses` in `post_ct_some_boxes_wp_placed`. -/
def IntoBoxedOptCapEnv (adCap : BitVec 64) :
    Option (List (BitVec 8)) → List AllocEvent → Prop
  | none => (· = [])
  | some ad => IntoBoxedCapEnv adCap ad

/-- Precondition budget envelope of `post_ct_some_boxes_wp_placed`:
a `FreeOnlyEvs` prefix (`drop_in_place::<SignalProtocolError>`) followed by `into_boxed_slice`
on `ciphertext` and (when `some`) `addresses`. -/
def PostCtBoxesEnv (ctCap adCap : BitVec 64) (ct : List (BitVec 8))
    (adOpt : Option (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs (SeqEnv (IntoBoxedCapEnv ctCap ct) (IntoBoxedOptCapEnv adCap adOpt))

/-- Postcondition event relation of `post_ct_some_boxes_wp_placed` recording the three
sequential event segments (`FreeOnlyEvs`, `IntoBoxedCapEnv ctCap ct`, `IntoBoxedOptCapEnv adCap adOpt`)
so callers can project `FitsEnv` for subsequent allocations via `FitsEnv.seq_right`. -/
def PostCtBoxesPost (ctCap adCap : BitVec 64) (ct : List (BitVec 8))
    (adOpt : Option (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  ∃ evs₀ evs₁ evs₂ : List AllocEvent,
    evs = evs₀ ++ evs₁ ++ evs₂ ∧
    FreeOnlyEvs evs₀ ∧
    IntoBoxedCapEnv ctCap ct evs₁ ∧
    IntoBoxedOptCapEnv adCap adOpt evs₂

/-- Slice-only allocator event list of `<Box<[u8]>>::try_clone_from_ref_in`
(`tryCloneFromRefEvents x = tryCloneBytesEvents x.bs`). -/
def tryCloneBytesEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs = [] then [] else rustAllocEvents bs.length 1

/-- Slice-only allocator event envelope of `<Box<[u8]>>::try_clone_from_ref_in`. -/
def TryCloneBytesEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = tryCloneBytesEvents bs

/-- Postcondition event envelope of `post_clone_and_pack_wp_placed`:
`try_clone_from_ref_in` on `msg.serialized` followed by `FreeOnlyEvs` (`rk` buffer dealloc). -/
def PostClonePackEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (TryCloneBytesEnv bs) FreeOnlyEvs

/-! ## Relocatable `[LibsignalPlacement]` box conversion and packing lemmas (Block `85`) -/

theorem post_ct_some_boxes_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x20 x21 x23 x24 ctCap ctPtr pqCap pqPtr pqLen adCap adPtr adLen w48 w136 w144 w152 : BitVec 64}
    {w60 prevCounter : BitVec 32}
    (ct : List (BitVec 8)) (pqOpt adOpt : Option (List (BitVec 8)))
    (hct_lt : ctCap.toNat < 2 ^ 63)
    (hFit : FitsEnv M lim st (PostCtBoxesEnv ctCap adCap ct adOpt))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1400#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 ctCap 1#64)
    (hx8 : s.readReg64 .x8 = prevCounter.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = x20)
    (hx21 : s.readReg64 .x21 = x21) (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg64 .x24 = x24)
    (hx25 : s.readReg64 .x25 = pqCap) (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1728#64) s
      (((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗
        ((sp' + 60#64) ↦₃₂ w60) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗
        ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        vecU8Buf A.repAlloc ctCap ctPtr ct ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen pqOpt ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen adOpt ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        ∃ pqCap' pqPtr' ctBoxPtr adBoxPtr w96 : BitVec 64,
        ∃ evs : List AllocEvent,
          PostCtBoxesPost ctCap adCap ct adOpt evs ∧
          PostEpilogueStatePlaced s0 sp' sf ∧
          sf.pc = (blkPl_85).base + 1728#64 ∧
          sf.status = .Running ∧
          sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
          sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = adBoxPtr ∧
          sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = x24 ∧
          sf.readReg64 .x25 = pqCap' ∧
          sf.readReg64 .x26 = BitVec.ofNat 64 ct.length ∧
          sf.readReg64 .x27 = BitVec.ofNat 64 (pqOpt.getD []).length ∧
          sf.readReg64 .x28 = pqPtr' ∧
          (Pf ⊢ ((sp' + 16#64) ↦₆₄ adLen) ∗
            ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
            ((sp' + 40#64) ↦₆₄ pqLen) ∗
            ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
            ((sp' + 60#64) ↦₃₂ prevCounter) ∗
            ((sp' + 88#64) ↦₆₄ adPtr) ∗
            ((sp' + 96#64) ↦₆₄ w96) ∗
            vecHeader (sp' + 136#64) ctCap ctPtr (BitVec.ofNat 64 ct.length) ∗
            memRegion (sp' + 176#64) 48 ∗
            vecU8Buf A.repAlloc pqCap' pqPtr' (pqOpt.getD []) ∗
            boxU8Buf A.repAlloc ctBoxPtr ct ∗
            optBoxU8Pending A.repAlloc adBoxPtr w96 adOpt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallSpe := hDropSpe
  have hcallBox := hIntoBox
  clear hDropSpe hIntoBox
  have hct_eq := cap_add1_eq_of_lt hct_lt
  have hpq_ent := optVecU8Buf_pq_to_vecU8Buf A.repAlloc pqCap pqPtr pqLen pqOpt
  dsimp only at hpq_ent
  refine WSepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpq_ent)))))))))))) ?_
  simp only [sepConj_assoc]
  refine WSepWPp.mono_pre (P' :=
      ⌜(if (pqCap + 1#64 == 0#64) then 0#64 else pqLen) = BitVec.ofNat 64 (pqOpt.getD []).length⌝ ∗
      (((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗
        ((sp' + 60#64) ↦₃₂ w60) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗
        ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        vecU8Buf A.repAlloc ctCap ctPtr ct ∗
        vecU8Buf A.repAlloc (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
          (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD []) ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen adOpt ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine WSepWPp.pure_pre fun hpq_len => ?_
  clear hpq_ent
  have hstackSpe := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStackX (skipFieldStackX 100)
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps_sync_boxes85 ((blkPl_85).ρ dropSpeName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  have hspe_eq : speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine wpp_call_s ((⟨sp' + 176#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + 1416#64) (by simp [arm64_norm])
    (fun s1 => speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding ∗
      A.pool lim st s1 ∗ stackAt sp' dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_85).base + 1416#64))
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    ⟨rfl, ⟨85, by decide, 1416, by decide, rfl⟩⟩
    (by rw [hspe_eq, hstackSpe]; sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine WSepWPp.exists_pre fun evs₀ => ?_
  refine WSepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_left_comm (memRegion (sp' + 176#64) 48) ⌜FreeOnlyEvs evs₀⌝]
  refine WSepWPp.pure_pre fun hfree₀ => ?_
  refine WSepWPp.mono_pre (P' :=
      memRegion (sp' + 176#64) 48 ∗ A.pool lim (M.stepEvents evs₀ st) s2 ∗
        stackAt sp' (skipFieldStackX 100) ∗
        ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₆₄ w48) ∗
        ((sp' + 60#64) ↦₃₂ prevCounter) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        ((sp' + 136#64) ↦₆₄ w136) ∗ ((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗
        vecU8Buf A.repAlloc ctCap ctPtr ct ∗
        vecU8Buf A.repAlloc (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
          (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD []) ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen adOpt)
    (by
      dsimp only [vecHeader]
      apply entails_of_eq
      simp only [hstackSpe, hsp_eq, arm64_norm]
      sep_ac_rfl) ?_
  have hFit1 := hFit.seq_right hfree₀
  set st₁ := M.stepEvents evs₀ st
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, _, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
  refine WSepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).ρ intoBoxedSliceName) ?_
  wp_steps_sync_boxes85 ((blkPl_85).ρ intoBoxedSliceName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  have hvec_ct : vecU8At A.repAlloc (sp' + 136#64) ctCap ctPtr ct =
      ((sp' + 136#64) ↦₆₄ ctCap) ∗ ((sp' + 144#64) ↦₆₄ ctPtr) ∗
        ((sp' + 152#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗ vecU8Buf A.repAlloc ctCap ctPtr ct := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  set x_ct : VecArg := ⟨sp' + 136#64, ctCap, ctPtr, ct⟩
  refine wpp_call_s (x_ct, st₁) hcallBox
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hcl3
    (ret_pc := (blkPl_85).base + 1436#64) (by simp [arm64_norm])
    (fun s3 => vecU8At A.repAlloc (sp' + 136#64) ctCap ctPtr ct ∗
      A.pool lim st₁ s3 ∗ stackAt sp' intoBoxedSliceStackX)
    (φ := sp' + 136#64 = sp' + 136#64 ∧ FitsEnv M lim st₁ (IntoBoxedCapEnv ctCap ct))
    (by
      dsimp only [intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack,
        IntoBoxedSliceEnv, intoBoxedSliceEvents, IntoBoxedCapEnv, intoBoxedCapEvents, VecArg.at, x_ct]
      simp only [hsp2_eq, arm64_norm]
      rfl)
    ⟨rfl, hFit1.seq_left⟩
    (by rw [hvec_ct, hstackBox]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hcl4 hcs4
  dsimp only [intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack]
  rw [sepConj_assoc]
  refine WSepWPp.pure_pre (fun ⟨hx1_4, htr4⟩ => ?_)
  set st₂ := M.stepEvents (intoBoxedSliceEvents x_ct) st₁
  have hct_env : IntoBoxedCapEnv ctCap ct (intoBoxedSliceEvents x_ct) := rfl
  rcases hcs4 with ⟨hx19_4cs, hx20_4cs, hx21_4cs, hx22_4cs, hx23_4cs, hx24_4cs, hx25_4cs, _⟩
  have hsp4_eq : s4.sp = sp' := by simp [hsp4, hsp2_eq, arm64_norm]
  have htr4_eq : s4.trace = s0.trace := by simp [htr4, htr2_eq, arm64_norm]
  have hx19_4 : s4.readReg64 .x19 = x19 := by simp [hx19_4cs, hx19_2, arm64_norm]
  have hx20_4 : s4.readReg64 .x20 = x20 := by simp [hx20_4cs, hx20_2, arm64_norm]
  have hx21_4 : s4.readReg64 .x21 = x21 := by simp [hx21_4cs, hx21_2, arm64_norm]
  have hx22_4 : s4.readReg64 .x22 = adCap := by simp [hx22_4cs, hx22_2, arm64_norm]
  have hx23_4 : s4.readReg64 .x23 = x23 := by simp [hx23_4cs, hx23_2, arm64_norm]
  have hx24_4 : s4.readReg64 .x24 = x24 := by simp [hx24_4cs, hx24_2, arm64_norm]
  have hx25_4 : s4.readReg64 .x25 = pqCap := by simp [hx25_4cs, hx25_2, arm64_norm]
  cases adOpt with
  | none =>
    clear hcallBox
    dsimp only [optVecU8Buf]
    refine WSepWPp.mono_pre (P' := ⌜adCap = noneCap⌝ ∗
        (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
          ((sp' + 136#64) ↦₆₄ ctCap) ∗ ((sp' + 144#64) ↦₆₄ ctPtr) ∗
          ((sp' + 152#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
          boxU8Buf A.repAlloc (s4.readReg64 .x0) ct ∗
          A.pool lim st₂ s4 ∗ stackAt sp' (skipFieldStackX 100) ∗
          ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₆₄ w48) ∗ ((sp' + 60#64) ↦₃₂ prevCounter) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          memRegion (sp' + 176#64) 48 ∗
          vecU8Buf A.repAlloc (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
            (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD [])))
      (by
        dsimp only [vecHeader, x_ct]
        apply entails_of_eq
        simp only [hstackBox, hsp2_eq, arm64_norm]
        sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun hadCap => ?_
    subst hadCap
    refine wpp_of_sepWP_end_noPanic_placed hcl4 ?_
    wp_steps_sync_boxes85 ((blkPl_85).base + 1728#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl5
    refine ⟨if (pqCap + 1#64 == 0#64) then 0#64 else pqCap,
      if (pqCap + 1#64 != 0#64) then pqPtr else 1#64,
      s4.readReg64 .x0, 0#64, pqPtr,
      evs₀ ++ intoBoxedSliceEvents x_ct,
      ⟨evs₀, intoBoxedSliceEvents x_ct, [], by simp, hfree₀, hct_env, rfl⟩,
      PostEpilogueStatePlaced.of_steps hcl5 (by simp [hsp4_eq, arm64_norm]) hsp_eq hsp
        (by simp [noneCap, htr4_eq, arm64_norm]),
      by simp [arm64_norm],
      by simp [hrun4, arm64_norm],
      by simp [hx19_4, arm64_norm],
      by simp [hx20_4, arm64_norm],
      by simp [hx21_4, arm64_norm],
      by simp [arm64_norm],
      by simp [hx23_4, arm64_norm],
      by simp [hx24_4, arm64_norm],
      by simp [arm64_norm],
      by simp [x_ct, arm64_norm],
      by rw [← hpq_len]; simp [arm64_norm],
      by simp [arm64_norm],
      ?_⟩
    have hst_eq : M.stepEvents (evs₀ ++ intoBoxedSliceEvents x_ct) st = st₂ := by
      dsimp only [st₂, st₁]; rw [M.stepEvents_append]
    rw [hst_eq]
    dsimp only [optBoxU8Pending, vecHeader, Reg.x0]
    rw [pure_true_emp rfl]
    apply entails_of_eq
    simp only [arm64_norm]
    sep_ac_rfl
  | some ad =>
    have hFit2 : FitsEnv M lim st₂ (IntoBoxedCapEnv adCap ad) := hFit1.seq_right hct_env
    refine WSepWPp.mono_pre (P' :=
        ⌜adLen = BitVec.ofNat 64 ad.length ∧ ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63 ∧ adPtr ≠ 0⌝ ∗
        (∃∗ w176 : BitVec 64, ∃∗ w184 : BitVec 64, ∃∗ w192 : BitVec 64,
          ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
          ((sp' + 136#64) ↦₆₄ ctCap) ∗ ((sp' + 144#64) ↦₆₄ ctPtr) ∗
          ((sp' + 152#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
          boxU8Buf A.repAlloc (s4.readReg64 .x0) ct ∗
          A.pool lim st₂ s4 ∗ stackAt sp' (skipFieldStackX 100) ∗
          ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₆₄ w48) ∗ ((sp' + 60#64) ↦₃₂ prevCounter) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          ((sp' + 176#64) ↦₆₄ w176) ∗ ((sp' + 184#64) ↦₆₄ w184) ∗ ((sp' + 192#64) ↦₆₄ w192) ∗
          memRegion (sp' + 200#64) 24 ∗
          vecU8Buf A.repAlloc (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
            (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD []) ∗
          vecU8Buf A.repAlloc adCap adPtr ad))
      (by
        rw [post_memRegion48_split24 sp']
        dsimp only [optVecU8Buf, vecHeader, vecU8Buf, x_ct]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
        simp only [sepExists_sepConj_right, hstackBox, hsp2_eq, arm64_norm]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun ⟨hadLen, had_le, had_lt, had_ptr⟩ => ?_
    subst hadLen
    have had_eq := cap_add1_eq_of_lt had_lt
    refine WSepWPp.exists_pre fun w176 => ?_
    refine WSepWPp.exists_pre fun w184 => ?_
    refine WSepWPp.exists_pre fun w192 => ?_
    refine WSepWPp.of_sepWP_placed hcl4 (mid := (blkPl_85).ρ intoBoxedSliceName) ?_
    wp_steps_sync_boxes85 ((blkPl_85).ρ intoBoxedSliceName)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl5
    have hvec_ad : vecU8At A.repAlloc (sp' + 176#64) adCap adPtr ad =
        ((sp' + 176#64) ↦₆₄ adCap) ∗ ((sp' + 184#64) ↦₆₄ adPtr) ∗
          ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 ad.length) ∗ vecU8Buf A.repAlloc adCap adPtr ad := by
      rw [vecU8At_eq_header_buf]
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    set x_ad : VecArg := ⟨sp' + 176#64, adCap, adPtr, ad⟩
    refine wpp_call_s (x_ad, st₂) hcallBox
      (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp4_align) hcl5
      (ret_pc := (blkPl_85).base + 1500#64) (by simp [arm64_norm])
      (fun s5 => vecU8At A.repAlloc (sp' + 176#64) adCap adPtr ad ∗
        A.pool lim st₂ s5 ∗ stackAt sp' intoBoxedSliceStackX)
      (φ := sp' + 176#64 = sp' + 176#64 ∧ FitsEnv M lim st₂ (IntoBoxedCapEnv adCap ad))
      (by
        dsimp only [intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack,
          IntoBoxedSliceEnv, intoBoxedSliceEvents, IntoBoxedCapEnv, intoBoxedCapEvents, VecArg.at, x_ad]
        simp only [hsp4_eq, arm64_norm]
        rfl)
      ⟨rfl, hFit2⟩
      (by rw [hvec_ad, hstackBox]; sep_focus)
      ?_
    clear hcallBox
    intro s6 hpc6 hrun6 hsp6 hsp6_align hcl6 hcs6
    dsimp only [intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack]
    rw [sepConj_assoc]
    refine WSepWPp.pure_pre (fun ⟨hx1_6, htr6⟩ => ?_)
    set st₃ := M.stepEvents (intoBoxedSliceEvents x_ad) st₂
    have had_env : IntoBoxedCapEnv adCap ad (intoBoxedSliceEvents x_ad) := rfl
    rcases hcs6 with ⟨hx19_6cs, hx20_6cs, hx21_6cs, _, hx23_6cs, hx24_6cs, hx25_6cs, hx26_6cs, hx27_6cs, hx28_6cs, _⟩
    have hsp6_eq : s6.sp = sp' := by simp [hsp6, hsp4_eq, arm64_norm]
    have htr6_eq : s6.trace = s0.trace := by simp [htr6, htr4_eq, arm64_norm]
    have hx19_6 : s6.readReg64 .x19 = x19 := by simp [hx19_6cs, hx19_4, arm64_norm]
    have hx20_6 : s6.readReg64 .x20 = x20 := by simp [hx20_6cs, hx20_4, arm64_norm]
    have hx21_6 : s6.readReg64 .x21 = x21 := by simp [hx21_6cs, hx21_4, arm64_norm]
    have hx23_6 : s6.readReg64 .x23 = x23 := by simp [hx23_6cs, hx23_4, arm64_norm]
    have hx24_6 : s6.readReg64 .x24 = x24 := by simp [hx24_6cs, hx24_4, arm64_norm]
    have hx25_6 : s6.readReg64 .x25 = if (pqCap + 1#64 == 0#64) then 0#64 else pqCap := by
      simp [hx25_6cs, arm64_norm]
    have hx26_6 : s6.readReg64 .x26 = BitVec.ofNat 64 ct.length := by
      simp [hx26_6cs, x_ct, arm64_norm]
    have hx27_6 : s6.readReg64 .x27 = BitVec.ofNat 64 (pqOpt.getD []).length := by
      simp [hx27_6cs, arm64_norm]
    have hx28_6 : s6.readReg64 .x28 = if (pqCap + 1#64 != 0#64) then pqPtr else 1#64 := by
      simp [hx28_6cs, arm64_norm]
    refine wpp_of_sepWP_end_noPanic_placed hcl6 ?_
    wp_steps_sync_boxes85 ((blkPl_85).base + 1728#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun6, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl7
    refine ⟨if (pqCap + 1#64 == 0#64) then 0#64 else pqCap,
      if (pqCap + 1#64 != 0#64) then pqPtr else 1#64,
      s4.readReg64 .x0, s6.readReg64 .x0, s6.readReg64 .x1,
      evs₀ ++ intoBoxedSliceEvents x_ct ++ intoBoxedSliceEvents x_ad,
      ⟨evs₀, intoBoxedSliceEvents x_ct, intoBoxedSliceEvents x_ad, rfl, hfree₀, hct_env, had_env⟩,
      PostEpilogueStatePlaced.of_steps hcl7 (by simp [hsp6_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr6_eq, arm64_norm]),
      by simp [arm64_norm],
      by simp [hrun6, arm64_norm],
      by simp [hx19_6, arm64_norm],
      by simp [hx20_6, arm64_norm],
      by simp [hx21_6, arm64_norm],
      by simp [arm64_norm],
      by simp [hx23_6, arm64_norm],
      by simp [hx24_6, arm64_norm],
      by simp [hx25_6, arm64_norm],
      by simp [hx26_6, arm64_norm],
      by simp [hx27_6, arm64_norm],
      by simp [hx28_6, arm64_norm],
      ?_⟩
    have hst_eq :
        M.stepEvents (evs₀ ++ intoBoxedSliceEvents x_ct ++ intoBoxedSliceEvents x_ad) st = st₃ := by
      dsimp only [st₃, st₂, st₁]; simp only [M.stepEvents_append]
    rw [hst_eq]
    have h48 := vecHeader_memRegion24_entails_48 sp' adCap adPtr (BitVec.ofNat 64 ad.length)
    dsimp only [optBoxU8Pending, x_ad]
    rw [pure_true_emp hx1_6]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left h48)))))))))
    dsimp only [vecHeader, Reg.x0]
    have hx1_6' : s6.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 ad.length := hx1_6
    apply entails_of_eq
    simp only [hstackBox, hsp4_eq, hx1_6', arm64_norm]
    sep_ac_rfl

theorem post_pack_msg_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr w96 rkCap rkPtr w0 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b_ver : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (rk : List (BitVec 8))
    (msg : SignalMessage) {out : Except SignalProtocolError SignalMessage} (hout : out = .ok msg)
    (hbnd : 8 + 1 ≤ msg.serialized.length ∧ msg.serialized.length < 2 ^ 40 ∧
      msg.ciphertext.length < 2 ^ 40 ∧ msg.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, msg.addresses = some ad → ad.length < 2 ^ 40))
    (hpk : msg.senderRatchetKey.bytes.toList =
      pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hver : b_ver >>> 4 = msg.messageVersion)
    (hser : serBoxPtr ≠ 0#64)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1740#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serBoxPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.serialized.length)
    (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = adBoxPtr)
    (hx23 : s.readReg64 .x23 = b_ver.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap')
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = pqPtr') :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 28#64) ↦₃₂ msg.counter) ∗
        ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
        ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
        ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
        boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
        boxU8Buf A.repAlloc serBoxPtr msg.serialized ∗
        optBoxU8Pending A.repAlloc adBoxPtr w96 msg.addresses ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 28#64) ↦₃₂ msg.counter) ∗
            ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
            ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
            ((sp' + 64#64) ↦₆₄ w15) ∗
            ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
            ((sp' + 112#64) ↦₈ b31) ∗
            ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
            sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := @cleanup_698_wp_placed _ M A lim H hS st s0
  have hunpack := memRegion104_unpack_x19 x19
  refine WSepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left hunpack)))))))))))))))) ?_
  clear hunpack
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine WSepWPp.exists_pre fun w16 => ?_
  refine WSepWPp.exists_pre fun w24 => ?_
  refine WSepWPp.exists_pre fun w32 => ?_
  refine WSepWPp.exists_pre fun w40 => ?_
  refine WSepWPp.exists_pre fun w48 => ?_
  refine WSepWPp.exists_pre fun c0 => ?_
  refine WSepWPp.exists_pre fun c1 => ?_
  refine WSepWPp.exists_pre fun c2 => ?_
  refine WSepWPp.exists_pre fun c3 => ?_
  refine WSepWPp.exists_pre fun c4 => ?_
  refine WSepWPp.exists_pre fun c5 => ?_
  refine WSepWPp.exists_pre fun c6 => ?_
  refine WSepWPp.exists_pre fun c7 => ?_
  refine WSepWPp.exists_pre fun c8 => ?_
  refine WSepWPp.exists_pre fun cw9 => ?_
  refine WSepWPp.exists_pre fun cw13 => ?_
  refine WSepWPp.exists_pre fun cw15 => ?_
  refine WSepWPp.exists_pre fun cw23 => ?_
  refine WSepWPp.exists_pre fun cb31 => ?_
  refine WSepWPp.exists_pre fun w88 => ?_
  refine WSepWPp.exists_pre fun w96_old => ?_
  refine WSepWPp.exists_pre fun w104 => ?_
  refine WSepWPp.exists_pre fun w108 => ?_
  refine WSepWPp.exists_pre fun b112 => ?_
  dsimp only [sevenBytesHeadAt, pkLayoutAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 1748#64) ?_
  wp_steps_sync_boxes85 ((blkPl_85).base + 1748#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  have h128_tail := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6
  dsimp only [sevenBytesHeadAt] at h128_tail
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h128_tail
  refine wpp_sync_pre (fun s1 =>
      ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
      ((sp' + 28#64) ↦₃₂ msg.counter) ∗
      ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
      ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
      ((sp' + 64#64) ↦₆₄ w15) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
      ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesTailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
      ((x19 + 16#64) ↦₆₄ w16) ∗ ((x19 + 24#64) ↦₆₄ w24) ∗
      ((x19 + 32#64) ↦₆₄ w32) ∗ ((x19 + 40#64) ↦₆₄ w40) ∗
      ((x19 + 48#64) ↦₆₄ w48) ∗
      ((x19 + 56#64) ↦₃₂ (c3 ++ c2 ++ c1 ++ c0)) ∗
      ((x19 + 60#64) ↦₈ c4) ∗ ((x19 + 61#64) ↦₈ c5) ∗ ((x19 + 62#64) ↦₈ c6) ∗
      pkRestAt (x19 + 56#64) c7 c8 cw9 cw13 cw15 cw23 cb31 ∗
      ((x19 + 88#64) ↦₆₄ w88) ∗ ((x19 + 96#64) ↦₆₄ w96_old) ∗
      ((x19 + 104#64) ↦₃₂ w104) ∗ ((x19 + 108#64) ↦₃₂ w108) ∗
      ((x19 + 112#64) ↦₈ b112) ∗ memRegion (x19 + 113#64) 7 ∗
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
      boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
      boxU8Buf A.repAlloc serBoxPtr msg.serialized ∗
      optBoxU8Pending A.repAlloc adBoxPtr w96 msg.addresses ∗
      A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
    (by rw [← h128_tail]; apply entails_of_eq; sep_ac_rfl) ?_
  dsimp only [sevenBytesTailAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine WSepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + 1776#64) ?_
  wp_steps_sync_boxes85 ((blkPl_85).base + 1776#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl2
  have h56_tail := sevenBytesHeadAt_eq_tailAt (x19 + 56#64) b0 b1 b2 b3 c4 c5 c6
  dsimp only [sevenBytesHeadAt] at h56_tail
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_tail
  refine wpp_sync_pre (fun s2 =>
      ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
      ((sp' + 28#64) ↦₃₂ msg.counter) ∗
      ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
      ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
      ((sp' + 64#64) ↦₆₄ w15) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
      ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      (x19 ↦₆₄ pqCap') ∗ ((x19 + 8#64) ↦₆₄ pqPtr') ∗
      ((x19 + 16#64) ↦₆₄ w16) ∗ ((x19 + 24#64) ↦₆₄ w24) ∗
      ((x19 + 32#64) ↦₆₄ w32) ∗ ((x19 + 40#64) ↦₆₄ w40) ∗
      ((x19 + 48#64) ↦₆₄ BitVec.ofNat 64 msg.serialized.length) ∗
      sevenBytesTailAt (x19 + 56#64) b0 b1 b2 b3 c4 c5 c6 ∗
      pkRestAt (x19 + 56#64) c7 c8 cw9 cw13 cw15 cw23 cb31 ∗
      ((x19 + 88#64) ↦₆₄ w88) ∗ ((x19 + 96#64) ↦₆₄ w96_old) ∗
      ((x19 + 104#64) ↦₃₂ w104) ∗ ((x19 + 108#64) ↦₃₂ w108) ∗
      ((x19 + 112#64) ↦₈ b112) ∗ memRegion (x19 + 113#64) 7 ∗
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
      boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
      boxU8Buf A.repAlloc serBoxPtr msg.serialized ∗
      optBoxU8Pending A.repAlloc adBoxPtr w96 msg.addresses ∗
      A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100))
    (by
      rw [← h56_tail, sevenBytesHeadAt_eq_tailAt (sp' + 128#64)]
      dsimp only [sevenBytesTailAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine WSepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 1860#64) ?_
  wp_steps_sync_boxes85 ((blkPl_85).base + 1860#64)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  have h56_head := sevenBytesHeadAt_eq_tailAt (x19 + 56#64) b0 b1 b2 b3 b4 b5 b6
  dsimp only [sevenBytesTailAt] at h56_head
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_head
  have hmsg := msgResultAt_ok_intro A.repAlloc x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr w96
    b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 msg hout hbnd hpk
  dsimp only [pkLayoutAt] at hmsg
  rw [h56_head] at hmsg
  dsimp only [pkRestAt] at hmsg
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmsg
  refine wpp_sync_pre (fun s3 =>
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      A.pool lim st s3 ∗ stackAt sp' (skipFieldStackX 100) ∗
      ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
      ((sp' + 28#64) ↦₃₂ msg.counter) ∗
      ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
      ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
      ((sp' + 64#64) ↦₆₄ w15) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
      ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      signalMessageResultAt A.repAlloc [] x19 out)
    (by
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right hmsg))))))))))))))))
      apply entails_of_eq; sep_ac_rfl) ?_
  by_cases hcap : rkCap = 0#64
  · clear hnext
    subst hcap
    rw [vecU8Buf_zero]
    refine WSepWPp.pure_pre fun _ => ?_
    refine wpp_of_sepWP_end_noPanic_placed hcl3 ?_
    wp_steps_sync_boxes85 ((blkPl_85).base + 1088#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl4
    refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]),
      [], .nil, ?_⟩
    rw [M.stepEvents_nil]
    dsimp only [sevenBytesHeadAt]
    apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  · refine WSepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc rkCap rkPtr rk hcap)) ?_
    simp only [sepConj_assoc]
    refine WSepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine WSepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 1688#64) ?_
    wp_steps_sync_boxes85 ((blkPl_85).base + 1688#64)
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
    intro hcl4
    refine wpp_sync_pre (fun s4 =>
        (A.repAlloc.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗
          A.pool lim st s4 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 28#64) ↦₃₂ msg.counter) ∗
          ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
          ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
          ((sp' + 64#64) ↦₆₄ w15) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
          signalMessageResultAt A.repAlloc [] x19 out))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (hnext
        (PostEpilogueStatePlaced.of_steps hcl4 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        hpos hlt hptr)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ => ⟨hstf, evs, hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [sevenBytesHeadAt]
    apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl

theorem post_clone_and_pack_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 pqCap' pqPtr' ctBoxPtr adBoxPtr w96 rkCap rkPtr w0 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b_ver : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (rk : List (BitVec 8))
    (msg : SignalMessage) {out : Except SignalProtocolError SignalMessage} (hout : out = .ok msg)
    (hbnd : 8 + 1 ≤ msg.serialized.length ∧ msg.serialized.length < 2 ^ 40 ∧
      msg.ciphertext.length < 2 ^ 40 ∧ msg.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, msg.addresses = some ad → ad.length < 2 ^ 40))
    (hpk : msg.senderRatchetKey.bytes.toList =
      pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hver : b_ver >>> 4 = msg.messageVersion)
    (hFit : FitsEnv M lim st (TryCloneBytesEnv msg.serialized))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1728#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 msg.serialized.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adBoxPtr)
    (hx23 : s.readReg64 .x23 = b_ver.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap')
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = pqPtr') :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      ((x21 ↦ₛ msg.serialized) ∗
        ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 28#64) ↦₃₂ msg.counter) ∗
        ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
        ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
        ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
        boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
        optBoxU8Pending A.repAlloc adBoxPtr w96 msg.addresses ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, PostClonePackEnv msg.serialized evs ∧
          (Pf ⊢ (x21 ↦ₛ msg.serialized) ∗
            ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 28#64) ↦₃₂ msg.counter) ∗
            ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
            ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
            ((sp' + 64#64) ↦₆₄ w15) ∗
            ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
            ((sp' + 112#64) ↦₈ b31) ∗
            ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
            sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallClone := hTryClone
  clear hTryClone
  have hser_lt40 : msg.serialized.length < 2 ^ 40 := hbnd.2.1
  have hser_toNat : (BitVec.ofNat 64 msg.serialized.length).toNat = msg.serialized.length :=
    Nat.mod_eq_of_lt (by omega)
  have hser_le63 : msg.serialized.length + 1 ≤ 2 ^ 63 := by omega
  have hstackClone := stackAt_sub_split sp' tryCloneFromRefStackX (skipFieldStackX 100)
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ tryCloneFromRefName) ?_
  wp_steps_sync_boxes85 ((blkPl_85).ρ tryCloneFromRefName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  set x_ser : TryCloneSliceCall := ⟨x21, msg.serialized⟩
  refine wpp_call_s (x_ser, st) hcallClone
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + 1740#64) (by simp [arm64_norm])
    (fun s1 => (x21 ↦ₛ msg.serialized) ∗ A.pool lim st s1 ∗ stackAt sp' tryCloneFromRefStackX)
    (φ := x21 = x21 ∧ (BitVec.ofNat 64 msg.serialized.length).toNat = msg.serialized.length ∧
      msg.serialized.length + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (TryCloneBytesEnv msg.serialized))
    (by
      dsimp only [tryCloneFromRefSpecX, tryCloneFromRefSpecWithStack,
        TryCloneFromRefEnv, tryCloneFromRefEvents, TryCloneBytesEnv, tryCloneBytesEvents, x_ser]
      simp only [hsp_eq, arm64_norm]
      rfl)
    ⟨rfl, hser_toNat, hser_le63, hFit⟩
    (by rw [hstackClone]; sep_focus)
    ?_
  clear hcallClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [tryCloneFromRefSpecX, tryCloneFromRefSpecWithStack]
  rw [sepConj_assoc]
  refine WSepWPp.pure_pre fun ⟨hx0_ne, hx1_2, htr2⟩ => ?_
  set st₁ := M.stepEvents (tryCloneFromRefEvents x_ser) st
  have hclone_env : TryCloneBytesEnv msg.serialized (tryCloneFromRefEvents x_ser) := rfl
  rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adBoxPtr := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = b_ver.zeroExtend 64 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = b7.zeroExtend 64 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap' := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length := by
    simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length := by
    simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = pqPtr' := by simp [hx28_cs, hx28, arm64_norm]
  have hpack := @post_pack_msg_wp_placed _ M A lim H hS st₁ s0
  refine WSepWPp.mono_pre (P' :=
      ((((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 28#64) ↦₃₂ msg.counter) ∗
        ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
        ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
        ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
        boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
        boxU8Buf A.repAlloc (s2.readReg64 .x0) msg.serialized ∗
        optBoxU8Pending A.repAlloc adBoxPtr w96 msg.addresses ∗
        A.pool lim st₁ s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (x21 ↦ₛ msg.serialized)))
    (by
      dsimp only [x_ser, Reg.x0]
      apply entails_of_eq; simp only [hstackClone, hsp_eq, arm64_norm]; sep_ac_rfl) ?_
  refine wpp_frame_noPanic
    (hpack rk msg hout hbnd hpk hver hx0_ne
      ⟨hsp2_eq, hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
    fun sf Pf ⟨hstf, evs_pack, hfree_pack, hent⟩ =>
      ⟨hstf, tryCloneFromRefEvents x_ser ++ evs_pack,
        SeqEnv.append hclone_env hfree_pack, ?_⟩
  have hst_eq :
      M.stepEvents (tryCloneFromRefEvents x_ser ++ evs_pack) st = M.stepEvents evs_pack st₁ := by
    dsimp only [st₁]; rw [M.stepEvents_append]
  rw [hst_eq]
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
