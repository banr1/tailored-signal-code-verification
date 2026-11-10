/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of the `StartGroup` `skip_field` Branch

Relocatable `RustCliAllocBudget`-threaded verification of the recursive `StartGroup` loop in
`prost::encoding::skip_field::<&mut &[u8]> [local#1]` (block 1).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupXBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   blkLib_eq_1 blkPC_1 blkPl_1 withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skipGroup skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix SepWPp.of_sepWP_lscl SkipFieldGhost VarintSlicePre
   bv32_sub_one_zeroExtend bv32_zeroExtend_ofNat bv_len_sub_consumed
   cbz_depth_succ cbz_len_cons_false decodeErrorHookStackX decodeVarint_1 decodeVarint_suffix
   getLsbD_7_of_gt getLsbD_7_of_le
   itag_beq_tag_false iwt_beq_4_false iwt_w0_setWidth8
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   len_cons_sub_one len_ult_consumed_false
   memRegion_48_skipSlice memRegion_48_split memRegion_48_split2
   pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16
   pointsToBytes_prefix_join pointsToBytes_split_last
   sf_truncate32_ofNat64 signExtend64_eq_and_0x7f
   signExtend64_getLsbD_63_of_gt signExtend64_getLsbD_63_of_le
   skipBelowX skipBelowX_err skipBelowX_err_entails
   skipBelowX_leaf skipBelowX_leaf_entails skipBelowX_slow skipBelowX_slow_entails
   skipFieldStackX skipField_succ_startGroup
   skipGroup_of_decodeVarint_none skipGroup_of_endGroup skipGroup_of_key_ge
   skipGroup_of_ne_endGroup skipGroup_of_tag_zero skipGroup_of_wt_none
   skipSliceErr_entails_memRegion48 skipSliceOk_entails_memRegion48 skip_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   stackAt_skipFieldX suffix_trans tag_cbz_false
   ult_10_of_ge_11 ult_10_of_lt_11 varintSliceResultAt w0_and_255_eq w1_tag_eq)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceSpecGen decodeVarintSliceSpecX
   skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
  (decodeVarintSlowSpecGen decodeVarintSlowSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
  (call_frame_budget_lscl fitsEnv_decodeErrorFrom_of_skipField_none
   fitsEnv_varintSlice_of_skipField fitsEnv_varintSlow_of_skipField
   skipFieldEnv_nil_of_some skipFieldEnv_of_decodeErrorFrom
   skipFieldEnv_of_varintSlice_none skipFieldEnv_of_varintSlow_none
   varintSliceEnv_some_eq_nil varintSlowEnv_some_eq_nil)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
  (skipFieldSpecAtX skipGroupLoopPreX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *]))

private theorem sepWPp_to_loopPre {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {ret : BitVec 64}
    {s0 s : State} {d : Nat} {bufRef slot ptr : BitVec 64} {bs cur : List (BitVec 8)}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (heq : P = skipGroupLoopPreX A lim st s0 s d bufRef slot ptr bs cur)
    (h : SepWPp prog ret s (skipGroupLoopPreX A lim st s0 s d bufRef slot ptr bs cur) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  heq ▸ h

private theorem fitsEnv_skipField_rec {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x_outer x_rec : SkipFieldGhost}
    (himp : skipField (2 * x_rec.bs.length + 2) x_rec.depth x_rec.tag x_rec.wt x_rec.bs = none →
      skipField (2 * x_outer.bs.length + 2) x_outer.depth x_outer.tag x_outer.wt x_outer.bs = none)
    (hfits : FitsEnv M lim st (SkipFieldEnv x_outer)) :
    FitsEnv M lim st (SkipFieldEnv x_rec) := by
  intro evs he
  simp only [SkipFieldEnv, skipFieldEventsCore] at he
  cases hs : skipField (2 * x_rec.bs.length + 2) x_rec.depth x_rec.tag x_rec.wt x_rec.bs with
  | some _ =>
    rw [hs] at he; subst he; simp
  | none =>
    rw [hs] at he; subst he
    exact hfits _ (by simp [SkipFieldEnv, skipFieldEventsCore, himp hs])

private theorem skipFieldEnv_of_rec_none {x_outer x_rec : SkipFieldGhost} {evs : List AllocEvent}
    (hs : skipField (2 * x_rec.bs.length + 2) x_rec.depth x_rec.tag x_rec.wt x_rec.bs = none)
    (hnone : skipField (2 * x_outer.bs.length + 2) x_outer.depth x_outer.tag x_outer.wt x_outer.bs = none)
    (he : SkipFieldEnv x_rec evs) :
    SkipFieldEnv x_outer evs := by
  simpa only [SkipFieldEnv, skipFieldEventsCore, hs, hnone] using he

private theorem skipFieldEnv_some_eq_nil {x_rec : SkipFieldGhost} {rest' : List (BitVec 8)}
    {evs : List AllocEvent}
    (hs : skipField (2 * x_rec.bs.length + 2) x_rec.depth x_rec.tag x_rec.wt x_rec.bs = some rest')
    (he : SkipFieldEnv x_rec evs) :
    evs = [] := by
  simpa only [SkipFieldEnv, skipFieldEventsCore, hs] using he

set_option maxHeartbeats 3200000 in
theorem skipField_startGroup_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim d (fun _ => True)))) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim (d + 1) (fun x => x.wt = .startGroup))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipFieldSpecAtX
    simp only [sliceCursorAt, stackAt_skipFieldX _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hwt_eq : wt = .startGroup := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0 : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.startGroup.toNat := by assumption
  have hx1 : (s0.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag := by assumption
  have htag_lt : tag < 2 ^ 32 := by assumption
  have hx3 : (s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1) := by assumption
  have h : bs.length < 2 ^ 63 := by assumption
  let x_outer : SkipFieldGhost := ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩
  have hfits : FitsEnv M lim st (SkipFieldEnv x_outer) := by assumption
  have hcbz := cbz_depth_succ hx3 hdepth
  have hw0 := w0_and_255_eq hx0
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat htag_lt
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  have hsf_eq_res : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = res := by
    rw [skipField_succ_startGroup, hres]
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (192)) hcl0
  wp_steps_sync_pool ((blkPl_1).base + bv% (192))
  simp only [State.setMem_setMem]
  wp_reach
  intro hcl_init
  apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := bs)
    (by dsimp only [skipGroupLoopPreX]; simp only [sliceCursorAfter, Nat.sub_self, BitVec.add_zero]; sep_ac_rfl)
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = (blkPl_1).base + bv% (192) →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved s0 s →
        LibsignalCodeLoaded lsmpl s.mem →
        SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPreX A lim st s0 s d bufRef slot ptr bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm]⟩
        hcl_init)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    cases cur with
    | nil =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) (cur := []) rfl
      rw [hnone] at hres_cur
      subst hres_cur
      have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hsf_eq_res hfits
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_s
      conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, pointsToBytes_nil, sepConj_emp,
        memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [List.length_nil, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps_sync_pool (lsmpl.base 261)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - 0)) 0#64) (by sep_focus)
      conv => arg 4; rw [Nat.sub_zero, List.take_length, skipBelowX_err s0.sp (d + 1) hdepth, ← hsp_s]
      wp_reach
      intro hcl_err
      refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
        (x := (s0.sp - 96#64, 0x8000000000000001#64, st))
        (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
        (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
        ?_
        (by sep_focus)
        ?_
      · exact ⟨by decide, hfits_de⟩
      intro sm hpcm hrunm hspm hcsm _
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, hsp_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
      apply SepWPp.of_sepWP_ret
      simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
        arm64_norm, htr_s, hsp_s]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hevs_de : DecodeErrorFromEnv evs := by assumption
      have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
      apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done
    | cons b0 bs1 =>
      simp only [List.length_cons] at hcur_n
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    cases cur with
    | nil =>
      exact ih [] s (by simp) hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    | cons b0 bs1 =>
      obtain ⟨hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
      have hcur_lt : (b0 :: bs1).length < 2 ^ 63 := by omega
      have hcbz_len := cbz_len_cons_false hcur_lt
      let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - (b0 :: bs1).length)
      refine (fun (Q_f Qp_f : State → SepProp → Prop)
          (hafter : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = (blkPl_1).base + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            LibsignalCodeLoaded lsmpl s1.mem →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A lim st s0 s1 d bufRef slot ptr bs rest) Q_f Qp_f)
          (hbody : (∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
            decodeVarint (b0 :: bs1) = some (key, rest) →
            s1.pc = (blkPl_1).base + bv% (296) →
            s1.status = .Running →
            s1.sp = s0.sp - 96#64 →
            s1.trace = s0.trace →
            s1.readReg64 (Reg.gpr 0#5) = key →
            s1.readReg64 (Reg.gpr 19#5) = bufRef →
            s1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
            s1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
            HighCalleeSaved s0 s1 →
            LibsignalCodeLoaded lsmpl s1.mem →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s1
              (skipGroupLoopPreX A lim st s0 s1 d bufRef slot ptr bs rest) Q_f Qp_f) →
            SepWPp ((blkPC_1).rebase (blkPl_1).base H) (s0.readReg64 Reg.lr) s
              (skipGroupLoopPreX A lim st s0 s d bufRef slot ptr bs (b0 :: bs1)) Q_f Qp_f) =>
          hbody hafter)
        _ _ ?_ ?_
      · intro key rest s1 hd hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hcs1 hcl1
        obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
        have hrest_lt_cur : rest.length < (b0 :: bs1).length := decodeVarint_length hd
        have hrest_le : rest.length ≤ bs.length := by omega
        have hrest_lt : rest.length < 2 ^ 63 := by omega
        have hrest_suf : IsDropSuffix bs rest :=
          suffix_trans hcur_le hcur_suf (Nat.le_of_lt hrest_lt_cur) (decodeVarint_suffix hd)
        by_cases hk_ge : 2 ^ 32 ≤ key.toNat
        · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
          rw [hnone] at hres_cur
          subst hres_cur
          have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hsf_eq_res hfits
          have hshr := key_shr32_of_ge hk_ge
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
            sliceCursorAt, memRegion_48_split2 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps_sync_pool (lsmpl.base 261)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
          rw [← bv_sub_add_lit s0.sp 96 8] at h40
          apply SepWP.fold h40 (by sep_focus)
          conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
          wp_reach
          intro hcl_err
          refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
            (x := (s0.sp - 96#64, 0x8000000000000004#64, st))
            (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
            (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
            ?_
            (by sep_focus)
            ?_
          · exact ⟨by decide, hfits_de⟩
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
            arm64_norm, htr1, hsp1]
          apply SepWP.exists_elim; intro evs
          wp_pull_pures
          have hevs_de : DecodeErrorFromEnv evs := by assumption
          have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
          apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          wp_done
        · have hshr := key_shr32_of_lt hk_ge
          cases hwt : WireType.ofNat? (key.toNat % 8) with
          | none =>
            have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
            rw [hnone] at hres_cur
            subst hres_cur
            have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hsf_eq_res hfits
            obtain ⟨hwt_cs1, hwt_cs2⟩ := key_wt_none hwt
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
              sliceCursorAt, memRegion_48_split2 s0.sp]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps_sync_pool (lsmpl.base 261)
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
            rw [← bv_sub_add_lit s0.sp 96 8] at h40
            apply SepWP.fold h40 (by sep_focus)
            conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
            wp_reach
            intro hcl_err
            refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
              (x := (s0.sp - 96#64, 0x8000000000000003#64, st))
              (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
              (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
              ?_
              (by sep_focus)
              ?_
            · exact ⟨by decide, hfits_de⟩
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
              arm64_norm, htr1, hsp1]
            apply SepWP.exists_elim; intro evs
            wp_pull_pures
            have hevs_de : DecodeErrorFromEnv evs := by assumption
            have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
            apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            wp_done
          | some iwt =>
            obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
            obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
            obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
            by_cases hitag0 : key.toNat / 8 < 1
            · have hnone := skipGroup_of_tag_zero (d := d) (tag := tag) hd hk_ge hwt hitag0
              rw [hnone] at hres_cur
              subst hres_cur
              have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hsf_eq_res hfits
              have htag_zero : key.toNat / 8 = 0 := by omega
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
              conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_err0
              wp_steps_sync_pool (lsmpl.base 261)
              simp only [State.setMem_setMem]
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
              wp_reach
              intro hcl_err
              refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
                (x := (s0.sp - 96#64, 0x8000000000000005#64, st))
                (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
                ?_
                (by sep_focus)
                ?_
              · exact ⟨by decide, hfits_de⟩
              intro sm hpcm hrunm hspm hcsm _
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              apply SepWPp.of_sepWP_ret
              simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
                arm64_norm, htr1, hsp1]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hevs_de : DecodeErrorFromEnv evs := by assumption
              have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
              apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done
            · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
              have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              by_cases hiwt_eg : iwt = .endGroup
              · subst hiwt_eg
                dsimp [WireType.toNat] at hand_wt hcc1_wt hcc2_wt
                have heg := skipGroup_of_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0
                rw [heg] at hres_cur
                by_cases hitag_eq : key.toNat / 8 = tag
                · simp only [hitag_eq, ↓reduceIte] at hres_cur
                  subst hres_cur
                  rw [hitag_eq] at hw1 hw1_2 hw1_zext1 hw1_zext2 hcbz_tag1 hcbz_tag2
                  have hevs_sf := skipFieldEnv_nil_of_some (x := x_outer) hsf_eq_res
                  apply SepWPp.of_sepWP_ret
                  simp only [skipGroupLoopPreX, sliceCursorAfter]
                  wp_steps_sync_pool (s0.readReg64 Reg.lr)
                  simp only [State.setMem_setMem]
                  conv => arg 4; rw [hpool_nil]
                  wp_done
                · simp only [hitag_eq, ↓reduceIte] at hres_cur
                  subst hres_cur
                  have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none hsf_eq_res hfits
                  obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt htag_lt
                  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl1
                  conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                    sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                  apply SepWP.exists_elim; intro v_err0
                  wp_steps_sync_pool (lsmpl.base 261)
                  simp only [State.setMem_setMem]
                  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  conv => arg 4; rw [skipBelowX_err s0.sp (d + 1) hdepth, ← hsp1]
                  wp_reach
                  intro hcl_err
                  refine call_frame_budget_lscl (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
                    (x := (s0.sp - 96#64, 0x8000000000000009#64, st))
                    (ret_pc := (blkPl_1).base + bv% (652)) hFromCall hcl_err
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                    (by simp only [arm64_norm])
                    (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
                    ?_
                    (by sep_focus)
                    ?_
                  · exact ⟨by decide, hfits_de⟩
                  intro sm hpcm hrunm hspm hcsm _
                  simp only [CalleeSavedPreserved] at hcsm
                  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                  simp (config := { decide := true }) only [arm64_norm, hsp1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                  apply SepWPp.of_sepWP_ret
                  simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
                    arm64_norm, htr1, hsp1]
                  apply SepWP.exists_elim; intro evs
                  wp_pull_pures
                  have hevs_de : DecodeErrorFromEnv evs := by assumption
                  have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
                  apply SepWP.fold (skipBelowX_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
                  wp_steps_sync_pool (s0.readReg64 Reg.lr)
                  simp only [State.setMem_setMem]
                  wp_done
              · have hne_eg := skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg
                rw [hne_eg] at hres_cur
                have hiwt_ne4 := iwt_beq_4_false hiwt_eg
                obtain ⟨hiwt_w0_1, hiwt_w0_2⟩ := iwt_w0_setWidth8 iwt
                have hd_lt : d < 2 ^ 32 := by omega
                let x_rec : SkipFieldGhost :=
                  ⟨iwt, key.toNat / 8, d, bufRef, slot,
                    ptr + BitVec.ofNat 64 (bs.length - rest.length), rest⟩
                have himp_rec : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest = none →
                    skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
                  intro hs_none
                  have hres_none := hres_cur
                  rw [hs_none] at hres_none
                  dsimp only at hres_none
                  rw [hsf_eq_res, ← hres_none]
                have hfits_rec : FitsEnv M lim st (SkipFieldEnv x_rec) :=
                  fitsEnv_skipField_rec (x_rec := x_rec) himp_rec hfits
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base) hcl1
                conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hrest_le hrest_suf,
                  show skipBelowX s0.sp (d + 1) = stackAt s1.sp (skipFieldStackX d) from by rw [hsp1]]; simp only [sepConj_assoc]
                wp_steps_sync_pool (blkPl_1).base
                simp only [State.setMem_setMem]
                wp_reach
                intro hcl_rec
                refine call_frame_budget_lscl (spec := skipFieldSpecAtX A lim d (fun _ => True))
                  (x := (x_rec, st))
                  (ret_pc := (blkPl_1).base + bv% (348)) hrec hcl_rec
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
                  (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align)
                  (by simp only [arm64_norm])
                  (by simp only [skipFieldSpecAtX, arm64_norm]; rfl)
                  ?_
                  (by sep_focus)
                  ?_
                · simp only [x_rec, arm64_norm, sf_truncate32_ofNat64]
                  exact ⟨by simp, hitag_lt, hd_lt, hrest_lt, hfits_rec⟩
                intro sm hpcm hrunm hspm hcsm hclm
                simp only [CalleeSavedPreserved] at hcsm
                obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
                simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
                cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
                | none =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  subst hres_cur
                  apply SepWPp.of_sepWP_ret
                  simp only [skipFieldSpecAtX, x_rec, hs, sepExists_sepConj_left, sepExists_sepConj_right,
                    sepConj_assoc, arm64_norm, htr1, hsp1]
                  apply SepWP.exists_elim; intro evs
                  wp_pull_pures
                  have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
                  have hevs_rec : SkipFieldEnv x_rec evs := by assumption
                  have hevs_sf := skipFieldEnv_of_rec_none (x_outer := x_outer) hs hsf_eq_res hevs_rec
                  have hcbz_sm0 : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
                  conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                  wp_steps_sync_pool (s0.readReg64 Reg.lr)
                  simp only [State.setMem_setMem]
                  wp_done
                | some rest' =>
                  rw [hs] at hres_cur
                  dsimp only at hres_cur
                  have hrest'_le_rest : rest'.length ≤ rest.length :=
                    (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                  have hrest'_le_n : rest'.length ≤ n := by
                    simp only [List.length_cons] at hcur_n hrest_lt_cur
                    omega
                  have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                  have hrest'_suf : IsDropSuffix bs rest' :=
                    suffix_trans hrest_le hrest_suf hrest'_le_rest
                      ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (192)) hclm
                  conv => arg 4; simp only [skipFieldSpecAtX, x_rec, hs, sepExists_sepConj_left, sepExists_sepConj_right,
                    sepConj_assoc, arm64_norm, hsp1]
                  apply SepWP.exists_elim; intro evs
                  wp_pull_pures
                  have htrm : sm.trace = s1.trace := by assumption
                  have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
                  have hevs_rec : SkipFieldEnv x_rec evs := by assumption
                  have hevs0 := skipFieldEnv_some_eq_nil hs hevs_rec
                  subst hevs0
                  conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl,
                    show stackAt (s0.sp - 96#64) (skipFieldStackX d) = skipBelowX s0.sp (d + 1) from rfl]
                  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                  wp_steps_sync_pool ((blkPl_1).base + bv% (192))
                  simp only [State.setMem_setMem]
                  wp_reach
                  intro hcl_next
                  apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := rest')
                    (by dsimp only [skipGroupLoopPreX]; sep_ac_rfl)
                  refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl_next
                  · simp only [arm64_norm]
                  · simp only [arm64_norm, hrunm]
                  · simp only [arm64_norm, hspm]
                  · simp only [arm64_norm, htrm, htr1]
                  · simp only [arm64_norm, hx19]
                  · simp only [arm64_norm, hx20]
                  · simp only [arm64_norm, hx21]
                  · simp only [arm64_norm, hx23]
                  · simp only [arm64_norm, hx24]
                  · simp only [arm64_norm, hx25]
                  · simp only [arm64_norm, hx26]
                  · simp only [arm64_norm, hx27]
                  · simp only [arm64_norm, hx28]
                  · simp only [arm64_norm, hvregs]
      · intro hafter
        have himp_none : decodeVarint (b0 :: bs1) = none →
            skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
          intro hd_none
          rw [hsf_eq_res, ← hres_cur]
          exact skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd_none
        have hfits_sl := fitsEnv_varintSlice_of_skipField himp_none hfits
        have hfits_slw := fitsEnv_varintSlow_of_skipField himp_none hfits
        by_cases hb0 : b0 ≤ 0x7f#8
        · have hbit0 := signExtend64_getLsbD_63_of_le hb0
          have hd := decodeVarint_1 bs1 hb0
          have hbs1_le : bs1.length ≤ (b0 :: bs1).length := by simp
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hcl_s
          conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
            sliceCursorAt, pointsToBytes_cons]
          wp_steps_sync_pool ((blkPl_1).base + bv% (296))
          simp only [State.setMem_setMem]
          apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (congrArg ((slot + 8#64) ↦₆₄ ·) (len_cons_sub_one b0 bs1))) (by sep_focus)
          have hcur_after :
              (slot ↦₆₄ (curPtr + 1#64)) ∗
                ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
                (curPtr ↦ₛ (b0 :: bs1)) ⊢
                sliceCursorAfter slot curPtr (b0 :: bs1) bs1 := by
            simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
            exact Entails.refl _
          apply SepWP.fold hcur_after (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hbs1_le) (by sep_focus)
          wp_reach
          intro hcl1
          apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := bs1)
            (by dsimp only [skipGroupLoopPreX]; sep_ac_rfl)
          refine hafter ((b0 &&& 0x7f#8).zeroExtend 64) bs1 _ hd
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
          · simp only [arm64_norm]
          · simp only [arm64_norm, hrun_s]
          · simp only [arm64_norm, hsp_s]
          · simp only [arm64_norm, htr_s]
          · simp only [arm64_norm, signExtend64_eq_and_0x7f hb0]
          · simp only [arm64_norm, hx19_s]
          · simp only [arm64_norm, hx20_s]
          · simp only [arm64_norm, hx21_s]
          · simp only [arm64_norm, hx23_s]
          · simp only [arm64_norm, hx24_s]
          · simp only [arm64_norm, hx25_s]
          · simp only [arm64_norm, hx26_s]
          · simp only [arm64_norm, hx27_s]
          · simp only [arm64_norm, hx28_s]
          · simp only [arm64_norm, hvregs_s]
        · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
          have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          by_cases h11 : 11 ≤ (b0 :: bs1).length
          · have hhi := ult_10_of_ge_11 h11 hcur_lt
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl_s
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons, memRegion_48_skipSlice s0.sp,
              skipBelowX_leaf s0.sp (d + 1) hdepth]
            wp_steps_sync_pool (lsmpl.base 76)
            simp only [State.setMem_setMem]
            wp_reach
            intro hcl_sl
            refine call_frame_budget_lscl (spec := decodeVarintSliceSpecX A lim)
              (x := (⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩, st))
              (ret_pc := (blkPl_1).base + bv% (256)) hSliceCall hcl_sl
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
              (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, arm64_norm, hsp_s, curPtr]; rfl)
              ?_
              (by sep_focus)
              ?_
            · exact ⟨hlen_toNat, hcur_lt, hpre_slice, hfits_sl⟩
            intro sm hpcm hrunm hspm hcsm hclm
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
              rw [hnone] at hres_cur
              subst hres_cur
              apply SepWPp.of_sepWP_ret
              simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
                sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, htr_s, hsp_s]
              apply SepWP.exists_elim; intro evs
              apply SepWP.exists_elim; intro e_err
              wp_pull_pures
              have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs_sf := skipFieldEnv_of_varintSlice_none (x := x_outer) hd hsf_eq_res hevs_sl
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
              apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨key, rest⟩
              have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
              have hcc := len_ult_consumed_false (rest := rest) hcur_lt
              have hsub_len := bv_len_sub_consumed hd
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
              conv => arg 4; simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd,
                varintSliceResultAt, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have htrm : sm.trace = s.trace := by assumption
              have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
              subst hevs0
              conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
              apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              wp_steps_sync_pool ((blkPl_1).base + bv% (296))
              simp only [State.setMem_setMem]
              apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
              apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
              have hcur_after :
                  (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                    ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                    (curPtr ↦ₛ (b0 :: bs1)) ⊢
                    sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                Entails.refl _
              apply SepWP.fold hcur_after (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
              wp_reach
              intro hcl1
              apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := rest)
                (by dsimp only [skipGroupLoopPreX]; sep_ac_rfl)
              refine hafter key rest _ hd
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
              · simp only [arm64_norm]
              · simp only [arm64_norm, hrunm]
              · simp only [arm64_norm, hspm]
              · simp only [arm64_norm, htrm, htr_s]
              · simp only [arm64_norm]
              · simp only [arm64_norm, hx19]
              · simp only [arm64_norm, hx20]
              · simp only [arm64_norm, hx21]
              · simp only [arm64_norm, hx23]
              · simp only [arm64_norm, hx24]
              · simp only [arm64_norm, hx25]
              · simp only [arm64_norm, hx26]
              · simp only [arm64_norm, hx27]
              · simp only [arm64_norm, hx28]
              · simp only [arm64_norm, hvregs]
          · have hhi := ult_10_of_lt_11 h11 hcur_lt
            have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (244)) hcl_s
            apply sepWP_seg_ls_vm
              (Q := (blkPC_1).rebase (blkPl_1).base (hooksException H))
              blkLib_eq_1 (mid := (blkPl_1).base + bv% (244))
            intro _m_strip
            conv => arg 4; rw [skipGroupLoopPreX, sliceCursorAfter_eq_split hcur_le hcur_suf,
              sliceCursorAt, pointsToBytes_cons]
            wp_steps
            apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
            conv => arg 4; rw [pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt]
            wp_steps
            apply SepWP.fold (Entails.of_eq (pointsToBytes_split_last curPtr (b0 :: bs1) hne_cons hcur_lt).symm) (by sep_focus)
            refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
            refine SepWP.transport_budgetPool
              (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
              (hnext := ?_)
            simp only [State.setMem_setMem]
            wp_reach
            intro hcl_244
            by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
            · have hbit_last := getLsbD_7_of_le hlast
              have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl_244
              conv => arg 4; rw [pointsToBytes_cons, memRegion_48_skipSlice s0.sp, skipBelowX_leaf s0.sp (d + 1) hdepth]
              wp_steps_sync_pool (lsmpl.base 76)
              simp only [State.setMem_setMem]
              wp_reach
              intro hcl_sl
              refine call_frame_budget_lscl (spec := decodeVarintSliceSpecX A lim)
                (x := (⟨s0.sp - 96#64, curPtr, b0 :: bs1⟩, st))
                (ret_pc := (blkPl_1).base + bv% (256)) hSliceCall hcl_sl
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, arm64_norm, hsp_s, curPtr]; rfl)
                ?_
                (by sep_focus)
                ?_
              · exact ⟨hlen_toNat, hcur_lt, hpre_slice, hfits_sl⟩
              intro sm hpcm hrunm hspm hcsm hclm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd, varintSliceResultAt,
                  sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, htr_s, hsp_s]
                apply SepWP.exists_elim; intro evs
                apply SepWP.exists_elim; intro e_err
                wp_pull_pures
                have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
                have hevs_sf := skipFieldEnv_of_varintSlice_none (x := x_outer) hd hsf_eq_res hevs_sl
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps_sync_pool (s0.readReg64 Reg.lr)
                simp only [State.setMem_setMem]
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot curPtr (BitVec.ofNat 64 (b0 :: bs1).length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                apply SepWP.fold (skipSliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                have hcc := len_ult_consumed_false (rest := rest) hcur_lt
                have hsub_len := bv_len_sub_consumed hd
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
                conv => arg 4; simp only [decodeVarintSliceSpecX, decodeVarintSliceSpecGen, hd,
                  varintSliceResultAt, sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.exists_elim; intro evs
                wp_pull_pures
                have htrm : sm.trace = s.trace := by assumption
                have hevs_sl : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
                have hevs0 := varintSliceEnv_some_eq_nil hd hevs_sl
                subst hevs0
                conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
                apply SepWP.fold (skipBelowX_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                wp_steps_sync_pool ((blkPl_1).base + bv% (296))
                simp only [State.setMem_setMem]
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (skipSliceOk_entails_memRegion48 s0.sp 0#64 key (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) (by sep_focus)
                have hcur_after :
                    (slot ↦₆₄ (curPtr + BitVec.ofNat 64 ((b0 :: bs1).length - rest.length))) ∗
                      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
                      (curPtr ↦ₛ (b0 :: bs1)) ⊢
                      sliceCursorAfter slot curPtr (b0 :: bs1) rest :=
                  Entails.refl _
                apply SepWP.fold hcur_after (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_reach
                intro hcl1
                apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := rest)
                  (by dsimp only [skipGroupLoopPreX]; sep_ac_rfl)
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]
            · have hbit_last := getLsbD_7_of_gt hlast
              apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl_244
              wp_steps_sync_pool (lsmpl.base 293)
              simp only [State.setMem_setMem]
              conv => arg 4; rw [skipBelowX_slow s0.sp (d + 1) hdepth]; simp only [sepConj_assoc]
              wp_reach
              intro hcl_slw
              refine call_frame_budget_lscl (spec := decodeVarintSlowSpecX A lim)
                (x := (⟨bufRef, slot, curPtr, b0 :: bs1⟩, st))
                (ret_pc := (blkPl_1).base + bv% (364)) hSlowCall hcl_slw
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
                (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, arm64_norm, hsp_s]; rfl)
                ?_
                (by simp only [sliceCursorAt]; sep_focus)
                ?_
              · exact ⟨hcur_lt, hfits_slw⟩
              intro sm hpcm hrunm hspm hcsm hclm
              simp only [CalleeSavedPreserved] at hcsm
              obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
              simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
              cases hd : decodeVarint (b0 :: bs1) with
              | none =>
                have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
                rw [hnone] at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd,
                  sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.exists_elim; intro evs
                wp_pull_pures
                have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 1#64 := by assumption
                have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
                have hevs_sf := skipFieldEnv_of_varintSlow_none (x := x_outer) hd hsf_eq_res hevs_slw
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (Entails.of_eq (pointsToBytes_cons curPtr b0 bs1).symm) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
                wp_steps_sync_pool (s0.readReg64 Reg.lr)
                simp only [State.setMem_setMem]
                wp_done
              | some p =>
                rcases p with ⟨key, rest⟩
                have hrest_le : rest.length ≤ (b0 :: bs1).length := Nat.le_of_lt (decodeVarint_length hd)
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_1).base + bv% (296)) hclm
                conv => arg 4; simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd,
                  sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.exists_elim; intro evs
                wp_pull_pures
                have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
                have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
                have htrm : sm.trace = s.trace := by assumption
                have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
                have hevs0 := varintSlowEnv_some_eq_nil hd hevs_slw
                subst hevs0
                conv => arg 4; rw [show M.stepEvents ([] : List AllocEvent) st = st from rfl]
                apply SepWP.fold (skipBelowX_slow_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le) (by sep_focus)
                wp_steps_sync_pool ((blkPl_1).base + bv% (296))
                simp only [State.setMem_setMem]
                wp_reach
                intro hcl1
                apply sepWPp_to_loopPre (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr) (bs := bs) (cur := rest)
                  (by dsimp only [skipGroupLoopPreX]; sep_ac_rfl)
                refine hafter key rest _ hd
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl1
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm]
                · simp only [arm64_norm, hspm]
                · simp only [arm64_norm, htrm, htr_s]
                · simp only [arm64_norm]
                · simp only [arm64_norm, hx19]
                · simp only [arm64_norm, hx20]
                · simp only [arm64_norm, hx21]
                · simp only [arm64_norm, hx23]
                · simp only [arm64_norm, hx24]
                · simp only [arm64_norm, hx25]
                · simp only [arm64_norm, hx26]
                · simp only [arm64_norm, hx27]
                · simp only [arm64_norm, hx28]
                · simp only [arm64_norm, hvregs]

end LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupXBudget
