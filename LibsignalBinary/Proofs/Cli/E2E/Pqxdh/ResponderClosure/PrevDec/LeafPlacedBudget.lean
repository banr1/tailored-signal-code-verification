/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `prost::encoding::skip_field::<&mut &[u8]> [local#5]`

Total-correctness (`RustCliAllocBudget M`) verification of `.startGroup` and full depth induction
(`skipField6_placed_ok`, `skipField6_placed_ok_cl`) for
`prost::encoding::skip_field::<&mut &[u8]> [local#5]` under `[LibsignalPlacement]`, plus
`growOneMessageKey_placed_ok_ext_x` at Block `43`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_261 blkPl_261 ls_subroutine_ok_cl_of_block lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalProtoCodec (
  WireType decodeVarint decodeVarint_length skipField skipGroup skip_length
)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  IsDropSuffix SepWPp.of_sepWP_lscl SkipFieldGhost
  bv32_sub_one_zeroExtend bv32_zeroExtend_ofNat cbz_depth_succ
  decodeErrorHookStackX decodeVarint_suffix
  itag_beq_tag_false iwt_beq_4_false iwt_w0_setWidth8
  key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
  memRegion_48_split memRegion_48_split2
  pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16
  pointsToBytes_prefix_join sf_truncate32_ofNat64 skipField_succ_startGroup
  skipGroup_of_decodeVarint_none skipGroup_of_endGroup skipGroup_of_key_ge
  skipGroup_of_ne_endGroup skipGroup_of_tag_zero skipGroup_of_wt_none
  skip_suffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
  sliceCursorAt suffix_trans tag_cbz_false w0_and_255_eq w1_tag_eq
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.CliHandshake.Placed (blkPl_507 blkPl_515 lsProg_507 lsProg_515)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  HighCalleeSaved3 skipBelow3 skipBelow3_err skipBelow3_err_entails
  skipBelow3_leaf skipBelow3_leaf_entails skipField3Stack stackAt_skipField3
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux (
  call_frame_budget_lscl fitsEnv_decodeErrorFrom_of_skipField_none
  fitsEnv_varintSlice_of_skipField skipFieldEnv_nil_of_some skipFieldEnv_of_decodeErrorFrom
  skipFieldEnv_of_varintSlice_none varintSliceEnv_some_eq_nil
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget (
  skipField3Spec skipField3SpecAt skipGroupLoopPre3
  subroutine_ok_skipField3Spec_of_at_depth_lscl
  subroutine_ok_skipField3_imp_lscl subroutine_ok_skipField3_or_lscl
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlacedBudget (
  SkipField6PlacedOkExtX subroutine_ok_skipField3Spec_of_at_depth_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafAPlacedBudget (
  SkipField6AtPlacedOk skipField6_depth_zero_placed_ok skipField6_endGroup_placed_ok
  skipField6_lengthDelimited_placed_ok skipField6_sixtyFourBit_placed_ok
  skipField6_thirtyTwoBit_placed_ok skipField6_varint_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  decodeVarint5_placed_ok dv5_decodeErrorFrom_placed_of_alloc
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  AllocContractsPlaced growOneChainSpecX growOneChain_placed_ok_cl growOneChain_placed_ok_x
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero_pl2 (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero_pl2 (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

private theorem lscl_of_cl {α : Type} {P : Program} {pl : Obj.MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl pl spec)) :
    subroutine_ok P entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem sepWPp_to_loopPre3 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {ret : BitVec 64}
    {s0 s : State} {d : Nat} {bufRef slot ptr v_pad : BitVec 64} {bs cur : List (BitVec 8)}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (heq : P = skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_pad bs cur)
    (h : SepWPp prog ret s (skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_pad bs cur) Q Qp) :
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

/-! ## Case 7 (`depth = d + 1`, `wt = .startGroup`) -/

set_option maxHeartbeats 2800000 in
theorem skipField6_startGroup_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim d (fun _ => True)))) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .startGroup))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .startGroup := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.startGroup.toNat := by assumption
  have htag_lt : tag < 2 ^ 32 := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  let x_outer : SkipFieldGhost := ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩
  have hfits : FitsEnv M lim st (SkipFieldEnv x_outer) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat htag_lt
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (by omega : d < 2 ^ 32)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  have hsf_eq_res : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = res := by
    rw [skipField_succ_startGroup, hres]
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_507).base + 232#64) hcl0
  wp_steps_sync_pool ((blkPl_507).base + 232#64)
  simp only [State.setMem_setMem]
  wp_reach
  intro hcl_init
  apply sepWPp_to_loopPre3 (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr)
    (v_pad := v_stk_2) (bs := bs) (cur := bs)
    (by dsimp only [skipGroupLoopPre3]; simp only [sliceCursorAfter, Nat.sub_self, BitVec.add_zero]; sep_ac_rfl)
  refine (fun (Q_f Qp_f : State → SepProp → Prop)
      (hloop : ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n →
        cur.length ≤ bs.length →
        IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = (blkPl_507).base + 232#64 →
        s.status = .Running →
        s.sp = s0.sp - 96#64 →
        s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef →
        s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag →
        HighCalleeSaved3 s0 s →
        LibsignalCodeLoaded lsmpl s.mem →
        SepWPp (lsProg_507 H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_stk_2 bs cur) Q_f Qp_f) =>
      hloop bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩
        hcl_init)
    _ _ ?_
  intro n
  induction n with
  | zero =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    have hcur_lt : cur.length < 2 ^ 63 := by omega
    let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
    have himp_dv : decodeVarint cur = none →
        skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
      intro hdv
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hdv
      rw [hsf_eq_res, ← hres_cur, hnone]
    have hfits_dv : FitsEnv M lim st (DecodeVarint2Env cur) :=
      fitsEnv_varintSlice_of_skipField (x := x_outer) himp_dv hfits
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl_s
    conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
      skipBelow3_leaf s0.sp (d + 1) hdepth]
    wp_steps_sync_pool (lsmpl.base 515)
    simp only [State.setMem_setMem]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl (spec := decodeVarint2SpecX A lim)
      (x := (⟨bufRef, slot, curPtr, cur⟩, st))
      (φ := bufRef = bufRef ∧ cur.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env cur))
      (ret_pc := (blkPl_507).base + 240#64) (lscl_of_cl hVarintCall) hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
      (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeVarint2SpecX, arm64_norm, hsp_s]; rfl)
      ⟨rfl, hcur_lt, hfits_dv⟩
      (by sep_focus)
      ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s,
      hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s]
      at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
    cases hd : decodeVarint cur with
    | none =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_ret
      simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, htr_s, hsp_s]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hevs_dv : DecodeVarint2Env cur evs := by assumption
      have hevs_sf := skipFieldEnv_of_varintSlice_none (x := x_outer) hd hsf_eq_res hevs_dv
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done
    | some p =>
      have hlt_cur := decodeVarint_length hd
      omega
  | succ n ih =>
    intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s hcl_s
    obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
    have hcur_lt : cur.length < 2 ^ 63 := by omega
    let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
    have himp_dv : decodeVarint cur = none →
        skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
      intro hdv
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hdv
      rw [hsf_eq_res, ← hres_cur, hnone]
    have hfits_dv : FitsEnv M lim st (DecodeVarint2Env cur) :=
      fitsEnv_varintSlice_of_skipField (x := x_outer) himp_dv hfits
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl_s
    conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
      skipBelow3_leaf s0.sp (d + 1) hdepth]
    wp_steps_sync_pool (lsmpl.base 515)
    simp only [State.setMem_setMem]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl (spec := decodeVarint2SpecX A lim)
      (x := (⟨bufRef, slot, curPtr, cur⟩, st))
      (φ := bufRef = bufRef ∧ cur.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env cur))
      (ret_pc := (blkPl_507).base + 240#64) (lscl_of_cl hVarintCall) hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
      (by simp only [State.spAligned, hsp_s, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeVarint2SpecX, arm64_norm, hsp_s]; rfl)
      ⟨rfl, hcur_lt, hfits_dv⟩
      (by sep_focus)
      ?_
    intro sm hpcm hrunm hspm hcsm hcl2
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s,
      hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s]
      at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
    cases hd : decodeVarint cur with
    | none =>
      have hnone := skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd
      rw [hnone] at hres_cur
      subst hres_cur
      apply SepWPp.of_sepWP_ret
      simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, htr_s, hsp_s]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hevs_dv : DecodeVarint2Env cur evs := by assumption
      have hevs_sf := skipFieldEnv_of_varintSlice_none (x := x_outer) hd hsf_eq_res hevs_dv
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ bs.length := by omega
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone := skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge
        rw [hnone] at hres_cur
        subst hres_cur
        have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none (x := x_outer) hsf_eq_res hfits
        have hshr := key_shr32_of_ge hk_ge
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
        conv => arg 4; simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, hsp_s]
        apply SepWP.exists_elim; intro evs_dv
        wp_pull_pures
        have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
        have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
        have htrm : sm.trace = s.trace := by assumption
        have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
        have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
        subst hevs0
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
          sliceCursorAt, memRegion_48_split2 s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps_sync_pool (lsmpl.base 261)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot
          (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
        wp_reach
        intro hcl3
        refine call_frame_budget_lscl
          (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
          (x := (s0.sp - 96#64, 0x8000000000000004#64, st))
          (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000004#64 ∧
            FitsEnv M lim st DecodeErrorFromEnv)
          (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl3
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
          ⟨rfl, by decide, hfits_de⟩
          (by sep_focus)
          ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
        simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm,
          hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
          at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
        apply SepWPp.of_sepWP_ret
        simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
          arm64_norm, htrm, htr_s, hspm]
        apply SepWP.exists_elim; intro evs2
        wp_pull_pures
        have hevs_de : DecodeErrorFromEnv evs2 := by assumption
        have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
        apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        wp_done
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt
          rw [hnone] at hres_cur
          subst hres_cur
          have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none (x := x_outer) hsf_eq_res hfits
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
          conv => arg 4; simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, hsp_s]
          apply SepWP.exists_elim; intro evs_dv
          wp_pull_pures
          have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
          have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
          have htrm : sm.trace = s.trace := by assumption
          have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
          have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
          subst hevs0
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
            sliceCursorAt, memRegion_48_split2 s0.sp]
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps_sync_pool (lsmpl.base 261)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot
            (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
          rw [← bv_sub_add_lit s0.sp 96 8] at h40
          apply SepWP.fold h40 (by sep_focus)
          conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
          wp_reach
          intro hcl3
          refine call_frame_budget_lscl
            (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
            (x := (s0.sp - 96#64, 0x8000000000000003#64, st))
            (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000003#64 ∧
              FitsEnv M lim st DecodeErrorFromEnv)
            (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl3
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
            ⟨rfl, by decide, hfits_de⟩
            (by sep_focus)
            ?_
          intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
          simp only [CalleeSavedPreserved] at hcsm2
          obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
          simp (config := { decide := true }) only [arm64_norm, hspm,
            hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
            at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
          apply SepWPp.of_sepWP_ret
          simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
            arm64_norm, htrm, htr_s, hspm]
          apply SepWP.exists_elim; intro evs2
          wp_pull_pures
          have hevs_de : DecodeErrorFromEnv evs2 := by assumption
          have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
          apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
            have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none (x := x_outer) hsf_eq_res hfits
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
            conv => arg 4; simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, hsp_s]
            apply SepWP.exists_elim; intro evs_dv
            wp_pull_pures
            have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
            have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
            have htrm : sm.trace = s.trace := by assumption
            have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
            have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
            subst hevs0
            apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
              sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
            conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_err0
            wp_steps_sync_pool (lsmpl.base 261)
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot
              (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
            wp_reach
            intro hcl3
            refine call_frame_budget_lscl
              (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
              (x := (s0.sp - 96#64, 0x8000000000000005#64, st))
              (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000005#64 ∧
                FitsEnv M lim st DecodeErrorFromEnv)
              (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
              ⟨rfl, by decide, hfits_de⟩
              (by sep_focus)
              ?_
            intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
            simp only [CalleeSavedPreserved] at hcsm2
            obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
            simp (config := { decide := true }) only [arm64_norm, hspm,
              hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
              at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
            apply SepWPp.of_sepWP_ret
            simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
              arm64_norm, htrm, htr_s, hspm]
            apply SepWP.exists_elim; intro evs2
            wp_pull_pures
            have hevs_de : DecodeErrorFromEnv evs2 := by assumption
            have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
            apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
                apply SepWPp.of_sepWP_ret
                simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, htr_s, hsp_s]
                apply SepWP.exists_elim; intro evs_dv
                wp_pull_pures
                have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
                have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
                have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
                have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
                subst hevs0
                have hevs_sf := skipFieldEnv_nil_of_some (x := x_outer) hsf_eq_res
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                simp only [sliceCursorAfter]
                wp_steps_sync_pool (s0.readReg64 Reg.lr)
                simp only [State.setMem_setMem]
                wp_done
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                subst hres_cur
                have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none (x := x_outer) hsf_eq_res hfits
                obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt htag_lt
                apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
                conv => arg 4; simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, hsp_s]
                apply SepWP.exists_elim; intro evs_dv
                wp_pull_pures
                have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
                have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
                have htrm : sm.trace = s.trace := by assumption
                have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
                have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
                subst hevs0
                apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
                apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
                conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                  sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                apply SepWP.exists_elim; intro v_err0
                wp_steps_sync_pool (lsmpl.base 261)
                simp only [State.setMem_setMem]
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot
                  (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
                wp_reach
                intro hcl3
                refine call_frame_budget_lscl
                  (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
                  (x := (s0.sp - 96#64, 0x8000000000000009#64, st))
                  (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64 ∧
                    FitsEnv M lim st DecodeErrorFromEnv)
                  (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl3
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                  (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                  (by simp only [arm64_norm])
                  (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
                  ⟨rfl, by decide, hfits_de⟩
                  (by sep_focus)
                  ?_
                intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
                simp only [CalleeSavedPreserved] at hcsm2
                obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
                simp (config := { decide := true }) only [arm64_norm, hspm,
                  hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
                  at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
                apply SepWPp.of_sepWP_ret
                simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
                  arm64_norm, htrm, htr_s, hspm]
                apply SepWP.exists_elim; intro evs2
                wp_pull_pures
                have hevs_de : DecodeErrorFromEnv evs2 := by assumption
                have hevs_sf := skipFieldEnv_of_decodeErrorFrom (x := x_outer) hsf_eq_res hevs_de
                apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
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
              have himp_rec :
                  skipField (2 * x_rec.bs.length + 2) x_rec.depth x_rec.tag x_rec.wt x_rec.bs = none →
                    skipField (2 * x_outer.bs.length + 2) x_outer.depth x_outer.tag x_outer.wt x_outer.bs = none := by
                intro hrec_none
                dsimp only [x_rec, x_outer] at hrec_none ⊢
                rw [hsf_eq_res, ← hres_cur, hrec_none]
              have hfits_rec : FitsEnv M lim st (SkipFieldEnv x_rec) :=
                fitsEnv_skipField_rec himp_rec hfits
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_507).base) hcl2
              conv => arg 4; simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, hsp_s]
              apply SepWP.exists_elim; intro evs_dv
              wp_pull_pures
              have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
              have hsm1 : sm.readReg64 (Reg.gpr 1#5) = key := by assumption
              have htrm : sm.trace = s.trace := by assumption
              have hevs_dv : DecodeVarint2Env cur evs_dv := by assumption
              have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
              subst hevs0
              apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                show skipBelow3 s0.sp (d + 1) = stackAt sm.sp (skipField3Stack d) from by
                  rw [hspm]]
              conv => arg 4; simp only [sepConj_assoc]
              wp_steps_sync_pool (blkPl_507).base
              simp only [State.setMem_setMem]
              wp_reach
              intro hcl3
              refine call_frame_budget_lscl
                (spec := skipField3SpecAt A lim d (fun _ => True))
                (x := (x_rec, st))
                (ret_pc := (blkPl_507).base + 304#64) hrec hcl3
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
                (by simp only [arm64_norm])
                (by simp only [skipField3SpecAt, arm64_norm]; rfl)
                ?_
                (by sep_focus)
                ?_
              · dsimp only [x_rec]
                simp only [arm64_norm, hiwt_w0_2, sf_truncate32_ofNat64]
                exact ⟨hitag_lt, hd_lt, hrest_lt, hfits_rec⟩
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hcl4
              simp only [CalleeSavedPreserved] at hcsm2
              obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
              simp (config := { decide := true }) only [arm64_norm, hspm,
                hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
                at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
              cases hs : skipField (2 * rest.length + 2) d (key.toNat / 8) iwt rest with
              | none =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                subst hres_cur
                apply SepWPp.of_sepWP_ret
                simp only [skipField3SpecAt, x_rec, hs, sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, htrm, htr_s, hspm]
                apply SepWP.exists_elim; intro evs_rec
                wp_pull_pures
                have hsm2_0 : sm2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
                have hevs_rec : SkipFieldEnv x_rec evs_rec := by assumption
                have hevs_sf := skipFieldEnv_of_rec_none (x_outer := x_outer) (x_rec := x_rec)
                  hs hsf_eq_res hevs_rec
                have hcbz_sm0 : (sm2.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
                  beq_eq_false_iff_ne.mpr hsm2_0
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl]
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                wp_steps_sync_pool (s0.readReg64 Reg.lr)
                simp only [State.setMem_setMem]
                wp_done
              | some rest' =>
                rw [hs] at hres_cur
                dsimp only at hres_cur
                have hrest'_le_rest : rest'.length ≤ rest.length :=
                  (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
                have hrest'_le_n : rest'.length ≤ n := by omega
                have hrest'_le_bs : rest'.length ≤ bs.length := by omega
                have hrest'_suf : IsDropSuffix bs rest' :=
                  suffix_trans hrest_le hrest_suf hrest'_le_rest
                    ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs)
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_507).base + 232#64) hcl4
                conv => arg 4; simp only [skipField3SpecAt, x_rec, hs, sepExists_sepConj_left, sepExists_sepConj_right,
                  sepConj_assoc, arm64_norm, hspm]
                apply SepWP.exists_elim; intro evs_rec
                wp_pull_pures
                have htrm2 : sm2.trace = sm.trace := by assumption
                have hsm2_0 : sm2.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
                have hevs_rec : SkipFieldEnv x_rec evs_rec := by assumption
                have hevs_nil := skipFieldEnv_some_eq_nil (x_rec := x_rec) hs hevs_rec
                subst hevs_nil
                conv => arg 4; rw [show stackAt (s0.sp - 96#64) (skipField3Stack d) = skipBelow3 s0.sp (d + 1) from rfl,
                  ← hpool_nil]
                apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by sep_focus)
                wp_steps_sync_pool ((blkPl_507).base + 232#64)
                simp only [State.setMem_setMem]
                wp_reach
                intro hcl5
                apply sepWPp_to_loopPre3 (d := d) (bufRef := bufRef) (slot := slot) (ptr := ptr)
                  (v_pad := v_stk_2) (bs := bs) (cur := rest')
                  (by dsimp only [skipGroupLoopPre3]; sep_ac_rfl)
                refine ih rest' _ hrest'_le_n hrest'_le_bs hrest'_suf hres_cur
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcl5
                · simp only [arm64_norm]
                · simp only [arm64_norm, hrunm2]
                · simp only [arm64_norm, hspm2]
                · simp only [arm64_norm, htrm2, htrm, htr_s]
                · simp only [arm64_norm, hx19_2]
                · simp only [arm64_norm, hx20_2]
                · simp only [arm64_norm, hx21_2]
                · simp only [arm64_norm, hx22_2]
                · simp only [arm64_norm, hx23_2]
                · simp only [arm64_norm, hx24_2]
                · simp only [arm64_norm, hx25_2]
                · simp only [arm64_norm, hx26_2]
                · simp only [arm64_norm, hx27_2]
                · simp only [arm64_norm, hx28_2]
                · simp only [arm64_norm, hvregs_2]

/-! ## Depth Induction Across All `WireType` Cases -/

theorem skipField6_at_depth_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth (fun _ => True))) := by
  induction depth with
  | zero => exact skipField6_depth_zero_placed_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or_lscl
        (skipField6_varint_placed_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or_lscl
          (skipField6_sixtyFourBit_placed_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or_lscl
            (skipField6_lengthDelimited_placed_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or_lscl
              (skipField6_startGroup_placed_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or_lscl
                (skipField6_endGroup_placed_ok hFromCall d hdepth)
                (skipField6_thirtyTwoBit_placed_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp_lscl (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem skipField6_placed_ok_of_contracts
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hVarint : subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim))) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) :=
  subroutine_ok_skipField3Spec_of_at_depth_lscl
    (skipField6_at_depth_placed_ok
      (ls_subroutine_ok_cl_of_block (callerProg := lsProg_507 H) hFrom)
      (ls_subroutine_ok_cl_of_block (callerProg := lsProg_507 H) hVarint))

/-- Relocatable `[LibsignalPlacement]` verification of `prost::encoding::skip_field::<&mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) from `AllocContractsPlaced M A lim H`. -/
theorem skipField6_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hAlloc : AllocContractsPlaced M A lim H) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) :=
  skipField6_placed_ok_of_contracts
    (dv5_decodeErrorFrom_placed_of_alloc hAlloc)
    (decodeVarint5_placed_ok hAlloc)

/-- Lift `skipField6_placed_ok` (Block `508`) to any caller block program `callerProg` at `lsmpl.base 507`. -/
theorem skipField6_placed_ok_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hAlloc : AllocContractsPlaced M A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 507)
      (withLsCl lsmpl (skipField3Spec A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg) (skipField6_placed_ok hAlloc) hi

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for `skip_field [local#5]`
(Block `508`) on `lsProg_518 ext`. -/
def SkipField6Placed508OkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (withLsCl lsmpl (skipField3Spec A lim))

theorem skipField6_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    SkipField6Placed508OkExtX A lim ext :=
  skipField6_placed_ok_cl (callerProg := lsProg_518 ext) hAlloc

/-- `RawVec<MessageKey>::grow_one` (= `RawVec<Chain>::grow_one`, Block `43`) on `lsProg_518 ext`. -/
theorem growOneMessageKey_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCl lsmpl (growOneChainSpecX M A lim)) :=
  growOneChain_placed_ok_cl (callerProg := lsProg_518 ext) (growOneChain_placed_ok_x hAlloc)

theorem skipField6_placed_of_at_depth [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : ∀ depth, depth < 2 ^ 32 → SkipField6AtPlacedOk A lim ext depth (fun _ => True)) :
    SkipField6PlacedOkExtX A lim ext :=
  subroutine_ok_skipField3Spec_of_at_depth_placed h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlacedBudget
