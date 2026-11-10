/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAuxFd
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable Top-Level `kpkMarkPoll` Proof

Proves `kpkMarkPoll_placed_ok_of_envSpec_fd` and `kpkMarkPoll_placed_ok_fd` against
`withFdsGe3Closed (kpkMarkPollSpecPlaced …)` on Block `578` (`lsProg_578 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv TraceFsSound extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkMarkPollGhost ReadRule cliBcmpName cliBcmpSpec dirAt keyName kpkMarkBoxAt
   subroutine_ok_withFsInv withFsInv_entry)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20 cs_x23 cs_x24 cs_x26 cs_x28 cs_x29 epiloguePre
   files_eq_of_fsInv_trace_eq kpkFrameSlots kpkMarkRoBundlePlaced kpkMarkRoDataPlaced_of_roLoaded
   kpkMinStk kpkSubMax savedCalleeSlots sepWPp_conseq sepWPp_of_sepWP_fs_placed
   sepWPp_with_stk_bound setWidth_32_setWidth_64 spAligned_sub_f0 stackAt_kpkMark_eq
   stackAt_sub_split subStack_merge_pool_mid subStack_split vecU8Tail vecU8_eq_bytes_tail)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   kpkMarkPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudgetFd
  (kpk_call_decimal_fs_placed_fd kpk_call_dirGet_fs_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkMarkEnvSpec KpkOneTimePreAfterGetEnv cliKpkMarkPollEnv_spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAuxFd
  (kpk_after_ot_get_58_placed_fd)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

set_option maxHeartbeats 1200000 in
/-- Envelope-parametric `FdsGe3Closed`-threaded top-level proof of
`mark_kyber_pre_key_used::{closure#0}` against `withFdsGe3Closed (kpkMarkPollSpecPlaced …)`. -/
theorem kpkMarkPoll_placed_ok_of_envSpec_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok (lsProg_578 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok (lsProg_578 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hEnv : ∀ (F0 : FsFiles) (x : KpkMarkPollGhost) (st0 : M.σ),
      KpkMarkEnvSpec M lim rd DecEnv GetEnv PutEnv MarkEnv F0 x st0)
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hpre_split :
      FdsGe3Closed s0.fs ∧
        (s0.mem ⊨ (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).pre (x, st0) s0 ∗ R) := by
    dsimp only [withFdsGe3Closed] at hpre
    rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre_split with ⟨hfds0, hpre_inner⟩
  obtain ⟨hcrl0, hpre_raw⟩ := extract_withLsCodeRoLoaded hpre_inner
  have hfs0 : FsInv s0.fs.files s0.trace s0 := withFsInv_entry s0
  obtain ⟨wDot, wR0, wR7, wM0, wM6, hwDot, hpre_ro⟩ :=
    kpkMarkRoDataPlaced_of_roLoaded hcrl0.2 hpre_inner
  refine ⟨(kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).pre (x, st0) s0 ∗
    kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6, R,
    by
      rwa [show ((kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).pre (x, st0) s0 ∗
            kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6) ∗ R =
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
            ((kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).pre (x, st0) s0 ∗ R) by sep_ac_rfl],
    ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post
            (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).onPanic
            (x, st0) s0 sf ∗ R))
    = Qp
  have hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post
          (x, st0) s0 sf) →
      Q sf P_f := by
    rw [← hQ_eq]
    intro sf P_f hsp_f hcs_f hPf
    refine ⟨fun hmf => ?_, hsp_f, hcs_f⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  have hEnv0 := hEnv s0.fs.files x st0
  clear hEnv hQ_eq hQp_eq hpre hpre_inner hpre_raw hpre_ro
  dsimp only [kpkMarkPollSpecPlaced, withLsCodeRoLoaded]
  rw [show ∀ (P0 : Prop) (Rest : SepProp) (P1 : Prop) (Ro : SepProp),
        ((⌜P0⌝ ∗ Rest) ∗ ⌜P1⌝) ∗ Ro = ⌜P1⌝ ∗ ⌜P0⌝ ∗ Rest ∗ Ro from fun _ _ _ _ => by sep_ac_rfl]
  kpk_sep_norm
  refine SepWPp.pure_elim fun _ => ?_
  refine SepWPp.pure_elim
    fun ⟨hx0_0, hx8_0, ⟨hkn_lt, hot_path_lt, hot_pOk⟩, hBkOk, hSeenOk, hot_chg, hlr_chg, hfit0⟩ => ?_
  have hfit_ot_pre :
      FitsEnv M lim st0 (KpkOneTimePreAfterGetEnv DecEnv GetEnv s0.fs.files x) :=
    hEnv0.fit_ot_pre hfit0
  have hfit_dec1 : FitsEnv M lim st0 (DecEnv x.id) := hfit_ot_pre.seq_left
  refine sepWPp_with_stk_bound (a := x.fut) (v := x.self)
    (Rest := kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      ((x.fut + 8#64) ↦₆₄ x.baseKeyA) ∗
      ((x.fut + 0x10#64) ↦₃₂ x.id) ∗ ((x.fut + 0x14#64) ↦₃₂ x.signedId) ∗
      ((x.fut + 0x18#64) ↦₈ 0#8) ∗ memRegion (x.fut + 0x19#64) 7 ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗ dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ memRegion x.out 48 ∗ A.pool lim st0 s0)
    (Entails.of_eq (by unfold kpkMarkBoxAt; sep_ac_rfl))
    fun hhi_stk => ?_
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi_stk
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hget_le : getStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hafter58 :=
    @kpk_after_ot_get_58_placed_fd _ M A lim H rd pathOk DecEnv GetEnv PutEnv MarkEnv
      decStk getStk putStk stk hFsAlloc hP hBcmp hDecimal hGet hPut hFs
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hGetFs := subroutine_ok_withFsInv hFs hGet s0.fs.files s0.trace
  clear hFsAlloc hP hBcmp hDecimal hGet hPut
  change s0.pc = (blkPl_578).base at hpc
  dsimp only [lsProg_578] at hFs hDecFs hGetFs hafter58 hpc ⊢

  rw [stackAt_sub_split s0.sp hstk hhi_stk,
      stackAt_kpkMark_eq s0.sp hhi,
      subStack_split s0.sp hdec_le hhi]
  unfold kpkMarkBoxAt kpkFrameSlots
  kpk_sep_norm
  refine SepWPp.exists_elim fun f0 => SepWPp.exists_elim fun f1 =>
    SepWPp.exists_elim fun f2 => SepWPp.exists_elim fun f3 =>
    SepWPp.exists_elim fun tmp32 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 => ?_
  apply sepWPp_of_sepWP_fs_placed
    (mid := lsmpl.base 597) hFs hcrl0 hfs0
  wp_steps_sync_pool (lsmpl.base 597)
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hcrl1 hfs1
  apply bind_sepWPp_state_mark; intro st1
  have hsp1 : st1.sp = s0.sp - 0xf0#64 := by dsimp only [st1]; (try kpk_norm)
  have hfds1 : FdsGe3Closed st1.fs := by
    have hfs_eq : st1.fs = s0.fs := by dsimp only [st1]; kpk_norm
    rwa [hfs_eq]
  dsimp only [st1] at *
  refine kpk_call_decimal_fs_placed_fd hDecFs { n := x.id, ret := s0.sp - 0x80#64 } st0
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - decStk) ∗
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := (blkPl_578).base + bv% (68))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp1)
    (by kpk_norm)
    hcrl1
    hfs1
    hfds1
    (by kpk_norm)
    (by kpk_norm)
    hfit_dec1
    (by
      rw [hsp1]
      unfold epiloguePre kpkMarkBoxAt savedCalleeSlots
      kpk_sep_norm
      sep_focus)
    fun sm1 evsDec1 hpcm1 hrunm1 hspm1 hcsm1 hcrlm1 hfsm1 hfdsm1 htrm1 hevsDec1 => ?_
  have hsm1_sp : sm1.sp = s0.sp - 0xf0#64 := hspm1.trans hsp1
  have hsm1_al : sm1.spAligned = true := spAligned_sub_f0 hsp_align hsm1_sp
  have hsm1_tr : sm1.trace = s0.trace := by rw [htrm1]; kpk_norm
  have hsm1_fp : sm1.readReg64 .x29 = s0.sp - 0x60#64 := by rw [(cs_x29 hcsm1)]; kpk_norm
  let st_get1 : M.σ := M.stepEvents evsDec1 st0
  have hfit_get1_s0 :
      FitsEnv M lim st_get1 (GetEnv s0.fs.files x.kg.oneTime (keyName x.id)) :=
    hfit_ot_pre.seq_right hevsDec1
  change SepWPp _ _ _ ((vecU8 A.repAlloc (s0.sp - 0x80#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
  rw [hsp1, subStack_merge_pool_mid s0.sp hdec_le hhi,
      vecU8_eq_bytes_tail A.repAlloc (s0.sp - 0x80#64) (keyName x.id)
        (s0.sp - 0x78#64) (s0.sp - 0x70#64) (by bv_omega) (by bv_omega)]
  kpk_sep_norm
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr => ?_
  refine SepWPp.pure_elim fun ⟨hn_len, hn_lt, hn_ptr⟩ => ?_
  apply sepWPp_of_sepWP_fs_placed
    (mid := lsmpl.base 589) hFs hcrlm1 hfsm1
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hcrl2 hfs2
  apply bind_sepWPp_state_mark; intro st2
  have hsp2 : st2.sp = s0.sp - 0xf0#64 := by
    dsimp only [st2]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_sp))
  have htr2 : st2.trace = s0.trace := by
    dsimp only [st2]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_tr))
  have hfds2 : FdsGe3Closed st2.fs := by
    have hfs_eq : st2.fs = sm1.fs := by
      dsimp only [st2]; simp only [wp_norm, arm64_norm]
    rwa [hfs_eq]
  have hfiles2 : st2.fs.files = s0.fs.files :=
    files_eq_of_fsInv_trace_eq hfs2 htr2
  have hfit_get1 : FitsEnv M lim st_get1 (GetEnv st2.fs.files x.kg.oneTime (keyName x.id)) := by
    rwa [hfiles2]
  dsimp only [st2] at *
  have htoNat_kn : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine kpk_call_dirGet_fs_placed_fd hGetFs
    { ret := s0.sp - 0xb0#64, self := x.self, dir := x.kg.oneTime,
      nameA := namePtr, name := keyName x.id, nameRo := false }
    st_get1
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - getStk) ∗
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      vecU8Tail A.repAlloc nameCap namePtr (keyName x.id) ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := (blkPl_578).base + bv% (88))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp2)
    (by kpk_norm)
    hcrl2
    hfs2
    hfds2
    (by (try rw [show sm1.sp = s0.sp - 0xf0#64 from hsm1_sp]); kpk_norm)
    (by rw [(cs_x26 hcsm1)]; kpk_norm)
    (by kpk_norm)
    (by
      refine Eq.trans (congrArg BitVec.toNat
        (show _ = BitVec.ofNat 64 (keyName x.id).length by kpk_norm)) ?_
      exact htoNat_kn)
    hkn_lt
    hot_path_lt
    hot_pOk
    hfit_get1
    (by
      rw [hsp2, subStack_split s0.sp hget_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun sm2 evsGet1 gr hpcm2 hrunm2 hspm2 hcsm2 hcrlm2 hfsm2 hfdsm2 hgr2 => ?_
  have hsm2_sp : sm2.sp = s0.sp - 0xf0#64 := hspm2.trans hsp2
  rcases hgr2 with ⟨hgr1, htrm2, hevsGet1⟩
  rw [hfiles2] at hgr1 hevsGet1
  have hgr2_s0 :
      gr = x.kg.oneTime.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace :=
    ⟨hgr1, htrm2.trans htr2⟩
  let evsOt : List AllocEvent := evsDec1 ++ evsGet1
  have hevsOt : KpkOneTimePreAfterGetEnv DecEnv GetEnv s0.fs.files x evsOt :=
    SeqEnv.append hevsDec1 hevsGet1
  have hst_ot : M.stepEvents evsGet1 st_get1 = M.stepEvents evsOt st0 := by
    simp only [st_get1, evsOt, M.stepEvents_append]
  refine sepWPp_conseq ?_
    (hafter58 x st0 (M.stepEvents evsGet1 st_get1) evsOt s0 sm2
      wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 nameCap namePtr tmp32 gr
      hst_ot hfit0 hEnv0 hevsOt
      hstk hhi_stk hsp_align hwDot hBkOk hSeenOk hot_chg hlr_chg
      hn_len hn_lt hn_ptr hgr2_s0
      (by kpk_norm) hrunm2 hsm2_sp
      (by rw [(cs_x29 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_fp)))
      hcrlm2 hfsm2 hfdsm2
      (by
        rw [(cs_vregs hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm1)])
        kpk_norm)
      (by rw [(cs_x19 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm1)]; kpk_norm))
      (by rw [(cs_x20 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm1)]; kpk_norm))
      (by rw [(cs_x23 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x23 hcsm1)]; kpk_norm))
      (by rw [(cs_x24 hcsm2)]; kpk_norm)
      (by rw [(cs_x26 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm1)]; kpk_norm))
      (by rw [(cs_x28 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm1)]; kpk_norm))
      hk_final)
  rw [hsp2, subStack_split s0.sp hget_le hhi]
  unfold epiloguePre
  kpk_sep_norm
  sep_focus

/-- Top-level `FdsGe3Closed`-threaded proof of `mark_kyber_pre_key_used::{closure#0}` against
`withFdsGe3Closed (kpkMarkPollSpecPlaced …)` with the concrete envelope `CliKpkMarkPollEnv`. -/
theorem kpkMarkPoll_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok (lsProg_578 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok (lsProg_578 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed
        (kpkMarkPollSpecPlaced rd pathOk A lim
          (CliKpkMarkPollEnv rd DecEnv GetEnv PutEnv) stk)) :=
  kpkMarkPoll_placed_ok_of_envSpec_fd hFsAlloc hP hBcmp hDecimal hGet hPut hFs
    (fun F0 x st0 => cliKpkMarkPollEnv_spec F0 x st0) hstk

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetFd
