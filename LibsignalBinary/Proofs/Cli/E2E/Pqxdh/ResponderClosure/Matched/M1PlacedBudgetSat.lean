/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat`-Backed `VmPreserved` `Matched/M1PlacedBudget` (`M1PlacedBudgetSat`)

Additive `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget` on Block `50`
(`<libsignal_protocol::state::session::SessionRecord>::promote_matching_session`), adding
`16` B below the inner `1184`-byte frame (`promoteMatchingSessionMatchStack16 = 1200` B)
for `blackBoxSpecSat` (`withVmPreserved (withStack blackBoxSpec 16)`) and weakening the
internal loop VReg postcondition to `calleeSavedVRegs` (`d8`–`d15`), discharged inside
`M2BridgePlacedBudgetSat`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SessionState PublicKey)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks blkPC_50 blkPl_50 lsmpl lsρ
   IsLsBlockProg ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_plain
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withLsCl
   ls_externAt?_of_mem)
open CryptoVerification.RustHeap
  (RustAlloc vecU8At vecHeader vecAt)
open CryptoVerification.LibsignalSessionRepr
  (VecGhost vecGhostAt chainAt leBytes)
open CryptoVerification.LibsignalTripleRatchet (blackBoxSpec)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost sessionStateAt optSenderChainAt optTailVecAt)
open CryptoVerification.LibsignalPublicApiRepr
  (RecordGhost sessionStateReprAt sessionRecordAt PendingRel KyberRel)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
  (PromoteMatchGhost PromoteRawGhost
   promoteSavedRegs promoteMatchingSessionMatchStack promoteMatchingSessionRawSpec
   lsBlackBoxU8Sym)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget
  (promote_prologue_placed_wp)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpec16 blackBoxSpecSat)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## 1. `1200`-Byte (`1184 + 16` B) Specs for `promote_matching_session` -/

/-- Stack depth (`1184 + 16 = 1200` B) for `promote_matching_session` under `blackBoxSpecSat`. -/
abbrev promoteMatchingSessionMatchStack16 : Nat :=
  promoteMatchingSessionMatchStack + 16

/-- Raw Block-`50` matched contract with `16` B below `sp - 1184` for `blackBoxSpecSat`. -/
@[expose] def promoteMatchingSessionRawSpec16 : Spec PromoteRawGhost where
  pre := fun x st =>
    promoteMatchingSessionRawSpec.pre x st ∗ stackAt (st.sp - 1184#64) 16
  post := fun x s0 sf =>
    promoteMatchingSessionRawSpec.post x s0 sf ∗ stackAt (s0.sp - 1184#64) 16

/-- `VmPreserved`-strengthened `promoteMatchingSessionRawSpec16`. -/
@[expose] def promoteMatchingSessionRawBudgetSpec16 : Spec PromoteRawGhost :=
  withVmPreserved promoteMatchingSessionRawSpec16

/-- Record-level Block-`50` matched contract with `promoteMatchingSessionMatchStack16` (`1200` B). -/
@[expose] def promoteMatchingSessionMatchSpec16 (A : RustAlloc) : Spec PromoteMatchGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     x.s.state.version = x.msgVer.zeroExtend 32 ∧
     x.s.aliceBaseKey = x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp promoteMatchingSessionMatchStack16
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp promoteMatchingSessionMatchStack16

/-- `VmPreserved`-strengthened `promoteMatchingSessionMatchSpec16`. -/
@[expose] def promoteMatchingSessionMatchBudgetSpec16 (A : RustAlloc) : Spec PromoteMatchGhost :=
  withVmPreserved (promoteMatchingSessionMatchSpec16 A)

/-! ## 2. Local Normalization, Epilogue (`calleeSavedVRegs`), & `HookSat` Loop -/

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align_pl (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align_pl (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align_pl (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self_pl (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self_pl (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self_pl (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]

private theorem cond_ne_subs64_one_pl {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  omega

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_self_pl (a : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 a) = false :=
  bne_self_eq_false _

private theorem ofNat64_succ_sub_one_pl (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

private theorem cells_96_12_eq_pl (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗
      ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
      ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗
      ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
      ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗
      ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
      ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗
      ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
      ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗
      ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
      ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗
      ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promote_epilogue_placed_sat_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (s0 s2 : State) (outPtr : BitVec 64)
    (hpc : s2.pc = (blkPl_50).base + 180#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = 1#64)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) (s0.readReg64 .x30) s2
      ((∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
       (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢
          (outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 8#64) ↦₈ 1#8) ∗
          cells (s0.sp - 96#64) 12) ∧
        VmPreserved s2 sf ∧
        sf.trace = s0.trace ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono
    (post := fun sf Pf =>
      VmPreserved s2 sf ∧
      (Pf ⊢
        (outPtr ↦₆₄ 0#64) ∗
        ((outPtr + 8#64) ↦₈ 1#8) ∗
        cells (s0.sp - 96#64) 12) ∧
      sf.trace = s0.trace ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf)
    (oom := fun _ => ⌜False⌝) ?_
    (fun _ _ _ _ ⟨hvm, hent, hrest⟩ => ⟨hent, hvm, hrest⟩)
    (fun _ _ _ hf => hf)
  unfold promoteSavedRegs
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  by_vm_steps (
    wp_pull_exists
    wp_steps
    refine SepWP.done (by simp only [hpc, hsp, wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm], ?_,
       by simp only [htr, wp_norm, arm64_norm],
       by simp only [hsp, wp_norm, arm64_norm],
       ⟨by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
        by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
        by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
        by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
        by simp only [hsp, wp_norm, arm64_norm], by simp only [hsp, wp_norm, arm64_norm],
        by simp only [hsp, wp_norm, arm64_norm],
        by simp only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm]
           exact hvregs⟩⟩
    rw [cells_96_12_eq_pl s0.sp]
    sep_frame)

private theorem black_box_placed_ok_m1 [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym)
      blackBoxSpecSat := by
  rcases h_bb with ⟨f_bb, hfH, hfOk⟩
  exact subroutine_ok_of_hookOk
    ((ls_externAt?_of_mem (prog := (blkPC_50).rebase (blkPl_50).base H)
      (sym := lsBlackBoxU8Sym)).trans hfH)
    hfOk

private theorem call_blackBox_sat_m1 [LibsignalPlacement] {H : LibsignalHooks}
    {target_pc ret_pc sp0 : BitVec 64} {s0 s_cur : State} {v : BitVec 64}
    {P F : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hvm0 : VmPreserved s0 s_cur)
    (hpc : s_cur.pc = lsρ lsBlackBoxU8Sym)
    (hrun : s_cur.status = .Running)
    (hsp : s_cur.sp = sp0)
    (hlr : s_cur.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : s_cur.readReg64 (Reg.gpr 0#5) = v)
    (hP : P = stackAt sp0 16 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      VmPreserved s0 sf →
      sf.trace = s_cur.trace →
      sf.sp = sp0 →
      sf.readReg64 (Reg.gpr 0#5) = (v.setWidth 8).zeroExtend 64 →
      CalleeSavedPreserved s_cur sf →
      SepWP ((blkPC_50).rebase (blkPl_50).base H) target_pc sf P post) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) target_pc s_cur P post := by
  have hsp_al : s_cur.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  rw [hP]
  refine SepWP.call_subroutine_frame hbb (x := v) (F := F)
    hpc hrun hsp_al hlr
    (fun R hm => by
      rw [sepConj_assoc] at hm
      dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec]
      simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx0, hm⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj (by
      simpa only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec] using hpost))
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj (by
      simpa only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec] using hpost))
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
    CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec]
  simp only [hsp, sepConj_assoc]
  apply SepWP.pure_elim
  intro hvm_bb
  apply SepWP.pure_elim
  rintro ⟨hx0_sf, htr_sf⟩
  rw [← hP]
  exact hnext sf hret_pc hret_run (hvm0.trans hvm_bb) htr_sf (hsp_eq.trans hsp) hx0_sf hcs

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_last_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (b0 : BitVec 8) (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 180#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0) ∗ stackAt s.sp 16)
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0) ∗ stackAt s.sp 16) ∧
        VmPreserved s sf ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  refine call_blackBox_sat_m1 (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
    (v := 1#64)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun s1 hpc1 hrun1 hvm1 htr1 hsp1 hx0_1 hcs1 => ?_
  have htr1' : s1.trace = s.trace := htr1.trans (by simp only [wp_norm, arm64_norm])
  have hx0_1' : s1.readReg64 (Reg.gpr 0#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_1
  have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = 1#64 :=
    hcs1.2.2.1.trans (by simp only [hx21', wp_norm, arm64_norm])
  have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = outPtr :=
    hcs1.2.2.2.2.1.trans (by simp only [hx23', wp_norm, arm64_norm])
  have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 1#64 :=
    hcs1.2.2.2.2.2.2.1.trans (by simp only [hx25', wp_norm, arm64_norm])
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s :=
    hcs1.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])
  clear hcs1 htr1 hx0_1
  wp_steps
  refine call_blackBox_sat_m1 (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
    (v := 1#64)
    (hvm1.trans (by simp only [wp_norm, arm64_norm]))
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm])
    (by simp only [hrun1, wp_norm, arm64_norm])
    (by simp only [hsp1, wp_norm, arm64_norm])
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm]; rfl)
    (by simp only [hx0_1', hx21_1, hx25_1, wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun sf hpcf hrunf hvmf htrf hspf hx0_f hcsf => ?_
  have htrf' : sf.trace = s.trace :=
    (htrf.trans (by simp only [wp_norm, arm64_norm])).trans htr1'
  have hx0_f' : sf.readReg64 .x0 = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_f
  have hx23_f : sf.readReg64 .x23 = outPtr :=
    hcsf.2.2.2.2.1.trans (by simp only [hx23_1, wp_norm, arm64_norm])
  have hvf : calleeSavedVRegs sf = calleeSavedVRegs s :=
    (hcsf.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])).trans hv1
  exact SepWP.done (by simp only [hpc1, hpcf, hx21_1, wp_norm, arm64_norm]) hrunf
    ⟨rfl, hvmf, htrf', hspf, hx0_f', hx23_f, hvf⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
private theorem promote_ct_eq_loop_step_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (b0 : BitVec 8) (m : Nat) (_hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 128#64) s
      ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0) ∗ stackAt s.sp 16)
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0) ∗ stackAt s.sp 16) ∧
        VmPreserved s s1 ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one_pl hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_pl m
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 1#64 := hx25
  wp_steps
  refine call_blackBox_sat_m1 (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0))
    (v := 1#64)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun sb hpcb hrunb hvmb htrb hspb hx0_b hcsb => ?_
  have htrb' : sb.trace = s.trace := htrb.trans (by simp only [wp_norm, arm64_norm])
  have hx0_b' : sb.readReg64 (Reg.gpr 0#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_b
  have hx19_b : sb.readReg64 (Reg.gpr 19#5) = alicePtr + 1#64 :=
    hcsb.1.trans (by simp only [wp_norm, arm64_norm])
  have hx21_b : sb.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) :=
    hcsb.2.2.1.trans (by simp only [hx21', wp_norm, arm64_norm])
  have hx22_b : sb.readReg64 (Reg.gpr 22#5) = serPtr + 1#64 :=
    hcsb.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])
  have hx23_b : sb.readReg64 (Reg.gpr 23#5) = outPtr :=
    hcsb.2.2.2.2.1.trans (by simp only [hx23', wp_norm, arm64_norm])
  have hx25_b : sb.readReg64 (Reg.gpr 25#5) = 1#64 :=
    hcsb.2.2.2.2.2.2.1.trans (by simp only [hx25', wp_norm, arm64_norm])
  have hvb : calleeSavedVRegs sb = calleeSavedVRegs s :=
    hcsb.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])
  clear hcsb htrb hx0_b
  wp_steps
  refine SepWP.done (by simp only [hpc, hpcb, hx21_b, hbr, wp_norm, arm64_norm])
    (by simp only [hrunb, wp_norm, arm64_norm])
    ⟨rfl, hvmb.trans (by simp only [wp_norm, arm64_norm]),
     by simp only [htrb', wp_norm, arm64_norm],
     by simp only [hspb, wp_norm, arm64_norm],
     by simp only [hx19_b, wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21_b, hsub1],
     by simp only [hx22_b, wp_norm, arm64_norm],
     by simp only [hx23_b, wp_norm, arm64_norm],
     by simp only [hx0_b', hx25_b, wp_norm, arm64_norm],
     by simp only [hvb, wp_norm, arm64_norm]⟩

private theorem promote_ct_eq_loop_placed_wp [LibsignalPlacement]
    {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (bs : List (BitVec 8)) (hne : bs ≠ []) (hlt : bs.length < 2 ^ 64)
    (serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = 1#64) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H)
      ((blkPl_50).base + 180#64) s
      ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs) ∗ stackAt s.sp 16)
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ bs) ∗ (alicePtr ↦ₛ bs) ∗ stackAt s.sp 16) ∧
        VmPreserved s sf ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = 1#64 ∧
        sf.readReg64 .x23 = outPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  induction bs generalizing serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons b0 rest ih =>
    cases rest with
    | nil =>
      dsimp only [List.length_cons, List.length_nil] at hx21
      have hpre_eq : ((serPtr ↦ₛ [b0]) ∗ (alicePtr ↦ₛ [b0]) ∗ stackAt s.sp 16) =
          ((serPtr ↦₈ b0) ∗ (alicePtr ↦₈ b0) ∗ stackAt s.sp 16) := by
        rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
          sepConj_emp, sepConj_emp]
      rw [hpre_eq]
      exact promote_ct_eq_loop_last_placed_wp hbb b0 serPtr alicePtr outPtr s
        hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25
    | cons b1 rest' =>
      have hm_pos : 0 < (b1 :: rest').length := by simp
      have hm_lt : (b1 :: rest').length + 1 < 2 ^ 64 := hlt
      have hlt' : (b1 :: rest').length < 2 ^ 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
        simp only [sepConj_assoc]
      refine SepWP.bind_seq_readOnly
        (promote_ct_eq_loop_step_placed_wp hbb b0 (b1 :: rest').length hm_pos hm_lt
          serPtr alicePtr outPtr s hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25)
        (by sep_focus)
        fun s1 hpc1 hrun1 ⟨hvm1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩ => ?_
      have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
      have hih := ih (by simp) hlt' (serPtr + 1#64) (alicePtr + 1#64) s1
        hpc1 hrun1 hsp_align1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1
      rw [hsp1] at hih
      refine SepWP.bind_seq_readOnly hih (by sep_focus)
        fun sf hpcf hrunf ⟨hvmf, htrf, hspf, hx0_f, hx23_f, hvregs_f⟩ => ?_
      refine SepWP.done hpcf hrunf
        ⟨?_, hvm1.trans hvmf, htrf.trans htr1, hspf, hx0_f, hx23_f, hvregs_f.trans hvregs1⟩
      rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
      sep_ac_rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
/-- `HookSat` `black_box` sibling of `M1PlacedBudget.promote_matching_session_raw_placed_ok`. -/
theorem promote_matching_session_raw_placed_ok_sat [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      promoteMatchingSessionRawBudgetSpec16 := by
  have hbb := black_box_placed_ok_m1 h_bb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, locCap, alicePtr, sessVer, msgVer, serPtr, serBytes, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionRawBudgetSpec16, withVmPreserved,
    promoteMatchingSessionRawSpec16, promoteMatchingSessionRawSpec] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver, hlen⟩ := hpure
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_prologue_placed_wp s0 recPtr locCap alicePtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcap hver)
  · intro s1 _ hpc1 hrun1 ⟨hent1, hvm1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hvregs1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hne : serBytes ≠ [] := by intro he; rw [he] at hlen; contradiction
    have hlt : serBytes.length < 2 ^ 64 := by omega
    have hx21_len : s1.readReg64 .x21 = BitVec.ofNat 64 serBytes.length := by
      rw [hlen]; exact hx21_1
    have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by
      rw [hsp1, sp_sub_1184_align_pl]
      exact hsp_align'
    have hloop := promote_ct_eq_loop_placed_wp hbb serBytes hne hlt serPtr alicePtr outPtr s1
      hpc1 hrun1 hsp1_al hx19_1 hx21_len hx22_1 hx23_1 hx25_1
    rw [hsp1] at hloop
    refine SepWP.bind_seq_readOnly hloop
      (by sep_focus) fun s2 hpc2 hrun2 ⟨hvm2, htr2, hsp2, hx0_2, hx23_2, hvregs2⟩ => ?_
    have hv10 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by simp [calleeSavedVRegs, hvregs1]
    apply SepWP.mono
    · exact SepWP.frame_auto (promote_epilogue_placed_sat_wp s0 s2 outPtr hpc2 hrun2 hsp_align'
        (htr2.trans htr1) hsp2 hx0_2 hx23_2 (hvregs2.trans hv10))
    · intro sf _ _ _ ⟨hentf, hvm3, htrf, hspf, hcsf⟩
      have hvm : VmPreserved s0 sf := hvm1.trans (hvm2.trans hvm3)
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      refine Entails.pure_right hvm ?_
      sep_frame
    · intro _ _ _ hf; exact hf

/-! ## 3. Record-Level `1200`-Byte Frame Refinement & Block-50 Entry Wrappers -/

private theorem subroutine_ok_vmPreserved_refine_frame {α β : Type}
    {prog : Program} {entry : BitVec 64}
    {inner : Spec α} {outer : Spec β}
    (h : subroutine_ok prog entry (withVmPreserved inner))
    (href : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ outer.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ inner.pre y s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ inner.post y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ outer.post x s0 sf ∗ R)))
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ inner.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ inner.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y F R (s0 sf : State),
      (sf.mem ⊨ inner.onOom y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ outer.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    subroutine_ok prog entry (withVmPreserved outer) := by
  refine subroutine_ok_refine_frame h (fun x R s0 hpre => ?_) hpanic hexit hoom
  obtain ⟨y, F, hy_pre, hy_post⟩ := href x R s0 hpre
  refine ⟨y, F, hy_pre, fun sf hpost => ?_⟩
  dsimp only [withVmPreserved] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hy_post sf hpost.2⟩

private theorem stackAt_promoteMatch16_split (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStack16 =
      stackAt (sp - 1184#64) 16 ∗
      stackAt sp promoteMatchingSessionMatchStack := by
  change memRegion (sp - 1200#64) 1200 =
    memRegion ((sp - 1184#64) - 16#64) 16 ∗ memRegion (sp - 1184#64) 1184
  rw [show (sp - 1184#64) - 16#64 = sp - 1200#64 by bv_omega]
  exact ProofLib.memRegion_split' (by decide) (by bv_omega) (by decide)

private theorem stackAt_promoteMatch_eq_pl (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStack =
      (∃∗ w4a0 : BitVec 64, (sp - 1184#64) ↦₆₄ w4a0) ∗
      memRegion (sp - 1176#64) 40 ∗
      (∃∗ w470 : BitVec 64, (sp - 1136#64) ↦₆₄ w470) ∗
      memRegion (sp - 1128#64) 1032 ∗
      cells (sp - 96#64) 12 := by
  change memRegion (sp - 1184#64) 1184 = _
  rw [show (1184 : Nat) = 8 + (40 + (8 + (1032 + 96))) by decide,
    memRegion_split (sp - 1184#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1184#64),
    show sp - 1184#64 + 8#64 = sp - 1176#64 by bv_omega,
    memRegion_split (sp - 1176#64) 40 _ (by decide),
    show sp - 1176#64 + 40#64 = sp - 1136#64 by bv_omega,
    memRegion_split (sp - 1136#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1136#64),
    show sp - 1136#64 + 8#64 = sp - 1128#64 by bv_omega,
    memRegion_split (sp - 1128#64) 1032 96 (by decide),
    show sp - 1128#64 + 1032#64 = sp - 96#64 by bv_omega,
    show (96 : Nat) = 8 * 12 by decide,
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]

private theorem outRegion16_split_pl (outPtr : BitVec 64) :
    memRegion outPtr 16 =
      (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
      memRegion (outPtr + 9#64) 7 := by
  rw [show (16 : Nat) = 8 + (1 + 7) by decide,
    memRegion_split outPtr 8 (1 + 7) (by decide),
    ProofLib.memRegion_eight outPtr,
    memRegion_split (outPtr + 8#64) 1 7 (by decide),
    ProofLib.memRegion_one (outPtr + 8#64),
    show outPtr + 8#64 + 1#64 = outPtr + 9#64 by bv_omega]

private theorem pure_keep_pl {ψ φ : Prop} (h : ψ → φ) :
    (⌜ψ⌝ : SepProp) = ⌜φ⌝ ∗ ⌜ψ⌝ := by
  rw [pure_sepConj_pure]
  congr 1
  exact propext ⟨fun hψ => ⟨h hψ, hψ⟩, fun ⟨_, hψ⟩ => hψ⟩

private def vecGhostRest0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vg.bytes.length) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  (if vg.cap = 0 then emp
   else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ vg.bytes) ∗
     memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length))

private theorem vecGhostAt_eq_split0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    vecGhostAt A vg v =
      ⌜vg.cap.toNat < 2 ^ 63⌝ ∗ (v ↦₆₄ vg.cap) ∗ vecGhostRest0_pl A v vg := by
  have hk := pure_keep_pl
    (ψ := vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0)
    (fun h => h.2.1)
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0_pl
  conv_lhs => rw [hk]
  sep_ac_rfl

private theorem vecGhostAt_restore0_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    (v ↦₆₄ vg.cap) ∗ vecGhostRest0_pl A v vg = vecGhostAt A vg v := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0_pl
  sep_ac_rfl

private def vecGhostRestAlice_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  (v ↦₆₄ vg.cap) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  A.live vg.ptr vg.cap.toNat 1 ∗
  memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length)

private theorem vecGhostAt_eq_split_alice_pl (A : RustAlloc) (v : BitVec 64) (vg : VecGhost)
    (serBytes : List (BitVec 8)) (heq : vg.bytes = serBytes) (hlen : serBytes.length = 33) :
    vecGhostAt A vg v =
      ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ 33#64) ∗
      (vg.ptr ↦ₛ serBytes) ∗ vecGhostRestAlice_pl A v vg := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRestAlice_pl
  rw [heq, hlen]
  have hcongr :
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        if vg.cap = 0 then emp
        else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33)) =
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        (A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33))) := by
    refine pure_sepConj_congr fun ⟨hle, _, _⟩ => ?_
    have hc : vg.cap ≠ 0#64 := by intro hc0; rw [hc0] at hle; simp at hle
    simp [hc]
  rw [hcongr]
  change _ = ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 33) ∗ _
  sep_ac_rfl

private def ssPureProp_pl (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
  (match st.remoteIdentity with
   | none => G.remoteIk.bytes = []
   | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
  G.chains.length = st.receiverChains.length ∧
  G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
  G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

private def ssMid1_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.remoteIk (ss + asm64% ssRemoteIdentityOff) ∗
  vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains)

private def ssMid2_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber

private def ssTail_pl (ss : BitVec 64) (_G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
  ((ss + asm64% ssRegistrationIdsOff) ↦ₛ _G.regIds)

private theorem sessionStateAt_eq_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜ssPureProp_pl G st⌝ ∗
      vecGhostAt A G.localIk ss ∗
      ssMid1_pl A ss G st ∗
      vecGhostAt A G.alice (ss + 0x60#64) ∗
      ssMid2_pl A ss G st ∗
      ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
      ssTail_pl ss G st := by
  unfold sessionStateAt ssPureProp_pl ssMid1_pl ssMid2_pl ssTail_pl
  simp only [sepConj_assoc]
  rfl

private def sessPureProp_pl (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
  G.alice.bytes = s.aliceBaseKey ∧
  G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
  (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

private theorem sessionAt_eq_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ⌜G.alice.bytes = s.aliceBaseKey⌝ ∗
      ⌜sessPureProp_pl G s⌝ ∗
      sessionStateAt A ss G s.state := by
  change ⌜sessPureProp_pl G s⌝ ∗ sessionStateAt A ss G s.state = _
  conv_lhs => rw [pure_keep_pl (ψ := sessPureProp_pl G s) (fun h => h.2.2.1)]
  rw [sepConj_assoc]

private theorem sessionAt_restore_chunks_pl (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    ⌜sessPureProp_pl G s⌝ ∗ sessionStateAt A ss G s.state = sessionStateReprAt A ss G s :=
  rfl

private def promoteMatchFrame_pl (A : RustAlloc) (recPtr outPtr sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost) (s : Session (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr g.prevCap g.prevPtr [] ∗
  ⌜sessPureProp_pl G s⌝ ∗
  ⌜ssPureProp_pl G s.state⌝ ∗
  vecGhostRest0_pl A (recPtr + 0x18#64) G.localIk ∗
  ssMid1_pl A (recPtr + 0x18#64) G s.state ∗
  vecGhostRestAlice_pl A (recPtr + 0x78#64) G.alice ∗
  ssMid2_pl A (recPtr + 0x18#64) G s.state ∗
  ssTail_pl (recPtr + 0x18#64) G s.state ∗
  memRegion (outPtr + 9#64) 7 ∗
  memRegion (sp - 1176#64) 40 ∗
  memRegion (sp - 1128#64) 1032

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_pre_entails_16 (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 : State)
    (hgc : x.g.cur = some G)
    (hx0 : s0.readReg64 .x0 = x.recPtr)
    (hx1 : s0.readReg64 .x1 = x.msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = x.serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hcur : x.r.currentSession = some x.s)
    (hver : x.s.state.version = x.msgVer.zeroExtend 32)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    sessionRecordAt A x.recPtr x.g x.r ∗
      (x.serPtr ↦ₛ x.serBytes) ∗
      memRegion x.outPtr 16 ∗
      stackAt s0.sp promoteMatchingSessionMatchStack16 ⊢
    promoteMatchingSessionRawSpec16.pre
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 ∗
      promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s := by
  dsimp only [promoteMatchingSessionRawSpec16, promoteMatchingSessionRawSpec, promoteMatchFrame_pl]
  simp only [sessionRecordAt, hgc, hcur,
    sessionAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s.state,
    vecGhostAt_eq_split0_pl A (x.recPtr + 0x18#64) G.localIk,
    outRegion16_split_pl x.outPtr,
    stackAt_promoteMatch16_split s0.sp,
    stackAt_promoteMatch_eq_pl s0.sp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ =
    (⌜G.alice.bytes = x.s.aliceBaseKey⌝ ∗ ⌜G.localIk.cap.toNat < 2 ^ 63⌝) ∗ _)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hal_g => Entails.pure_left fun hcap => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hal_g.trans halice
  have hver' : (if x.s.state.sessionVersion = 0#32 then 2#32 else x.s.state.sessionVersion) =
      x.msgVer.zeroExtend 32 := hver
  simp only [vecGhostAt_eq_split_alice_pl A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver', hlen⟩ ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_post_entails_16 (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 sf : State)
    (hgc : x.g.cur = some G)
    (hcur : x.r.currentSession = some x.s)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    promoteMatchingSessionRawSpec16.post
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 sf ∗
      promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s ⊢
    (promoteMatchingSessionMatchSpec16 A).post x s0 sf := by
  dsimp only [promoteMatchingSessionRawSpec16, promoteMatchingSessionRawSpec,
    promoteMatchingSessionMatchSpec16, promoteMatchFrame_pl]
  simp only [sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ = ⌜sessPureProp_pl G x.s⌝ ∗ _)) ?_
  refine Entails.pure_left fun hsess => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hsess.2.2.1.trans halice
  simp only [sessionRecordAt, hgc, hcur,
    ← sessionAt_restore_chunks_pl A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks_pl A (x.recPtr + 0x18#64) G x.s.state,
    ← vecGhostAt_restore0_pl A (x.recPtr + 0x18#64) G.localIk,
    vecGhostAt_eq_split_alice_pl A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    stackAt_promoteMatch16_split s0.sp,
    stackAt_promoteMatch_eq_pl s0.sp,
    pure_sepConj_of_true hsess,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `HookSat` `black_box` sibling of `M1PlacedBudget.promote_matching_session_match_placed_ok`. -/
theorem promote_matching_session_match_placed_ok_sat [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H)
      (blkPl_50).base
      (promoteMatchingSessionMatchBudgetSpec16 A) := by
  refine subroutine_ok_vmPreserved_refine_frame (promote_matching_session_raw_placed_ok_sat h_bb) ?_
  intro x R s0 hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.recPtr ∧
       s0.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
       s0.readReg64 .x2 = x.serPtr ∧
       s0.readReg64 .x3 = 33#64 ∧
       s0.readReg64 .x8 = x.outPtr ∧
       x.r.currentSession = some x.s ∧
       x.s.state.version = x.msgVer.zeroExtend 32 ∧
       x.s.aliceBaseKey = x.serBytes ∧
       x.serBytes.length = 33⌝ ∗
      ((sessionRecordAt A x.recPtr x.g x.r ∗
        (x.serPtr ↦ₛ x.serBytes) ∗
        memRegion x.outPtr 16 ∗
        stackAt s0.sp promoteMatchingSessionMatchStack16) ∗ R) := by
    dsimp only [promoteMatchingSessionMatchSpec16] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hver, halice, hlen⟩, hpre_sp⟩ := hpre'
  cases hgc : x.g.cur with
  | none =>
    exfalso
    have hfalse : s0.mem ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.g.prevCap x.g.prevPtr [] ∗
         (x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
         stackAt s0.sp promoteMatchingSessionMatchStack16 ∗ R) := by
      simp only [sessionRecordAt, hgc, hcur] at hpre_sp
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre_sp
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1
  | some G =>
    refine ⟨⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
             x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩,
            promoteMatchFrame_pl A x.recPtr x.outPtr s0.sp x.g G x.s, ?_, ?_⟩
    · rw [← sepConj_assoc]
      exact Satisfies.mono
        (sepConj_mono_left
          (promoteMatch_pre_entails_16 A x G s0 hgc hx0 hx1 hx2 hx3 hx8 hcur hver halice hlen))
        hpre_sp
    · intro sf hpost
      rw [← sepConj_assoc] at hpost
      exact Satisfies.mono
        (sepConj_mono_left (promoteMatch_post_entails_16 A x G s0 sf hgc hcur halice hlen))
        hpost

/-- Caller-lifted `withLsCodeLoaded` sibling of `M1PlacedBudget.promote_matching_session_match_placed_ok_at`. -/
theorem promote_matching_session_match_placed_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMatchBudgetSpec16 A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 50)
    (subroutine_ok_withLsCodeLoaded_of_plain (promote_matching_session_match_placed_ok_sat h_bb)) hi

/-- Caller-lifted `withLsCl` sibling of `M1PlacedBudget.promote_matching_session_match_placed_cl_ok_at`. -/
theorem promote_matching_session_match_placed_cl_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 50)
      (withLsCl lsmpl (promoteMatchingSessionMatchBudgetSpec16 A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg) (entry := lsmpl.base 50)
    (promote_matching_session_match_placed_ok_sat h_bb) hi

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat
