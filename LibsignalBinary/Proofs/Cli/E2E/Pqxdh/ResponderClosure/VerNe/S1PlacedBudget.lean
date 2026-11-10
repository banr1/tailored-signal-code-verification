/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Version-Mismatch Entry Segment (`+0x1e04 → +0x1e78`)

Allocator-budget (`RustCliAllocBudget M`) proof of the initial version-mismatch segment on
Block `518` (`lsProg_518`) under `FitsEnv M lim st0 VerNeS1Env`, threading `LibsignalCodeRoLoaded`,
plain `CodeLoaded`, and `LibsignalFrozen` memory invariants.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack growOneSpeStack
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (pqxdhClosureStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (memRegion48_words6_split_eq)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (memRegion344_3e0_split_eq)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
  rustAllocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget (
  growOneSpe_post_zero_eq growOneSpe_pre_zero_eq
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  bind_sepWP_cl_frame_tail bind_sepWP_cro_frame_tail call_lscl_nopanic_tail
  call_raw_nopanic_cl_tail weaken_frame_tail
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal2Spec growOneSpeSpec
)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Allocation envelope (`VerNeS1Env`) and spatial helpers -/

/-- Allocation event envelope for `VerNe/S1PlacedBudget` (`+0x1e04 → +0x1e78`):
192-byte initial `Vec<SignalProtocolError>` growth (`growOneSpe` from `cap = 0`) followed by
free-only `SessionStructure` drop (`dropSessionStructureLocal2`). -/
def VerNeS1Env : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 192 8) FreeOnlyEvs

theorem fitsGrowZero_of_fitsS1 {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    (h : FitsEnv M lim st0 VerNeS1Env) :
    FitsEnv M lim st0 (GrowOneSpeEnv 0#64) := by
  intro evs hg
  rcases hg with ⟨_, rfl⟩ | ⟨hne, _⟩
  · exact h (rustAllocEvents 192 8) (Or.inl rfl)
  · exact False.elim (hne rfl)

theorem verNeS1Env_of_freeSuffix {evs_f : List AllocEvent} (hf : FreeOnlyEvs evs_f) :
    VerNeS1Env (rustAllocEvents 192 8 ++ evs_f) :=
  Or.inr ⟨rustAllocEvents 192 8, evs_f, rfl, rfl, hf⟩

private theorem sp3e8_336_fold_s1 (sp e1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ e1) ∗
    ((sp + 0x3f0#64) ↦₆₄ e2) ∗
    ((sp + 0x3f8#64) ↦₆₄ e3) ∗
    ((sp + 0x400#64) ↦₆₄ e4) ∗
    ((sp + 0x408#64) ↦₆₄ e5) ∗
    memRegion (sp + 0x410#64) 296 ⊢
    memRegion (sp + 0x3e8#64) 336 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 328) (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320) (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312) (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304) (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296) (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

private theorem pointsTo64_split_sp3e8_s1 (sp w : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ w) =
      (((sp + 0x3e8#64) ↦₃₂ (w.extractLsb' 0 32)) ∗
       ((sp + 0x3ec#64) ↦₃₂ (w.extractLsb' 32 32))) := by
  have h1 : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h1, pointsTo64_split32]

private theorem pointsTo32_pair_sp3e8_s1 (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0x3e8#64) ↦₃₂ lo) ∗ ((sp + 0x3ec#64) ↦₃₂ hi)) =
      ((sp + 0x3e8#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem errs192_split_eq_s1 (errsPtr : BitVec 64) :
    memRegion errsPtr 192 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      (errsPtr ↦₆₄ u_e0) ∗ ((errsPtr + 8#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 16#64) ↦₆₄ u_e2) ∗ ((errsPtr + 24#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 32#64) ↦₆₄ u_e4) ∗ ((errsPtr + 40#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 48#64) 144) := by
  rw [ProofLib.memRegion_split' (b := errsPtr) (n := 8) (k := 184) (b' := errsPtr + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 8#64) (n := 8) (k := 176) (b' := errsPtr + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 16#64) (n := 8) (k := 168) (b' := errsPtr + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 24#64) (n := 8) (k := 160) (b' := errsPtr + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 32#64) (n := 8) (k := 152) (b' := errsPtr + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 40#64) (n := 8) (k := 144) (b' := errsPtr + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight errsPtr, ProofLib.memRegion_eight (errsPtr + 8#64),
      ProofLib.memRegion_eight (errsPtr + 16#64), ProofLib.memRegion_eight (errsPtr + 24#64),
      ProofLib.memRegion_eight (errsPtr + 32#64), ProofLib.memRegion_eight (errsPtr + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_s1 (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer u3ec : BitVec 32) :
    (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₆₄ (u3ec ++ msgVer)) ∗
    ((errsPtr + 16#64) ↦₆₄ e2) ∗ ((errsPtr + 24#64) ↦₆₄ e3) ∗ ((errsPtr + 32#64) ↦₆₄ e4) ∗
    ((errsPtr + 40#64) ↦₆₄ e5) ⊢
    (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 12#64) 36 := by
  have hpair : ((errsPtr + 8#64) ↦₆₄ (u3ec ++ msgVer)) =
      ((errsPtr + 8#64) ↦₃₂ msgVer) ∗ ((errsPtr + 12#64) ↦₃₂ u3ec) := by
    have h12 : errsPtr + 12#64 = (errsPtr + 8#64) + 4#64 := by bv_omega
    rw [h12, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 12#64) (n := 4) (k := 32) (b' := errsPtr + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 16#64) (n := 8) (k := 24) (b' := errsPtr + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 24#64) (n := 8) (k := 16) (b' := errsPtr + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 32#64) (n := 8) (k := 8) (b' := errsPtr + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

/-! ## Budget-synchronized basic-block segments (`+0x1e04 → +0x1e78`) -/

set_option maxHeartbeats 600000 in
theorem p3_ver_ne_1e04_s1_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr u3e0 : BitVec 64) (msgVer u3e8 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x1e04#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx9 : s.readReg64 .x9 = msgVer.setWidth 64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 519) s
      (((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0x3e8#64) ↦₃₂ u3e8) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((s.sp + 0x3e8#64) ↦₃₂ msgVer) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x2 = 7#64 ∧ s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 0x1e30#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgVer.setWidth 64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsmpl.base 519)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 600000 in
theorem p3_err_ver_b_s1_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e30#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 42) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 0x1e48#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsmpl.base 42)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p3_err_ver_c_s1_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State)
    (coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e48#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗
       ((s.sp + 0x408#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗ ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xc0#64) ↦₆₄ s.readReg64 .x27) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗
          ((s.sp + 0x408#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((errsPtr + 0x8#64) ↦₆₄ e1) ∗ ((errsPtr + 0x10#64) ↦₆₄ e2) ∗
          ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1e78#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## `LibsignalCodeRoLoaded`-threaded composition -/

set_option maxHeartbeats 1200000 in
/-- General-`x29`, polymorphic-`Qp`, `LibsignalCodeRoLoaded lsmpl`-threaded proof of `VerNe/S1`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext` under
`FitsEnv M lim st0 VerNeS1Env`. -/
theorem overVerNe_1e04_to_1e78_cro_placed_at_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeS1Env)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
          VerNeS1Env evs ∧
          (P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) s6b ∗
            stackAt s.sp growOneSpeStack)) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s1.readReg64 .x29 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      Qp := by
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine weaken_frame_tail (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine weaken_frame_tail (Entails.of_eq (pointsTo64_split_sp3e8_s1 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_s1_placed_wp A lim ext st0 s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_cro_frame_tail hcro1 hL1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hcro2 hL2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_lscl_nopanic_tail
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hcro2 hL2 hLogClosure hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_s])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hcro3 hL3 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp2_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr3_2, hvm3_2⟩ => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm3_2 (hnext := ?_)
  refine weaken_frame_tail (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs3.trans hx24_2'
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2'
  have hx29_3 : s3.readReg64 .x29 = s1.readReg64 .x29 := hx29_cs3.trans hx29_2
  have hstep3 := p3_err_ver_b_s1_placed_wp A lim ext st0 s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine bind_sepWP_cro_frame_tail hcro3 hL3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hcro4 hL4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_nopanic_tail
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st0))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st0 s4 ∗ stackAt s.sp growOneSpeStack)
    hcro4 hL4 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq M A lim st0 s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne
        (fitsGrowZero_of_fitsS1 hfits), hsp4_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 hL5 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st0 s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine weaken_frame_tail
    (Entails.of_eq (pointsTo32_pair_sp3e8_s1 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (errs192_split_eq_s1 errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = 0#64 := hx21_cs5.trans hx21_4
  have hx24_5 : s5.readReg64 .x24 = s5.sp + 0x370#64 := by
    rw [hx24_cs5, hx24_4, hx24_3, hsp5_s]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans hx27_3)
  have hx29_5 : s5.readReg64 .x29 = s1.readReg64 .x29 := hx29_cs5.trans (hx29_4.trans hx29_3)
  let st5 := M.stepEvents (rustAllocEvents 192 8) st0
  have hstep5 := p3_err_ver_c_s1_placed_wp A lim ext st5 s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_cro_frame_tail hcro5 hL5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hcro6 hL6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine weaken_frame_tail
    (errs48_fold_ver_s1 errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine weaken_frame_tail
    (sp3e8_336_fold_s1 s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_tail
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost), st5))
    (φ := s6.readReg64 .x0 = s.sp + 0xa90#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗ A.pool lim st5 s6 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro6 hL6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_s])
    (And.intro hx0_6 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr) by
      simp (config := { decide := true }) [show s6.readReg64 .lr = _ from hx30_6, wp_norm]))
    (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b hL6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp6_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_d => ?_
  refine SepWPp.pure_elim fun ⟨htr6b_6, hfree_d⟩ => ?_
  refine weaken_frame_tail (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, hx29_cs6b, hvregs_cs6b⟩
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_s
  have htr6b_0 : s6b.trace = s0.trace :=
    htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))
  have hx19_6b : s6b.readReg64 .x19 = coroPtr := hx19_cs6b.trans hx19_6
  have hx29_6b : s6b.readReg64 .x29 = s1.readReg64 .x29 :=
    hx29_cs6b.trans (hx29_6.trans hx29_5)
  have hvregs_6b : calleeSavedVRegs s6b = calleeSavedVRegs s1 := by
    rw [hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]
  have hstep_ev : M.stepEvents evs_d st5 = M.stepEvents (rustAllocEvents 192 8 ++ evs_d) st0 :=
    (M.stepEvents_append (rustAllocEvents 192 8) evs_d st0).symm
  refine SepWPp.done hpc6b hrun6b
    ⟨⟨errsPtr, rustAllocEvents 192 8 ++ evs_d, verNeS1Env_of_freeSuffix hfree_d, ?_⟩,
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hcro6b, hL6b⟩
  rw [← hstep_ev]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `s.sp + 0xc70#64`-specialized `LibsignalCodeRoLoaded lsmpl`-threaded proof of `VerNe/S1`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_to_1e78_cro_placed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeS1Env)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
          VerNeS1Env evs ∧
          (P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) s6b ∗
            stackAt s.sp growOneSpeStack)) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      Qp := by
  have hgen := overVerNe_1e04_to_1e78_cro_placed_at_gen (Qp := Qp)
    ext hLogClosure hGrow hDropSS3 st0 hfits s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne
    msgVer G₁ st hcro1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  rwa [hx29_1] at hgen

/-! ## Plain `CodeLoaded`-threaded composition -/

/-- Budget-threaded `[LibsignalPlacement]` Stage P3 `VerNe` entry segment statement
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`. -/
def OverVerNe1e04To1e78CliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (st0 : M.σ),
    FitsEnv M lim st0 VerNeS1Env →
    ∀ (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64),
      initErrsPtr ≠ 0#64 →
      ∀ (msgVer : BitVec 32) (G₁ : SessionGhost) (st : SessionState (List (BitVec 8))),
        (lsProg_518 ext).CodeLoaded s1.mem →
        s1.pc = (blkPl_518).base + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        s1.readReg64 .x29 = s.sp + 0xc70#64 →
        SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
          (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
           ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
           ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
           ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
           memRegion (s.sp + 0x3e0#64) 344 ∗
           sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
           pqLogLevelCellPlaced ∗
           A.pool lim st0 s1 ∗
           stackAt s.sp growOneSpeStack)
          (fun s6b P_f =>
            (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
              VerNeS1Env evs ∧
              (P_f ⊢
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
                ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
                ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
                ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
                memRegion (s.sp + 0x3e8#64) 336 ∗
                memRegion (s.sp + 0xa90#64) 344 ∗
                A.live errsPtr 192 8 ∗
                (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
                ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
                memRegion (errsPtr + 12#64) 36 ∗
                memRegion (errsPtr + 48#64) 144 ∗
                pqLogLevelCellPlaced ∗
                A.pool lim (M.stepEvents evs st0) s6b ∗
                stackAt s.sp growOneSpeStack)) ∧
            s6b.sp = s.sp ∧
            s6b.trace = s0.trace ∧
            s6b.readReg64 .x19 = coroPtr ∧
            s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
            calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
            (lsProg_518 ext).CodeLoaded s6b.mem)
          Qp

set_option maxHeartbeats 1200000 in
/-- Pointwise proof of `OverVerNe1e04To1e78CliPlacedStmt`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_to_1e78_cli_placed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519) pqxdhLogClosurePlacedSpec)
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (growOneSpeSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (dropSessionStructureLocal2Spec M A lim))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeS1Env)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
          VerNeS1Env evs ∧
          (P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) s6b ∗
            stackAt s.sp growOneSpeStack)) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      Qp := by
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine weaken_frame_tail (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine weaken_frame_tail (Entails.of_eq (pointsTo64_split_sp3e8_s1 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_s1_placed_wp A lim ext st0 s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_cl_frame_tail hL1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hL2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hx29_2' : s2.readReg64 .x29 = s.sp + 0xc70#64 := hx29_2.trans hx29_1
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_cl_tail
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL2 hLogClosure hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_s])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hL3 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp2_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr3_2, hvm3_2⟩ => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm3_2 (hnext := ?_)
  refine weaken_frame_tail (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs3.trans hx24_2'
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2'
  have hx29_3 : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_cs3.trans hx29_2'
  have hstep3 := p3_err_ver_b_s1_placed_wp A lim ext st0 s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine bind_sepWP_cl_frame_tail hL3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hL4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_raw_nopanic_cl_tail
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st0))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st0 s4 ∗ stackAt s.sp growOneSpeStack)
    hL4 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq M A lim st0 s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne
        (fitsGrowZero_of_fitsS1 hfits), hsp4_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hL5 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st0 s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine weaken_frame_tail
    (Entails.of_eq (pointsTo32_pair_sp3e8_s1 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (errs192_split_eq_s1 errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = 0#64 := hx21_cs5.trans hx21_4
  have hx24_5 : s5.readReg64 .x24 = s5.sp + 0x370#64 := by
    rw [hx24_cs5, hx24_4, hx24_3, hsp5_s]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans hx27_3)
  have hx29_5 : s5.readReg64 .x29 = s.sp + 0xc70#64 := hx29_cs5.trans (hx29_4.trans hx29_3)
  let st5 := M.stepEvents (rustAllocEvents 192 8) st0
  have hstep5 := p3_err_ver_c_s1_placed_wp A lim ext st5 s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_cl_frame_tail hL5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hL6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine weaken_frame_tail
    (errs48_fold_ver_s1 errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine weaken_frame_tail
    (sp3e8_336_fold_s1 s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cl_tail
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost), st5))
    (φ := s6.readReg64 .x0 = s.sp + 0xa90#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗ A.pool lim st5 s6 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hL6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_s])
    (And.intro hx0_6 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr) by
      simp (config := { decide := true }) [show s6.readReg64 .lr = _ from hx30_6, wp_norm]))
    (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hL6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp6_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_d => ?_
  refine SepWPp.pure_elim fun ⟨htr6b_6, hfree_d⟩ => ?_
  refine weaken_frame_tail (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, hx29_cs6b, hvregs_cs6b⟩
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_s
  have htr6b_0 : s6b.trace = s0.trace :=
    htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))
  have hx19_6b : s6b.readReg64 .x19 = coroPtr := hx19_cs6b.trans hx19_6
  have hx29_6b : s6b.readReg64 .x29 = s.sp + 0xc70#64 :=
    hx29_cs6b.trans (hx29_6.trans hx29_5)
  have hvregs_6b : calleeSavedVRegs s6b = calleeSavedVRegs s1 := by
    rw [hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]
  have hstep_ev : M.stepEvents evs_d st5 = M.stepEvents (rustAllocEvents 192 8 ++ evs_d) st0 :=
    (M.stepEvents_append (rustAllocEvents 192 8) evs_d st0).symm
  refine SepWPp.done hpc6b hrun6b
    ⟨⟨errsPtr, rustAllocEvents 192 8 ++ evs_d, verNeS1Env_of_freeSuffix hfree_d, ?_⟩,
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hL6b⟩
  rw [← hstep_ev]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Proves `OverVerNe1e04To1e78CliPlacedStmt` on `lsProg_518 ext`. -/
theorem overVerNe_1e04_to_1e78_cli_placed [LibsignalPlacement]
    (hLogClosure : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 519) pqxdhLogClosurePlacedSpec)
    (hGrow : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (growOneSpeSpec M A lim))
    (hDropSS3 : ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 512) (dropSessionStructureLocal2Spec M A lim)) :
    OverVerNe1e04To1e78CliPlacedStmt :=
  fun {_M} A lim {Qp} ext st0 hfits s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
    overVerNe_1e04_to_1e78_cli_placed_at (Qp := Qp) ext (hLogClosure ext)
      (hGrow (A := A) (lim := lim) ext) (hDropSS3 (A := A) (lim := lim) ext)
      st0 hfits s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1



/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` corollaries -/

set_option maxHeartbeats 1200000 in
/-- General-`x29`, polymorphic-`Qp`, `LibsignalFrozen`-threaded proof of `VerNe/S1`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext` under
`FitsEnv M lim st0 VerNeS1Env`. -/
theorem overVerNe_1e04_to_1e78_frozen_placed_at_gen [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeS1Env)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
          VerNeS1Env evs ∧
          (P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) s6b ∗
            stackAt s.sp growOneSpeStack)) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s1.readReg64 .x29 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      Qp := by
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine weaken_frame_tail (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine weaken_frame_tail (Entails.of_eq (pointsTo64_split_sp3e8_s1 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_s1_placed_wp A lim ext st0 s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.bind_sepWP_fr_frame_budget hL1 hfr1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hL2 hfr2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.call_raw_nopanic_fr_budget
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL2 hfr2 (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext)) hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_s])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hL3 hfr3 => ?_)
  have hcro3 : LibsignalCodeRoLoaded lsmpl s3.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.lscro_of_frozen hfr3
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp2_s, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr3_2, hvm3_2⟩ => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm3_2 (hnext := ?_)
  refine weaken_frame_tail (Entails.of_eq hstack_log.symm) (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs3.trans hx24_2'
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2'
  have hx29_3 : s3.readReg64 .x29 = s1.readReg64 .x29 := hx29_cs3.trans hx29_2
  have hstep3 := p3_err_ver_b_s1_placed_wp A lim ext st0 s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine bind_sepWP_cro_frame_tail hcro3 hL3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hcro4 hL4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_lscl_nopanic_tail
    (spec := growOneSpeSpec M A lim)
    (x := ((s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))), st0))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool lim st0 s4 ∗ stackAt s.sp growOneSpeStack)
    hcro4 hL4 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq M A lim st0 s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne
        (fitsGrowZero_of_fitsS1 hfits), hsp4_s, pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 hL5 => ?_)
  rw [growOneSpe_post_zero_eq M A lim st0 s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine weaken_frame_tail
    (Entails.of_eq (pointsTo32_pair_sp3e8_s1 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (errs192_split_eq_s1 errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = 0#64 := hx21_cs5.trans hx21_4
  have hx24_5 : s5.readReg64 .x24 = s5.sp + 0x370#64 := by
    rw [hx24_cs5, hx24_4, hx24_3, hsp5_s]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans hx27_3)
  have hx29_5 : s5.readReg64 .x29 = s1.readReg64 .x29 := hx29_cs5.trans (hx29_4.trans hx29_3)
  let st5 := M.stepEvents (rustAllocEvents 192 8) st0
  have hstep5 := p3_err_ver_c_s1_placed_wp A lim ext st5 s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_cro_frame_tail hcro5 hL5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hcro6 hL6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine weaken_frame_tail
    (errs48_fold_ver_s1 errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine weaken_frame_tail
    (sp3e8_336_fold_s1 s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_lscl_nopanic_tail
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost), st5))
    (φ := s6.readReg64 .x0 = s.sp + 0xa90#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗ A.pool lim st5 s6 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro6 hL6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_s])
    (And.intro hx0_6 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s6.readReg64 .lr) by
      simp (config := { decide := true }) [show s6.readReg64 .lr = _ from hx30_6, wp_norm]))
    (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b hL6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp6_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_d => ?_
  refine SepWPp.pure_elim fun ⟨htr6b_6, hfree_d⟩ => ?_
  refine weaken_frame_tail (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, hx29_cs6b, hvregs_cs6b⟩
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_s
  have htr6b_0 : s6b.trace = s0.trace :=
    htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))
  have hx19_6b : s6b.readReg64 .x19 = coroPtr := hx19_cs6b.trans hx19_6
  have hx29_6b : s6b.readReg64 .x29 = s1.readReg64 .x29 :=
    hx29_cs6b.trans (hx29_6.trans hx29_5)
  have hvregs_6b : calleeSavedVRegs s6b = calleeSavedVRegs s1 := by
    rw [hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]
  have hstep_ev : M.stepEvents evs_d st5 = M.stepEvents (rustAllocEvents 192 8 ++ evs_d) st0 :=
    (M.stepEvents_append (rustAllocEvents 192 8) evs_d st0).symm
  refine SepWPp.done hpc6b hrun6b
    ⟨⟨errsPtr, rustAllocEvents 192 8 ++ evs_d, verNeS1Env_of_freeSuffix hfree_d, ?_⟩,
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hcro6b, hL6b⟩
  rw [← hstep_ev]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Specialization of `overVerNe_1e04_to_1e78_frozen_placed_at_gen` to `x29 = s.sp + 0xc70#64`. -/
theorem overVerNe_1e04_to_1e78_frozen_placed_at [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeS1Env)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ (errsPtr : BitVec 64) (evs : List AllocEvent),
          VerNeS1Env evs ∧
          (P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents evs st0) s6b ∗
            stackAt s.sp growOneSpeStack)) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      Qp := by
  have hgen := overVerNe_1e04_to_1e78_frozen_placed_at_gen (Qp := Qp)
    ext hGrow hDropSS3 st0 hfits s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne
    msgVer G₁ st hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  rwa [hx29_1] at hgen

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
