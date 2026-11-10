/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.Record.SegTail
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Version-Mismatch Tail Envelope and Part A (`+0x2cfc → +0x3410`)

Defines the tail allocation envelope `VerNeTailEnv` (`SeqEnv (· = rustAllocEvents 17 1) FreeOnlyEvs`),
budget-synchronized basic-block lemmas, framing combinators, the total-correctness 17-byte
allocation step (`+0x33b0 → +0x33b4`), and Part A (`over_ver_ne_tail_partA_cli_placed_ok`) on
Block `518` (`lsProg_518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsLogFilterAddr lsmpl lsro_intro_chk lsρ
  withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (decryptionFailedStr)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (SessionInline sessionHeap)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStack withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.LibsignalTripleRatchet.Record (decryptionFailedStr_split_shared_lb)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt cell_join_head8 cell_split_head8 extractLsb0_8_of_unpack64_cons
  memRegion48_words6_split_eq memRegion_17_split_eq sessionStateAt_pack_head_tail
  sessionStateAt_unpack_head_tail
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (
  dropSpe2VerSpec drop_spe2_ver_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

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

/-! ## Allocation envelope (`VerNeTailEnv`) -/

/-- Allocation event envelope for `VerNe/TailPlacedBudget` (`+0x2cfc → s0.readReg64 .x30`):
17-byte `"decryption failed"` allocation followed by free-only cleanup (`errs` dealloc,
`SessionStructure` drop, and K2 `previous_sessions` epilogue). -/
def VerNeTailEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 17 1) FreeOnlyEvs

theorem fitsAlloc17_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    (h : FitsEnv M lim st0 VerNeTailEnv) :
    FitsEvents M lim st0 (rustAllocEvents 17 1) :=
  h (rustAllocEvents 17 1) (Or.inl rfl)

theorem verNeTailEnv_of_freeSuffix {evs_f : List AllocEvent} (hf : FreeOnlyEvs evs_f) :
    VerNeTailEnv (rustAllocEvents 17 1 ++ evs_f) :=
  Or.inr ⟨rustAllocEvents 17 1, evs_f, rfl, rfl, hf⟩

theorem freeOnlyEvs_dealloc_192_8 : FreeOnlyEvs (rustDeallocEvents 192 8) := by
  intro ev h
  simp only [rustDeallocEvents, List.mem_singleton] at h
  exact ⟨8, 192, h⟩

theorem freeOnlyEvs_append {l₁ l₂ : List AllocEvent}
    (h₁ : FreeOnlyEvs l₁) (h₂ : FreeOnlyEvs l₂) : FreeOnlyEvs (l₁ ++ l₂) := by
  intro ev h
  rcases List.mem_append.mp h with h | h
  · exact h₁ ev h
  · exact h₂ ev h

/-! ## Basic blocks for Part A (`+0x2cfc → +0x3410`) -/

theorem cond_eq_adds64_of_ne_neg1_tail_pl {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; revert h; bv_omega

set_option maxHeartbeats 800000 in
theorem p3_ver_ne_2cfc_33b0_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (st : M.σ) (s : State) (coroPtr retPtr savedX27 ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x2cfc#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x33b0#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ pqLogLevelCellPlaced ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ pqLogLevelCellPlaced ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail_pl hcap_ne
  unfold pqLogLevelCellPlaced lsLogFilterAddr
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_518 ext ((blkPl_518).base + 0x33b0#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p3_ver_ne_33b4_dropspe_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hdf_nz : dfPtr ≠ 0#64) (hpc : s.pc = (blkPl_518).base + 0x33b4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗ ((s.sp + 0x278#64) ↦₆₄ u_278) ∗
       ((s.sp + 0x280#64) ↦₆₄ u_280) ∗ ((s.sp + 0x288#64) ↦₆₄ u_288) ∗
       ((s.sp + 0x290#64) ↦₈ u_290) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ ro0) ∗
          ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗ ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x290#64) ↦₈ 3#8) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧ s1.readReg64 .x23 = 2#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext (lsmpl.base 511)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 600000 in
theorem p3_ver_ne_3410_loop_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x3410#64) (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = errsPtr)
    (hx22 : s.readReg64 .x22 = errsPtr) (hx23 : s.readReg64 .x23 = 2#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 511) s
      (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr + 0x30#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr + 0x30#64 ∧ s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 2#64 := hx23
  wp_steps_sync_518 ext (lsmpl.base 511)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## Framing and call combinators -/

theorem weaken_frame_tail {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hP : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.weaken_pre (sepConj_mono_left hent) h

theorem bind_sepWP_cl_frame_tail {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_raw_nopanic_cl_tail {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = spec.post x s sm ∗ F) Qp := by
    refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code R' _ hex => by
        rw [hexit_false] at hex
        exact allowPanic_not_exited hex)
      (fun sf _ ⟨R', hpan⟩ => by
        rw [hpan_false] at hpan
        exact (allowPanic_not_exited hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' _ hoom_post => by
        rw [hoom_false] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  intro R hm _
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem bind_sepWP_cro_frame_tail [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hcrom : LibsignalCodeRoLoaded lsmpl sm.mem :=
    hcro.of_keepsFrozen hsteps.keepsFrozen
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hcrom hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_lscl_nopanic_tail [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (withLsCodeLoaded lsmpl spec).post x s sm ∗ F) Qp := by
    refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code R' _ hex => by
        dsimp only [withLsCodeLoaded] at hex
        rw [hexit_false] at hex
        exact allowPanic_not_exited hex)
      (fun sf _ ⟨R', hpan⟩ => by
        dsimp only [withLsCodeLoaded] at hpan
        rw [hpan_false] at hpan
        exact (allowPanic_not_exited hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' _ hoom_post => by
        dsimp only [withLsCodeLoaded] at hoom_post
        rw [hoom_false] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have hpre1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre1
  intro R hm _
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · dsimp only [withLsCodeLoaded] at hpost
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrom : LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcro.of_keepsFrozen hsteps.keepsFrozen
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hcrom hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem call_lscl_ro_nopanic_tail [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl spec)))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (withLsRoLoaded lsmpl spec).pre x s = (⌜φ ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [withLsRoLoaded]
    rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_lscl_nopanic_tail (spec := withLsRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ LibsignalRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hL hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro.2⟩ hP hpan_false hexit_false hoom_false hnext

private theorem pointsToBytesRO_decryptionFailed_tail_pl (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  rw [decryptionFailedStr_split_shared_lb, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO_cons,
    pointsToBytesRO_nil, sepConj_emp, show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rfl

theorem drop_frame_tail {prog : Program} {ret : BitVec 64} {s : State}
    {P_all P_drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P_all = P_drop ∗ P)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P_all Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem bind_sepWPp_nopanic_tail {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  rcases hstage (F ∗ R) hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem intro_lsro_decryptionFailed_tail_pl [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hro0 : s.mem ⊨ ((lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) :=
    lsro_intro_chk hcro.2 (by rw [decryptionFailedStr_split_shared_lb]; decide +kernel) hm
  change s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦ᵣ decryptionFailedStr) ∗ (P ∗ R) at hro0
  rw [pointsToBytesRO_decryptionFailed_tail_pl] at hro0
  have hro1 : s.mem ⊨ ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 16#64) ↦₈ᵣ 0x64#8) ∗
      ((((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
        ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hro0
  exact hwp R (Satisfies.of_sep_right hro1) hL

theorem sepWPp_add_cro_tail [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P
      (fun sf P_f => Q sf P_f ∧ LibsignalCodeRoLoaded lsmpl sf.mem) Qp := by
  intro R hm hL
  rcases hwp R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ, hcro.of_keepsFrozen hsteps.keepsFrozen⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem errs48_48_96_join_tail_pl (errsPtr : BitVec 64) :
    memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
      memRegion errsPtr 192 := by
  have h1 :
      memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
        memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr + 0x30#64) (n := 48) (k := 96)
          (b' := errsPtr + 0x60#64) rfl (by bv_omega) (by decide)]
  rw [h1, ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
        (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]

/-! ## Total-correctness 17-byte allocation and Part A (`+0x2cfc → +0x3410`) -/

section Alloc17
attribute [local irreducible] FitsEvents

set_option maxHeartbeats 800000 in
theorem p3_alloc_33b0_tail_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (st0 : M.σ) (hfit17 : FitsEvents M lim st0 (rustAllocEvents 17 1))
    (s : State) (F : SepProp)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x33b4#64) s
      ((A.pool lim st0 s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool lim (M.stepEvents (rustAllocEvents 17 1) st0) s2 ∗
                stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ (lsProg_518 ext).CodeLoaded s2.mem)
      Qp := by
  have hbl : SepWP (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s (A.pool lim st0 s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st0 s1) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x33b4#64) := by
    wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
    refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
    refine ⟨Entails.of_eq (by sep_ac_rfl),
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      ?_, by simp_all [wp_norm, arm64_norm]⟩
    refine ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  refine bind_sepWP_cl_frame_tail hL hbl (by sep_focus)
    fun s1 hpc1 hrun1 hL1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hlay : RustLayoutOk 17 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have hφ :
      (s1.readReg64 .x0).toNat = 17 ∧ (s1.readReg64 .x1).toNat = 1 ∧
        RustLayoutOk 17 1 ∧ FitsEvents M lim st0 (rustAllocEvents 17 1) ∧
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .lr) :=
    ⟨by rw [hx0_1]; rfl, by rw [hx1_1]; rfl, hlay, hfit17,
      ⟨518, by decide, 0x33b4, by decide, hlr1⟩⟩
  refine call_raw_nopanic_cl_tail
    (spec := rustCliAllocNoOomSpec M A lim false) (x := (17, 1, st0))
    (T := A.pool lim st0 s1 ∗ stackAt s.sp allocHookStack) (F := F)
    hL1 (subroutine_ok_allocNoOom_of_budget halloc) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
    hφ (by sep_focus) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustCliAllocNoOomSpec]
  conv => arg 4; simp only [hsp1, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hacp, hoom, _⟩ => ?_
  refine SepWPp.done hpc2 hrun2
    ⟨Entails.of_eq (by sep_ac_rfl), hoom, hsp2, hacp.2.1.trans htr1, hcs, hL2⟩

end Alloc17

set_option maxHeartbeats 1000000 in
/-- Budget-threaded Part A (`+0x2cfc → +0x3410`) on `lsProg_518 ext`. -/
theorem over_ver_ne_tail_partA_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (st0 : M.σ) (hfit17 : FitsEvents M lim st0 (rustAllocEvents 17 1))
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : LibsignalCodeRoLoaded lsmpl s7.mem)
    (hL7 : (lsProg_518 ext).CodeLoaded s7.mem)
    (hpc7 : s7.pc = (blkPl_518).base + 0x2cfc#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x3410#64) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       pqLogLevelCellPlaced ∗ memRegion (s.sp + 0x270#64) 48 ∗
       A.pool lim st0 s7 ∗ stackAt s.sp growOneSpeStack)
      (fun s11 P_f =>
        (∃ dfPtr w3' w4 : BitVec 64, dfPtr ≠ 0#64 ∧ w3'.extractLsb' 0 8 = 3#8 ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion errsPtr 192 ∗
            A.live dfPtr 17 1 ∗ ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
            ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x290#64) ↦₆₄ w3') ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ pqLogLevelCellPlaced ∗
            A.pool lim (M.stepEvents (rustAllocEvents 17 1) st0) s11 ∗
            stackAt s.sp growOneSpeStack)) ∧
        s11.sp = s.sp ∧ s11.trace = s0.trace ∧ s11.readReg64 .x19 = coroPtr ∧
        s11.readReg64 .x22 = errsPtr ∧ s11.readReg64 .x23 = 1#64 ∧
        s11.readReg64 .x24 = s.sp + 0x370#64 ∧ s11.readReg64 .x25 = s.sp + 0x210#64 ∧
        s11.readReg64 .x26 = outPtr ∧ s11.readReg64 .x27 = ctxPtr ∧
        s11.readReg64 .x28 = 0x8000000000000018#64 ∧
        calleeSavedVRegs s11 = calleeSavedVRegs s7 ∧
        LibsignalCodeRoLoaded lsmpl s11.mem ∧ (lsProg_518 ext).CodeLoaded s11.mem)
      Qp := by
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  refine weaken_frame_tail
    (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine weaken_frame_tail
    (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep7b := p3_ver_ne_2cfc_33b0_cli_placed_wp A lim ext hshim st0 s7
    coroPtr outPtr ctxPtr recG.localIk.cap
    (cap_ne_noneCap_of_lt hcap_lt) hpc7 hrun7 hsp7_align hx19_7
  rw [hs7_sp] at hstep7b
  refine bind_sepWP_cro_frame_tail hcro7 hL7 hstep7b (by sep_focus)
    fun s7b hpc7b hrun7b hcro7b hL7b hregs7b => ?_
  rcases hregs7b with ⟨hsp7b, htr7b, hx0_7b, hx1_7b, hx19_7b, hx24_7b, hx25_7b,
    hx26_7b, hx27_7b, _, hvregs_7b⟩
  have hpack_ss7b :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG st ⊢
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  refine weaken_frame_tail hpack_ss7b (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp7b_align : (s7b.sp &&& 15#64 == 0#64) = true := by rw [hsp7b]; exact hsp_align
  have htr7b_0 : s7b.trace = s0.trace := htr7b.trans htr7
  have halloc17 := sepWPp_add_cro_tail hcro7b
    (p3_alloc_33b0_tail_placed_ok (M := M) (A := A) (lim := lim) (Qp := fun _ _ => False)
      ext halloc st0 hfit17 s7b emp hL7b hpc7b hrun7b hsp7b_align hx0_7b hx1_7b)
  rw [sepConj_emp, hsp7b] at halloc17
  refine bind_sepWPp_nopanic_tail
    halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨⟨hP8, hdf_ne, hsp8_7b, htr8_7b, hcs8, hL8⟩, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine weaken_frame_tail hP8 (by sep_focus) ?_
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine weaken_frame_tail hstack_restore8 (by sep_focus) ?_
  let st1 := M.stepEvents (rustAllocEvents 17 1) st0
  refine weaken_frame_tail (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 =>
    SepWPp.exists_elim fun u_df0 => ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64)))
    (by sep_focus) ?_
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine weaken_frame_tail (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7b
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, hx27_cs8, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7b
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7b
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7b
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7b
  have hx27_8 : s8.readReg64 .x27 = ctxPtr := hx27_cs8.trans hx27_7b
  refine intro_lsro_decryptionFailed_tail_pl hcro8 ?_
  have hstep9 := p3_ver_ne_33b4_dropspe_cli_placed_wp A lim ext st1 s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64
    u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine bind_sepWP_cro_frame_tail hcro8 hL8 hstep9 (by sep_focus)
    fun s9 hpc9 hrun9 hcro9 hL9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, _, hx30_9, hvregs_9⟩
  refine drop_frame_tail
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine weaken_frame_tail (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_tail
    (spec := dropSpe2VerSpec M A lim)
    (x := (errsPtr, msgVer0, st1))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool lim st1 s9 ∗ stackAt s.sp dropSpeStack)
    hcro9 hL9 (drop_spe2_ver_placed_ok_at (M := M) (A := A) (lim := lim))
    hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_s])
    hx0_9
    (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 hL10 => ?_)
  dsimp only [dropSpe2VerSpec]
  conv => arg 4; rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, hx27_cs10, hx28_cs10, _, hvregs_cs10⟩
  have hx19_10 : s10.readReg64 .x19 = coroPtr := hx19_cs10.trans hx19_9
  have hx21_10' : s10.readReg64 .x21 = errsPtr := hx21_cs10.trans hx21_9
  have hx22_10 : s10.readReg64 .x22 = errsPtr := hx22_cs10.trans hx22_9
  have hx23_10 : s10.readReg64 .x23 = 2#64 := hx23_cs10.trans hx23_9
  have hloop := p3_ver_ne_3410_loop_cli_placed_wp A lim ext st1 s10 coroPtr errsPtr
    hpc10 hrun10 hsp10_align hx19_10 hx21_10' hx22_10 hx23_10
  refine bind_sepWP_cro_frame_tail hcro10 hL10 hloop (by sep_focus)
    fun s10b hpc10b hrun10b hcro10b hL10b hregs10b => ?_
  rcases hregs10b with ⟨hsp10b_10, htr10b_10, hx0_10b, hx19_10b, _, hx22_10b, hx23_10b,
    hx24_10b, hx25_10b, hx26_10b, hx27_10b, hx28_10b, _, hx30_10b, hvregs_10b⟩
  have hsp10b_s : s10b.sp = s.sp := hsp10b_10.trans hsp10_s
  have hsp10b_al : s10b.spAligned = true := by simpa only [State.spAligned, hsp10b_s] using hsp_align
  have herrs_off :
      ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
      ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
      memRegion (errsPtr + 60#64) 36 =
      ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
      (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
      memRegion ((errsPtr + 0x30#64) + 12#64) 36 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine weaken_frame_tail (Entails.of_eq herrs_off) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_tail
    (spec := dropSpe2VerSpec M A lim)
    (x := (errsPtr + 0x30#64, msgVer1, st1))
    (φ := s10b.readReg64 .x0 = errsPtr + 0x30#64)
    (T := ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
          (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
          memRegion ((errsPtr + 0x30#64) + 12#64) 36 ∗
          A.pool lim st1 s10b ∗ stackAt s.sp dropSpeStack)
    hcro10b hL10b (drop_spe2_ver_placed_ok_at (M := M) (A := A) (lim := lim))
    hpc10b hrun10b hsp10b_al hx30_10b
    (by dsimp only [dropSpe2VerSpec]; rw [hsp10b_s])
    hx0_10b
    (by sep_focus)
    (hnext := fun s11 hpc11 hrun11 hsp11_10b _ hcs11 hcro11 hL11 => ?_)
  dsimp only [dropSpe2VerSpec]
  conv => arg 4; rw [hsp10b_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr11_10b => ?_
  refine weaken_frame_tail (Entails.of_eq (errs48_48_96_join_tail_pl errsPtr)) (by sep_focus) ?_
  have hstack_restore11 :
      memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_spe]; exact Entails.refl _
  refine weaken_frame_tail hstack_restore11 (by sep_focus) ?_
  rcases hcs11 with ⟨hx19_cs11, _, _, hx22_cs11, hx23_cs11, hx24_cs11, hx25_cs11,
    hx26_cs11, hx27_cs11, hx28_cs11, _, hvregs_cs11⟩
  have hsp11_s : s11.sp = s.sp := hsp11_10b.trans hsp10b_s
  have htr11_0 : s11.trace = s0.trace :=
    htr11_10b.trans (htr10b_10.trans (htr10_9.trans (htr9_8.trans (htr8_7b.trans htr7b_0))))
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10b
  have hx22_11 : s11.readReg64 .x22 = errsPtr := hx22_cs11.trans hx22_10b
  have hx23_11 : s11.readReg64 .x23 = 1#64 := hx23_cs11.trans hx23_10b
  have hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64 :=
    hx24_cs11.trans (hx24_10b.trans (hx24_cs10.trans (hx24_9.trans hx24_8)))
  have hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64 :=
    hx25_cs11.trans (hx25_10b.trans (hx25_cs10.trans (hx25_9.trans hx25_8)))
  have hx26_11 : s11.readReg64 .x26 = outPtr :=
    hx26_cs11.trans (hx26_10b.trans (hx26_cs10.trans (hx26_9.trans hx26_8)))
  have hx27_11 : s11.readReg64 .x27 = ctxPtr :=
    hx27_cs11.trans (hx27_10b.trans (hx27_cs10.trans (hx27_9.trans hx27_8)))
  have hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64 :=
    hx28_cs11.trans (hx28_10b.trans (hx28_cs10.trans hx28_9))
  have hvregs_11_7 : calleeSavedVRegs s11 = calleeSavedVRegs s7 := by
    rw [hvregs_cs11, hvregs_10b, hvregs_cs10, hvregs_9, hvregs_cs8, hvregs_7b]
  refine SepWPp.done hpc11 hrun11 ?_
  refine ⟨⟨s8.readReg64 .x0, w3', w4, hdf_ne, hw3'_head, Entails.of_eq (by sep_ac_rfl)⟩,
    hsp11_s, htr11_0, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11,
    hvregs_11_7, hcro11, hL11⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
