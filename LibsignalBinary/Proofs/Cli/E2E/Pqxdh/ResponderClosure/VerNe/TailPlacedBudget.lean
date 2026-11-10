/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
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
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Version-Mismatch Error Tail (`+0x2cfc → s0.readReg64 .x30`)

Allocator-budget (`RustCliAllocBudget M`) Part B (`+0x3410 → s0.readReg64 .x30`) and combined tail
composition (`over_ver_ne_tail_2cfc_cro_placed_at`, `over_ver_ne_tail_2cfc_cli_placed_ok`) on
Block `518` (`lsProg_518`) under `FitsEnv M lim st0 VerNeTailEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (SessionInline sessionHeap)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack growOneSpeStack
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (words6At)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt decryptPrekeySavedRegsAt_add_cd0 dfPtr_words_eq_decryptionFailedStr
  memRegion20_fold memRegion20_split_eq outPtr48_split_eq repack20_32_64_64_to_64_64_32
  sessionStateAt_pack_head_tail sessionStateAt_unpack_head_tail sp370_36_err_fold
  sp370_36_err_split_eq words3_repack_w32_2w64_w32
  words6At_preKey_decryptionFailed_entails_recordResultAt words6_entails_memRegion48
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (
  HdrP hdrP_coro_344_entails_368 pqLogLevelCellPlaced prevVecAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2PlacedBudget (
  overK2Seg_cli_placed_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv bind_sepWP_cro_frame_tail bind_sepWPp_nopanic_tail call_lscl_nopanic_tail
  cond_eq_adds64_of_ne_neg1_tail_pl fitsAlloc17_of_fitsEnv freeOnlyEvs_append
  freeOnlyEvs_dealloc_192_8 over_ver_ne_tail_partA_cli_placed_ok verNeTailEnv_of_freeSuffix
  weaken_frame_tail
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

/-! ## Loop exit block (`+0x3410 → lsmpl.base 512`) and K2 specialization -/

set_option maxHeartbeats 800000 in
theorem p3_ver_ne_3410_exit_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (blkPl_518).base + 0x3410#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = errsPtr) (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗ ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗ ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗ ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗ ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗ ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 192 8) st) s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗ ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗ ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗ ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗ ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗ ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗ ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗ ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail_pl hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (errsPtr, 192, 8, st)
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-- Pointwise `(M, A, lim, ext)` body of `ErrK2PlacedBudget.OverK2SegCliPlacedStmt`. -/
def OverK2SegCliPlacedAt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s : State) (coroPtr outPtr errTag prevCap prevPtr
      w_370 w_378 w_380 w_388
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)),
    s.pc = lsmpl.base 518 + 0x359c#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.readReg64 .x19 = coroPtr →
    s.readReg64 .x22 = w_22.zeroExtend 64 →
    s.readReg64 .x25 = s.sp + 0x210#64 →
    s.readReg64 .x26 = outPtr →
    s.readReg64 .x28 = errTag →
    SepWP (lsProg_518 ext) retAddr s
      (prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1) ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)

/-! ## Part B (`+0x3410 → s0.readReg64 .x30`) and combined tail theorems -/

set_option maxHeartbeats 1000000 in
/-- Budget-threaded Part B (`+0x3410 → s0.readReg64 .x30`) emitting `FreeOnlyEvs`. -/
theorem over_ver_ne_tail_partB_cli_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hK2 : OverK2SegCliPlacedAt M A lim ext)
    (st1 : M.σ) (s0 s s11 : State) (coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hdf_ne : dfPtr ≠ 0#64) (hw3'_head : w3'.extractLsb' 0 8 = 3#8)
    (hcro11 : LibsignalCodeRoLoaded lsmpl s11.mem)
    (hL11 : (lsProg_518 ext).CodeLoaded s11.mem)
    (hpc11 : s11.pc = (blkPl_518).base + 0x3410#64) (hrun11 : s11.status = .Running)
    (hs11_sp : s11.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr11 : s11.trace = s0.trace) (hx19_11 : s11.readReg64 .x19 = coroPtr)
    (hx22_11 : s11.readReg64 .x22 = errsPtr) (hx23_11 : s11.readReg64 .x23 = 1#64)
    (hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64) (hx26_11 : s11.readReg64 .x26 = outPtr)
    (hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s11
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ A.live errsPtr 192 8 ∗ memRegion errsPtr 192 ∗
       A.live dfPtr 17 1 ∗ ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
       ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗ ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗ ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3') ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st1 s11 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs_b : List AllocEvent, FreeOnlyEvs evs_b ∧
          (P_f ⊢
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs_b st1) sf ∗ stackAt s.sp growOneSpeStack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s11)
      Qp := by
  refine weaken_frame_tail
    (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr dfPtr)) (by sep_focus) ?_
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
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 dfPtr 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine weaken_frame_tail (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64)))
    (by sep_focus) ?_
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine weaken_frame_tail (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hs11_sp]; exact hsp_align
  have hx24_11' : s11.readReg64 .x24 = s11.sp + 0x370#64 := by rw [hx24_11, hs11_sp]
  have hx25_11' : s11.readReg64 .x25 = s11.sp + 0x210#64 := by rw [hx25_11, hs11_sp]
  have hstep12 := p3_ver_ne_3410_exit_cli_placed_wp ext hdealloc st1 s11
    coroPtr errsPtr recG.localIk.cap
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32)
    u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc11 hrun11 hsp11_align
    hx19_11 hx22_11 hx23_11 hx24_11' hx25_11' hx28_11
  rw [hs11_sp] at hstep12
  refine bind_sepWP_cro_frame_tail hcro11 hL11 hstep12 (by sep_focus)
    fun s12 hpc12 hrun12 hcro12 hL12 hregs12 => ?_
  rcases hregs12 with ⟨hsp12_11, htr12_11, hx0_12, hx19_12, hx22_12, _, hx25_12,
    hx26_12, _, hx28_12, _, hx30_12, hvregs_12⟩
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine weaken_frame_tail hstack_restore8 (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG st ⊢
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  refine weaken_frame_tail hpack_ss (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine weaken_frame_tail
    (words6_entails_memRegion48 (s.sp + 0x270#64)
      0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 32 32)
  refine weaken_frame_tail hfold250 (by sep_focus) ?_
  let st2 := M.stepEvents (rustDeallocEvents 192 8) st1
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp12_s : s12.sp = s.sp := hsp12_11
  have hsp12_al : s12.spAligned = true := by simpa only [State.spAligned, hsp12_s] using hsp_align
  refine call_lscl_nopanic_tail
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨coroPtr + 0xf8#64, recG, st⟩ : DropSessionStructureGhost), st2))
    (φ := s12.readReg64 .x0 = coroPtr + 0xf8#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s12.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗ A.pool lim st2 s12 ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro12 hL12 hDropSS3 hpc12 hrun12 hsp12_al hx30_12
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp12_s])
    (And.intro hx0_12 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s12.readReg64 .lr) by
      simp (config := { decide := true }) [show s12.readReg64 .lr = _ from hx30_12, wp_norm]))
    (by sep_focus)
    (hnext := fun s13 hpc13 hrun13 hsp13_12 _ hcs13 hcro13 hL13 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  conv => arg 4; simp only [hsp12_s, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => ?_
  refine SepWPp.pure_elim fun ⟨htr13_12, hfree_ss⟩ => ?_
  let st3 := M.stepEvents evs_ss st2
  have hstack_k2 :
      stackAt s.sp dropSessionStructureLocal2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_k2) (by sep_focus) ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine weaken_frame_tail (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine weaken_frame_tail
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hsp13_s : s13.sp = s.sp := hsp13_12.trans hsp12_s
  have hsp13_align : (s13.sp &&& 15#64 == 0#64) = true := by rw [hsp13_s]; exact hsp_align
  rcases hcs13 with ⟨hx19_cs13, _, _, hx22_cs13, _, _, hx25_cs13, hx26_cs13, _, hx28_cs13, _, hvregs_cs13⟩
  have hx19_13 : s13.readReg64 .x19 = coroPtr := hx19_cs13.trans hx19_12
  have hx22_13 : s13.readReg64 .x22 = ((17#64 : BitVec 64).extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs13.trans hx22_12
  have hx25_13 : s13.readReg64 .x25 = s13.sp + 0x210#64 := by rw [hx25_cs13, hx25_12, hsp13_s]
  have hx26_13 : s13.readReg64 .x26 = outPtr := hx26_cs13.trans (hx26_12.trans hx26_11)
  have hx28_13 : s13.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs13.trans hx28_12
  have hk2 := hK2 st3 s13 coroPtr outPtr 0x8000000000000018#64
    prevCap prevPtr
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    (w3'.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3'.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    ((17#64 : BitVec 64).extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0 enc
    hpc13 hrun13 hsp13_align hx19_13 hx22_13 hx25_13 hx26_13 hx28_13
  rw [hsp13_s] at hk2
  refine bind_sepWP_cro_frame_tail hcro13 hL13 hk2 (by sep_focus)
    fun sf hpcf hrunf hcrof hLf hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_13, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregs_f⟩
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_k2 => ?_
  refine weaken_frame_tail
    (T := ⌜FreeOnlyEvs evs_k2⌝) (T' := ⌜FreeOnlyEvs evs_k2⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hfree_k2 => ?_
  refine weaken_frame_tail
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine weaken_frame_tail
    (sp370_36_err_fold s.sp
      (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
      w3' w4 ((17#64 : BitVec 64).extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) 17#64 dfPtr 17#64).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗ ((outPtr + 0x8#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x10#64) ↦₆₄ dfPtr) ∗ ((outPtr + 0x18#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3') ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr 0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  refine weaken_frame_tail (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine weaken_frame_tail
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine weaken_frame_tail hout_words (by sep_focus) ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr dfPtr w3' w4 hdf_ne hw3'_head
  rw [show A.repAlloc.live dfPtr 17 1 = A.live dfPtr 17 1 from rfl] at hrec
  refine weaken_frame_tail hrec (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstack_k2.symm) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  have hpool_eq :
      A.pool lim (M.stepEvents evs_k2 st3) sf =
        A.pool lim (M.stepEvents (rustDeallocEvents 192 8 ++ evs_ss ++ evs_k2) st1) sf := by
    dsimp only [st3, st2]
    rw [← M.stepEvents_append, ← M.stepEvents_append]
    simp only [List.append_assoc]
  have hfree_all : FreeOnlyEvs (rustDeallocEvents 192 8 ++ evs_ss ++ evs_k2) :=
    freeOnlyEvs_append (freeOnlyEvs_append freeOnlyEvs_dealloc_192_8 hfree_ss) hfree_k2
  have htrf_0 : sf.trace = s0.trace :=
    htrf_13.trans (htr13_12.trans (htr12_11.trans htr11))
  have hvregsf_11 : calleeSavedVRegs sf = calleeSavedVRegs s11 := by
    rw [hvregs_f, hvregs_cs13, hvregs_12]
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨rustDeallocEvents 192 8 ++ evs_ss ++ evs_k2, hfree_all, ?_⟩, hspf_s, htrf_0,
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
    hcrof, hLf, hvregsf_11⟩
  rw [← hpool_eq]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 600000 in
/-- Pointwise `(M, A, lim, ext)` `LibsignalCodeRoLoaded`-threaded Stage P3/P4 `VerNe` tail
(`(blkPl_518).base + 0x2cfc → s0.readReg64 .x30`) on `lsProg_518 ext`. -/
theorem over_ver_ne_tail_2cfc_cro_placed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hK2 : OverK2SegCliPlacedAt M A lim ext)
    (st0 : M.σ) (hfit : FitsEnv M lim st0 VerNeTailEnv)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : LibsignalCodeRoLoaded lsmpl s7.mem)
    (hL7 : (lsProg_518 ext).CodeLoaded s7.mem)
    (hpc7 : s7.pc = (blkPl_518).base + 0x2cfc#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s7 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, VerNeTailEnv evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            pqLogLevelCellPlaced ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp growOneSpeStack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      Qp := by
  have hpartA := over_ver_ne_tail_partA_cli_placed_ok (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False)
    ext hshim halloc st0 (fitsAlloc17_of_fitsEnv hfit)
    s0 s s7 coroPtr ctxPtr outPtr errsPtr msgVer0 msgVer1 recG st
    hcro7 hL7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine bind_sepWPp_nopanic_tail hpartA (by sep_focus)
    fun s11 P_m11 hpc11 hrun11
      ⟨⟨dfPtr, w3', w4, hdf_ne, hw3'_head, hP11⟩,
       hs11_sp, htr11, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, _, hx28_11,
       hvregs_11, hcro11, hL11⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP11) ?_
  have hpartB := over_ver_ne_tail_partB_cli_placed_ok (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False)
    ext hdealloc hDropSS3 hK2
    (M.stepEvents (rustAllocEvents 17 1) st0)
    s0 s s11 coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 b_2c0 enc recG st
    hdf_ne hw3'_head hcro11 hL11 hpc11 hrun11 hs11_sp hsp_align htr11
    hx19_11 hx22_11 hx23_11 hx24_11 hx25_11 hx26_11 hx28_11
  refine bind_sepWPp_nopanic_tail hpartB (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨⟨evs_b, hfree_b, hP_b⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨rustAllocEvents 17 1 ++ evs_b, verNeTailEnv_of_freeSuffix hfree_b, ?_⟩,
    hspf, htrf, hcc, hcrof, hLf, hvregs_f.trans hvregs_11⟩
  rw [M.stepEvents_append]
  exact Entails.trans (sepConj_mono_left hP_b) (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded relocatable `[LibsignalPlacement]` Stage P3/P4 `VerNe` tail statement
(`(blkPl_518).base + 0x2cfc → s0.readReg64 .x30` with `errs.len = 2`) on `lsProg_518 ext`. -/
def OverVerNeTail2cfcCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (st0 : M.σ) (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))),
    FitsEnv M lim st0 VerNeTailEnv →
    LibsignalCodeRoLoaded lsmpl s7.mem →
    (lsProg_518 ext).CodeLoaded s7.mem → s7.pc = (blkPl_518).base + 0x2cfc#64 →
    s7.status = .Running → s7.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true →
    s7.trace = s0.trace → s7.readReg64 .x19 = coroPtr →
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗ memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s7 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, VerNeTailEnv evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            pqLogLevelCellPlaced ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp growOneSpeStack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      Qp

/-- Discharges `OverVerNeTail2cfcCliPlacedStmt` from allocator, shim, and `dropSessionStructureLocal2`
subroutine contracts, instantiating K2 via `ErrK2PlacedBudget.overK2Seg_cli_placed_at`. -/
theorem over_ver_ne_tail_2cfc_cli_placed_ok [LibsignalPlacement]
    (hshim : ∀ ext, subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))) :
    OverVerNeTail2cfcCliPlacedStmt := by
  intro M A lim Qp ext st0 s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr
    msgVer0 msgVer1 b_2c0 enc recG st hfit hcro7 hL7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  have hwp := over_ver_ne_tail_2cfc_cro_placed_at (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False)
    ext (hshim ext) (halloc A lim ext) (hdealloc A lim ext) (hDropSS3 A lim ext)
    (overK2Seg_cli_placed_at A lim ext (hdealloc A lim ext))
    st0 hfit s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr
    msgVer0 msgVer1 b_2c0 enc recG st hcro7 hL7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine bind_sepWPp_nopanic_tail (F := emp) hwp (sepConj_emp _).symm
    fun sf P_mf hpcf hrunf ⟨hpost, hspf, htrf, hcc, _, hLf, hvregs⟩ => ?_
  rw [sepConj_emp]
  exact SepWPp.done hpcf hrunf ⟨hpost, hspf, htrf, hcc, hLf, hvregs⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudget
