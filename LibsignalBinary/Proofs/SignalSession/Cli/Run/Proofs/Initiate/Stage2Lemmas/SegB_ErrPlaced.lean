/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegB_Err
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 Early `Err` Unwind (`0x0584 → 0x157c → 0x0350 → ret`)

Verifies `segB_err_placed_ok` on `initProgPlaced` under `[LibsignalPlacement]`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16

set_option maxHeartbeats 1600000 in
/-- Relocatable early `Err` unwind from `0x0584` on `initProgPlaced`: skips drop on the empty
`SessionRecord`, stores the 6 `SpeOwned` words to `x.ret`, and returns via `0x0350`. -/
theorem segB_err_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    {k : RunDrop.SpeOwned} {w0 w1 w2 w3 w4 w5 : BitVec 64} {R_spe Plocals F_extra : SepProp}
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0584)
    (htrace : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hkerr : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error ())
    (hx22 : s.readReg64 (.gpr 22#5) = 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = w0)
    (hx27 : s.readReg64 (.gpr 27#5) = w1)
    (hx25 : s.readReg64 (.gpr 25#5) = w2)
    (hx28 : s.readReg64 (.gpr 28#5) = w3)
    (hx24 : s.readReg64 (.gpr 24#5) = w4)
    (hx21 : s.readReg64 (.gpr 21#5) = w5)
    (hw0 : w0 ≠ (0#64 - 3#64))
    (hspe :
      ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A x.ret k)
    (hLocals :
      initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗ Plocals ⊢
        memRegion (s0.sp - BitVec.ofNat 64 cliInitiateFrame) initLocalsSize)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (memRegion x.ret 48 ∗
        initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗
        initSaved s0 ∗
        (R_spe ∗ Plocals ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ∗
          F_extra))
      Q Qp (initOom s0) := by
  have hpc : s.pc = (blkPl_521).base + 1412#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask4096 : (((s.sp + 4096#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_4096 hsp_mask
  have hsp_mask7312 : (((s.sp + 7312#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_7312 hsp_mask
  have hx19 : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hw0_ne : w0 + 3#64 ≠ 0#64 := by bv_omega
  have hw0_beq : (w0 + 3#64 == 0#64) = false := beq_false_of_ne hw0_ne
  have hw0_dec : decide (w0 + 3#64 = 0#64) = false := decide_eq_false hw0_ne
  have hm1_add : (0#64 - 1#64) + 1#64 = 0#64 := rfl
  have hm1_beq : ((0#64 - 1#64) + 1#64 == 0#64) = true := rfl
  have hm1_dec : decide ((0#64 - 1#64) + 1#64 = 0#64) = true := rfl
  apply sepWPp_of_sepWP_exit
  rw [← hctrl.sp]
  have hfr_fsp : initFreshRecAt s.sp =
      ((s.sp + 296#64) ↦₆₄ 0#64) ∗ ((s.sp + 304#64) ↦₆₄ 8#64) ∗
      ((s.sp + 312#64) ↦₆₄ 0#64) ∗ ((s.sp + 320#64) ↦₆₄ (0#64 - 1#64)) := rfl
  rw [memRegion_48_eq_words6 x.ret, initSaved_eq_fsp hctrl.sp, hfr_fsp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro u5
  apply SepWP.exists_left; intro u4
  apply SepWP.exists_left; intro u3
  apply SepWP.exists_left; intro u2
  apply SepWP.exists_left; intro u1
  apply SepWP.exists_left; intro u0
  dsimp only [initProgPlaced, lsProg_521]
  wp_steps
  have hsp_raw : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl.sp
  have hsp : s.sp = s0.sp - 7408#64 := hctrl.sp
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply hpost
  refine ⟨?_, ?_, ?_⟩
  · simp only [arm64_norm, hsp]
  · apply calleeSavedPreserved_of_regs
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [calleeSavedVRegs, arm64_norm]
      exact hctrl.vregs
  · dsimp only [initSlotSpecPlaced]
    refine Entails.sepExists_right StoresGhost.opened ?_
    refine Entails.sepExists_right initErrVal ?_
    refine Entails.pure_right ⟨slotTrace_of_eq
      (by simp only [arm64_norm, htrace])
      (by simp only [arm64_norm]; exact hctrl.files0), by
        refine ⟨initErrVal_ne_panic, initErrVal_ne_store, ?_⟩
        rw [hS]
        exact initDef_eq_some_none_of_keyPair_err X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle
          x.coins hkerr⟩ ?_
    have hSavedFold :
        ((s.sp + 7312#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s.sp + 7320#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s.sp + 7328#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s.sp + 7336#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s.sp + 7344#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s.sp + 7352#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s.sp + 7360#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s.sp + 7368#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s.sp + 7376#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s.sp + 7384#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s.sp + 7392#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s.sp + 7400#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) = initSaved s0 :=
      (initSaved_eq_fsp hsp_raw).symm
    have hFreshFold :
        ((s.sp + 296#64) ↦₆₄ 0#64) ∗
        ((s.sp + 304#64) ↦₆₄ 8#64) ∗
        ((s.sp + 312#64) ↦₆₄ 0#64) ∗
        ((s.sp + 320#64) ↦₆₄ (0#64 - 1#64)) =
        initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) := by
      rw [← hsp_raw]; rfl
    have hRetEnt :
        ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
          ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        initResAt A x.ret initErrVal :=
      Entails.trans hspe (initResAt_err_of_speOwned A x.ret k)
    have hStkEnt :
        (initFreshRecAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) ∗ Plocals) ∗
          initSaved s0 ∗
          stackAt (s.sp) (stk - cliInitiateFrame) ⊢
        stackAt s0.sp stk := by
      rw [hsp_raw]
      exact Entails.trans
        (sepConj_mono hLocals (Entails.refl _))
        (err_stack_fold s0 (stk_ge_frame hstk) hstk64)
    have hHeap : F_extra ⊢ anyHeap := entails_anyHeap F_extra
    have foc : ∀ {Full Sub Target F Goal : SepProp},
        (Full ⊢ Sub ∗ F) → (Sub ⊢ Target) → (Target ∗ F ⊢ Goal) → (Full ⊢ Goal) :=
      fun hfoc h hrest => Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)
    refine foc (by sep_frame) (Entails.of_eq hSavedFold) ?_
    refine foc (by sep_frame) (Entails.of_eq hFreshFold) ?_
    refine foc (by sep_frame) hRetEnt ?_
    refine foc (by sep_frame) hStkEnt ?_
    refine foc (by sep_frame) hHeap ?_
    sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
end
