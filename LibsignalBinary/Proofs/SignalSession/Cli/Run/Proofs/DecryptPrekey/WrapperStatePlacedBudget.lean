/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.ProloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced

/-!
# Budget-Threaded Relocatable Wrapper Reduction for `decrypt_prekey`

Proves the budget-threaded `[LibsignalPlacement]` wrapper reduction for
`signal_session_handshake::decrypt_prekey` on block `520` (`lsProg_520`), along with caller-block
transfer and `LibsignalFrozen` variants.
-/
@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.SpqrV1.Alloc.DoReserveNorm CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl)
open CryptoVerification.CliHandshake.Placed (blkPC_520_pairStep_0x40 blkPl_520 lsProg_520)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.SignalSession.Cli.RunProofs (DpPollK dpCxAt dpFutStartAt dpWordsAt dpWrapFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (DpPrologueMid1Placed DpPrologueMid2Placed DpProloguePostPlaced args13_unpack bv128_hi_append bv128_lo_append bv_add_16_8 bv_add_32_8 bv_off_01 bv_off_02 bv_off_03 bv_off_04 bv_off_05 bv_off_06 bv_off_07 bv_off_08 bv_off_09 bv_off_10 bv_off_11 bv_off_12 bv_off_13 bv_off_14 bv_off_15 bv_off_15b bv_off_16 bv_off_17 bv_off_17b bv_off_18 bv_off_19 bv_off_20 bv_off_21 bv_off_22 bv_off_23 bv_off_24 bv_off_25 bv_off_26 bv_off_27 bv_off_28 bv_off_29 bv_off_30 bv_off_31 bv_off_32 bv_off_33 cmn3_ne_zero dpCallerFrame dpCallerFrame_pack dpCxAt_pack dpFutDoneAt_eq dpFutStartAt_pack dpPrologueMid2Prop dpRetRes_pack dpWords5_eq dpWords6_eq readVReg128_setMem_setPC_pre readVReg128_setPC_pre sepWP_unpack_callerFrame sepWP_with_dp_locals sepWP_with_dp_saved sep_rearrange stackAt_dp_epilogue ws6_unpack)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget

noncomputable section

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DecryptPrekeyGhostStateBudget DpPollGhostStateBudget DpPollKStateBudget
   cliDecryptPrekeySpecStateBudget dpPollSpecStateBudget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
  bv128_lo_append bv128_hi_append bv_add_16_8 bv_add_32_8
  bv_off_01 bv_off_02 bv_off_03 bv_off_04 bv_off_05 bv_off_06 bv_off_07 bv_off_08
  bv_off_09 bv_off_10 bv_off_11 bv_off_12 bv_off_13 bv_off_14 bv_off_15 bv_off_15b
  bv_off_16 bv_off_17 bv_off_17b bv_off_18 bv_off_19 bv_off_20 bv_off_21 bv_off_22
  bv_off_23 bv_off_24 bv_off_25 bv_off_26 bv_off_27 bv_off_28 bv_off_29 bv_off_30
  bv_off_31 bv_off_32 bv_off_33
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre

private theorem sepWP_of_vm {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP prog mid s P post :=
  SepWP.mono h (fun _ _ _ _ ⟨hvmp, hpost⟩ => hpost hvmp)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

private def dps_fixedK_placed {M : AllocCostModel}
    (K : DpPollKStateBudget M) (st : M.σ) (s0 : State) : DpPollK where
  Ghost := K.Ghost
  args := K.args
  inv := fun g => K.inv g st s0
  res := fun _ _ => emp
  io := fun _ _ _ _ _ => True
  panics := K.panics
  need := K.need

private theorem dps_sepWPp_seq_keepsFrozen_placed {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P
      (fun sm Pm => s.mem.KeepsFrozen sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (Φ := fun m => s.mem.KeepsFrozen m)
    (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s.mem) h

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_a1_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 : State} {ret : BitVec 64} {g : K.Ghost} {a8 a9 a10 a11 a12 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_520).base)
    (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true)
    (hx8 : s0.readReg64 (Reg.gpr 8#5) = ret)
    (hdrop_eq : (K.args g).drop 8 = [a8, a9, a10, a11, a12])
    (hk : ∀ sa Pa,
      DpPrologueMid1Placed s0 ret a8 a9 a10 a11 a12 sa →
      VmPreserved s0 sa →
      Pa = memRegion (s0.sp - 2144#64) 2088 ∗
             (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗
               dpCallerFrame s0 ret ((K.args g).drop 8)) →
      Q sa Pa) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      ((blkPl_520).base + 36#64)
      s0 (dpWordsAt s0.sp ((K.args g).drop 8) ∗ memRegion ret 48 ∗ K.inv g ∗ stackAt s0.sp stk) Q := by
  dsimp only [lsProg_520]
  rw [← BitVec.add_zero (blkPl_520).base] at hpc
  rw [← sepConj_assoc, ← sepConj_assoc]
  refine sepWP_with_dp_saved hge_wrap hle_wrap fun sfp slr sx28 sx21 sx20 sx19 => ?_
  rw [hdrop_eq, dpWords5_eq s0.sp a8 a9 a10 a11 a12]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (Entails.of_eq (dpWords5_eq s0.sp a8 a9 a10 a11 a12).symm) (by sep_focus)
    rw [← hdrop_eq]
    apply SepWP.fold (dpCallerFrame_pack s0 ret ((K.args g).drop 8)) (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ ?_ hvmp (sep_rearrange (by sep_focus))
    exact
      { pc := by simp only [wp_norm, arm64_norm]
        run := by simp only [wp_norm, arm64_norm, *]
        sp := by simp only [wp_norm, arm64_norm]
        sp_align := by simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢; exact hsp_align
        fp := by simp only [wp_norm, arm64_norm]
        x0 := by simp only [wp_norm, arm64_norm]
        x1 := by simp only [wp_norm, arm64_norm]
        x2 := by simp only [wp_norm, arm64_norm]
        x3 := by simp only [wp_norm, arm64_norm]
        x4 := by simp only [wp_norm, arm64_norm]
        x5 := by simp only [wp_norm, arm64_norm]
        x6 := by simp only [wp_norm, arm64_norm]
        x7 := by simp only [wp_norm, arm64_norm]
        x8 := by simp only [wp_norm, arm64_norm]
        x9 := by simp only [wp_norm, arm64_norm]
        q0 := by simp only [wp_norm, arm64_norm]
        q1 := by simp only [wp_norm, arm64_norm]
        x19 := by simp only [wp_norm, arm64_norm]
        x22 := by simp only [wp_norm, arm64_norm]
        x23 := by simp only [wp_norm, arm64_norm]
        x24 := by simp only [wp_norm, arm64_norm]
        x25 := by simp only [wp_norm, arm64_norm]
        x26 := by simp only [wp_norm, arm64_norm]
        x27 := by simp only [wp_norm, arm64_norm]
        vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm]
        fs := by simp only [wp_norm, arm64_norm]
        trace := by simp only [wp_norm, arm64_norm] }
  )

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_a2_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sa : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 : BitVec 64} {Q : State → SepProp → Prop}
    (ha : DpPrologueMid1Placed s0 ret a8 a9 a10 a11 a12 sa)
    (hk : ∀ sb Pb (f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64) (fstate : BitVec 8) (cx0 cx1 cx2 : BitVec 64),
      DpPrologueMid2Placed s0 ret a8 a9 a10 a11 sb →
      VmPreserved sa sb →
      Pb = dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 →
      Q sb Pb) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      ((blkPl_520).base + 64#64) sa
      (memRegion (s0.sp - 2144#64) 2088 ∗
        (stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗ K.inv g ∗
          dpCallerFrame s0 ret ((K.args g).drop 8)))
      Q := by
  rcases ha with ⟨hpc_a, hrun_a, hsp_a, hsp_align_a, hfp_a, hx0_a, hx1_a,
    hx2_a, hx3_a, hx4_a, hx5_a, hx6_a, hx7_a, hx8_a, hx9_a, hq0_a, hq1_a, hx19_a,
    hx22_a, hx23_a, hx24_a, hx25_a, hx26_a, hx27_a, hvregs_a, hfs_a, htr_a⟩
  dsimp only [lsProg_520]
  refine sepWP_with_dp_locals s0.sp fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 fcoins fstate cx0 cx1 cx2 => ?_
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 ?_ hvmp
      (sep_rearrange (by dsimp only [dpPrologueMid2Prop]; sep_focus))
    exact
      { pc := by simp only [wp_norm, arm64_norm]
        run := by simp only [wp_norm, arm64_norm, *]
        sp := by simp only [wp_norm, arm64_norm, *]
        sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_a ⊢; exact hsp_align_a
        fp := by simp only [wp_norm, arm64_norm, *]
        x0 := by simp only [wp_norm, arm64_norm, *]
        x1 := by simp only [wp_norm, arm64_norm, *]
        x2 := by simp only [wp_norm, arm64_norm, *]
        x4 := by simp only [wp_norm, arm64_norm, *]
        x5 := by simp only [wp_norm, arm64_norm, *]
        x6 := by simp only [wp_norm, arm64_norm, *]
        x7 := by simp only [wp_norm, arm64_norm, *]
        q0 := by simp only [wp_norm, arm64_norm, *]
        q1 := by simp only [wp_norm, arm64_norm, *]
        x19 := by simp only [wp_norm, arm64_norm, *]
        x22 := by simp only [wp_norm, arm64_norm, *]
        x23 := by simp only [wp_norm, arm64_norm, *]
        x24 := by simp only [wp_norm, arm64_norm, *]
        x25 := by simp only [wp_norm, arm64_norm, *]
        x26 := by simp only [wp_norm, arm64_norm, *]
        x27 := by simp only [wp_norm, arm64_norm, *]
        vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
        fs := by simp only [wp_norm, arm64_norm, *]
        trace := by simp only [wp_norm, arm64_norm, *] }
  )

set_option maxHeartbeats 400000 in
private theorem dpWrapper_prologue_b_vm_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {K : DpPollK} {stk : Nat} {s0 sb : State} {ret : BitVec 64} {g : K.Ghost}
    {a8 a9 a10 a11 a12 f4 f5 f6 f7 f8 f9 f10 f11 : BitVec 64}
    {fstate : BitVec 8} {cx0 cx1 cx2 : BitVec 64} {Q : State → SepProp → Prop}
    (hb : DpPrologueMid2Placed s0 ret a8 a9 a10 a11 sb)
    (hargs_eq : K.args g =
      [s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5), s0.readReg64 (Reg.gpr 2#5), s0.readReg64 (Reg.gpr 3#5),
       s0.readReg64 (Reg.gpr 4#5), s0.readReg64 (Reg.gpr 5#5), s0.readReg64 (Reg.gpr 6#5), s0.readReg64 (Reg.gpr 7#5),
       a8, a9, a10, a11, a12])
    (hk : ∀ s1 P1,
      DpProloguePostPlaced s0 ret s1 →
      VmPreserved sb s1 →
      P1 = (memRegion (s0.sp - 104#64) 48 ∗ dpFutStartAt (s0.sp - 2144#64) (K.args g) ∗
              dpCxAt (s0.sp - 136#64) ∗ K.inv g ∗ stackAt (s0.sp - 2144#64) (stk - dpWrapFrame)) ∗
           dpCallerFrame s0 ret ((K.args g).drop 8) →
      Q s1 P1) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      (lsmpl.base 518)
      sb (dpPrologueMid2Prop stk s0 ret g a12 f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2) Q := by
  rcases hb with ⟨hpc_b, hrun_b, hsp_b, hsp_align_b, hfp_b, hx0_b, hx1_b,
    hx2_b, hx4_b, hx5_b, hx6_b, hx7_b, hq0_b, hq1_b, hx19_b,
    hx22_b, hx23_b, hx24_b, hx25_b, hx26_b, hx27_b, hvregs_b, hfs_b, htr_b⟩
  dsimp only [lsProg_520, dpPrologueMid2Prop]
  have hvm_pair :
      VmPreserved sb
        ((sb.writeReg64 (Reg.gpr 8#5)
          (blkPl_520.ρ "libsignal_cli_handshake:.rodata..Lanon.1")).setPC
          (blkPl_520.base + 72#64)) := by
    simp only [wp_norm, arm64_norm]
  apply blkPC_520_pairStep_0x40 blkPl_520.base (Rust.withPanics ext) rfl hpc_b hrun_b
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (dpFutStartAt_pack s0.sp _ _ _ _ _ _ _ _ a8 a9 a10 a11 a12 _) (by sep_focus)
    rw [← hargs_eq]
    apply SepWP.fold (dpCxAt_pack s0.sp _) (by sep_focus)
    apply sepWP_done_tpidr (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hk _ _ ?_ (hvm_pair.trans hvmp) (sep_rearrange (by sep_focus))
    exact
      { pc := by simp only [wp_norm, arm64_norm]
        run := by simp only [wp_norm, arm64_norm, *]
        sp := by simp only [wp_norm, arm64_norm, *]
        sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_b ⊢; exact hsp_align_b
        x0 := by simp only [wp_norm, arm64_norm, *]
        x1 := by simp only [wp_norm, arm64_norm, *]
        x2 := by simp only [wp_norm, arm64_norm, *]
        lr := by simp only [wp_norm, arm64_norm, *]
        fp := by simp only [wp_norm, arm64_norm, *]
        x19 := by simp only [wp_norm, arm64_norm, *]
        x22 := by simp only [wp_norm, arm64_norm, *]
        x23 := by simp only [wp_norm, arm64_norm, *]
        x24 := by simp only [wp_norm, arm64_norm, *]
        x25 := by simp only [wp_norm, arm64_norm, *]
        x26 := by simp only [wp_norm, arm64_norm, *]
        x27 := by simp only [wp_norm, arm64_norm, *]
        vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
        fs := by simp only [wp_norm, arm64_norm, *]
        trace := by simp only [wp_norm, arm64_norm, *] }
  )

private structure dps_EpilogueMidPlaced [LibsignalPlacement] (s0 sm se : State) : Prop where
  pc : se.pc = (blkPl_520).base + 176#64
  run : se.status = .Running
  sp : se.sp = s0.sp - 2144#64
  sp_align : se.spAligned = true
  x22 : se.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : se.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : se.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : se.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : se.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : se.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  vregs : calleeSavedVRegs se = calleeSavedVRegs s0
  fs : se.fs = sm.fs
  trace : se.trace = sm.trace
  vm : VmPreserved sm se

private abbrev dps_epilogueMidProp_placed {M : AllocCostModel}
    (stk : Nat) (s0 s1 sm : State) (ret : BitVec 64)
    {K : DpPollKStateBudget M} (g : K.Ghost) (st : M.σ)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (∃∗ ws : List (BitVec 64),
      ⌜ws.length = 6 ∧ ws.head? ≠ some (BitVec.ofNat 64 (2 ^ 64 - 3))⌝ ∗
        dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
    dpWordsAt s0.sp ((K.args g).drop 8) ∗
    stackAt (s0.sp - 2144#64) (stk - dpWrapFrame) ∗
    memRegion (s0.sp - 2144#64) 704 ∗
    ((s0.sp - 1440#64) ↦₈ 1#8) ∗
    memRegion (s0.sp - 1439#64) 1303 ∗
    memRegion (s0.sp - 136#64) 32 ∗
    ((s0.sp - 104#64) ↦₆₄ w0) ∗ ((s0.sp - 96#64) ↦₆₄ w1) ∗
    ((s0.sp - 88#64) ↦₆₄ w2) ∗ ((s0.sp - 80#64) ↦₆₄ w3) ∗
    ((s0.sp - 72#64) ↦₆₄ w4) ∗ ((s0.sp - 64#64) ↦₆₄ w5) ∗
    memRegion (s0.sp - 56#64) 8 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_a_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    {K : DpPollKStateBudget M} {stk : Nat}
    {s0 s1 sm : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ}
    {Q : State → SepProp → Prop}
    (hp1 : DpProloguePostPlaced s0 ret s1)
    (hpcm : sm.pc = (blkPl_520).base + 100#64)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s1.sp)
    (hcsm : CalleeSavedPreserved s1 sm)
    (hk : ∀ se Pe w0 w1 w2 w3 w4 w5,
      dps_EpilogueMidPlaced s0 sm se →
      Pe = dps_epilogueMidProp_placed stk s0 s1 sm ret g st w0 w1 w2 w3 w4 w5 →
      Q se Pe) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      ((blkPl_520).base + 176#64)
      sm
      ((dpPollSpecStateBudget K (stk - dpWrapFrame)).post
          ⟨s0.sp - 104#64, s0.sp - 2144#64, s0.sp - 136#64, g, st⟩ s1 sm ∗
        dpCallerFrame s0 ret ((K.args g).drop 8))
      Q := by
  dsimp only [lsProg_520]
  have hsp_align_sm : sm.spAligned = true := by
    simp only [State.spAligned, hspm]; exact hp1.sp_align
  have hfp_sm : sm.readReg64 Reg.fp = s0.sp - 48#64 := hcsm.readReg64_fp.trans hp1.fp
  have hx19_sm : sm.readReg64 (.gpr 19#5) = ret := hcsm.readReg64_x19.trans hp1.x19
  have hx22_sm : sm.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) := hcsm.readReg64_x22.trans hp1.x22
  have hx23_sm : sm.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) := hcsm.readReg64_x23.trans hp1.x23
  have hx24_sm : sm.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) := hcsm.readReg64_x24.trans hp1.x24
  have hx25_sm : sm.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) := hcsm.readReg64_x25.trans hp1.x25
  have hx26_sm : sm.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) := hcsm.readReg64_x26.trans hp1.x26
  have hx27_sm : sm.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) := hcsm.readReg64_x27.trans hp1.x27
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs s0 := hcsm.vregs.trans hp1.vregs
  have hsp_s1 : s1.sp = s0.sp - 2144#64 := hp1.sp
  refine sepWP_unpack_callerFrame fun r0 r1 r2 r3 r4 r5 => ?_
  dsimp only [dpPollSpecStateBudget]
  rw [hsp_s1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i ws
  wp_focus_pure; rintro ⟨hws_len, hws_head⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl, hw0_ne⟩ := ws6_unpack hws_len hws_head
  obtain ⟨hw0_add3, hcmn_ne⟩ := cmn3_ne_zero hw0_ne
  rw [dpFutDoneAt_eq s0.sp, dpWords6_eq (s0.sp - 104#64) w0 w1 w2 w3 w4 w5]
  simp only [bv_off_14, bv_off_15, bv_off_15b, bv_off_17, bv_off_17b, sepConj_assoc]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (Entails.of_eq (dpWords6_eq ret w0 w1 w2 w3 w4 w5).symm) (by sep_focus)
    apply SepWP.fold (dpRetRes_pack (res := K.res g st s1 sm)
      ret w0 w1 w2 w3 w4 w5 hw0_ne) (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvm_ea
    refine hk _ _ w0 w1 w2 w3 w4 w5 ?_ (sep_rearrange (by dsimp only [dps_epilogueMidProp_placed]; sep_focus))
    exact
      { pc := by simp only [wp_norm, arm64_norm]
        run := by simp only [wp_norm, arm64_norm, *]
        sp := by simp only [wp_norm, arm64_norm, *]
        sp_align := by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_sm ⊢; exact hsp_align_sm
        x22 := by simp only [wp_norm, arm64_norm, *]
        x23 := by simp only [wp_norm, arm64_norm, *]
        x24 := by simp only [wp_norm, arm64_norm, *]
        x25 := by simp only [wp_norm, arm64_norm, *]
        x26 := by simp only [wp_norm, arm64_norm, *]
        x27 := by simp only [wp_norm, arm64_norm, *]
        vregs := by simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
        fs := by simp only [wp_norm, arm64_norm, *]
        trace := by simp only [wp_norm, arm64_norm, *]
        vm := hvm_ea }
  )

private theorem dps_epilogue_post_mono [LibsignalPlacement] {M : AllocCostModel}
    {K : DpPollKStateBudget M} {stk : Nat}
    {s0 s1 sm sf : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ} {R : SepProp}
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hfs01 : s1.fs = s0.fs) (htr01 : s1.trace = s0.trace) (hvm01 : VmPreserved s0 s1)
    (hfs_mf : sf.fs = sm.fs) (htr_mf : sf.trace = sm.trace) (hvm_mf : VmPreserved sm sf)
    (hm : sf.mem ⊨
      (((∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
        dpWordsAt s0.sp ((K.args g).drop 8) ∗ stackAt s0.sp stk) ∗ emp) ∗ R) :
    sf.mem ⊨
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecStateBudget K stk)).post
        ⟨ret, g, st⟩ s0 sf ∗ R := by
  rw [sepConj_emp] at hm
  dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliDecryptPrekeySpecStateBudget]
  have hent_res :
      (∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ⊢
        (∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s0 sf ws) :=
    Entails.sepExists_elim fun ws =>
      Entails.sepExists_right ws
        (sepConj_mono_right
          (sepConj_mono_right
            (hres g st s0 s1 sm sf ws hfs01 htr01 hvm01 hfs_mf htr_mf hvm_mf)))
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_res)) hm

set_option maxHeartbeats 400000 in
private theorem dps_wrapper_epilogue_b_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    {K : DpPollKStateBudget M} {stk : Nat} (hge_wrap : dpWrapFrame ≤ stk) (hle_wrap : stk ≤ 2 ^ 64)
    {s0 s1 sm se : State} {ret : BitVec 64} {g : K.Ghost} {st : M.σ}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {R : SepProp}
    (hp1 : DpProloguePostPlaced s0 ret s1)
    (hvm01 : VmPreserved s0 s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hsp_align : s0.spAligned = true)
    (he : dps_EpilogueMidPlaced s0 sm se) :
    SepWP (lsProg_520 (Rust.withPanics ext))
      (s0.readReg64 Reg.lr) se
      (dps_epilogueMidProp_placed stk s0 s1 sm ret g st w0 w1 w2 w3 w4 w5)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecStateBudget K stk)).post
              ⟨ret, g, st⟩ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rcases he with ⟨hpc_e, hrun_e, hsp_e, hsp_align_e, hx22_e, hx23_e, hx24_e,
    hx25_e, hx26_e, hx27_e, hvregs_e, hfs_e, htr_e, hvm_ea⟩
  dsimp only [lsProg_520, dps_epilogueMidProp_placed]
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply SepWP.fold (stackAt_dp_epilogue s0.sp hge_wrap hle_wrap w0 w1 w2 w3 w4 w5
      (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
      (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))) (by sep_focus)
    apply SepWP.fold
      (Entails.refl ((∃∗ ws : List (BitVec 64),
          ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
            dpWordsAt ret ws ∗ K.res g st s1 sm ws) ∗
        dpWordsAt s0.sp ((K.args g).drop 8) ∗ stackAt s0.sp stk))
      (by sep_focus)
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvm_eb
    refine ⟨fun hm =>
        dps_epilogue_post_mono hres hp1.fs hp1.trace hvm01
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (hvm_ea.trans hvm_eb) hm,
      by simp only [wp_norm, arm64_norm, *], ?_⟩
    constructor <;> simp only [calleeSavedVRegs, wp_norm, arm64_norm, *]
  )

theorem dps_cliDecryptPrekey_ok_state_impl_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecStateBudget K stk)) := by
  have hge_wrap : dpWrapFrame ≤ stk := by omega
  have hle_wrap : stk ≤ 2 ^ 64 := by omega
  have hpoll_rocl : subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (dpPollSpecStateBudget K (stk - dpWrapFrame))) :=
    CryptoVerification.LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := lsProg_520 (Rust.withPanics ext))
      (hK (stk - dpWrapFrame) (by omega) (by omega))
  clear hK
  wpp_init x s0
  obtain ⟨ret, g, st⟩ := x
  dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliDecryptPrekeySpecStateBudget] at *
  have hx8 : s0.readReg64 Reg.x8 = ret := by assumption
  have hlen13 : (K.args g).length = 13 := by assumption
  have htake8 : (K.args g).take 8 =
      [s0.readReg64 Reg.x0, s0.readReg64 Reg.x1, s0.readReg64 Reg.x2, s0.readReg64 Reg.x3,
       s0.readReg64 Reg.x4, s0.readReg64 Reg.x5, s0.readReg64 Reg.x6, s0.readReg64 Reg.x7] := by
    assumption
  have hsp_le : stk ≤ s0.sp.toNat := by assumption
  have hcrl0 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  obtain ⟨a8, a9, a10, a11, a12, hdrop_eq, hargs_eq⟩ := args13_unpack hlen13 htake8
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a1_vm_placed (K := dps_fixedK_placed K st s0) (g := g)
    hge_wrap hle_wrap hpc hrun hsp_align hx8 hdrop_eq ?_
  rintro sa _ ha hvm_a1 rfl hkf1
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a2_vm_placed (K := dps_fixedK_placed K st s0) (g := g) ha ?_
  rintro sb _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 hb hvm_a2 rfl hkf2
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_b_vm_placed (K := dps_fixedK_placed K st s0) (g := g) hb hargs_eq ?_
  rintro s1 _ hp1 hvm_b rfl hkf3
  have hvm01 : VmPreserved s0 s1 := (hvm_a1.trans hvm_a2).trans hvm_b
  have hsp_le1 : stk - dpWrapFrame ≤ (s0.sp - 2144#64).toNat := by
    have hw : dpWrapFrame = 2144 := rfl
    rw [hw] at hge_wrap ⊢
    bv_omega
  have hcrl1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    hcrl0.of_keepsFrozen ((hkf1.trans hkf2).trans hkf3)
  exact CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SepWPp.call_withLsRoCl
    (spec := dpPollSpecStateBudget K (stk - dpWrapFrame))
    (x := LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.DpPollGhostStateBudget.mk (s0.sp - 104#64) (s0.sp - 2144#64) (s0.sp - 136#64) g st)
    (F := dpCallerFrame s0 ret ((K.args g).drop 8))
    hpoll_rocl hcrl1 hp1.pc hp1.run hp1.sp_align hp1.lr
    (fun R' hm => by
      dsimp only [dpPollSpecStateBudget]
      rw [hp1.sp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hp1.x0, hp1.x1, hp1.x2, hlen13, hsp_le1⟩, ?_⟩
      dsimp only [dps_fixedK_placed] at hm
      have hm' :=
        Satisfies.mono
          (sepConj_mono_left
            (sepConj_mono_left
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_left (hinv g st s0 s1 hp1.fs hp1.trace hvm01)))))))
          hm
      simpa only [sepConj_assoc] using hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf_pan _ hmpan => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        dpPollSpecStateBudget, cliDecryptPrekeySpecStateBudget] at hmpan ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmpan
      obtain ⟨⟨htr_pan, hpan_k⟩, hmpan_rest⟩ := hmpan
      rw [hp1.trace] at htr_pan
      rw [← sepConj_assoc] at hmpan_rest
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_pan, hpan_k⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmpan_rest⟩)
    (fun sm hpcm hrunm hspm hcsm _ => by
      apply dps_sepWPp_seq_keepsFrozen_placed
      refine dps_wrapper_epilogue_a_placed hp1 hpcm hrunm hspm hcsm ?_
      rintro se _ w0 w1 w2 w3 w4 w5 he rfl _
      exact SepWPp.of_sepWP_ret
        (dps_wrapper_epilogue_b_placed hge_wrap hle_wrap hp1 hvm01 hres hsp_align he))
    (fun _ _ _ hmo => (not_satisfies_false_sepConj hmo).elim)

/-- Budget-threaded relocatable wrapper reduction on block `520`: given `dpPollSpecStateBudget K`
on block `518` for `K.need ≤ stk' ≤ 2 ^ 63`, `decrypt_prekey` satisfies
`cliDecryptPrekeySpecStateBudget K` for `dpWrapFrame + K.need ≤ stk ≤ 2 ^ 63`. -/
theorem cliDecryptPrekey_ok_state_placed [LibsignalPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecStateBudget K stk)) :=
  dps_cliDecryptPrekey_ok_state_impl_placed K hinv hres hK stk hstk hstk64

/-- Transfers `cliDecryptPrekey_ok_state_placed` to any caller block `i < 619`. -/
theorem cliDecryptPrekey_ok_state_placed_at_block [LibsignalPlacement] {M : AllocCostModel}
    {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 520)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (cliDecryptPrekeySpecStateBudget K stk)) := by
  have hrocl := CryptoVerification.LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
    (cliDecryptPrekey_ok_state_placed K hinv hres hK stk hstk hstk64) hi
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-! ## `LibsignalFrozen` variants -/

theorem dps_cliDecryptPrekey_ok_state_impl_frozen_placed [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)) := by
  have hge_wrap : dpWrapFrame ≤ stk := by omega
  have hle_wrap : stk ≤ 2 ^ 64 := by omega
  have hpoll_fr : subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 518)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K (stk - dpWrapFrame))) :=
    _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
      (callerProg := lsProg_520 (Rust.withPanics ext))
      (hK (stk - dpWrapFrame) (by omega) (by omega))
  clear hK
  wpp_init x s0
  obtain ⟨ret, g, st⟩ := x
  dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen, cliDecryptPrekeySpecStateBudget] at *
  have hx8 : s0.readReg64 Reg.x8 = ret := by assumption
  have hlen13 : (K.args g).length = 13 := by assumption
  have htake8 : (K.args g).take 8 =
      [s0.readReg64 Reg.x0, s0.readReg64 Reg.x1, s0.readReg64 Reg.x2, s0.readReg64 Reg.x3,
       s0.readReg64 Reg.x4, s0.readReg64 Reg.x5, s0.readReg64 Reg.x6, s0.readReg64 Reg.x7] := by
    assumption
  have hsp_le : stk ≤ s0.sp.toNat := by assumption
  have hfr0 : CryptoVerification.LibsignalFrozen lsmpl s0.mem := by assumption
  obtain ⟨a8, a9, a10, a11, a12, hdrop_eq, hargs_eq⟩ := args13_unpack hlen13 htake8
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a1_vm_placed (K := dps_fixedK_placed K st s0) (g := g)
    hge_wrap hle_wrap hpc hrun hsp_align hx8 hdrop_eq ?_
  rintro sa _ ha hvm_a1 rfl hkf1
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_a2_vm_placed (K := dps_fixedK_placed K st s0) (g := g) ha ?_
  rintro sb _ f4 f5 f6 f7 f8 f9 f10 f11 fstate cx0 cx1 cx2 hb hvm_a2 rfl hkf2
  apply dps_sepWPp_seq_keepsFrozen_placed
  refine dpWrapper_prologue_b_vm_placed (K := dps_fixedK_placed K st s0) (g := g) hb hargs_eq ?_
  rintro s1 _ hp1 hvm_b rfl hkf3
  have hvm01 : VmPreserved s0 s1 := (hvm_a1.trans hvm_a2).trans hvm_b
  have hsp_le1 : stk - dpWrapFrame ≤ (s0.sp - 2144#64).toNat := by
    have hw : dpWrapFrame = 2144 := rfl
    rw [hw] at hge_wrap ⊢
    bv_omega
  have hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem :=
    CryptoVerification.libsignalFrozen_of_keepsFrozen hfr0 ((hkf1.trans hkf2).trans hkf3)
  have hcrl1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  exact CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SepWPp.call_lscro_plain
    (spec := CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K (stk - dpWrapFrame)))
    (x := LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.DpPollGhostStateBudget.mk (s0.sp - 104#64) (s0.sp - 2144#64) (s0.sp - 136#64) g st)
    (F := dpCallerFrame s0 ret ((K.args g).drop 8))
    hpoll_fr hcrl1 hp1.pc hp1.run hp1.sp_align hp1.lr
    (fun R' hm => by
      dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen, dpPollSpecStateBudget]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr1, ?_⟩
      rw [hp1.sp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hp1.x0, hp1.x1, hp1.x2, hlen13, hsp_le1⟩, ?_⟩
      dsimp only [dps_fixedK_placed] at hm
      have hm' :=
        Satisfies.mono
          (sepConj_mono_left
            (sepConj_mono_left
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_left (hinv g st s0 s1 hp1.fs hp1.trace hvm01)))))))
          hm
      simpa only [sepConj_assoc] using hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf_pan _ hmpan => by
      dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
        dpPollSpecStateBudget, cliDecryptPrekeySpecStateBudget] at hmpan ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmpan
      obtain ⟨⟨htr_pan, hpan_k⟩, hmpan_rest⟩ := hmpan
      rw [hp1.trace] at htr_pan
      rw [← sepConj_assoc] at hmpan_rest
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨htr_pan, hpan_k⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmpan_rest⟩)
    (fun sm hpcm hrunm hspm hcsm _ => by
      apply dps_sepWPp_seq_keepsFrozen_placed
      refine dps_wrapper_epilogue_a_placed hp1 hpcm hrunm hspm hcsm ?_
      rintro se _ w0 w1 w2 w3 w4 w5 he rfl _
      exact SepWPp.of_sepWP_ret
        (dps_wrapper_epilogue_b_placed hge_wrap hle_wrap hp1 hvm01 hres hsp_align he))
    (fun _ _ _ hmo => (not_satisfies_false_sepConj hmo).elim)

theorem cliDecryptPrekey_ok_state_frozen_placed [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {ext : String → Option (State → State)}
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics ext)) (lsmpl.base 520)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)) :=
  dps_cliDecryptPrekey_ok_state_impl_frozen_placed K hinv hres hK stk hstk hstk64

theorem cliDecryptPrekey_ok_state_frozen_placed_at_block [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (K : DpPollKStateBudget M)
    (hinv : ∀ g st s0 s1,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      K.inv g st s0 ⊢ K.inv g st s1)
    (hres : ∀ g st s0 s1 sm sf ws,
      s1.fs = s0.fs → s1.trace = s0.trace → VmPreserved s0 s1 →
      sf.fs = sm.fs → sf.trace = sm.trace → VmPreserved sm sf →
      K.res g st s1 sm ws ⊢ K.res g st s0 sf ws)
    (hK : ∀ stk', K.need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 518)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')))
    (stk : Nat) (hstk : dpWrapFrame + K.need ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 520)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (cliDecryptPrekeySpecStateBudget K stk)) := by
  let _ := hi
  exact _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    (callerProg := callerProg)
    (cliDecryptPrekey_ok_state_frozen_placed K hinv hres hK stk hstk hstk64)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
