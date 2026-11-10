/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R1c` Placed Proof

Proves the `SignalProtocolError` drop error tail (`r1c_err_after_drop`, `r1c_err_tail`) and the
budget-threaded Arm `R1c` hop theorems `run_hop_init3_placed_ok_of_env` and `run_hop_init3_placed_ok`
on Block `579` (`runProgPlaced H`) over `R1cInit3Env`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliWrOk coinsInstalledPlaced coinsOf inputOf namedWrites ownedBytes runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (AtInit2Placed AtRunEntryPlaced InRunPlaced Init2Data InitGhost PanicK RejectKind RunHistOk RunNeeds RunSem addrNameHeap cliBundleAt idVtPlaced initResAt runFiles runFsp runLocalBytes runPcPlaced runPcPlaced_eq runProgPlaced runSaved sessVtPlaced slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers (R1cCodeOk r1c_W6 r1c_addr_to_mem32 r1c_addr_unpack r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2 r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState r1c_calleeSavedVRegs_writeReg64 r1c_cliBundleAt_unpack r1c_errCore r1c_extractLsb_append_hi r1c_extractLsb_append_lo r1c_files_of_trace_eq r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_hist_of_eq r1c_init2Locals_unpack r1c_lowCells r1c_lowGaps r1c_mem48_to_slot6 r1c_mem_setPState r1c_okCore r1c_ownedBytes_entails_nameHeap r1c_readReg64_setPState r1c_rewrite_front r1c_sepWPp_exists_left r1c_sepWPp_pure_left r1c_sepWPp_weaken_pre r1c_slot6 r1c_slot6_to_mem48 r1c_spAligned r1c_sp_setPState r1c_split_at r1c_status_setPState r1c_symtab_setPState r1c_trace_setPState r1c_with_speOwned_words6)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
  (r1c_call_dealloc r1c_call_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
  (RunHopInit3Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
  (r1cFreeNamesEvs r1cOkTailEvs r1c_err_free_me r1c_ok_tail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlaced RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs initSlotSpecPlaced slotFramePlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init2MemPlaced runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget
  (dropSpeOwnedSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r1c_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runPcPlaced_eq, BitVec.ofNat_eq_ofNat, runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

private theorem r1c_frame_seq_vm [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : R1cCodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post s1 ∧ P1 = P'))
    (hk : ∀ s1 : State, VmPreserved s s1 → R1cCodeOk s1.mem → s1.pc = mid →
      s1.status = .Running → post s1 → SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hvm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 hvm1 (hinv.of_keepsFrozen hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

/-! ## 1. Error Tail After `drop_glue<SignalProtocolError>` (`R+0x29d0` / `R+0x28f4` → `R+0x2c7c`) -/

theorem r1c_err_after_drop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x29d0)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r1cOkTailEvs d) st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  have hres_split : r1c_okCore A.repAlloc g g' s0 ⊢
      ∃∗ rv0 : BitVec 64, (g.res ↦₆₄ rv0) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ anyHeap) := by
    dsimp only [r1c_okCore, runResSize]
    rw [ProofLib.memRegion_split' (b := g.res) (n := 8) (k := 336) (b' := g.res + 8#64) rfl rfl (by decide)]
    simp only [ProofLib.memRegion_eight, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro rv0
    exact Entails.sepExists_right rv0 (Entails.of_eq (by sep_ac_rfl))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      hres_split (by sep_ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro rv0
  let lowRest := ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hlow_eq :
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ lowRest =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, lowRest]; sep_ac_rfl
  let coreRest := memRegion (g.res + 8#64) (runResSize - 8) ∗
    (memRegion g.call 56 ∗ storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗ anyHeap)
  let tailHold := addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
    addrNameHeap A.repAlloc d.peerG ∗
    lowRest ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
      ((g.res ↦₆₄ rv0) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x29f0 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.spkSigPtr ∧ s1.readReg64 .x1 = 64#64 ∧ s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗
          (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))) := by
    have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := hs.spAligned_cur
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s.sp from hsp.symm]; clear hsp
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ tailHold ∗ coreRest)
    hs.inv (Entails.of_eq (by dsimp only [tailHold, coreRest]; rw [← hlow_eq]; sep_ac_rfl)) hstep1
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx21_1⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm1]
  have herr_core : (g.res ↦₆₄ 0xffffffffffffffff#64) ∗ coreRest = r1c_errCore A.repAlloc g g' s0 := by
    dsimp only [r1c_errCore, runResAt, coreRest]; sep_ac_rfl
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        tailHold ∗ r1c_errCore A.repAlloc g g' s0))
    (Entails.of_eq (by rw [← herr_core]; sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
      hx0_1 (by rw [hx1_1]; rfl) hx2_1 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  let st1 := M.stepEvents (rustDeallocEvents 64 1) st
  rcases hcs2 with ⟨hx19_2, _, hx21_2, _, _, _, _, _, _, _, hfp2, hv2⟩
  have hstep2 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s2
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s3 P3 => VmPreserved s2 s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          s3.readReg64 .lr = runPcPlaced 0x2a08 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 .x0 = d.kpkPtr ∧ s3.readReg64 .x1 = 1568#64 ∧ s3.readReg64 .x2 = 1#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P3 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))) := by
    rw [runPcPlaced_eq] at hpc2
    have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
    have hx19' := hx19_2.trans hx19_1; have hx21' := hx21_2.trans hx21_1
    have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s2.sp from hsp2.symm]; clear hsp2
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s2 ∗ tailHold ∗ r1c_errCore A.repAlloc g g' s0)
    hinv2 (Entails.of_eq (by dsimp only [fsp, st1]; sep_ac_rfl)) hstep2
    fun s3 hvm3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx21_3⟩ => ?_
  rw [← A.pool_transport lim st1 s2 s3 hvm3]
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s3 ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        tailHold ∗ r1c_errCore A.repAlloc g g' s0))
    (Entails.of_eq (by sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv3 hpc3 hrun3 hsp3 hlr3
      hx0_3 (by rw [hx1_3]; rfl) hx2_3 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s4 hinv4 hpc4 hrun4 hsp4 hcs4 hfs4 htr4 => ?_)
  let st2 := M.stepEvents (rustDeallocEvents 1568 1) st1
  rcases hcs4 with ⟨hx19_4, _, hx21_4, _, _, _, _, _, _, _, hfp4, hv4⟩
  have hstep3 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s4
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s5 P5 => VmPreserved s4 s5 ∧
        (s5.sp = fsp ∧ s5.readReg64 .fp = s0.sp - 0x60#64 ∧
          s5.readReg64 .lr = runPcPlaced 0x2a20 ∧
          calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧ s5.trace = s4.trace ∧ s5.fs = s4.fs ∧
          s5.readReg64 .x0 = d.kpkSigPtr ∧ s5.readReg64 .x1 = 64#64 ∧ s5.readReg64 .x2 = 1#64 ∧
          s5.readReg64 (.gpr 19#5) = g.stores ∧ s5.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P5 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))) := by
    rw [runPcPlaced_eq] at hpc4
    have hfp := hfp4.trans hfp3; have hv := hv4.trans hv3
    have hx19' := hx19_4.trans hx19_3; have hx21' := hx21_4.trans hx21_3
    have hal : s4.spAligned = true := r1c_spAligned hs.spAligned hsp4
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s4.sp from hsp4.symm]; clear hsp4
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st2 s4 ∗ tailHold ∗ r1c_errCore A.repAlloc g g' s0)
    hinv4 (Entails.of_eq (by dsimp only [fsp, st2]; sep_ac_rfl)) hstep3
    fun s5 hvm5 hinv5 hpc5 hrun5 ⟨hsp5, hfp5, hlr5, hv5, htr5, hfs5, hx0_5, hx1_5, hx2_5, hx19_5, hx21_5⟩ => ?_
  rw [← A.pool_transport lim st2 s4 s5 hvm5]
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st2 s5 ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        tailHold ∗ r1c_errCore A.repAlloc g g' s0))
    (Entails.of_eq (by sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv5 hpc5 hrun5 hsp5 hlr5
      hx0_5 (by rw [hx1_5]; rfl) hx2_5 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s6 hinv6 hpc6 hrun6 hsp6 hcs6 hfs6 htr6 => ?_)
  rcases hcs6 with ⟨hx19_6, _, hx21_6, _, _, _, _, _, _, _, hfp6, hv6⟩
  have hs6 : InRunPlaced R1cCodeOk s0 s6 0x2a20 :=
    ⟨hpc6, hrun6, hsp6, hfp6.trans hfp5, hinv6, hv6.trans hv5, hs.spAligned⟩
  have htr_all : s6.trace = s.trace :=
    ((((htr6.trans htr5).trans htr4).trans htr3).trans htr2).trans htr1
  have hfs_all : s6.fs = s.fs :=
    ((((hfs6.trans hfs5).trans hfs4).trans hfs3).trans hfs2).trans hfs1
  have henv3 : EnvAt g' .postDispatch
      (M.stepEvents (r1cFreeNamesEvs d) (M.stepEvents (rustDeallocEvents 64 1) st2)) := by
    dsimp only [st2, st1]
    rw [← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
    simpa [r1cOkTailEvs, List.append_assoc] using henv
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_err_free_me (g' := g') (d := d) hh hext_le hsub64 hs6
      (hx19_6.trans hx19_5) (hx21_6.trans hx21_5)
      (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist)
      hans henv3 hrej)
  exact Entails.of_eq (by dsimp only [tailHold, dirG, fsp, st2]; rw [← hlow_eq]; sep_ac_rfl)

theorem r1c_err_tail [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {k : SpeOwned} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x28f4)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_drop, FreeOnlyEvs evs_drop →
      EnvAt g' .postDispatch (M.stepEvents (evs_drop ++ r1cOkTailEvs d) st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗
        (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  let heaps := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
    (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
    (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64)
  let names := addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
    addrNameHeap A.repAlloc d.peerG
  let lowPeer := r1c_lowCells fsp d ∗
    memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16)
  let gaps2c0 := memRegion (fsp + 0x2c0#64) (0x1750 - 0x2c0) ∗
    memRegion (fsp + 0x1780#64) (0x23b0 - 0x1780) ∗
    memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have hcarve_dst : memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
      (∃∗ dst0 : r1c_W6, r1c_slot6 (fsp + 0x1750#64) dst0) ∗ gaps2c0 := by
    rw [r1c_split_at fsp 0x2c0 (0x1750 - 0x2c0) 0x23b0 (by decide) (by decide),
        show (0x2c0 : Nat) + (0x1750 - 0x2c0) = 0x1750 from rfl,
        r1c_split_at fsp 0x1750 48 0x23b0 (by decide) (by decide),
        show (0x1750 : Nat) + 48 = 0x1780 from rfl]
    exact r1c_rewrite_front gaps2c0 (r1c_mem48_to_slot6 (fsp + 0x1750#64))
      (by dsimp only [gaps2c0]; sep_ac_rfl) rfl
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗ heaps ∗ names ∗ lowPeer ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      hcarve_dst (by dsimp only [heaps, names, lowPeer]; sep_ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro dst0
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗
      (r1c_slot6 (fsp + 0x1750#64) dst0 ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x1750#64)
    fun sw Hspe hw0_3 hw0_2 hrebuild => ?_
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_3
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hw0_2
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true := bne_iff_ne.mpr hw0_2
  have hstep_copy : SepWP (runProgPlaced H) (blkPl_553).base s
      (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) dst0)
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x29d0 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = fsp + 0x1750#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw)) := by
    have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := hs.spAligned_cur
    dsimp only [runProgPlaced, lsProg_579, r1c_slot6]
    rw [show (blkPl_553).base = lsmpl.base 553 from rfl, show fsp = s.sp from hsp.symm]; clear hsp
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_,
        by simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := Hspe ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
    hs.inv (Entails.of_eq (by sep_ac_rfl)) hstep_copy
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm1]
  have hwand_src :
      r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw ∗ Hspe ⊢
      speOwnedAt A.repAlloc (fsp + 0x1750#64) k ∗ memRegion (fsp + 0x23b0#64) 48 :=
    Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono hrebuild (r1c_slot6_to_mem48 (fsp + 0x23b0#64) sw))
  refine r1c_call_lscro
    (spec := dropSpeOwnedSpec A lim (resStack - runFrame))
    (F := memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
      r1c_okCore A.repAlloc g g' s0)
    (⟨fsp + 0x1750#64, k⟩, st)
    (hdrop (resStack - runFrame) hstk32 hsub64)
    hinv1 hpc1 hrun1 (r1c_spAligned hs.spAligned hsp1) hlr1
    (by
      dsimp only [dropSpeOwnedSpec]
      rw [hsp1]
      refine Entails.trans
        (r1c_rewrite_front
          (gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗ r1c_okCore A.repAlloc g g' s0)
          hwand_src (by sep_ac_rfl) rfl) ?_
      conv => rhs; rw [sepConj_assoc]
      exact Entails.pure_right
        ⟨hx0_1, ⟨579, by decide, 0x29d0, by decide, hlr1.trans (runPcPlaced_eq 0x29d0)⟩⟩
        (Entails.of_eq (by sep_ac_rfl)))
    (hnext := fun sm hsteps_m hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [dropSpeOwnedSpec]
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro evs_drop
  rw [hsp1, sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨htr_m, hfree_drop⟩
  have hfs_m : sm.fs.files = s1.fs.files :=
    r1c_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_m htr_m
  have hmerge_2c0 :
      memRegion (fsp + 0x1750#64) 48 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
    dsimp only [gaps2c0]
    rw [r1c_split_at fsp 0x2c0 (0x1750 - 0x2c0) runLocalBytes (by decide) (by decide),
        show (0x2c0 : Nat) + (0x1750 - 0x2c0) = 0x1750 from rfl,
        r1c_split_at fsp 0x1750 48 runLocalBytes (by decide) (by decide),
        show (0x1750 : Nat) + 48 = 0x1780 from rfl,
        r1c_split_at fsp 0x1780 (0x23b0 - 0x1780) runLocalBytes (by decide) (by decide),
        show (0x1780 : Nat) + (0x23b0 - 0x1780) = 0x23b0 from rfl,
        r1c_split_at fsp 0x23b0 48 runLocalBytes (by decide) (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  have hsm : InRunPlaced R1cCodeOk s0 sm 0x29d0 :=
    ⟨hpcm, hrunm, hspm.trans hsp1, hfp_m.trans hfp1, hinv_m, hv_m.trans hv1, hs.spAligned⟩
  have henv_drop : EnvAt g' .postDispatch
      (M.stepEvents (r1cOkTailEvs d) (M.stepEvents evs_drop st)) := by
    rw [← M.stepEvents_append]
    exact henv evs_drop hfree_drop
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_err_after_drop (g' := g') (d := d) hh hext_le hsub64 hsm
      (hx19_m.trans hx19_1) (hx20_m.trans hx20_1) (hx21_m.trans hx21_1)
      ((htr_m.trans htr1) ▸ htr)
      (r1c_hist_of_eq (htr_m.trans htr1) (hfs_m.trans (congrArg FsState.files hfs1)) hhist)
      hans henv_drop hrej)
  exact r1c_rewrite_front
    (A.pool lim (M.stepEvents evs_drop st) sm ∗ stackAt fsp (resStack - runFrame) ∗
      heaps ∗ names ∗ lowPeer ∗ r1c_okCore A.repAlloc g g' s0)
    hmerge_2c0 (by sep_ac_rfl) (by dsimp only [heaps, names, lowPeer, dirG, fsp]; sep_ac_rfl)

theorem r1c_err_after_drop_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x29d0)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A lim g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom :=
  r1c_err_after_drop (EnvAt := fun _ _ _ => True) hh hext_le hsub64 hs hx19 hx20 hx21
    htr hhist hans trivial fun s' st' g'' rk' hat _ => hrej s' st' g'' rk' hat

theorem r1c_err_tail_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {k : SpeOwned} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x28f4)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A lim g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗
        (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom :=
  r1c_err_tail (EnvAt := fun _ _ _ => True) hh hdrop hstk32 hext_le hsub64 hs hx19 hx20 hx21
    htr hhist hans (fun _ _ => trivial) fun s' st' g'' rk' hat _ => hrej s' st' g'' rk' hat

/-! ## 2. Arm `R1c` Sub-Hop 3 Envelope & `run_hop_init3_placed_ok` (`R+0x28f0` → Join/Reject) -/

/-- `InitGhost` passed to `sEnvs.initiate` at `signal_session::run` frame stack pointer `fsp`. -/
def r1cInitGhost (g : RunCall) (d2 : Init2Data) (fsp : BitVec 64) : InitGhost where
  peer := d2.peerG
  peerA := fsp + 0x2a0#64
  me := d2.meG
  meA := fsp + 0x320#64
  stores := g.stores
  ret := fsp + 0x23b0#64
  coinsP := g.coins
  F := runFiles g.i
  coins := coinsOf g.i
  bundleA := fsp + 0x4d0#64
  bundle := d2.bundle
  spkSigPtr := d2.spkSigPtr
  kpkSigPtr := d2.kpkSigPtr
  kpkPtr := d2.kpkPtr

/-- Canonical Arm `R1c` Sub-Hop 3 event envelope: composes `sEnvs.initiate (r1cInitGhost g d2 0#64)`
with either `r1cOkTailEvs d2` (`.ok ()` path) or `drop_glue<SignalProtocolError>` (`FreeOnlyEvs`)
followed by `r1cOkTailEvs d2` (`.error _` path). -/
def R1cInit3Env (sEnvs : RunSlotEnvs) (g : RunCall) (d2 : Init2Data)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (sEnvs.initiate (r1cInitGhost g d2 0#64))
    (fun evs_tail =>
      evs_tail = r1cOkTailEvs d2 ∨
        ∃ evs_drop, FreeOnlyEvs evs_drop ∧ evs_tail = evs_drop ++ r1cOkTailEvs d2)
    evs

/-- Budget-threaded Arm `R1c` hop proof (`R+0x28f0 → R+0xf8c / R+0x2c7c`) on Block `579`
(`runProgPlaced H`), parameterized over any `Init3Env` closed under pre-call `sEnvs.initiate`,
success-tail `r1cOkTailEvs`, and error-tail `FreeOnlyEvs ++ r1cOkTailEvs`. -/
theorem run_hop_init3_placed_ok_of_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {Init3Env : RunCall → Init2Data → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (h_pre : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → Init3Env g d2 evs)
    (h_ok : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → Init3Env g d2 (evs ++ r1cOkTailEvs d2))
    (h_err : ∀ g d2 fsp evs₁ evs₂,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs₁ → FreeOnlyEvs evs₂ →
        Init3Env g d2 (evs₁ ++ (evs₂ ++ r1cOkTailEvs d2))) :
    RunHopInit3Placed (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs Init3Env H B S needs resStack := by
  intro g st s0 s2 d2 Q Qp hh hc hdrop hres hres64 hspb he hi2 hfits hpanic hrej hjoin
  obtain ⟨hrf, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hstk32, _, hext_le, _, _, hinit_stk, _, _⟩ := runNeed_bounds_placed hres hres64
  have hspb_slot : resStack - runFrame ≤ s2.sp.toNat := by
    have hrf_eq : runFrame = 0x2a50 := rfl
    have hsp2 : s2.sp = s0.sp - 0x2a50#64 := hi2.base.sp
    have hle : (0x2a50#64 : BitVec 64) ≤ s0.sp := by
      rw [BitVec.le_def]; change 0x2a50 ≤ s0.sp.toNat; omega
    rw [hsp2, BitVec.toNat_sub_of_le hle, hrf_eq]
    change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
  obtain ⟨hcoins63, hfs2, hspk64, hkpk64, hkpk1568, hfilesOk, hinitOk, hga⟩ :=
    AtInit2Placed.init_facts he hi2
  let fsp := runFsp s0
  let dirG : AddrGhost := ⟨⟨d2.dirCap, d2.dirPtr, d2.dir⟩, 0#8⟩
  have hstep_bl : SepWP (runProgPlaced H) (lsmpl.base 521) s2 emp
      (fun s3 P3 => VmPreserved s2 s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          s3.readReg64 .lr = runPcPlaced 0x28f4 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 .x0 = fsp + 0x2a0#64 ∧ s3.readReg64 .x1 = fsp + 0x320#64 ∧
          s3.readReg64 .x2 = g.stores + 0xf0#64 ∧ s3.readReg64 .x3 = sessVtPlaced ∧
          s3.readReg64 .x4 = g.stores ∧ s3.readReg64 .x5 = idVtPlaced ∧
          s3.readReg64 .x6 = fsp + 0x4d0#64 ∧ s3.readReg64 .x7 = 0#64 ∧
          s3.readReg64 .x8 = fsp + 0x23b0#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧ P3 = emp) := by
    have hpc := hi2.base.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hi2.base.run; have hsp := hi2.base.sp
    have hfp := hi2.base.fp; have hv := hi2.base.vregs
    have hx0 := hi2.x0; have hx1 := hi2.x1; have hx2 := hi2.x2; have hx3 := hi2.x3
    have hx4 := hi2.x4; have hx5 := hi2.x5; have hx6 := hi2.x6; have hx7 := hi2.x7
    have hx8 := hi2.x8; have hx19 := hi2.x19; have hx20 := hi2.x20; have hx21 := hi2.x21
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm (F := init2MemPlaced A lim st g d2 s0 s2 resStack)
    hi2.base.inv (Entails.of_eq (emp_sepConj _).symm) hstep_bl
    fun s3 hvm3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3,
      hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
      hx19_3, hx20_3, hx21_3⟩ => ?_
  rw [emp_sepConj]
  dsimp only [init2MemPlaced]
  rw [← A.atState_eq_of_vmPreserved lim st hvm3]
  let initX : InitGhost := r1cInitGhost g d2 fsp
  have hfits_init : FitsEnv M lim st (sEnvs.initiate initX) :=
    hfits.mono (h_pre g d2 fsp)
  let lowPre := memRegion (fsp + 4#64) (0x110 - 4) ∗
    ((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
    memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
    memRegion (fsp + 0x180#64) 56
  let hiGaps := memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
    memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
    memRegion (fsp + 0x590#64) (0x23b0 - 0x590)
  let initFrame := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
    ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
    lowPre ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ hi2.trace
  have hspb_s3 : resStack - runFrame ≤ s3.sp.toNat := by
    rw [hsp3]; dsimp only [fsp]; rwa [← hi2.base.sp]
  have hfs_s3 : s3.fs.files = runFiles g.i := (congrArg FsState.files hfs3).trans hfs2
  have hcall_init : subroutine_ok (runProgPlaced H) (lsmpl.base 521)
      (initSlotSpecPlaced A lim sEnvs.initiate S (resStack - runFrame)) :=
    hc.initiate (resStack - runFrame) hinit_stk hsub63
  dsimp only [initSlotSpecPlaced] at hcall_init
  refine r1c_call_lscro (F := initFrame) (initX, st) hcall_init
    hinv3 hpc3 hrun3 (r1c_spAligned hi2.base.spAligned hsp3) hlr3
    (by
      dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.init2MemPlaced,
        slotFramePlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
        CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced,
        initX, r1cInitGhost]
      refine Entails.trans
        (r1c_rewrite_front
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt (A.atState lim st s3) g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗ lsLogOff ∗
            A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
            ownedBytes (A.atState lim st s3) d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
            runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ (A.atState lim st s3).pool)
          (r1c_init2Locals_unpack (A.atState lim st s3) fsp d2)
          (by sep_ac_rfl) rfl) ?_
      simp only [sepConj_assoc]
      apply Entails.pure_right
        ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
         hfs_s3, hfilesOk, hinitOk, hspb_s3, hfits_init⟩
      apply Entails.pure_right hcoins63
      rw [hsp3]
      exact Entails.of_eq (by
        dsimp only [initFrame, lowPre, hiGaps, LibsignalBinary.Heap.RustCliAllocBudget.atState]
        change _ = _
        sep_ac_rfl))
    (hpanic := fun sf _ _ hp => by
      dsimp only [initX, r1cInitGhost] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga, hp.1]; rfl)))
    (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [initX, r1cInitGhost]
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro evs_init
  apply r1c_sepWPp_exists_left; intro g'
  apply r1c_sepWPp_exists_left; intro e
  rw [sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨hinit_ev, hslotTr, hslotOut⟩
  rw [hsp3]
  let st_m := M.stepEvents evs_init st
  have hsp_m : sm.sp = fsp := hspm.trans hsp3
  have hs_m : InRunPlaced R1cCodeOk s0 sm 0x28f4 :=
    ⟨hpcm, hrunm, hsp_m, hfp_m.trans hfp3, hinv_m, hv_m.trans hv3, hi2.base.spAligned⟩
  have hx19_m' : sm.readReg64 (.gpr 19#5) = g.stores := hx19_m.trans hx19_3
  have hx20_m' : sm.readReg64 (.gpr 20#5) = g.res := hx20_m.trans hx20_3
  have hx21_m' : sm.readReg64 (.gpr 21#5) = d2.meG.name.cap := hx21_m.trans hx21_3
  have htr_m : s0.trace <+: sm.trace := htr_s3.trans hslotTr.1
  have hhist_m : RunHistOk g.i s0 sm :=
    ⟨hslotTr.2.1.trans hfs_s3, hslotTr.2.2.trans (htr3 ▸ hi2.stdout)⟩
  have hcollapse_post :
      protocolAddressAt A.repAlloc d2.peerG (fsp + 0x2a0#64) ∗
        protocolAddressAt A.repAlloc d2.meG (fsp + 0x320#64) ∗
        cliBundleAt (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr ∗
        (fsp ↦₃₂ 0#32) ∗ lsLogOff ∗ anyHeap ∗ initFrame ⊢
      (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
        (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
        (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d2.peerG ∗
        r1c_lowCells fsp d2 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap) := by
    have hlow : (fsp ↦₃₂ 0#32) ∗ lowPre ⊢ r1c_lowCells fsp d2 := by
      have hm110 : (fsp ↦₃₂ 0#32) ∗ memRegion (fsp + 4#64) (0x110 - 4) ⊢ memRegion fsp 0x110 := by
        rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 0x110 - 4)
              (b' := fsp + 4#64) rfl rfl (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion fsp 0#32)
      dsimp only [lowPre, r1c_lowCells, r1c_lowGaps]
      exact r1c_rewrite_front
        (((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
          ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
          ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
          memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
          memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
          memRegion (fsp + 0x180#64) 56)
        hm110 (by sep_ac_rfl) (by sep_ac_rfl)
    have hhi : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x4d0#64) 192 ∗ hiGaps ⊢
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) := by
      dsimp only [hiGaps]
      rw [ProofLib.memRegion_split' (b := fsp + 0x2c0#64) (n := 0x320 - 0x2c0)
            (k := 0x23b0 - 0x320) (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32)
            (k := 0x23b0 - 0x340) (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340)
            (k := 0x23b0 - 0x4d0) (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 192)
            (k := 0x23b0 - 0x590) (b' := fsp + 0x590#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by sep_ac_rfl)
    have hdir : ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ⊢
        addrNameHeap A.repAlloc dirG := by
      refine Entails.trans
        (r1c_ownedBytes_entails_nameHeap A.repAlloc d2.dirCap d2.dirPtr
          (BitVec.ofNat 64 d2.dir.length) d2.dir) ?_
      exact Entails.pure_left fun _ => Entails.refl _
    have hpeer : protocolAddressAt A.repAlloc d2.peerG (fsp + 0x2a0#64) ⊢
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1c_addr_unpack A.repAlloc d2.peerG (fsp + 0x2a0#64)
    have hany : lsLogOff ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [initFrame]
    refine Entails.trans
      (sepConj_mono hpeer
        (sepConj_mono (r1c_addr_to_mem32 A.repAlloc d2.meG (fsp + 0x320#64))
          (sepConj_mono
            (r1c_cliBundleAt_unpack (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr)
            (Entails.refl _)))) ?_
    refine Entails.trans
      (r1c_rewrite_front
        ((((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
          memRegion (fsp + 0x320#64) 32 ∗ addrNameHeap A.repAlloc d2.meG ∗
          memRegion (fsp + 0x4d0#64) 192 ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hlow (by sep_ac_rfl) rfl) ?_
    refine Entails.trans
      (r1c_rewrite_front
        (r1c_lowCells fsp d2 ∗
          (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
          addrNameHeap A.repAlloc d2.meG ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hhi (by sep_ac_rfl) rfl) ?_
    exact r1c_rewrite_front
      (memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        r1c_lowCells fsp d2 ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
        addrNameHeap A.repAlloc d2.meG ∗
        memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
      (sepConj_mono hdir hany) (by sep_ac_rfl) (by sep_ac_rfl)
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (storesAt A.repAlloc g.stores g' ∗ initResAt A.repAlloc (fsp + 0x23b0#64) e ∗
        A.pool lim st_m sm ∗ stackAt fsp (resStack - runFrame))
      hcollapse_post (by dsimp only [st_m]; sep_ac_rfl) rfl)
  cases e with
  | ok u =>
    cases u
    rcases hslotOut with ⟨_, _, hans_ok, hwr⟩
    have hans : g.a = some (some (namedWrites g'.writes, [])) := by
      rw [hga, hans_ok]; rfl
    dsimp only [initResAt]
    have hcmn3_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 3#64 == 0#64) = false := by decide
    have hcmn2_ne_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 != 0#64) = false := by decide
    have hcmn2_eq_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 == 0#64) = true := by decide
    have hstep_ok : SepWP (runProgPlaced H) (runPcPlaced 0x2908) sm
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)
        (fun s4 P4 => VmPreserved sm s4 ∧
          (s4.sp = fsp ∧ s4.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s4 = calleeSavedVRegs s0 ∧ s4.trace = sm.trace ∧ s4.fs = sm.fs ∧
            s4.readReg64 (.gpr 19#5) = g.stores ∧ s4.readReg64 (.gpr 20#5) = g.res ∧
            s4.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧
          P4 = ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)) := by
      have hpc := hs_m.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs_m.run; have hfp := hs_m.fp; have hv := hs_m.vregs
      have hal : sm.spAligned = true := r1c_spAligned hi2.base.spAligned hsp_m
      rw [runPcPlaced_eq, show fsp = sm.sp from hsp_m.symm]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    let okRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m sm ∗ r1c_okCore A.repAlloc g g' s0
    refine r1c_frame_seq_vm
      (F := memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗ okRest)
      hs_m.inv (Entails.of_eq (by dsimp only [okRest, r1c_okCore]; sep_ac_rfl)) hstep_ok
      fun s4 hvm4 hinv4 hpc4 hrun4 ⟨hsp4, hfp4, hv4, htr4, hfs4, hx19_4, hx20_4, hx21_4⟩ => ?_
    dsimp only [okRest]
    rw [← A.pool_transport lim st_m sm s4 hvm4]
    have hmerge_ok :
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [r1c_split_at fsp 0x2c0 (0x23b0 - 0x2c0) runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b0 8 runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b8 40 runLocalBytes (by decide) (by decide)]
      exact r1c_rewrite_front
        (memRegion (fsp + 0x23b8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        (pointsTo64_entails_memRegion _ _) (by sep_ac_rfl) (by sep_ac_rfl)
    have henv_ok : ∃ evs, Init3Env g d2 evs ∧
        M.stepEvents (r1cOkTailEvs d2) st_m = M.stepEvents evs st :=
      ⟨evs_init ++ r1cOkTailEvs d2, h_ok g d2 fsp evs_init hinit_ev,
        (M.stepEvents_append evs_init (r1cOkTailEvs d2) st).symm⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_tail (g' := g') (d := d2) hh hext_le hsub64
        ⟨hpc4, hrun4, hsp4, hfp4, hinv4, hv4, hi2.base.spAligned⟩
        hx19_4 hx20_4 hx21_4 (htr4 ▸ htr_m)
        (r1c_hist_of_eq htr4 (congrArg FsState.files hfs4) hhist_m)
        hans hwr henv_ok hjoin)
    let okRest4 := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m s4 ∗ r1c_okCore A.repAlloc g g' s0
    exact r1c_rewrite_front okRest4 hmerge_ok (by dsimp only [okRest4]; sep_ac_rfl)
      (by dsimp only [okRest4, fsp, dirG, st_m]; sep_ac_rfl)
  | error err =>
    have hans : g.a = some none := by
      rw [hga, hslotOut.2.2]; rfl
    dsimp only [initResAt]
    let errRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m sm ∗ r1c_okCore A.repAlloc g g' s0
    apply r1c_sepWPp_weaken_pre
      (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x23b0#64) k) ∗ errRest)
      (Entails.of_eq (by dsimp only [errRest, r1c_okCore]; sep_ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r1c_sepWPp_exists_left; intro k
    have henv_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
        ∃ evs, Init3Env g d2 evs ∧
          M.stepEvents (evs_drop ++ r1cOkTailEvs d2) st_m = M.stepEvents evs st :=
      fun evs_drop hfree =>
        ⟨evs_init ++ (evs_drop ++ r1cOkTailEvs d2),
          h_err g d2 fsp evs_init evs_drop hinit_ev hfree,
          (M.stepEvents_append evs_init (evs_drop ++ r1cOkTailEvs d2) st).symm⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_tail (g' := g') (d := d2) (k := k) hh hdrop hstk32 hext_le hsub64 hs_m
        hx19_m' hx20_m' hx21_m' htr_m hhist_m hans henv_err hrej)
    exact Entails.of_eq (by dsimp only [errRest, fsp, dirG, st_m])

/-- Budget-threaded Arm `R1c` hop proof (`R+0x28f0 → R+0xf8c / R+0x2c7c`) on Block `579`
(`runProgPlaced H`), instantiated with `R1cInit3Env sEnvs` for any stack-address-invariant
`sEnvs.initiate`. -/
theorem run_hop_init3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl) :
    RunHopInit3Placed (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (R1cInit3Env sEnvs) H B S needs resStack :=
  run_hop_init3_placed_ok_of_env
    (fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.inl h)
    (fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.append h (Or.inl rfl))
    (fun g d2 fsp _ evs_d h hf => by
      rw [hinit_addr] at h; exact SeqEnv.append h (Or.inr ⟨evs_d, hf, rfl⟩))


theorem run_hop_init3_of_slots_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B slots =
      CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hinit_eq : slots.initiate = (slotsOfPlaced A lim sEnvs S needs).initiate)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget.RunHopInit3PlacedOf
      (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (R1cInit3Env sEnvs) H B S slots resStack := by
  have h_pre : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → R1cInit3Env sEnvs g d2 evs :=
    fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.inl h
  have h_ok : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → R1cInit3Env sEnvs g d2 (evs ++ r1cOkTailEvs d2) :=
    fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.append h (Or.inl rfl)
  have h_err : ∀ g d2 fsp evs₁ evs₂,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs₁ → FreeOnlyEvs evs₂ →
        R1cInit3Env sEnvs g d2 (evs₁ ++ (evs₂ ++ r1cOkTailEvs d2)) :=
    fun g d2 fsp _ evs_d h hf => by
      rw [hinit_addr] at h; exact SeqEnv.append h (Or.inr ⟨evs_d, hf, rfl⟩)
  intro g st s0 s2 d2 Q Qp hh hc hdrop hres_slots hres64 hspb he hi2 hfits hpanic hrej hjoin
  have hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hneed_eq ▸ hres_slots
  obtain ⟨hrf, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hstk32, _, hext_le, _, _, hinit_stk, _, _⟩ := runNeed_bounds_placed hres hres64
  have hspb_slot : resStack - runFrame ≤ s2.sp.toNat := by
    have hrf_eq : runFrame = 0x2a50 := rfl
    have hsp2 : s2.sp = s0.sp - 0x2a50#64 := hi2.base.sp
    have hle : (0x2a50#64 : BitVec 64) ≤ s0.sp := by
      rw [BitVec.le_def]; change 0x2a50 ≤ s0.sp.toNat; omega
    rw [hsp2, BitVec.toNat_sub_of_le hle, hrf_eq]
    change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
  obtain ⟨hcoins63, hfs2, hspk64, hkpk64, hkpk1568, hfilesOk, hinitOk, hga⟩ :=
    AtInit2Placed.init_facts he hi2
  let fsp := runFsp s0
  let dirG : AddrGhost := ⟨⟨d2.dirCap, d2.dirPtr, d2.dir⟩, 0#8⟩
  have hstep_bl : SepWP (runProgPlaced H) (lsmpl.base 521) s2 emp
      (fun s3 P3 => VmPreserved s2 s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          s3.readReg64 .lr = runPcPlaced 0x28f4 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 .x0 = fsp + 0x2a0#64 ∧ s3.readReg64 .x1 = fsp + 0x320#64 ∧
          s3.readReg64 .x2 = g.stores + 0xf0#64 ∧ s3.readReg64 .x3 = sessVtPlaced ∧
          s3.readReg64 .x4 = g.stores ∧ s3.readReg64 .x5 = idVtPlaced ∧
          s3.readReg64 .x6 = fsp + 0x4d0#64 ∧ s3.readReg64 .x7 = 0#64 ∧
          s3.readReg64 .x8 = fsp + 0x23b0#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧ P3 = emp) := by
    have hpc := hi2.base.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hi2.base.run; have hsp := hi2.base.sp
    have hfp := hi2.base.fp; have hv := hi2.base.vregs
    have hx0 := hi2.x0; have hx1 := hi2.x1; have hx2 := hi2.x2; have hx3 := hi2.x3
    have hx4 := hi2.x4; have hx5 := hi2.x5; have hx6 := hi2.x6; have hx7 := hi2.x7
    have hx8 := hi2.x8; have hx19 := hi2.x19; have hx20 := hi2.x20; have hx21 := hi2.x21
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm (F := init2MemPlaced A lim st g d2 s0 s2 resStack)
    hi2.base.inv (Entails.of_eq (emp_sepConj _).symm) hstep_bl
    fun s3 hvm3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3,
      hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
      hx19_3, hx20_3, hx21_3⟩ => ?_
  rw [emp_sepConj]
  dsimp only [init2MemPlaced]
  rw [← A.atState_eq_of_vmPreserved lim st hvm3]
  let initX : InitGhost := r1cInitGhost g d2 fsp
  have hfits_init : FitsEnv M lim st (sEnvs.initiate initX) :=
    hfits.mono (h_pre g d2 fsp)
  let lowPre := memRegion (fsp + 4#64) (0x110 - 4) ∗
    ((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
    memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
    memRegion (fsp + 0x180#64) 56
  let hiGaps := memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
    memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
    memRegion (fsp + 0x590#64) (0x23b0 - 0x590)
  let initFrame := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
    ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
    lowPre ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ hi2.trace
  have hspb_s3 : resStack - runFrame ≤ s3.sp.toNat := by
    rw [hsp3]; dsimp only [fsp]; rwa [← hi2.base.sp]
  have hfs_s3 : s3.fs.files = runFiles g.i := (congrArg FsState.files hfs3).trans hfs2
  have hcall_init : subroutine_ok (runProgPlaced H) (lsmpl.base 521)
      (initSlotSpecPlaced A lim sEnvs.initiate S (resStack - runFrame)) :=
    (hinit_eq ▸ hc.initiate) (resStack - runFrame) hinit_stk hsub63
  dsimp only [initSlotSpecPlaced] at hcall_init
  refine r1c_call_lscro (F := initFrame) (initX, st) hcall_init
    hinv3 hpc3 hrun3 (r1c_spAligned hi2.base.spAligned hsp3) hlr3
    (by
      dsimp only [CryptoVerification.SignalSession.Cli.RunCompose.init2MemPlaced,
        slotFramePlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
        CryptoVerification.SignalSession.Cli.RunCompose.slotFramePlaced,
        initX, r1cInitGhost]
      refine Entails.trans
        (r1c_rewrite_front
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt (A.atState lim st s3) g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗ lsLogOff ∗
            A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
            ownedBytes (A.atState lim st s3) d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
            runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ (A.atState lim st s3).pool)
          (r1c_init2Locals_unpack (A.atState lim st s3) fsp d2)
          (by sep_ac_rfl) rfl) ?_
      simp only [sepConj_assoc]
      apply Entails.pure_right
        ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
         hfs_s3, hfilesOk, hinitOk, hspb_s3, hfits_init⟩
      apply Entails.pure_right hcoins63
      rw [hsp3]
      exact Entails.of_eq (by
        dsimp only [initFrame, lowPre, hiGaps, LibsignalBinary.Heap.RustCliAllocBudget.atState]
        change _ = _
        sep_ac_rfl))
    (hpanic := fun sf _ _ hp => by
      dsimp only [initX, r1cInitGhost] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga, hp.1]; rfl)))
    (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [initX, r1cInitGhost]
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro evs_init
  apply r1c_sepWPp_exists_left; intro g'
  apply r1c_sepWPp_exists_left; intro e
  rw [sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨hinit_ev, hslotTr, hslotOut⟩
  rw [hsp3]
  let st_m := M.stepEvents evs_init st
  have hsp_m : sm.sp = fsp := hspm.trans hsp3
  have hs_m : InRunPlaced R1cCodeOk s0 sm 0x28f4 :=
    ⟨hpcm, hrunm, hsp_m, hfp_m.trans hfp3, hinv_m, hv_m.trans hv3, hi2.base.spAligned⟩
  have hx19_m' : sm.readReg64 (.gpr 19#5) = g.stores := hx19_m.trans hx19_3
  have hx20_m' : sm.readReg64 (.gpr 20#5) = g.res := hx20_m.trans hx20_3
  have hx21_m' : sm.readReg64 (.gpr 21#5) = d2.meG.name.cap := hx21_m.trans hx21_3
  have htr_m : s0.trace <+: sm.trace := htr_s3.trans hslotTr.1
  have hhist_m : RunHistOk g.i s0 sm :=
    ⟨hslotTr.2.1.trans hfs_s3, hslotTr.2.2.trans (htr3 ▸ hi2.stdout)⟩
  have hcollapse_post :
      protocolAddressAt A.repAlloc d2.peerG (fsp + 0x2a0#64) ∗
        protocolAddressAt A.repAlloc d2.meG (fsp + 0x320#64) ∗
        cliBundleAt (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr ∗
        (fsp ↦₃₂ 0#32) ∗ lsLogOff ∗ anyHeap ∗ initFrame ⊢
      (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
        (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
        (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d2.peerG ∗
        r1c_lowCells fsp d2 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap) := by
    have hlow : (fsp ↦₃₂ 0#32) ∗ lowPre ⊢ r1c_lowCells fsp d2 := by
      have hm110 : (fsp ↦₃₂ 0#32) ∗ memRegion (fsp + 4#64) (0x110 - 4) ⊢ memRegion fsp 0x110 := by
        rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 0x110 - 4)
              (b' := fsp + 4#64) rfl rfl (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion fsp 0#32)
      dsimp only [lowPre, r1c_lowCells, r1c_lowGaps]
      exact r1c_rewrite_front
        (((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
          ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
          ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
          memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
          memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
          memRegion (fsp + 0x180#64) 56)
        hm110 (by sep_ac_rfl) (by sep_ac_rfl)
    have hhi : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x4d0#64) 192 ∗ hiGaps ⊢
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) := by
      dsimp only [hiGaps]
      rw [ProofLib.memRegion_split' (b := fsp + 0x2c0#64) (n := 0x320 - 0x2c0)
            (k := 0x23b0 - 0x320) (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32)
            (k := 0x23b0 - 0x340) (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340)
            (k := 0x23b0 - 0x4d0) (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 192)
            (k := 0x23b0 - 0x590) (b' := fsp + 0x590#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by sep_ac_rfl)
    have hdir : ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ⊢
        addrNameHeap A.repAlloc dirG := by
      refine Entails.trans
        (r1c_ownedBytes_entails_nameHeap A.repAlloc d2.dirCap d2.dirPtr
          (BitVec.ofNat 64 d2.dir.length) d2.dir) ?_
      exact Entails.pure_left fun _ => Entails.refl _
    have hpeer : protocolAddressAt A.repAlloc d2.peerG (fsp + 0x2a0#64) ⊢
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1c_addr_unpack A.repAlloc d2.peerG (fsp + 0x2a0#64)
    have hany : lsLogOff ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [initFrame]
    refine Entails.trans
      (sepConj_mono hpeer
        (sepConj_mono (r1c_addr_to_mem32 A.repAlloc d2.meG (fsp + 0x320#64))
          (sepConj_mono
            (r1c_cliBundleAt_unpack (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr)
            (Entails.refl _)))) ?_
    refine Entails.trans
      (r1c_rewrite_front
        ((((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
          memRegion (fsp + 0x320#64) 32 ∗ addrNameHeap A.repAlloc d2.meG ∗
          memRegion (fsp + 0x4d0#64) 192 ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hlow (by sep_ac_rfl) rfl) ?_
    refine Entails.trans
      (r1c_rewrite_front
        (r1c_lowCells fsp d2 ∗
          (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
          addrNameHeap A.repAlloc d2.meG ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          lsLogOff ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A.repAlloc d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hhi (by sep_ac_rfl) rfl) ?_
    exact r1c_rewrite_front
      (memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        r1c_lowCells fsp d2 ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A.repAlloc d2.peerG ∗
        addrNameHeap A.repAlloc d2.meG ∗
        memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
      (sepConj_mono hdir hany) (by sep_ac_rfl) (by sep_ac_rfl)
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (storesAt A.repAlloc g.stores g' ∗ initResAt A.repAlloc (fsp + 0x23b0#64) e ∗
        A.pool lim st_m sm ∗ stackAt fsp (resStack - runFrame))
      hcollapse_post (by dsimp only [st_m]; sep_ac_rfl) rfl)
  cases e with
  | ok u =>
    cases u
    rcases hslotOut with ⟨_, _, hans_ok, hwr⟩
    have hans : g.a = some (some (namedWrites g'.writes, [])) := by
      rw [hga, hans_ok]; rfl
    dsimp only [initResAt]
    have hcmn3_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 3#64 == 0#64) = false := by decide
    have hcmn2_ne_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 != 0#64) = false := by decide
    have hcmn2_eq_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 == 0#64) = true := by decide
    have hstep_ok : SepWP (runProgPlaced H) (runPcPlaced 0x2908) sm
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)
        (fun s4 P4 => VmPreserved sm s4 ∧
          (s4.sp = fsp ∧ s4.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s4 = calleeSavedVRegs s0 ∧ s4.trace = sm.trace ∧ s4.fs = sm.fs ∧
            s4.readReg64 (.gpr 19#5) = g.stores ∧ s4.readReg64 (.gpr 20#5) = g.res ∧
            s4.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧
          P4 = ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)) := by
      have hpc := hs_m.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs_m.run; have hfp := hs_m.fp; have hv := hs_m.vregs
      have hal : sm.spAligned = true := r1c_spAligned hi2.base.spAligned hsp_m
      rw [runPcPlaced_eq, show fsp = sm.sp from hsp_m.symm]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    let okRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m sm ∗ r1c_okCore A.repAlloc g g' s0
    refine r1c_frame_seq_vm
      (F := memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗ okRest)
      hs_m.inv (Entails.of_eq (by dsimp only [okRest, r1c_okCore]; sep_ac_rfl)) hstep_ok
      fun s4 hvm4 hinv4 hpc4 hrun4 ⟨hsp4, hfp4, hv4, htr4, hfs4, hx19_4, hx20_4, hx21_4⟩ => ?_
    dsimp only [okRest]
    rw [← A.pool_transport lim st_m sm s4 hvm4]
    have hmerge_ok :
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [r1c_split_at fsp 0x2c0 (0x23b0 - 0x2c0) runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b0 8 runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b8 40 runLocalBytes (by decide) (by decide)]
      exact r1c_rewrite_front
        (memRegion (fsp + 0x23b8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        (pointsTo64_entails_memRegion _ _) (by sep_ac_rfl) (by sep_ac_rfl)
    have henv_ok : ∃ evs, (R1cInit3Env sEnvs) g d2 evs ∧
        M.stepEvents (r1cOkTailEvs d2) st_m = M.stepEvents evs st :=
      ⟨evs_init ++ r1cOkTailEvs d2, h_ok g d2 fsp evs_init hinit_ev,
        (M.stepEvents_append evs_init (r1cOkTailEvs d2) st).symm⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_tail (g' := g') (d := d2) hh hext_le hsub64
        ⟨hpc4, hrun4, hsp4, hfp4, hinv4, hv4, hi2.base.spAligned⟩
        hx19_4 hx20_4 hx21_4 (htr4 ▸ htr_m)
        (r1c_hist_of_eq htr4 (congrArg FsState.files hfs4) hhist_m)
        hans hwr henv_ok hjoin)
    let okRest4 := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m s4 ∗ r1c_okCore A.repAlloc g g' s0
    exact r1c_rewrite_front okRest4 hmerge_ok (by dsimp only [okRest4]; sep_ac_rfl)
      (by dsimp only [okRest4, fsp, dirG, st_m]; sep_ac_rfl)
  | error err =>
    have hans : g.a = some none := by
      rw [hga, hslotOut.2.2]; rfl
    dsimp only [initResAt]
    let errRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A.repAlloc d2.meG ∗ addrNameHeap A.repAlloc dirG ∗
      addrNameHeap A.repAlloc d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st_m sm ∗ r1c_okCore A.repAlloc g g' s0
    apply r1c_sepWPp_weaken_pre
      (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x23b0#64) k) ∗ errRest)
      (Entails.of_eq (by dsimp only [errRest, r1c_okCore]; sep_ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r1c_sepWPp_exists_left; intro k
    have henv_err : ∀ evs_drop, FreeOnlyEvs evs_drop →
        ∃ evs, (R1cInit3Env sEnvs) g d2 evs ∧
          M.stepEvents (evs_drop ++ r1cOkTailEvs d2) st_m = M.stepEvents evs st :=
      fun evs_drop hfree =>
        ⟨evs_init ++ (evs_drop ++ r1cOkTailEvs d2),
          h_err g d2 fsp evs_init evs_drop hinit_ev hfree,
          (M.stepEvents_append evs_init (evs_drop ++ r1cOkTailEvs d2) st).symm⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_tail (g' := g') (d := d2) (k := k) hh hdrop hstk32 hext_le hsub64 hs_m
        hx19_m' hx20_m' hx21_m' htr_m hhist_m hans henv_err hrej)
    exact Entails.of_eq (by dsimp only [errRest, fsp, dirG, st_m])


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
