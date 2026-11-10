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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed`-Threaded `signal_session::run` Arm `R1c` Placed Proof

Proves `run_hop_init3_of_slots_placed_ok_of_env_fd` and its `slotsOfPlaced` / `R1cInit3Env`
corollaries on Block `579` (`runProgPlaced H`), transporting `FdsGe3Closed` from `AtInit2PlacedFd`
(`R+0x28f0`) into the `withPreFdsGe3Closed` guard of `hc.initiate` and reusing `r1c_ok_tail` and
`r1c_err_tail` on return.
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
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk coinsInstalledPlaced coinsOf inputOf namedWrites ownedBytes runResAt runResSize
   storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtInit2Placed AtRunEntryPlaced InRunPlaced Init2Data InitGhost PanicK RejectKind RunHistOk
   RunNeeds RunSem addrNameHeap cliBundleAt idVtPlaced initResAt runFiles runFsp runLocalBytes
   runPcPlaced runPcPlaced_eq runProgPlaced runSaved sessVtPlaced slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (R1cCodeOk r1c_W6 r1c_addr_to_mem32 r1c_addr_unpack r1c_calleeSavedVRegs_q0
   r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2 r1c_calleeSavedVRegs_setMem
   r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState r1c_calleeSavedVRegs_writeReg64
   r1c_cliBundleAt_unpack r1c_errCore r1c_extractLsb_append_hi r1c_extractLsb_append_lo
   r1c_files_of_trace_eq r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64
   r1c_fs_writeVReg128 r1c_hist_of_eq r1c_init2Locals_unpack r1c_lowCells r1c_lowGaps
   r1c_mem48_to_slot6 r1c_mem_setPState r1c_okCore r1c_ownedBytes_entails_nameHeap
   r1c_readReg64_setPState r1c_rewrite_front r1c_sepWPp_exists_left r1c_sepWPp_pure_left
   r1c_sepWPp_weaken_pre r1c_slot6 r1c_slot6_to_mem48 r1c_spAligned r1c_sp_setPState r1c_split_at
   r1c_status_setPState r1c_symtab_setPState r1c_trace_setPState r1c_with_speOwned_words6)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopInit3PlacedFd RunHopInit3PlacedFdOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
  (r1c_call_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (R1cInit3Env r1cInitGhost r1c_err_tail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
  (r1cOkTailEvs r1c_ok_tail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs initSlotSpecPlaced slotFramePlaced slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init2MemPlaced runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtInit2PlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd slotWithPreFdsGe3Closed withPreFdsGe3Closed)

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

/-- Commute outer `withPreFdsGe3Closed` inside `withLsCodeRoLoaded lsmpl`. -/
theorem subroutine_ok_withLsCodeRoLoaded_preFds_of_outer [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withPreFdsGe3Closed (withLsCodeRoLoaded lsmpl spec))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (withPreFdsGe3Closed spec)) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  simpa only [withPreFdsGe3Closed, withLsCodeRoLoaded, sepConj_assoc] using hpre

/-- Unified `RunSlots`- and `Init3Env`-parametric proof of `RunHopInit3PlacedFdOf`. -/
theorem run_hop_init3_of_slots_placed_ok_of_env_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {Init3Env : RunCall → Init2Data → List AllocEvent → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hinit_eq : slots.initiate = (slotsOfPlaced A lim sEnvs S needs).initiate)
    (h_pre : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → Init3Env g d2 evs)
    (h_ok : ∀ g d2 fsp evs,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs → Init3Env g d2 (evs ++ r1cOkTailEvs d2))
    (h_err : ∀ g d2 fsp evs₁ evs₂,
      sEnvs.initiate (r1cInitGhost g d2 fsp) evs₁ → FreeOnlyEvs evs₂ →
        Init3Env g d2 (evs₁ ++ (evs₂ ++ r1cOkTailEvs d2))) :
    RunHopInit3PlacedFdOf (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs Init3Env H B S slots resStack := by
  intro g st s0 s2 d2 Q Qp hh hc hdrop hres_slots hres64 hspb he hi2Fd hfits hpanic hrej hjoin
  rcases hi2Fd with ⟨hi2, hfd2⟩
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
  have hfd3 : FdsGe3Closed s3.fs := hfs3 ▸ hfd2
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
  have hinit_ok := hc.initiate
  rw [hinit_eq] at hinit_ok
  have hcall_init_raw : subroutine_ok (runProgPlaced H) (lsmpl.base 521)
      (withPreFdsGe3Closed (initSlotSpecPlaced A lim sEnvs.initiate S (resStack - runFrame))) :=
    hinit_ok (resStack - runFrame) hinit_stk hsub63
  dsimp only [initSlotSpecPlaced] at hcall_init_raw
  have hcall_init := subroutine_ok_withLsCodeRoLoaded_preFds_of_outer hcall_init_raw
  refine r1c_call_lscro (F := initFrame) (initX, st) hcall_init
    hinv3 hpc3 hrun3 (r1c_spAligned hi2.base.spAligned hsp3) hlr3
    (by
      dsimp only [withPreFdsGe3Closed,
        CryptoVerification.SignalSession.Cli.RunCompose.init2MemPlaced,
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
      apply Entails.pure_right hfd3
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
      dsimp only [withPreFdsGe3Closed, initX, r1cInitGhost] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hpanic sf _ (Or.inl (by rw [hga, hp.1]; rfl)))
    (hoom := fun _ _ _ ho => (not_satisfies_false_sepConj ho).elim)
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [withPreFdsGe3Closed, initX, r1cInitGhost]
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

theorem run_hop_init3_placed_ok_of_env_fd [LibsignalPlacement] {M : AllocCostModel}
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
    RunHopInit3PlacedFd (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs Init3Env H B S needs resStack :=
  run_hop_init3_of_slots_placed_ok_of_env_fd
    (slots := slotsOfPlaced A lim sEnvs S needs) rfl rfl h_pre h_ok h_err

theorem run_hop_init3_of_slots_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hinit_eq : slots.initiate = (slotsOfPlaced A lim sEnvs S needs).initiate)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl) :
    RunHopInit3PlacedFdOf (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs (R1cInit3Env sEnvs) H B S slots resStack :=
  run_hop_init3_of_slots_placed_ok_of_env_fd hneed_eq hinit_eq
    (fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.inl h)
    (fun g d2 fsp _ h => by rw [hinit_addr] at h; exact SeqEnv.append h (Or.inl rfl))
    (fun g d2 fsp _ evs_d h hf => by
      rw [hinit_addr] at h; exact SeqEnv.append h (Or.inr ⟨evs_d, hf, rfl⟩))

theorem run_hop_init3_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl) :
    RunHopInit3PlacedFd (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (R1cInit3Env sEnvs) H B S needs resStack :=
  run_hop_init3_of_slots_placed_ok_fd
    (slots := slotsOfPlaced A lim sEnvs S needs) rfl rfl hinit_addr

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd
