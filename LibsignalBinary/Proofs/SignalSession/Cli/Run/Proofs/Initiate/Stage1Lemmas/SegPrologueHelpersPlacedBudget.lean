/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Stage 1 Frame Combinators and Early Error Exits

Provides `VmPreserved`-preserving basic-block steppers (`sepWPp_step_to_vm_placed`,
`sepWPp_step_vm_placed`) and budget-threaded Stage 1 early `Err` exit lemmas
(`stage1_plain11_exit_placed_ok`, `stage1_untrusted_exit_placed_ok`) over `RustCliAllocBudget M`,
while re-exporting pure frame/layout helpers from `SegPrologueHelpers`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (speUntrustedIdentity)
open CryptoVerification.LibsignalSessionRepr (vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt speWord)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced coinsCursorAtPlaced initArgsAtPlaced initLocalsSize initPcPlaced initProgExtPlaced initProgPlaced
   initSaved)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (boxU8Buf_serialize_unpack byte_and_pad7_entails_word64 bytes32_eq_exists_words4
   cliBundleAt_unpack cliBundleBody cliBundleBody_pack cs_fp cs_vregs cs_x19 cs_x20 cs_x21 cs_x22
   cs_x23 cs_x24 cs_x25 cs_x26 cs_x27 cs_x28 false_entails initDef_eq_some_none_of_trust_false
   memRegion_32_words memRegion_merge poll_frame_5ba_merge poll_frame_5ba_split
   prologue_high_5ba_merge prologue_locals_split prologue_low_d0_merge pure_sepConj_intro
   sepWPp_drop_left sepWPp_exists_elim sepWPp_exists_left sepWPp_exists_pos2 sepWPp_exists_pos3
   sepWPp_exists_pos4 sepWPp_mono_pre sepWPp_pure_elim sepWPp_step_to_placed spAligned_of_frame
   spAligned_of_sp_eq sp_sub_4192_sub_3216 sp_sub_96_add_96 sp_sub_96_sub_4096 stage1VecBuf
   stage2LocalsPlaced_entails_memRegion vecU8_unpack_words words4_to_bytes32
   words_to_plain11_initResAt words_to_untrusted_initResAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
  (init_stringClone_placed_ok_at stage1_epilogue_err_placed_ok stringCloneAtStkSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
  (initCallLscro)

export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (sepWPp_step_to_placed sepWPp_drop_left sepWPp_exists_left sepWPp_exists_pos2 sepWPp_exists_pos3)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (sepWPp_exists_pos4 spAligned_of_sp_eq spAligned_of_frame bytes32_eq_exists_words4
   words4_to_bytes32)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (cs_x19 cs_x20 cs_x21 cs_x22 cs_x23)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (cs_x24 cs_x25 cs_x26 cs_x27 cs_x28)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (cs_fp cs_vregs memRegion_32_words boxU8Buf_serialize_unpack cliBundleBody)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (cliBundleAt_unpack cliBundleBody_pack prologue_locals_split prologue_low_d0_merge
   prologue_high_5ba_merge)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (poll_frame_5ba_split poll_frame_5ba_merge sepWPp_mono_pre sepWPp_exists_elim sepWPp_pure_elim)
export CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (false_entails memRegion_merge pure_sepConj_intro)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-! ## `VmPreserved`-preserving basic-block steppers -/

theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

/-- Single-goal `VmPreserved` basic-block stepper over `SepWP` under `LibsignalCodeRoLoaded lsmpl`. -/
theorem sepWPp_step_to_vm_placed [LibsignalPlacement] {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => VmPreserved s sm ∧
        (∀ sNext : State, sm = sNext →
          sNext.pc = mid → sNext.status = .Running →
          LibsignalCodeRoLoaded lsmpl sNext.mem →
          VmPreserved s sNext →
          SepWPp prog ret sNext Pm Q Qp oom))) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, hnext⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext sm rfl hpc hrun (hinv.of_keepsFrozen hsteps.keepsFrozen) hvm
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

/-- Two-goal sequential `VmPreserved` basic-block stepper over `SepWP` with explicit post-block assertion `P'`. -/
theorem sepWPp_step_vm_placed [LibsignalPlacement] {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} (P' : SepProp) {R_st : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (R_st sm ∧ Pm = P')))
    (hcont : ∀ sm : State,
      sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      VmPreserved s sm → R_st sm →
      SepWPp prog ret sm P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases hstep.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvm, hrst, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hpc hrun (hinv.of_keepsFrozen hsteps.keepsFrozen) hvm hrst
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

/-! ## Budget-threaded shared early `Err` exits -/

set_option maxHeartbeats 2400000 in
/-- Budget-threaded `SpeOwned.plain 11` (`SignatureValidationFailed`) error return from `0x0350`. -/
theorem stage1_plain11_exit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs : List AllocEvent}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : InitEnv x evs)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 11) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A lim (M.stepEvents evs st0) x stk s0 s) Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_mono_pre ?_
    (stage1_epilogue_err_placed_ok hEnv hstk hstk64 hctrl htr hx8 hans hpost
      (H_err := emp)
      (H_extra := coinsCursorAtPlaced x.coinsP x.coins 0 ∗ tokenInitPlacedAt)
      (by
        rw [sepConj_emp]
        exact words_to_plain11_initResAt A.repAlloc x.ret
          (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
          (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 28#5))
          (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 21#5)) hx26))
  unfold stage2MemPlaced
  dsimp only [fsp]
  have foc : ∀ {Full Sub Target F Goal : SepProp},
      (Full ⊢ Sub ∗ F) → (Sub ⊢ Target) → (Target ∗ F ⊢ Goal) → (Full ⊢ Goal) :=
    fun hfoc h hrest => Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)
  refine foc (by sep_frame) (stage2LocalsPlaced_entails_memRegion fsp x s0) ?_
  sep_frame

theorem stage1_plain11_exit_placed_ok_of_st [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : ∃ evs, InitEnv x evs ∧ st = M.stepEvents evs st0)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 11) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A lim st x stk s0 s) Q Qp oom := by
  rcases hEnv with ⟨evs, hEnvEvs, rfl⟩
  exact stage1_plain11_exit_placed_ok hEnvEvs hstk hstk64 hx8 hctrl htr hans hpost hx26

set_option maxHeartbeats 2400000 in
set_option maxHeartbeats 2400000 in
private theorem stage1_untrusted_step3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st1 : M.σ} {stk : Nat} {s0 s sMid : State}
    {cap ptr w4 : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : ∃ evs, InitEnv x evs ∧ st1 = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hal0 : s0.spAligned = true)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpcMid : sMid.pc = (blkPl_521).base + 620#64)
    (hrunMid : sMid.status = .Running)
    (hinvMid : LibsignalCodeRoLoaded lsmpl sMid.mem)
    (hspMid : sMid.sp = s.sp)
    (hx27Mid : sMid.readReg64 (.gpr 27#5) = cap)
    (hx25Mid : sMid.readReg64 (.gpr 25#5) = ptr)
    (hx28Mid : sMid.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length)
    (hfpMid : sMid.readReg64 .fp = s0.sp - 0x60#64)
    (hx19Mid : sMid.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hvregsMid : calleeSavedVRegs sMid = calleeSavedVRegs s0)
    (htrMid : sMid.trace = s0.trace)
    (hfsMid : sMid.fs.files = s0.fs.files)
    (hw4 : BitVec.extractLsb' 0 8 w4 = x.peer.device) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sMid
      (((s.sp + 0x1618#64) ↦₆₄ w4) ∗
        ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
        ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
        ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
        stage1VecBuf A.repAlloc cap ptr x.peer.val.name ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ A.pool lim st1 sMid ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))
      Q Qp oom := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed ((blkPl_521).base + 848#64) hinvMid ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sErr hsErr hpcErr hrunErr hinvErr hvm3
    have hspErr : sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hspMid, hsp]
    have hfpErr : sErr.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hfpMid]
    have hx19Err : sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hx19Mid]
    have hvregsErr : calleeSavedVRegs sErr = calleeSavedVRegs s0 := by
      rw [← hsErr]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsMid]
    have hfsErr : sErr.fs.files = s0.fs.files := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hfsMid]
    have htrErr : sErr.trace = s0.trace := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, htrMid]
    have hx26Err : sErr.readReg64 (.gpr 26#5) = speWord speUntrustedIdentity := by
      rw [← hsErr]; simp [wp_norm, arm64_norm]; rfl
    have hx27Err : sErr.readReg64 (.gpr 27#5) = cap := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hx27Mid]
    have hx25Err : sErr.readReg64 (.gpr 25#5) = ptr := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hx25Mid]
    have hx28Err : sErr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hx28Mid]
    have hx24Err : sErr.readReg64 (.gpr 24#5) = w4 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm]
    clear hsErr
    have hctrlErr : InInitiatePlaced s0 sErr 0x0350 :=
      ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
    have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_trust_false X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
        x.bundle x.coins htrustF
    rcases hEnv with ⟨evs, hEnvEvs, hStEq⟩
    have hpoolErr : A.pool lim st1 sMid = A.pool lim (M.stepEvents evs st0) sErr := by
      rw [hStEq]
      exact (A.pool_of_vmPreserved hvm3).symm
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sErr _ Q Qp oom
    refine sepWPp_mono_pre ?_
      (stage1_epilogue_err_placed_ok hEnvEvs hstk hstk64 hctrlErr htrErr hx8 hans hpost
        (H_err := stage1VecBuf A.repAlloc cap ptr x.peer.val.name)
        (H_extra := coinsCursorAtPlaced x.coinsP x.coins 0 ∗ tokenInitPlacedAt)
        (by
          rw [hx27Err, hx25Err]
          exact words_to_untrusted_initResAt A.repAlloc x.ret x.peer.val
            (sErr.readReg64 (.gpr 26#5)) cap ptr
            (sErr.readReg64 (.gpr 28#5))
            (sErr.readReg64 (.gpr 24#5)) (sErr.readReg64 (.gpr 21#5))
            hx26Err hx28Err (hx24Err ▸ hw4)))
    rw [← hsp, hpoolErr]
    have hlocMerge :
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
          memRegion (s.sp + 0x128#64) 0x490 ∗
          ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
          (memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
            ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
            ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
            ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
            ((s.sp + 0x1618#64) ↦₆₄ w4) ∗
            memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620)) ⊢
          memRegion s.sp initLocalsSize := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right ?_)))))
        (stage2LocalsPlaced_entails_memRegion s.sp x s0)
      have m64 := pointsTo64_entails_memRegion
      refine Entails.trans (sepConj_mono (Entails.refl _)
        (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _)
        (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _) (Entails.refl _)))))) ?_
      rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1600#64) (0x1600 - 0x5ba) 8 (0x1608 - 0x5ba) (by bv_omega) (by decide) (by decide)]
      rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1608#64) (0x1608 - 0x5ba) 8 (0x1610 - 0x5ba) (by bv_omega) (by decide) (by decide)]
      rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1610#64) (0x1610 - 0x5ba) 8 (0x1618 - 0x5ba) (by bv_omega) (by decide) (by decide)]
      rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1618#64) (0x1618 - 0x5ba) 8 (0x1620 - 0x5ba) (by bv_omega) (by decide) (by decide)]
      rw [memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1620#64) (0x1620 - 0x5ba) (initLocalsSize - 0x1620)
        (initLocalsSize - 0x5ba) (by bv_omega) (by decide) (by decide)]
      exact Entails.refl _
    have foc : ∀ {Full Sub Target F Goal : SepProp},
        (Full ⊢ Sub ∗ F) → (Sub ⊢ Target) → (Target ∗ F ⊢ Goal) → (Full ⊢ Goal) :=
      fun hfoc h hrest => Entails.trans hfoc (Entails.trans (sepConj_mono_left h) hrest)
    refine foc (by sep_frame) hlocMerge ?_
    sep_frame)

set_option maxHeartbeats 2400000 in
private theorem stage1_untrusted_step2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st1 : M.σ} {stk : Nat} {s0 s sm : State}
    {b0 : BitVec 8} {cap ptr : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : ∃ evs, InitEnv x evs ∧ st1 = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hal0 : s0.spAligned = true)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpcM : sm.pc = (blkPl_521).base + 600#64)
    (hrunM : sm.status = .Running)
    (hinvM : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hspM' : sm.sp = s.sp)
    (hx20M : sm.readReg64 (.gpr 20#5) = x.peerA)
    (hx21M : sm.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (hfpM : sm.readReg64 .fp = s0.sp - 0x60#64)
    (hx19M : sm.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hvregsM : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (htrM' : sm.trace = s0.trace)
    (hfsM' : sm.fs.files = s0.fs.files) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
      ((vecGhostAt A.repAlloc x.peer.name x.peerA ∗
          (((s.sp + 0x1600#64) ↦₆₄ cap) ∗
            ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
            ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
            stage1VecBuf A.repAlloc cap ptr x.peer.val.name) ∗
          A.pool lim st1 sm ∗
          stackAt s.sp (stk - cliInitiateFrame)) ∗
        (((s.sp + 0x1618#64) ↦₈ b0) ∗ memRegion (s.sp + 0x1619#64) 7 ∗
          (((x.peerA + asm64% addrDeviceOff) ↦₈ x.peer.device) ∗
            memRegion (x.peerA + asm64% (addrDeviceOff + 1))
              (asm% (protocolAddressSize - (addrDeviceOff + 1)))) ∗
          storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          coinsCursorAtPlaced x.coinsP x.coins 0 ∗
          tokenInitPlacedAt ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          lsLogOff ∗ initSaved s0 ∗
          memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
          memRegion (s.sp + 0x128#64) 0x490 ∗
          ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620)))
      Q Qp oom := by
  have haddr1618 : (s.sp + 0xfe0#64) + 0x638#64 = s.sp + 0x1618#64 := by bv_omega
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed ((blkPl_521).base + 620#64) hinvM ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sMid hsMid hpcMid hrunMid hinvMid hvm2
    have hspMid : sMid.sp = s.sp := by rw [← hsMid]; simp [wp_norm, arm64_norm, hspM']
    have hx27Mid : sMid.readReg64 (.gpr 27#5) = cap := by rw [← hsMid]; simp [wp_norm, arm64_norm]
    have hx25Mid : sMid.readReg64 (.gpr 25#5) = ptr := by rw [← hsMid]; simp [wp_norm, arm64_norm]
    have hx28Mid : sMid.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
      rw [← hsMid]; simp [wp_norm, arm64_norm]
    have hfpMid : sMid.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsMid]; simp [wp_norm, arm64_norm, hfpM]
    have hx19Mid : sMid.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsMid]; simp [wp_norm, arm64_norm, hx19M]
    have hvregsMid : calleeSavedVRegs sMid = calleeSavedVRegs s0 := by
      rw [← hsMid]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsM]
    have htrMid : sMid.trace = s0.trace := by rw [← hsMid]; simp [wp_norm, arm64_norm, htrM']
    have hfsMid : sMid.fs.files = s0.fs.files := by
      rw [← hsMid]; simp [wp_norm, arm64_norm, hfsM']
    clear hsMid
    have hdev8 : BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
      bv_bits
    have htrunc8 : BitVec.truncate 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
      bv_bits
    try rw [haddr1618]
    try rw [hdev8]
    try rw [htrunc8]
    have hpoolMid : A.pool lim st1 sm = A.pool lim st1 sMid := (A.pool_of_vmPreserved hvm2).symm
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sMid _ Q Qp oom
    refine sepWPp_mono_pre (P' :=
        ((∃∗ w4 : BitVec 64,
            ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗
            ((s.sp + 0x1618#64) ↦₆₄ w4)) ∗
          ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
          ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
          stage1VecBuf A.repAlloc cap ptr x.peer.val.name ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          coinsCursorAtPlaced x.coinsP x.coins 0 ∗
          tokenInitPlacedAt ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          lsLogOff ∗ A.pool lim st1 sMid ∗ initSaved s0 ∗
          memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
          memRegion (s.sp + 0x128#64) 0x490 ∗
          ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
          stackAt s.sp (stk - cliInitiateFrame))) ?_ ?_
    · rw [hpoolMid]
      unfold protocolAddressAt
      have hpack4 : ((s.sp + 0x1618#64) ↦₈ x.peer.device) ∗ memRegion (s.sp + 0x1619#64) 7 ⊢
          ∃∗ w4 : BitVec 64, ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗ ((s.sp + 0x1618#64) ↦₆₄ w4) := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          byte_and_pad7_entails_word64 (s.sp + 0x1618#64) x.peer.device
      refine Entails.trans ?_ (sepConj_mono_left hpack4)
      sep_frame
    simp only [sepExists_sepConj_left]
    refine sepWPp_exists_elim fun w4 => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun hw4 => ?_
    exact stage1_untrusted_step3_placed_ok hEnv hS hstk hstk64 hx8 hsp hal0 htrustF hpost
      hpcMid hrunMid hinvMid hspMid hx27Mid hx25Mid hx28Mid hfpMid hx19Mid hvregsMid
      htrMid hfsMid hw4)

set_option maxHeartbeats 2400000 in
/-- Budget-threaded untrusted-identity `Err` exit (`0x0244 → String::clone → 0x026c → 0x0350 → ret`). -/
theorem stage1_untrusted_exit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFitsClone : FitsEvents M lim st (stringCloneEvents x.peer.name))
    (hEnv : ∃ evs, InitEnv x evs ∧
      M.stepEvents (stringCloneEvents x.peer.name) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0244)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (htr : s.trace = s0.trace)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A lim st x stk s0 s) Q Qp oom := by
  have hpc : s.pc = (blkPl_521).base + 580#64 := hctrl.pc
  have hrun := hctrl.run; have hsp := hctrl.sp
  have hfp := hctrl.fp; have hx19 := hctrl.x19; have hfs0 := hctrl.files0
  have hvregs := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal :=
    CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas.InInitiatePlaced.spAligned_cur hctrl
  unfold stage2MemPlaced; dsimp only; rw [← hsp]
  have hsplit5ba :
      memRegion (s.sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1600#64) 24 ∗
          (∃∗ b0 : BitVec 8, (s.sp + 0x1618#64) ↦₈ b0) ∗
          memRegion (s.sp + 0x1619#64) 7 ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) := by
    rw [show initLocalsSize - 0x5ba = (0x1600 - 0x5ba) + (24 + (1 + (7 + (initLocalsSize - 0x1620)))) by decide,
      memRegion_split (s.sp + 0x5ba#64) (0x1600 - 0x5ba) _ (by decide),
      memRegion_split _ 24 _ (by decide),
      memRegion_split _ 1 _ (by decide), ProofLib.memRegion_one,
      memRegion_split _ 7 _ (by decide)]
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit5ba]
  refine sepWPp_mono_pre (P' :=
      ∃∗ b0 : BitVec 8,
        ((s.sp + 0x1618#64) ↦₈ b0) ∗
        memRegion (s.sp + 0x1619#64) 7 ∗
        memRegion (s.sp + 0x1600#64) 24 ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro b0
      exact Entails.sepExists_right b0 (by sep_frame)) ?_
  refine sepWPp_exists_elim fun b0 => ?_
  unfold initArgsAtPlaced
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed (lsmpl.base 623) hctrl.inv ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sClone hsClone hpcC hrunC hinvC hvm1
    have hspC : sClone.sp = s.sp := by rw [← hsClone]; simp [wp_norm, arm64_norm]
    have hx0C : sClone.readReg64 .x0 = x.peerA := by rw [← hsClone]; simp [wp_norm, arm64_norm]
    have hx8C : sClone.readReg64 .x8 = s.sp + 0x1600#64 := by
      rw [← hsClone]; simp [wp_norm, arm64_norm, hsp]; try bv_omega
    have hlrC : sClone.readReg64 .lr = initPcPlaced 0x0258 := by
      rw [← hsClone]
      change _ = (blkPl_521).base + 600#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hx20C : sClone.readReg64 (.gpr 20#5) = x.peerA := by
      rw [← hsClone]; simp [wp_norm, arm64_norm]
    have hx21C : sClone.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := by
      rw [← hsClone]; simp [wp_norm, arm64_norm, hx21]
    have hfpC : sClone.readReg64 .fp = s.readReg64 .fp := by
      rw [← hsClone]; simp [wp_norm, arm64_norm]
    have hx19C : sClone.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by
      rw [← hsClone]; simp [wp_norm, arm64_norm]
    have hvregsC : calleeSavedVRegs sClone = calleeSavedVRegs s0 := by
      rw [← hsClone]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs]
    have htrC : sClone.trace = s0.trace := by rw [← hsClone]; simp [wp_norm, arm64_norm, htr]
    have hfsC : sClone.fs.files = s0.fs.files := by rw [← hsClone]; simp [wp_norm, arm64_norm, hfs0]
    have halC : sClone.spAligned = true := by simpa only [State.spAligned, hspC] using hal
    clear hsClone
    have hpoolC : A.pool lim st s = A.pool lim st sClone := (A.pool_of_vmPreserved hvm1).symm
    rw [hpoolC]
    have hclone := init_stringClone_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
    have hpcC' : sClone.pc = lsmpl.base 623 := hpcC
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sClone _ Q Qp oom
    refine sepWPp_mono_pre (P' :=
        ((stringCloneAtStkSpec M A lim (stk - cliInitiateFrame)).pre
          ((x.peerA, s.sp + 0x1600#64, x.peer.name), st) sClone) ∗
        (((s.sp + 0x1618#64) ↦₈ b0) ∗ memRegion (s.sp + 0x1619#64) 7 ∗
          (((x.peerA + asm64% addrDeviceOff) ↦₈ x.peer.device) ∗
            memRegion (x.peerA + asm64% (addrDeviceOff + 1))
              (asm% (protocolAddressSize - (addrDeviceOff + 1)))) ∗
          storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          coinsCursorAtPlaced x.coinsP x.coins 0 ∗
          tokenInitPlacedAt ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          lsLogOff ∗ initSaved s0 ∗
          memRegion s.sp 0xd0 ∗ initArgsAtPlaced s.sp x s0 ∗
          memRegion (s.sp + 0x128#64) 0x490 ∗
          ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620))) ?_ ?_
    · unfold stringCloneAtStkSpec protocolAddressAt initArgsAtPlaced
      dsimp only
      rw [hspC]
      repeat rw [sepConj_assoc]
      exact pure_sepConj_intro ⟨hx0C, hx8C, hFitsClone,
        by rw [hlrC]; exact lsRetAddr_blockPlacement_base_add 521 600#64 (by decide) (by decide)⟩
        (by sep_frame)
    refine initCallLscro hh hpanic hclone hpcC' hrunC halC hinvC htrC hfsC hlrC
      (Entails.refl _) (fun _ => false_entails _) ?_
    intro sm hpcM hrunM hspM hcsM hinvM hfsM
    unfold stringCloneAtStkSpec; dsimp only
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun htrM => ?_
    have htrM' : sm.trace = s0.trace := htrM.trans htrC
    have hfsM' : sm.fs.files = s0.fs.files := hfsM htrM'
    have hspM' : sm.sp = s.sp := hspM.trans hspC
    have hx20M : sm.readReg64 (.gpr 20#5) = x.peerA := (cs_x20 hcsM).trans hx20C
    have hx21M : sm.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := (cs_x21 hcsM).trans hx21C
    have hfpM : sm.readReg64 .fp = s0.sp - 0x60#64 := ((cs_fp hcsM).trans hfpC).trans hfp
    have hx19M : sm.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      ((cs_x19 hcsM).trans hx19C).trans hx19
    have hvregsM : calleeSavedVRegs sm = calleeSavedVRegs s0 := (cs_vregs hcsM).trans hvregsC
    rw [hspC]
    have hunpack :
        vecU8 A.repAlloc (s.sp + 0x1600#64) x.peer.val.name ⊢
          ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
              ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
              ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
              stage1VecBuf A.repAlloc cap ptr x.peer.val.name := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        vecU8_unpack_words A.repAlloc (s.sp + 0x1600#64) x.peer.val.name
    refine sepWPp_mono_pre
      (sepConj_mono (sepConj_mono_right (sepConj_mono_left hunpack)) (Entails.refl _)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim fun cap => ?_
    refine sepWPp_exists_elim fun ptr => ?_
    change sm.pc = (blkPl_521).base + 600#64 at hpcM
    exact stage1_untrusted_step2_placed_ok hEnv hS hstk hstk64 hx8 hsp hal0 htrustF hpost
      hpcM hrunM hinvM hspM' hx20M hx21M hfpM hx19M hvregsM htrM' hfsM')

theorem stage1_untrusted_exit_placed_ok_of_append [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evsPre : List AllocEvent} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFits : FitsEnv M lim st0 (InitEnv x))
    (hEnv : InitEnv x (evsPre ++ stringCloneEvents x.peer.name))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiatePlaced s0 s 0x0244)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (htr : s.trace = s0.trace)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (stage2MemPlaced A lim (M.stepEvents evsPre st0) x stk s0 s) Q Qp oom :=
  stage1_untrusted_exit_placed_ok hh
    ((fitsEvents_append M lim evsPre (stringCloneEvents x.peer.name) st0).mp (hFits _ hEnv)).2
    ⟨evsPre ++ stringCloneEvents x.peer.name, hEnv,
      (M.stepEvents_append evsPre (stringCloneEvents x.peer.name) st0).symm⟩
    hS hstk hstk64 hx8 hctrl hx21 htr htrustF hpost hpanic

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
