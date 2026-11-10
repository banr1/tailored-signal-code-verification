/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable Stage 1 Segment 1 (`0x0000 → 0x0154`): Prologue and `is_trusted_identity`

Composes `SegPrologueTrustPlacedBudgetAux` (`0x0000 → 0x00b8`) with optional `futDrop`,
`__rust_dealloc(32, 8)`, and the trust boolean branch (`0x00b8 → 0x0154` / `0x0244`) over
`RustCliAllocBudget M` and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost idTrustBoxAt idTrustFutVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateFrame cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced InInitiatePlaced coinsCursorAtPlaced initArgsAtPlaced initLocalsSize
   initPcPlaced initProgExtPlaced initProgPlaced initSaved)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (bundleRestAt cliBundleBody cliBundleBody_pack cs_fp cs_vregs cs_x19 cs_x20 cs_x22
   cs_x26 cs_x27 false_entails getLsbD0_of_extract8_one getLsbD0_of_extract8_zero
   idTrustBoxAt_entails_memRegion memRegion_48_words poll_frame_5ba_merge pure_sepConj_intro
   sepWPp_drop_left sepWPp_mono_pre sepWPp_pure_elim sepWPp_with_rodata spAligned_of_frame
   spAligned_of_sp_eq sp_sub_4192_sub_3216 sp_sub_96_add_96 sp_sub_96_sub_4096)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
  (init_dealloc_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
  (initCallLscro rodata_idTrustFut_align_placed' rodata_idTrustFut_drop_placed'
   rodata_idTrustFut_size_placed')
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
  (sepWP_done_tpidr sepWPp_step_to_vm_placed stage1_untrusted_exit_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux
  (afterTrustPollMemPlaced afterTrustShimMemPlaced initEntryMemPlaced'
   stage1_prologue_to_shim_placed_ok stage1_trust_to_poll_placed_ok trustPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux
  (initEntryMemPlaced' afterTrustShimMemPlaced afterTrustPollMemPlaced)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux
  (trustPollGhostOf stage1_prologue_to_shim_placed_ok stage1_trust_to_poll_placed_ok)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-! ## `VmPreserved` transport lemmas -/

theorem afterTrustPollMemPlaced_of_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 : State) {s s' : State} (futPtr : BitVec 64) (opkId2 : BitVec 32)
    (w_tb o2 o3 o4 o5 : BitVec 64) (hvm : VmPreserved s s') :
    afterTrustPollMemPlaced A lim st x stk s0 s futPtr opkId2 w_tb o2 o3 o4 o5 =
      afterTrustPollMemPlaced A lim st x stk s0 s' futPtr opkId2 w_tb o2 o3 o4 o5 := by
  unfold afterTrustPollMemPlaced
  rw [A.pool_of_vmPreserved hvm]

theorem stage2MemPlaced_of_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 : State) {s s' : State} (hvm : VmPreserved s s') :
    stage2MemPlaced A lim st x stk s0 s = stage2MemPlaced A lim st x stk s0 s' := by
  unfold stage2MemPlaced
  rw [A.pool_of_vmPreserved hvm]

/-! ## Optional `futDrop` and `__rust_dealloc(32, 8)` (`0x00b8 → 0x0144`) -/

set_option maxHeartbeats 1600000 in
private theorem stage1_trust_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st2 : M.σ} {stk : Nat} {s0 sAfterDrop : State}
    {futPtr : BitVec 64} {opkId2 : BitVec 32}
    {w_tb o2 o3 o4 o5 : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hopk2 : ∀ p, x.bundle.opk = some p → opkId2 = p.1)
    (hal0 : s0.spAligned = true)
    (hpcAD : sAfterDrop.pc = (blkPl_521).base + 304#64)
    (hrunAD : sAfterDrop.status = .Running)
    (hspAD' : sAfterDrop.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (_hx20AD : sAfterDrop.readReg64 (.gpr 20#5) = futPtr)
    (hx22AD : sAfterDrop.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym)
    (hx26AD : sAfterDrop.readReg64 (.gpr 26#5) = 0#64 - 2#64)
    (hx27AD : sAfterDrop.readReg64 (.gpr 27#5) = w_tb)
    (hfpAD : sAfterDrop.readReg64 .fp = s0.sp - 0x60#64)
    (hx19AD : sAfterDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hvregsAD : calleeSavedVRegs sAfterDrop = calleeSavedVRegs s0)
    (htrAD' : sAfterDrop.trace = s0.trace)
    (hfsAD' : sAfterDrop.fs.files = s0.fs.files)
    (hinvAD : LibsignalCodeRoLoaded lsmpl sAfterDrop.mem)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAfterDealloc : State,
      InInitiatePlaced s0 sAfterDealloc 0x0144 →
      sAfterDealloc.trace = s0.trace →
      sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDealloc.readReg64 (.gpr 27#5) = w_tb →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDealloc
        (stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 32 8) st2) x stk s0 sAfterDealloc)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDrop
      (afterTrustPollMemPlaced A lim st2 x stk s0 sAfterDrop futPtr opkId2 w_tb o2 o3 o4 o5)
      Q Qp oom := by
  have halAD := spAligned_of_frame hal0 hspAD'
  unfold afterTrustPollMemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAD' ⊢
  refine sepWPp_with_rodata (rodata_idTrustFut_size_placed' hinvAD) ?_
  refine sepWPp_with_rodata (rodata_idTrustFut_align_placed' hinvAD) ?_
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed (lsρ lsRustDeallocSymCli) hinvAD ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sDealloc hsDealloc hpcF hrunF hinvF hvmF
    refine sepWPp_drop_left (sepWPp_drop_left ?_)
    have hspF : sDealloc.sp = fsp := by rw [← hsDealloc]; simp [wp_norm, arm64_norm, hspAD']
    have hx0F : sDealloc.readReg64 .x0 = futPtr := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm]
    have hx1F : (sDealloc.readReg64 .x1).toNat = 32 := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm]
    have hx2F : (sDealloc.readReg64 .x2).toNat = 8 := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm]
    have hlrF : sDealloc.readReg64 .lr = initPcPlaced 0x0144 := by
      rw [← hsDealloc]
      change _ = (blkPl_521).base + 324#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hx26F : sDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx26AD]
    have hx27F : sDealloc.readReg64 (.gpr 27#5) = w_tb := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx27AD]
    have hfpF : sDealloc.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, hfpAD]
    have hx19F : sDealloc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx19AD]
    have hvregsF : calleeSavedVRegs sDealloc = calleeSavedVRegs s0 := by
      rw [← hsDealloc]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAD]
    have htrF : sDealloc.trace = s0.trace := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, htrAD']
    have hfsF : sDealloc.fs.files = s0.fs.files := by
      rw [← hsDealloc]; simp [wp_norm, arm64_norm, hfsAD']
    clear hsDealloc
    have halF : sDealloc.spAligned = true := spAligned_of_sp_eq halAD (hspF.trans hspAD'.symm)
    have hpoolF : A.pool lim st2 sAfterDrop = A.pool lim st2 sDealloc :=
      (A.pool_of_vmPreserved hvmF).symm
    rw [hpoolF]
    have hdealloc := init_dealloc_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
    have hpcF' : sDealloc.pc = lsρ lsRustDeallocSymCli := hpcF
    let frameNoPool : SepProp :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sDealloc _ Q Qp oom
    refine sepWPp_mono_pre (P' :=
        ((rustCliDeallocBudgetExternSpecWithStack M A lim (stk - cliInitiateFrame)).pre
          (futPtr, 32, 8, st2) sDealloc) ∗
        frameNoPool) ?_ ?_
    · dsimp only [frameNoPool]
      unfold rustCliDeallocBudgetExternSpecWithStack storesAt
      dsimp only
      rw [hspF]
      have hboxMem := idTrustBoxAt_entails_memRegion futPtr x.stores x.peerA
        (x.bundleA + 120#64) 1#8 0#8
      have hpackB :
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗ bundleRestAt x opkId2 ⊢
            cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr := by
        refine Entails.trans ?_
          (cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
            (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
            (opkId := opkId2) h1 h2 h3 hopk2)
        unfold cliBundleBody bundleRestAt
        rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
      have h48 :
          ((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
            ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
            ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
            ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5) ⊢
            memRegion (fsp + 0x1600#64) 48 := by
        rw [memRegion_48_words (fsp + 0x1600#64)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        sep_frame
      have hmergePoll48 :
          memRegion (fsp + 0x5ba#64) 6 ∗
            ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
            ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
            memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
            (((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
              ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
              ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
              ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5)) ∗
            memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630) ⊢
            memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) :=
        Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left h48)))))
          (poll_frame_5ba_merge fsp futPtr (lsρ idTrustFutVtSym) 48 (by decide))
      repeat rw [sepConj_assoc]
      refine pure_sepConj_intro ⟨hx0F, hx1F, hx2F, ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩,
        by rw [hlrF]; exact lsRetAddr624_blockPlacement_base_add 521 _ (by decide) (by decide)⟩ ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hboxMem
            (sepConj_mono_right (sepConj_mono hpackB (sepConj_mono_left hmergePoll48))))))
      sep_frame
    refine initCallLscro hh hpanic hdealloc hpcF' hrunF halF hinvF htrF hfsF hlrF
      (Entails.refl _) (fun _ => false_entails _) ?_
    intro sAfterDealloc hpcAF hrunAF hspAF hcsAF hinvAF hfsAF
    unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun htrAF => ?_
    have htrAF' : sAfterDealloc.trace = s0.trace := htrAF.trans htrF
    have hfsAF' : sAfterDealloc.fs.files = s0.fs.files := hfsAF htrAF'
    have hspAF' : sAfterDealloc.sp = fsp := hspAF.trans hspF
    have hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 :=
      (cs_x26 hcsAF).trans hx26F
    have hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb :=
      (cs_x27 hcsAF).trans hx27F
    have hfpAF : sAfterDealloc.readReg64 .fp = s0.sp - 0x60#64 :=
      (cs_fp hcsAF).trans hfpF
    have hx19AF : sAfterDealloc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (cs_x19 hcsAF).trans hx19F
    have hvregsAF : calleeSavedVRegs sAfterDealloc = calleeSavedVRegs s0 :=
      (cs_vregs hcsAF).trans hvregsF
    refine sepWPp_mono_pre
      (P' := stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 32 8) st2) x stk s0 sAfterDealloc)
      ?_ ?_
    · unfold stage2MemPlaced
      dsimp only [frameNoPool]
      rw [hspF, ← hfsp]
      sep_frame
    have hctrlAF : InInitiatePlaced s0 sAfterDealloc 0x0144 :=
      ⟨hpcAF, hrunAF, hspAF'.trans hfsp.symm, hfpAF, hx19AF, hfsAF', hinvAF, hvregsAF, hal0⟩
    exact hnext sAfterDealloc hctrlAF htrAF' hx26AF hx27AF)

set_option maxHeartbeats 1600000 in
/-- Optional `futDrop`, `__rust_dealloc(32, 8)`, and `stage2MemPlaced` packing (`0x00b8 → 0x0144`). -/
theorem stage1_trust_drop_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st2 : M.σ} {stk : Nat} {s0 sAfterPoll : State}
    {futPtr : BitVec 64} {opkId2 : BitVec 32}
    {w_tb o2 o3 o4 o5 : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hopk2 : ∀ p, x.bundle.opk = some p → opkId2 = p.1)
    (hctrlAP : InInitiatePlaced s0 sAfterPoll 0x00b8)
    (htrAP' : sAfterPoll.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAfterDealloc : State,
      InInitiatePlaced s0 sAfterDealloc 0x0144 →
      sAfterDealloc.trace = s0.trace →
      sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDealloc.readReg64 (.gpr 27#5) = w_tb →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDealloc
        (stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 32 8) st2) x stk s0 sAfterDealloc)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterPoll
      (afterTrustPollMemPlaced A lim st2 x stk s0 sAfterPoll futPtr opkId2 w_tb o2 o3 o4 o5)
      Q Qp oom := by
  have hpcAP : sAfterPoll.pc = (blkPl_521).base + 184#64 := hctrlAP.pc
  have hrunAP := hctrlAP.run; have hspAP' := hctrlAP.sp
  have hfpAP := hctrlAP.fp; have hx19AP := hctrlAP.x19; have hfsAP' := hctrlAP.files0
  have hinvAP := hctrlAP.inv; have hvregsAP := hctrlAP.vregs; have hal0 := hctrlAP.spAligned
  have halAP := spAligned_of_frame hal0 hspAP'
  have hfspAl : ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAP'] using halAP
  refine sepWPp_with_rodata (rodata_idTrustFut_drop_placed' hinvAP) ?_
  by_cases hdz0 : lsmpl.base 547 = 0#64
  · rw [hdz0]
    unfold afterTrustPollMemPlaced; dsimp only
    generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAP' hfspAl ⊢
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    refine sepWPp_step_to_vm_placed ((blkPl_521).base + 304#64) hinvAP ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro sAD hsAD hpcAD hrunAD hinvAD hvmAD
      refine sepWPp_drop_left ?_
      have hspAD : sAD.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
        rw [← hsAD, hfsp]; simp [wp_norm, arm64_norm, hspAP']
      have hx20AD : sAD.readReg64 (.gpr 20#5) = futPtr := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx22AD : sAD.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx26AD : sAD.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx27AD : sAD.readReg64 (.gpr 27#5) = w_tb := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hfpAD : sAD.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfpAP]
      have hx19AD : sAD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hx19AP]
      have hvregsAD : calleeSavedVRegs sAD = calleeSavedVRegs s0 := by
        rw [← hsAD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAP]
      have htrAD : sAD.trace = s0.trace := by rw [← hsAD]; simp [wp_norm, arm64_norm, htrAP']
      have hfsAD : sAD.fs.files = s0.fs.files := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfsAP']
      clear hsAD
      have hpoolAD : A.pool lim st2 sAfterPoll = A.pool lim st2 sAD :=
        (A.pool_of_vmPreserved hvmAD).symm
      rw [hpoolAD, ← hfsp]
      exact stage1_trust_dealloc_placed_ok hh hstk hstk64 h1 h2 h3 hopk2 hal0
        hpcAD hrunAD hspAD hx20AD hx22AD hx26AD hx27AD hfpAD hx19AD hvregsAD htrAD hfsAD hinvAD
        hpanic hnext)
  · have hdz : (lsmpl.base 547 == 0#64) = false := beq_eq_false_iff_ne.2 hdz0
    generalize hdropA : lsmpl.base 547 = dropAddr at hdz ⊢
    unfold afterTrustPollMemPlaced; dsimp only
    generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAP' hfspAl ⊢
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    refine sepWPp_step_to_vm_placed dropAddr hinvAP ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro sDrop hsDrop hpcD hrunD hinvD hvmD
      subst hdropA
      refine sepWPp_drop_left ?_
      have hspD : sDrop.sp = fsp := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hspAP']
      have hlrD : sDrop.readReg64 .lr = initPcPlaced 0x0130 := by
        rw [← hsDrop]
        change _ = (blkPl_521).base + 304#64
        simp [wp_norm, arm64_norm]; try bv_omega
      have hx20D : sDrop.readReg64 (.gpr 20#5) = futPtr := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hx22D : sDrop.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hx26D : sDrop.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hx27D : sDrop.readReg64 (.gpr 27#5) = w_tb := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hfpD : sDrop.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hfpAP]
      have hx19D : sDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hx19AP]
      have hvregsD : calleeSavedVRegs sDrop = calleeSavedVRegs s0 := by
        rw [← hsDrop]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAP]
      have htrD : sDrop.trace = s0.trace := by rw [← hsDrop]; simp [wp_norm, arm64_norm, htrAP']
      have hfsD : sDrop.fs.files = s0.fs.files := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hfsAP']
      clear hsDrop
      have halD : sDrop.spAligned = true := spAligned_of_sp_eq halAP (hspD.trans hspAP'.symm)
      rw [← hfsp]
      change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sDrop
        (afterTrustPollMemPlaced A lim st2 x stk s0 sAfterPoll futPtr opkId2 w_tb o2 o3 o4 o5)
        Q Qp oom
      refine initCallLscro hh hpanic hStore.futDrop (gx := ())
        (F := afterTrustPollMemPlaced A lim st2 x stk s0 sAfterPoll futPtr opkId2 w_tb o2 o3 o4 o5)
        hpcD hrunD halD hinvD htrD hfsD hlrD
        (by unfold futDropBudgetSpec; rw [emp_sepConj]; exact Entails.refl _)
        (fun _ => false_entails _) ?_
      intro sAfterDrop hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
      unfold futDropBudgetSpec; dsimp only
      refine sepWPp_pure_elim fun ⟨htrAD, hvmCall⟩ => ?_
      have htrAD' : sAfterDrop.trace = s0.trace := htrAD.trans htrD
      have hvmAD : VmPreserved sAfterPoll sAfterDrop := hvmD.trans hvmCall
      rw [afterTrustPollMemPlaced_of_vmPreserved A lim st2 x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5 hvmAD]
      exact stage1_trust_dealloc_placed_ok hh hstk hstk64 h1 h2 h3 hopk2 hal0
        hpcAD hrunAD ((hspAD.trans hspD).trans hfsp.symm)
        ((cs_x20 hcsAD).trans hx20D) ((cs_x22 hcsAD).trans hx22D)
        ((cs_x26 hcsAD).trans hx26D) ((cs_x27 hcsAD).trans hx27D)
        ((cs_fp hcsAD).trans hfpD) ((cs_x19 hcsAD).trans hx19D)
        ((cs_vregs hcsAD).trans hvregsD) htrAD' (hfsAD htrAD') hinvAD hpanic hnext)

/-! ## Trust boolean branch (`0x0144 → 0x0154` / `0x0244`) -/

set_option maxHeartbeats 1200000 in
/-- Branches on trust boolean `tb` (`0x0144 → 0x0154` on `true`, `0x0244` on `false`). -/
theorem stage1_trust_branch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st3 : M.σ} {stk : Nat} {s0 sAfterDealloc : State}
    {tb : Bool} {w_tb : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFitsClone : tb = false → FitsEvents M lim st3 (stringCloneEvents x.peer.name))
    (hEnvUntrusted :
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
        ∃ evs, InitEnv x evs ∧
          M.stepEvents (stringCloneEvents x.peer.name) st3 = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAF : InInitiatePlaced s0 sAfterDealloc 0x0144)
    (htrAF' : sAfterDealloc.trace = s0.trace)
    (hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64)
    (hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb)
    (hw_tb : BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8))
    (htb2 : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A lim st3 x stk s0 s1) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDealloc
      (stage2MemPlaced A lim st3 x stk s0 sAfterDealloc) Q Qp oom := by
  have hx8 := hs0.x8; have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAF : sAfterDealloc.pc = (blkPl_521).base + 324#64 := hctrlAF.pc
  have hrunAF := hctrlAF.run; have hspAF' := hctrlAF.sp
  have hfpAF := hctrlAF.fp; have hx19AF := hctrlAF.x19; have hfsAF' := hctrlAF.files0
  have hinvAF := hctrlAF.inv; have hvregsAF := hctrlAF.vregs
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  cases tb
  · have hbit0 : w_tb.getLsbD 0 = false := getLsbD0_of_extract8_zero hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 0#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = false := hbit0
    refine sepWPp_step_to_vm_placed ((blkPl_521).base + 580#64) hinvAF ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro sU hsU hpcU hrunU hinvU hvmU
      have hspU : sU.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
        rw [← hsU]; simp [wp_norm, arm64_norm, hspAF']
      have hx21U : sU.readReg64 (.gpr 21#5) = sU.sp + 0xfe0#64 := by
        rw [← hsU]; simp [wp_norm, arm64_norm, hspAF', cliInitiateFrame]
      have hfpU : sU.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsU]; simp [wp_norm, arm64_norm, hfpAF]
      have hx19U : sU.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsU]; simp [wp_norm, arm64_norm, hx19AF]
      have hvregsU : calleeSavedVRegs sU = calleeSavedVRegs s0 := by
        rw [← hsU]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAF]
      have htrU : sU.trace = s0.trace := by
        rw [← hsU]; simp [wp_norm, arm64_norm, htrAF']
      have hfsU : sU.fs.files = s0.fs.files := by
        rw [← hsU]; simp [wp_norm, arm64_norm, hfsAF']
      clear hsU
      rw [stage2MemPlaced_of_vmPreserved A lim st3 x stk s0 hvmU]
      have hctrlU : InInitiatePlaced s0 sU 0x0244 :=
        ⟨hpcU, hrunU, hspU, hfpU, hx19U, hfsU, hinvU, hvregsU, hal0⟩
      exact stage1_untrusted_exit_placed_ok hh (hFitsClone rfl) (hEnvUntrusted htb2)
        hS hstk hstk64 hx8 hctrlU hx21U htrU htb2 hpost hpanic)
  · have hbit0 : w_tb.getLsbD 0 = true := getLsbD0_of_extract8_one hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 1#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = true := hbit0
    refine sepWPp_step_to_vm_placed ((blkPl_521).base + 340#64) hinvAF ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro s1 hs1 hpc1 hrun1 hinv1 hvm1
      have hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
        rw [← hs1]; simp [wp_norm, arm64_norm, hspAF']
      have hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hs1]; simp [wp_norm, arm64_norm, hfpAF]
      have hx19_1 : s1.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hs1]; simp [wp_norm, arm64_norm, hx19AF]
      have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
        rw [← hs1]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAF]
      have htr1 : s1.trace = s0.trace := by
        rw [← hs1]; simp [wp_norm, arm64_norm, htrAF']
      have hfs1 : s1.fs.files = x.F := by
        rw [← hs1]; simp [wp_norm, arm64_norm, hfsAF', hfs0]
      clear hs1
      rw [stage2MemPlaced_of_vmPreserved A lim st3 x stk s0 hvm1]
      have hctrl1 : InInitiatePlaced s0 s1 0x0154 :=
        ⟨hpc1, hrun1, hsp1, hfp1, hx19_1, hfs1.trans hfs0.symm, hinv1, hvregs1, hal0⟩
      exact hnext s1 h1 h2 h3 hctrl1 htr1 hfs1 htb2)

/-! ## Full Segment 1 composition (`0x0000 → 0x0154`) -/

/-- Budget-threaded `idTrustPoll`, `futDrop`, `dealloc`, and trust branch (`0x009c → 0x0154`). -/
theorem stage1_trust_poll_drop_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st1 : M.σ} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsPoll : FitsEnv M lim st1
      (eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0))))
    (hFitsClone : ∀ evs2 : List AllocEvent,
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0)) evs2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      FitsEvents M lim (M.stepEvents (evs2 ++ rustDeallocEvents 32 8) st1)
        (stringCloneEvents x.peer.name))
    (hEnvUntrusted : ∀ evs2 : List AllocEvent,
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0)) evs2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs2 ++ rustDeallocEvents 32 8 ++ stringCloneEvents x.peer.name) st1 =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State) (evs2 : List AllocEvent)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0)) evs2 →
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A lim (M.stepEvents (evs2 ++ rustDeallocEvents 32 8) st1) x stk s0 s1)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMemPlaced A lim st1 x stk s0 sAfterShim) Q Qp oom :=
  stage1_trust_to_poll_placed_ok hh hStore hFitsPoll hinitOk hs0 hctrlAS htrAS' hvtAS hpanic
    fun _ evs2 _ tb _ _ _ _ _ hevs2 hopk2 hctrlAP htrAP' hw_tb htb2 =>
      stage1_trust_drop_dealloc_placed_ok hh hStore hstk hstk64 h1 h2 h3 hopk2 hctrlAP htrAP' hpanic
        fun sAfterDealloc hctrlAF htrAF' hx26AF hx27AF => by
          rw [← M.stepEvents_append evs2 (rustDeallocEvents 32 8) st1]
          exact stage1_trust_branch_placed_ok hh
            (fun htbF => hFitsClone evs2 hevs2 (htbF ▸ htb2))
            (fun htrustF => by
              rw [← M.stepEvents_append (evs2 ++ rustDeallocEvents 32 8)
                (stringCloneEvents x.peer.name) st1]
              exact hEnvUntrusted evs2 hevs2 htrustF)
            hS hstk hstk64 hs0 h1 h2 h3 hctrlAF htrAF' hx26AF hx27AF hw_tb htb2 hpost hpanic
            (fun s1 h1' h2' h3' => hnext s1 evs2 h1' h2' h3' hevs2)

/-- Budget-threaded prologue and `is_trusted_identity` (`0x0000 → 0x0154` and untrusted exit). -/
theorem stage1_prologue_trust_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (futPtr : BitVec 64),
      BoxAllocEnv 32 evs1 → futPtr ≠ 0#64 → futPtr.toNat % 8 = 0 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futPtr)))
    (hFitsClone : ∀ (evs1 evs2 : List AllocEvent) (futPtr : BitVec 64),
      BoxAllocEnv 32 evs1 → futPtr ≠ 0#64 → futPtr.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futPtr) evs2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 32 8) st)
        (stringCloneEvents x.peer.name))
    (hEnvUntrusted : ∀ (evs1 evs2 : List AllocEvent) (futPtr : BitVec 64),
      BoxAllocEnv 32 evs1 → futPtr ≠ 0#64 → futPtr.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futPtr) evs2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 32 8 ++ stringCloneEvents x.peer.name) st =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State) (evs1 evs2 : List AllocEvent) (futPtr : BitVec 64)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      BoxAllocEnv 32 evs1 →
      futPtr ≠ 0#64 →
      futPtr.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futPtr) evs2 →
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 32 8) st) x stk s0 s1)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced' A lim st x stk s0) Q Qp oom :=
  stage1_prologue_to_shim_placed_ok hh hStore hFitsShim hstk hstk64 hs0 hpanic
    fun sAfterShim evs1 h1 h2 h3 hevs1 hfutNZ hfutAl hctrlAS htrAS' hvtAS =>
      stage1_trust_poll_drop_placed_ok hh hStore
        (hFitsPoll evs1 (sAfterShim.readReg64 .x0) hevs1 hfutNZ hfutAl)
        (fun evs2 hevs2 htrustF => by
          rw [← M.stepEvents_append evs1 (evs2 ++ rustDeallocEvents 32 8) st, ← List.append_assoc]
          exact hFitsClone evs1 evs2 (sAfterShim.readReg64 .x0) hevs1 hfutNZ hfutAl hevs2 htrustF)
        (fun evs2 hevs2 htrustF => by
          rw [← M.stepEvents_append evs1
            (evs2 ++ rustDeallocEvents 32 8 ++ stringCloneEvents x.peer.name) st,
            ← List.append_assoc, ← List.append_assoc]
          exact hEnvUntrusted evs1 evs2 (sAfterShim.readReg64 .x0) hevs1 hfutNZ hfutAl hevs2 htrustF)
        hS hinitOk hstk hstk64 hs0 h1 h2 h3 hctrlAS htrAS' hvtAS hpost hpanic
        (fun s1 evs2 h1' h2' h3' hevs2 hctrl1 htr1 hfs1 htrust => by
          rw [← M.stepEvents_append evs1 (evs2 ++ rustDeallocEvents 32 8) st, ← List.append_assoc]
          exact hnext s1 evs1 evs2 (sAfterShim.readReg64 .x0)
            h1' h2' h3' hevs1 hfutNZ hfutAl hevs2 hctrl1 htr1 hfs1 htrust)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
