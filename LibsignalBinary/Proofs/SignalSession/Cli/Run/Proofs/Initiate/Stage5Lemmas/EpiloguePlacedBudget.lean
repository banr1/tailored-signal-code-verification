/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Stage 5 Shared Epilogue and Error Cleanup (`[LibsignalPlacement]`)

Verifies `stage5_epilogue_placed_ok` (`+0x0350..+0x037c → lr`) and `stage5_err_cleanup_placed_ok`
(`+0x1858 → +0x0350 → lr`) on `initProgPlaced W` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (spAligned_mask_of_frame spAligned_mask_add_4096 spAligned_mask_add_7312)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  stage5_epilogue_placed_ok stage5_err_cleanup_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
  (s5_call_dealloc_placed s5_call_dropSS_placed s5_dealloc_ok_at_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

private theorem sepWP_of_vm {prog : Program} {mid : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP prog mid s P post oom :=
  SepWP.mono h (fun _ _ _ _ ⟨hvmp, hpost⟩ => hpost hvmp)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

section EpilogueBlockPlaced

private theorem sp_epilogue_add1_placed (a : BitVec 64) : (a - 7408#64) + 4096#64 = a - 3312#64 := by
  bv_omega
private theorem sp_epilogue_add2_placed (a : BitVec 64) : (a - 3312#64) + 3216#64 = a - 96#64 := by
  bv_omega
private theorem sp_epilogue_add3_placed (a : BitVec 64) : (a - 96#64) + 96#64 = a := by
  bv_omega
attribute [local arm64_norm, local wp_norm]
  sp_epilogue_add1_placed sp_epilogue_add2_placed sp_epilogue_add3_placed

/-- Budget-threaded shared epilogue (`+0x0350..+0x037c → lr` on `initProgPlaced W`): writes
`(x26, x27, x25, x28, x24, x21)` to `x.ret`, restores `s0.sp` and all callee-saved registers,
transports `A.pool` via `VmPreserved`, and discharges `Q` via `InitExitPostPlaced`. -/
theorem stage5_epilogue_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost}
    {st0 st : M.σ} {evs : List AllocEvent} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEnv : InitEnv x evs)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) Unit)
    (OutHeap Junk : SepProp)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = initEntryPlaced + offEpilogue)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F)
    (hfss : s.fs.files = x.F)
    (hout : ∀ sf, slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' res s0 sf)
    (hres :
      ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ OutHeap) ⊢
        initResAt A.repAlloc x.ret res)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hst : st = M.stepEvents evs st0 := by rfl) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (memRegion x.ret 48 ∗ initSaved s0 ∗
        memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame) ∗
        OutHeap ∗ storesAt A.repAlloc x.stores g' ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ Junk)
      Q Qp oom := by
  intro fsp
  subst hst
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offEpilogue] at hpc ⊢
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply SepWPp.of_sepWP_ret
  conv =>
    arg 4
    rw [sret48_words6_split x.ret]
    unfold initSaved
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hsp hsp_align
  have hsp_mask4096 : (((s.sp + 4096#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_4096 hsp_mask
  have hsp_mask7312 : (((s.sp + 7312#64) &&& 15#64) == 0#64) = true :=
    spAligned_mask_add_7312 hsp_mask
  apply sepWP_of_vm
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    intro hvmp
    refine hpost _ _ ⟨by wp_norm_goal, ?_, ?_⟩
    · simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs]
    · dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      refine Entails.sepExists_right evs ?_
      refine Entails.sepExists_right g' (Entails.sepExists_right res ?_)
      refine Entails.pure_right
        ⟨hEnv,
         slotTrace_of_trace_eq (x := x)
           (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]; exact htr)
           hfs0
           (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]; exact hfss),
         hout _⟩ ?_
      have hstkFull := reassemble_stackAt_full (B := B) s0 hstk hstk64
      dsimp only at hstkFull
      rw [A.pool_of_vmPreserved hvmp]
      refine Entails.trans (Q :=
          (((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
            ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
            ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
            ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
            ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ OutHeap) ∗
            (memRegion fsp initLocalsSize ∗ initSaved s0 ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
            storesAt A.repAlloc x.stores g' ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
            cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
            (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents evs st0) s ∗ Junk))
        (Entails.of_eq ?_) ?_
      · unfold initSaved
        simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
        s5_ac_rfl
      refine Entails.trans
        (sepConj_mono hres (sepConj_mono hstkFull
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (entails_anyHeap _)))))))))) ?_
      exact Entails.of_eq (by s5_ac_rfl))

end EpilogueBlockPlaced

/-- VM-preserving basic-block stepper preserving `LibsignalCodeRoLoaded pl` and `VmPreserved s`
for polymorphic `{oom : State → SepProp}`. -/
theorem sepWPp_step_to_lscro_vm_mem {prog : Program} {pl : MultiPlacement} {ret mid : BitVec 64}
    {s sm : State} {P Pm : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (hstep : SepWP prog mid s P
      (fun s' P' => VmPreserved s s' ∧ (∃ m, s' = sm.setMem m) ∧ P' = Pm))
    (hcont : ∀ m, VmPreserved s (sm.setMem m) →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl (sm.setMem m).mem →
      SepWPp prog ret (sm.setMem m) Pm Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases hstep.elim hm hL with ⟨_, hsteps, ⟨-, -, _, hmm, hvmp, ⟨m, rfl⟩, rfl⟩ | ⟨_, hfalse⟩⟩
  · have hcrl' := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := hcont m hvmp hcrl' R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

attribute [local arm64_norm, local wp_norm] fsp_err_eqs

set_option maxHeartbeats 800000 in
/-- Budget-threaded error cleanup starting at `+0x1858` on `initProgPlaced W`: drops
`SessionStructure` (`[fsp + 0x5b9] = 1#8`), deallocates `pqspkPtr` (`1568` bytes, align `1`),
skips empty `initFreshRecAt`, and enters `stage5_epilogue_placed_ok` to establish
`InitExitPostPlaced` with `SpeOwned` at `x.ret`. -/
theorem stage5_err_cleanup_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {B : RunBudgets} {S : RunSem} {x : InitGhost}
    {st0 st : M.σ}
    {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg' : SessionGhost} {ss' : SessionState (List (BitVec 8))}
    {k : RunDrop.SpeOwned} {SpeHeap Extra : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hEnv : ∀ evsDrop, FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents evsDrop st) = M.stepEvents evs st0)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpc : s.pc = initEntryPlaced + offErrEntry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfs0 : s0.fs.files = x.F)
    (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hw0_ne3 : s.readReg64 (.gpr 26#5) ≠ 0xFFFFFFFFFFFFFFFD#64)
    (hspe :
      ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((x.ret + 0x08#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 0x10#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 0x18#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 0x20#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 0x28#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ SpeHeap) ⊢
        RunDrop.speOwnedAt A.repAlloc x.ret k)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗
        initArgsAtPlaced fsp x s0 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg' ss' ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        SpeHeap ∗ Extra)
      Q Qp oom := by
  intro fsp
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem hinv (mid := lsmpl.base 512)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offErrEntry] at hpc ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp1 hcrl1
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dropSS_placed (s0 := s0) (ret_pc := initEntryPlaced + offErrEntryDropDone)
    hDropSS fsp (fsp + 0x460#64) sg' ss' st ?errF1
    (by wp_norm_goal; try rfl) (by wp_norm_lhs) (by simp only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offErrEntryDropDone]; wp_norm_goal; try rfl)
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hcrl1
    (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
    ?errPre1 ?_
  case errPre1 =>
    rw [A.pool_of_vmPreserved hvmp1]
    s5_close_frame
  intro sm1 evsDrop hfreeDrop hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hfss
  simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hvregs] at hcs1
  rcases hcs1 with ⟨hx19_1, _, hx21_1, _, _, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (dropSS_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; rw [stage3KeySlotsAt_unfold]; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_vm_mem hinv1 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offErrEntryDropDone] at hpc1 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp2 hcrl2
  have hkpkMem : (pqspkPtr ↦ₛ x.bundle.kpk) ⊢ memRegion pqspkPtr 1568 := by
    simpa [hkpkLen] using pointsToBytes_entails_memRegion pqspkPtr x.bundle.kpk
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine CallKitPlacedBudget.s5_call_dealloc_placed (s0 := s0) (ret_pc := initEntryPlaced + offErrAfterDealloc)
    (CallKitPlacedBudget.s5_dealloc_ok_at_placed hAlloc) fsp pqspkPtr 1568 1 (M.stepEvents evsDrop st) ?errF2
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offErrAfterDealloc]; wp_norm_goal; try rfl)
    (by simp only [wp_norm, arm64_norm, htr1]) hcrl2
    (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) ⟨layoutOk_1568_1, by decide⟩
    ?errPre2 ?_
  case errPre2 =>
    inImageKitClearInvHyps
    rw [A.pool_of_vmPreserved hvmp2]
    s5_have_eq hpull : (pqspkPtr ↦ₛ x.bundle.kpk) ∗ ?restKpk := by
      conv => lhs; simp only [wp_norm, arm64_norm, hsp1]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hkpkMem) ?_)
    s5_close_frame
  intro sm2 hpc2 hrun2 hsp2 hal2 hcs2 hinv2 htr2 hfs2
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1'
  simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx21_1, hx24_1, hx25_1,
    hx26_1, hx27_1, hx28_1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, _, hx21_2, _, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; unfold initFreshRecAt; simp only [sepConj_assoc]
  have hw0_ne3' : sm2.readReg64 (.gpr 26#5) + 3#64 ≠ 0#64 := by
    rw [hx26_2]
    intro h
    exact hw0_ne3 (by bv_omega)
  rw [initEntryPlaced_eq_blkPl] at hpc2
  apply sepWPp_step_to_lscro_vm_mem hinv2 (mid := initEntryPlaced + offEpilogue)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offErrAfterDealloc, offEpilogue] at hpc2 ⊢
    rw [initEntryPlaced_eq_blkPl]
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp3 _
  obtain ⟨evs, hInitEnv, hevsEq⟩ := hEnv evsDrop hfreeDrop
  have hrec344 :
      ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (fsp + 0x148#64) 0x150 ⊢
        memRegion (fsp + 0x140#64) 344 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [← ProofLib.memRegion_split' (b := fsp + 0x140#64) (n := 8) (k := 336)
          (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hloc := collapse_initLocals_placed fsp (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (opkId := opkId) (s0 := s0)
    0#64 8#64 0#64 0#8 0#8 hekLen
  refine sepWPp_conseq ?_
    (stage5_epilogue_placed_ok (B := B) hInitEnv StoresGhost.opened
      (.error (.protocol .invalidProtobufEncoding)) SpeHeap Extra
      hstk hstk64
      (by dsimp only [initEntryPlaced, offEpilogue]; wp_norm_goal; try rfl)
      (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm]; exact hsp2)
      hsp_align
      (by simp only [wp_norm, arm64_norm, hvregs_2])
      (by simp only [wp_norm, arm64_norm, hx19_2])
      (by simp only [wp_norm, arm64_norm, htr2])
      hfs0 hfs2'
      (fun _ => slotOut_err_of_some_none hans)
      (by
        simp only [wp_norm, arm64_norm, hx26_2, hx27_2, hx25_2, hx28_2, hx24_2, hx21_2]
        exact Entails.trans hspe
          (Entails.sepExists_right k (Entails.refl _)))
      hpost
      hevsEq)
  inImageKitClearInvHyps
  rw [← A.pool_of_vmPreserved hvmp3]
  s5_have_eq hperm1 :
      (((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (fsp + 0x148#64) 0x150) ∗
      ?remAfterRec := by
    conv => lhs; simp only [wp_norm, arm64_norm]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hperm1)
    (Entails.trans (sepConj_mono_left hrec344) ?_)
  s5_have_eq hperm2 :
      (memRegion fsp 0xd0 ∗
        initArgsAtPlaced fsp x s0 ∗
        ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗ ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
        memRegion (fsp + 0x140#64) 344 ∗
        (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
          memRegion (fsp + 0x2b8#64) 0x48 ∗
          ((fsp + 0x300#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((fsp + 0x304#64) ↦₃₂ opkId) ∗
          memRegion (fsp + 0x308#64) 0x40 ∗
          ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
          ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
          ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x438#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
          stage3OpkSlotAt fsp x.bundle ∗
          ((fsp + 0x459#64) ↦₈ 0#8) ∗
          memRegion (fsp + 0x45a#64) 6) ∗
        memRegion (fsp + 0x460#64) 344 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ∗ ?remFinal := by
    conv => lhs; simp only [opk8_truncate_eq]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hperm2)
    (Entails.trans (sepConj_mono_left hloc) ?_)
  exact Entails.of_eq (by s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
end
