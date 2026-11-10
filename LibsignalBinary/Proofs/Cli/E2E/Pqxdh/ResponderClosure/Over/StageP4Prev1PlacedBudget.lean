/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1MarkPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1RemovePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveIdPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefused
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNone
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProof
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P4 Over-Path Top-Level Specification (`previous_sessions = [enc]`)

Proves budget-threaded `[LibsignalPlacement]` Stage P4 (`+0x34dc → s0.readReg64 .x30`) over
`opkId? = none`, `opkId? = some opkId`, and unified `opkId? : Option (BitVec 32)` when
`coroPtr + 0xe0` holds a 1-element `prevVecAt [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
  PreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4_markKyber_none_dispatch_vregs_mark_placed
  stageP4_markKyber_none_dispatch_vregs_kits_placed
  stageP4_markKyber_some_dispatch_vregs_mark_placed
  stageP4_markKyber_some_dispatch_vregs_kits_placed
  stageP4RemovePreKeySharedPlaced stageP4RemovePreKeyPrePlaced
  stageP4RemovePreKeyOkPostPlaced stageP4RemovePreKeyErrPostPlaced
  PreKeyRemoveKitPlacedOk preKeyRemoveKitPlacedOk_of_store
  stageP4_removePreKey_some_dispatch_vregs_remove_placed
  stageP4_removePreKey_some_dispatch_vregs_kits_placed
  stageP4StoreSessionSharedPlaced stageP4StoreSessionPrePlaced
  stageP4StoreSessionOkPostPlaced stageP4StoreSessionErrPostPlaced
  stageP4_storeSession_dispatch_vregs_kits_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced
  stageP4At3ccPrePlaced stageP4_at_3cc_vregs_kits_placed
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  StorePrev1Ops prevVecAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget (
  StageP4KyberRefusedMarkErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  KyberPreKeyMarkKitPlacedOk MarkStepEnv StageP4MarkErrEnv kyberPreKeyMarkKitPlacedOk_of_store
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget (
  StageP4RemoveBranchErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  PreKeyRemoveKitPlacedOk RemoveStepEnv StageP4RemoveErrEnv preKeyRemoveKitPlacedOk_of_store
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedSaveErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrPlacedBudget (
  dpClosureEntryP34Placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1BranchPlaced StageP4Prev1ExitEnv StageP4Prev1NoneExitEnv StageP4Prev1NoneStepEnv
  StageP4Prev1RawBranchPlaced StageP4Prev1StepEnv StageP4Prev1StoreBranchEnv
  fitsEnv_prev1NoneStep_of_noneExit fitsEnv_prev1Step_of_exit
  stageP4At3ccPrev1PrePlaced stageP4Prev1ExitAtPlaced stageP4Prev1PrePlaced
  stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
  stageP4_at_3cc_prev1_vregs_kits_p4_placed stageP4_at_3cc_prev1_vregs_kits_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1MarkPlacedBudget (
  stageP4MarkKyberPrev1ErrPostPlaced stageP4MarkKyberPrev1OkPostPlaced
  stageP4MarkKyberPrev1PrePlaced stageP4MarkKyberPrev1SharedPlaced
  stageP4_markKyber_none_prev1_vregs_mark_p4_placed
  stageP4_markKyber_some_prev1_vregs_mark_p4_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1RemovePlacedBudget (
  stageP4RemovePreKeyPrev1ErrPostPlaced stageP4RemovePreKeyPrev1OkPostPlaced
  stageP4RemovePreKeyPrev1PrePlaced stageP4RemovePreKeyPrev1SharedPlaced
  stageP4_removePreKey_some_prev1_vregs_remove_p4_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveIdPlacedBudget (
  stageP4SaveIdPrev1ErrPostPlaced stageP4SaveIdPrev1OkPostPlaced
  stageP4SaveIdPrev1PrePlaced stageP4SaveIdPrev1SharedPlaced
  stageP4_saveIdentity_prev1_vregs_kits_p4_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  SessionPrev1KitPlacedOkSE StageP4StorePrev1ExitEnv StorePrev1BudgetEnv StorePrev1StepEnv
)

private theorem sepConj_assoc5_prev1_pl (a b c d e f : SepProp) :
    (a ∗ b ∗ c ∗ d ∗ e) ∗ f = a ∗ b ∗ c ∗ d ∗ e ∗ f := by
  simp only [sepConj_assoc]

/-! ## Budget-Threaded Placed Stage P4 (`opkId? = none`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Stage P4 (`opkId? = none`, `+0x34dc → s0.readReg64 .x30`) over a
1-element `prevVecAt [enc]` under `StageP4Prev1NoneStepEnv`. -/
theorem stageP4_none_prev1_vregs_mark_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1NoneStepEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrev1PrePlaced A lim st0 ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
      remoteIkPtr idStorePtr kyberStorePtr kpkKit.kpk_vt prevCap prevPtr ptCap ptPtr v_3d0
      0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
        stageP4SaveIdPrev1PrePlaced stageP4SaveIdPrev1SharedPlaced
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_prev1_vregs_kits_p4_placed ext ikit ikitEnv hdealloc hDropSS3
    hikit hiVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (0#64 + kpkKit.markShimOff) prevCap prevPtr ptCap ptPtr v_3d0
    0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state _ _
    haddr_id hfits.seq_left (by decide) hpt_le hsp_save
    (fun hro' hP' => hkVt.markSlot hro' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c evs1 s1 P1 hevs1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hcro1 hvregs1 hP1 => ?_)
    (fun evs1 sf Pf hevs1 hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  ·
    let st1 := M.stepEvents evs1 st0
    have hfits_after1 := hfits.seq_right hevs1
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrev1PrePlaced A lim st1 kpkKit s0 s1 coroPtr msgPtr outPtr
        kyberStorePtr prevCap prevPtr ptCap ptPtr b_2c0 pt enc baseKey kst0 G ss.state ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdPrev1OkPostPlaced stageP4SaveIdPrev1SharedPlaced; sep_focus)
      (by
        unfold stageP4MarkKyberPrev1PrePlaced stageP4MarkKyberPrev1SharedPlaced
        rw [hsp1]
        sep_focus)
      ?_
    rw [sepConj_assoc]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_none_prev1_vregs_mark_p4_placed ext kpkKit kpkKitEnv
      hdealloc hDropSS3 hkpkKit hkVt
      st1 s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevCap prevPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt enc baseKey kst0 G ss.state _ _
      hmark_ok hfits_after1.seq_left hpt_le hsp_mark
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hcro1 hpc1 hrun1 hsp1_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun evs2 s2 P2 hevs2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx19_2 hx24_2 hx25_2 hx26_2 hx27_2 _
        hcro2 hvregs2 hP2 => ?_)
      (fun e evs2 sf Pf hevs2 hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    ·
      let st2 := M.stepEvents evs2 st1
      have hfits_store := hfits_after1.seq_right hevs2
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      have hto3cc :
          P2 ⊢ markKyberVtablesAt kpkKit ∗
            stageP4At3ccPrev1PrePlaced A lim st2 kit ikit pkKit kpkKit s0 s s2 coroPtr msgPtr outPtr
              remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
              prevCap prevPtr ptCap ptPtr v_3d0
              (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
              kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
              sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
        refine Entails.trans hP2
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4MarkKyberPrev1OkPostPlaced stageP4MarkKyberPrev1SharedPlaced
              rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
              sep_focus)
            (by
              unfold stageP4At3ccPrev1PrePlaced stageP4Prev1SharedPlaced
              rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
              sep_ac_rfl))
      refine SepWPp.drop_pre_of_entails hto3cc ?_
      refine stageP4_at_3cc_prev1_vregs_kits_p4_placed ext kit ops opsEnv ikit pkKit kpkKit
        hdealloc hDropSS3 hkit hsVt st2 s0 s s2
        coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
        hExtra hrec_ok haddr_ss hfits_store hpt_le hcap_lt hptr_nz hsp_ub
        (hfs2.mono (fun _ h => h.1) id)
        hcro2 hpc2 hrun2 hsp2 hsp_align
        hx19_2 (hsp1 ▸ hx24_2) (hsp1 ▸ hx25_2) hx26_2 hx27_2 hvregs2
        (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
        (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
      · have hst_eq : M.stepEvents evs4 st2 = M.stepEvents (evs1 ++ (evs2 ++ evs4)) st0 := by
          dsimp only [st2, st1]
          simp only [AllocCostModel.stepEvents_append]
        exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
          hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hcrof,
          .ok c (evs1 ++ (evs2 ++ evs4))
            (SeqEnv.append hevs1 (SeqEnv.append hevs2 hevs4))
            hrel1 hrel2 trivial hrel4
            (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
            (hst_eq ▸ hPf)⟩
      · have hst_eq : M.stepEvents evs4 st2 = M.stepEvents (evs1 ++ (evs2 ++ evs4)) st0 := by
          dsimp only [st2, st1]
          simp only [AllocCostModel.stepEvents_append]
        exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
          hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hcrof,
          .storeErr c (evs1 ++ (evs2 ++ evs4))
            (SeqEnv.append hevs1 (SeqEnv.append hevs2 hevs4))
            hrel1 hrel2 trivial hrel4
            (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
            (hst_eq ▸ hPf)⟩
    ·
      have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st0 :=
        (M.stepEvents_append evs1 evs2 st0).symm
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs1 ++ evs2) st0) kit ikit pkKit kpkKit
          s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
          preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .markErr c e (evs1 ++ evs2) (SeqEnv.append hevs1 hevs2) hrel1 hrel2
          (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberPrev1ErrPostPlaced stageP4MarkKyberPrev1SharedPlaced
            rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
            sep_focus)
          (by
            unfold stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
            rw [hst_eq, stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            sep_ac_rfl))
  ·
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)),
      stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs1 st0) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr evs1 hevs1 hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdPrev1ErrPostPlaced stageP4SaveIdPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl

theorem stageP4_none_prev1_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1NoneStepEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp :=
  stageP4_none_prev1_vregs_mark_placed_ok ext kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt
    (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr
    remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap
    prevPtr ptCap ptPtr v_3d0 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk
    baseKey sst0 ist0 pst0 kst0 G ss hExtra hrec_ok haddr_ss haddr_id hmark_ok hfits hpt_le
    hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs

abbrev stageP4_none_prev1_vregs_kits_dealloc_placed_ok := @stageP4_none_prev1_vregs_kits_placed_ok
abbrev stageP4_none_prev1_vregs_kits_p4_placed := @stageP4_none_prev1_vregs_kits_placed_ok

/-! ## Budget-Threaded Placed Stage P4 (`opkId? = some opkId`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Stage P4 (`opkId? = some opkId`, `+0x34dc → s0.readReg64 .x30`) over a
1-element `prevVecAt [enc]` under `StageP4Prev1StepEnv`. -/
theorem stageP4_some_prev1_vregs_mark_remove_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyRemoveKitPlacedOk A lim pkKit pkKitEnv ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1StepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 (some opkId) peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_rem : removePreKeyCallStack pkKit ≤ 2 ^ 64 :=
    Nat.le_trans (removePreKeyStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrev1PrePlaced A lim st0 ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
      remoteIkPtr idStorePtr kyberStorePtr kpkKit.kpk_vt prevCap prevPtr ptCap ptPtr v_3d0
      1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
        stageP4SaveIdPrev1PrePlaced stageP4SaveIdPrev1SharedPlaced
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_prev1_vregs_kits_p4_placed ext ikit ikitEnv hdealloc hDropSS3
    hikit hiVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (0#64 + kpkKit.markShimOff) prevCap prevPtr ptCap ptPtr v_3d0
    1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state _ _
    haddr_id hfits.seq_left (by decide) hpt_le hsp_save
    (fun hro' hP' => hkVt.markSlot hro' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c evs1 s1 P1 hevs1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hcro1 hvregs1 hP1 => ?_)
    (fun evs1 sf Pf hevs1 hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  ·
    let st1 := M.stepEvents evs1 st0
    have hfits_after1 := hfits.seq_right hevs1
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrev1PrePlaced A lim st1 kpkKit s0 s1 coroPtr msgPtr outPtr
        kyberStorePtr prevCap prevPtr ptCap ptPtr b_2c0 pt enc baseKey kst0 G ss.state ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdPrev1OkPostPlaced stageP4SaveIdPrev1SharedPlaced; sep_focus)
      (by
        unfold stageP4MarkKyberPrev1PrePlaced stageP4MarkKyberPrev1SharedPlaced
        rw [hsp1]
        sep_focus)
      ?_
    rw [sepConj_assoc5_prev1_pl]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_some_prev1_vregs_mark_p4_placed ext kpkKit kpkKitEnv
      hdealloc hDropSS3 hkpkKit hkVt
      st1 s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr pkKit.pk_vt
      (0#64 + pkKit.removeShimOff) prevCap prevPtr ptCap ptPtr
      opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc baseKey kst0 G ss.state _ _
      hmark_ok hfits_after1.seq_left hpt_le hsp_mark
      (fun hro' hP' => hpVt.removeSlot hro' hP')
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hcro1 hpc1 hrun1 hsp1_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun evs2 s2 P2 hevs2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx0_2 hx1_2 hx19_2 hx24_2 hx25_2
        hx26_2 hx27_2 _ hlr2 hcro2 hvregs2 hP2 => ?_)
      (fun e evs2 sf Pf hevs2 hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    ·
      let st2 := M.stepEvents evs2 st1
      have hfits_after2 := hfits_after1.seq_right hevs2
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      refine SepWPp.drop_swap_focus_pre
        (Drop := markKyberVtablesAt kpkKit ∗
          ((pkKit.pk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + pkKit.removeShimOff)))
        (T := stageP4RemovePreKeyPrev1PrePlaced A lim st2 pkKit s0 s2 coroPtr outPtr preKeyStorePtr
          prevCap prevPtr ptCap ptPtr b_2c0 pt enc pst0 G ss.state)
        hP2
        ((stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
          (stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub))
        (by
          unfold stageP4MarkKyberPrev1OkPostPlaced stageP4MarkKyberPrev1SharedPlaced
          rw [hsp1]
          sep_focus)
        (by
          unfold stageP4RemovePreKeyPrev1PrePlaced stageP4RemovePreKeyPrev1SharedPlaced
          rw [hsp2]
          sep_focus)
        ?_
      refine stageP4_removePreKey_some_prev1_vregs_remove_p4_placed ext pkKit pkKitEnv
        hdealloc hDropSS3 hpkKit hpVt
        st2 s0 s2 coroPtr ctxPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr opkId
        b_2c0 pt enc pst0 G ss.state _ _
        hrem_ok hfits_after2.seq_left hpt_le hsp_rem
        (hfs2.mono (fun _ h => h.2.2.1) id)
        hcro2 hpc2 hrun2 hsp2_align
        hx0_2 hx1_2 hx19_2 (hsp2.symm ▸ hsp1 ▸ hx24_2) (hsp2.symm ▸ hsp1 ▸ hx25_2)
        hx26_2 hx27_2 hlr2 hvregs2
        (fun evs3 s3 P3 hevs3 hst3 hrel3 hpc3 hrun3 hsp3_2 htr3 hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 _
          hvregs3 hcro3 hP3 => ?_)
        (fun e evs3 sf Pf hevs3 hst3 hrel3 _ _ hspf htr3 hcsf hvregsf hcrof hPf => ?_)
      ·
        let st3 := M.stepEvents evs3 st2
        have hfits_store := hfits_after2.seq_right hevs3
        have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
        have hfs3 := hfs2.of_steps hst3 htr3 (fun hQ => hQ.2.2.1.2 opkId (.ok ()))
        have hto3cc :
            P3 ⊢ removePreKeyVtablesAt pkKit ∗
              stageP4At3ccPrev1PrePlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr
                outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
                kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
                (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
                kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
                sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
                (pkKit.removeUpdate pst0 opkId (.ok ()))
                (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
          refine Entails.trans hP3
            (Entails.replace_factor
              (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
                kyberPreKeyId signedPreKeyId)
              (by
                unfold stageP4RemovePreKeyPrev1OkPostPlaced stageP4RemovePreKeyPrev1SharedPlaced
                rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
                sep_focus)
              (by
                unfold stageP4At3ccPrev1PrePlaced stageP4Prev1SharedPlaced
                rw [stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
                sep_ac_rfl))
        refine SepWPp.drop_pre_of_entails hto3cc ?_
        refine stageP4_at_3cc_prev1_vregs_kits_p4_placed ext kit ops opsEnv ikit pkKit kpkKit
          hdealloc hDropSS3 hkit hsVt st3 s0 s s3
          coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
          preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
          (pkKit.removeUpdate pst0 opkId (.ok ()))
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
          hExtra hrec_ok haddr_ss hfits_store hpt_le hcap_lt hptr_nz hsp_ub
          (hfs3.mono (fun _ h => h.1) id)
          hcro3 hpc3 hrun3 hsp3 hsp_align
          hx19_3 (hsp2 ▸ hx24_3) (hsp2 ▸ hx25_3) hx26_3 hx27_3 hvregs3
          (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
          (fun evs4 sf Pf hevs4 hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf => ?_)
        · have hst_eq :
              M.stepEvents evs4 st3 =
              M.stepEvents (evs1 ++ (evs2 ++ (evs3 ++ evs4))) st0 := by
            dsimp only [st3, st2, st1]
            simp only [AllocCostModel.stepEvents_append]
          exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hcrof,
            .ok c (evs1 ++ (evs2 ++ (evs3 ++ evs4)))
              (SeqEnv.append hevs1 (SeqEnv.append hevs2 (SeqEnv.append hevs3 hevs4)))
              hrel1 hrel2 hrel3 hrel4
              (by simp only [htr4, htr3, htr2, htr1, List.append_assoc])
              (hst_eq ▸ hPf)⟩
        · have hst_eq :
              M.stepEvents evs4 st3 =
              M.stepEvents (evs1 ++ (evs2 ++ (evs3 ++ evs4))) st0 := by
            dsimp only [st3, st2, st1]
            simp only [AllocCostModel.stepEvents_append]
          exact ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hcrof,
            .storeErr c (evs1 ++ (evs2 ++ (evs3 ++ evs4)))
              (SeqEnv.append hevs1 (SeqEnv.append hevs2 (SeqEnv.append hevs3 hevs4)))
              hrel1 hrel2 hrel3 hrel4
              (by simp only [htr4, htr3, htr2, htr1, List.append_assoc])
              (hst_eq ▸ hPf)⟩
      ·
        have hst_eq : M.stepEvents evs3 st2 = M.stepEvents (evs1 ++ (evs2 ++ evs3)) st0 := by
          dsimp only [st2, st1]
          simp only [AllocCostModel.stepEvents_append]
        refine ⟨removePreKeyVtablesAt pkKit,
          stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs1 ++ (evs2 ++ evs3)) st0) kit ikit pkKit
            kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
            preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
            (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
            (speErrAt pkKit.removeErr outPtr e)
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
            sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
            (pkKit.removeUpdate pst0 opkId (.error e))
            (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())),
          ?_, hst1.trans (hst2.trans hst3), by rw [hspf, hsp2], hcsf, hvregsf, hcrof,
          .removeErr opkId c e (evs1 ++ (evs2 ++ evs3)) rfl
            (SeqEnv.append hevs1 (SeqEnv.append hevs2 hevs3))
            hrel1 hrel2 hrel3
            (by simp only [htr3, htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
        refine Entails.trans hPf
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4RemovePreKeyPrev1ErrPostPlaced stageP4RemovePreKeyPrev1SharedPlaced
              rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
              sep_focus)
            (by
              unfold stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
              rw [hst_eq, stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
              sep_ac_rfl))
    ·
      have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st0 :=
        (M.stepEvents_append evs1 evs2 st0).symm
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs1 ++ evs2) st0) kit ikit pkKit kpkKit
          s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
          preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .markErr c e (evs1 ++ evs2) (SeqEnv.append hevs1 hevs2) hrel1 hrel2
          (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberPrev1ErrPostPlaced stageP4MarkKyberPrev1SharedPlaced
            rw [hsp1, coro298_split_eq coroPtr 1#32 opkId]
            sep_focus)
          (by
            unfold stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
            rw [hst_eq, stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            sep_ac_rfl))
  ·
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)),
      stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs1 st0) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr evs1 hevs1 hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdPrev1ErrPostPlaced stageP4SaveIdPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl

theorem stageP4_some_prev1_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyStoreKitPlacedOk A lim pkKit pkKitEnv ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1StepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 (some opkId) peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp :=
  stageP4_some_prev1_vregs_mark_remove_placed_ok ext kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt
    (preKeyRemoveKitPlacedOk_of_store hpkKit) hpVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit)
    hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId kyberPreKeyId
    signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hfits hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs

abbrev stageP4_some_prev1_vregs_kits_dealloc_placed_ok := @stageP4_some_prev1_vregs_kits_placed_ok
abbrev stageP4_some_prev1_vregs_kits_p4_placed := @stageP4_some_prev1_vregs_kits_placed_ok

/-! ## Unified Budget-Threaded Placed Stage P4 (`opkId? : Option (BitVec 32)`) -/

/-- Unified budget-threaded placed Stage P4 (`+0x34dc → s0.readReg64 .x30`) over
`opkId? : Option (BitVec 32)` and a 1-element `prevVecAt [enc]`, delivering `StageP4Prev1BranchPlaced`. -/
theorem stageP4_prev1_vregs_mark_remove_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyRemoveKitPlacedOk A lim pkKit pkKitEnv ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1StepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1PrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
        peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1BranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkId?
          kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp := by
  cases opkId? with
  | none =>
    unfold stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced coroOpkIdAtP4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun opkIdDummy => ?_
    refine SepWPp.mono_post_panic ?_ (fun _ _ h => h)
      (stageP4_none_prev1_vregs_mark_placed_ok ext kit ops opsEnv ikit ikitEnv
        pkKit pkKitEnv kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt hkpkKit hkVt
        st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkIdDummy kyberPreKeyId
        signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
        hExtra hrec_ok haddr_ss haddr_id hmark_ok hfits hpt_le hcap_lt hptr_nz
        hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
    rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩
    exact ⟨hst, hspf, hcsf, hvregsf, hcrof,
      hbr.mono_opkSlot
        (by unfold coroOpkIdAtP4; exact Entails.sepExists_right opkIdDummy (Entails.refl _))⟩
  | some opkId =>
    exact stageP4_some_prev1_vregs_mark_remove_placed_ok ext kit ops opsEnv ikit ikitEnv
      pkKit pkKitEnv kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt hpkKit hpVt
      hkpkKit hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
      idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId kyberPreKeyId
      signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
      hExtra hrec_ok haddr_ss haddr_id hmark_ok (hrem_ok opkId rfl) hfits
      hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_prev1_vregs_kits_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64) (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyStoreKitPlacedOk A lim pkKit pkKitEnv ext)
    (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkKitEnv ext)
    (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hfits : FitsEnv M lim st0
      (StageP4Prev1StepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey
        G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4Prev1PrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
        peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4Prev1BranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
          kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
          idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkId?
          kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      Qp :=
  stageP4_prev1_vregs_mark_remove_placed_ok ext kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv hdealloc hDropSS3 hkit hsVt hikit hiVt
    (preKeyRemoveKitPlacedOk_of_store hpkKit) hpVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit)
    hkVt st0 s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
    signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hfits hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align hx19 hx24 hx25 hx26 hx27 hx28 hvregs

abbrev stageP4_prev1_vregs_kits_dealloc_placed_ok := @stageP4_prev1_vregs_kits_placed_ok
abbrev stageP4_prev1_vregs_kits_p4_placed := @stageP4_prev1_vregs_kits_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1PlacedBudget
