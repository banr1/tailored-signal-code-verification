/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 PQXDH Step B2 (`[LibsignalPlacement]`, `+0x0968 → +0x0a70`: `DH3`)

Advances `+0x0968 → +0x0a70` across `DH3 = X25519(ekASk, spkB)` under `RustCliAllocBudget M`,
discharging the zero-DH unwind (`unwind1548Events`) and writing `F_X25519 ++ dh1 ++ dh2 ++ dh3`
(`len = 128`) at `secretsPtr` (`dh3StepOkEvents`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives initiateInput modelPrims toU8)
open CryptoVerification.E2E.Pqxdh.Initiator (F_X25519 bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore (and_ff32_hi56_3 and_ff_hi56_3 bytesToBv8_length extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (BundleV InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed initDef padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (AtStage3Placed InInitiatePlaced coinsCursorAtPlaced initProgPlaced stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas (append_bv8_at bundleEOf_props bytesToBv8_toU8_eq cells3_to_memRegion24 dh3_model_eq initDef_some_none_of_dh_bad lay32 memRegion_merge_at modelPrims_x25519_len pointsToBytes_entails_memRegion_len sepWPp_conseq_oom sep_replace toU8_length_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2PlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (Params)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved rustAllocEvents
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced calculateAgreement_cli_placed_ok pqxdhCalculateAgreementPlacedInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_in_vm_placed s3_block_to_call_vm_placed s3_dealloc_stack_placed s3_done_call_vm
   s3_done_in_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_memcpy_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced fitsEvents_s3CalcAgreeEvents_of_alloc32 s3CalcAgreeEvents s3_calc_agree_of_ok
   s3_dh_unwind_1544_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget
  (stepEvents_unwind1548Events unwind1548Events)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-- Allocator events along the non-zero `DH3` path (`+0x0968 → +0x0a70`). -/
def dh3StepOkEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustDeallocEvents 32 1

theorem stepEvents_dh3StepOkEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 32 1) (M.stepEvents (rustAllocEvents 32 1) st) =
      M.stepEvents dh3StepOkEvents st :=
  (M.stepEvents_append (rustAllocEvents 32 1) (rustDeallocEvents 32 1) st).symm

private theorem sec96_re_placed (secretsPtr : BitVec 64) (bs : SignalPqxdh.Bytes)
    (h96 : (bytesToBv8 bs).length = 96) :
    (secretsPtr ↦ₛ bytesToBv8 bs) ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
    memRegion secretsPtr 192 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion_len h96)) ?_
  rw [memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at secretsPtr 96 96 (secretsPtr + 96#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

private theorem s3_repack3_placed (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId : BitVec 32) :
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
       memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
       ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
       ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]
  rcases b.opk with _ | ⟨_, k⟩ <;>
    (simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
     sep_ac_rfl)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded `DH3` step (`+0x0968 → +0x0a70`) from a Block `207` witness. -/
theorem dh3_step_of_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCalc : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A lim)))
    (hFit : FitsEvents M lim st
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiatePlaced s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh3StepOkEvents st) sa ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, hspkLen, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  obtain ⟨halign_0, hx29_0, hfsp_0⟩ := hctrl.step_ctx fsp
  refine' s3_block_to_call_vm_placed hh
    (lsmpl.base 207)
    0x97c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
      sm.readReg64 .x8 = fsp + 0x1600#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 96#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + 0x968#64 := hctrl.pc; have hrun := hctrl.run
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx24 hx26
    by_vm_steps (
      wp_steps
      refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal,
         by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
         by wp_norm_goal,
         by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm]⟩
        (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
        (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
  · intro sm_c3 hvm_c3 hctrl_c3 hpcm_c3 hlrm_c3 htrm_c3
      ⟨hx0_c3, hx1_c3, hx8_c3, hx20_c3, hx21_c3, hx22_c3, hx26_c3⟩
    have hpool_c3 : A.pool lim st s = A.pool lim st sm_c3 :=
      (A.pool_transport lim st s sm_c3 hvm_c3).symm
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr_c3 : sm_c3.trace = s0.trace := htrm_c3.trans htr
    refine s3_calc_agree_of_ok (X := X) hh hCalc
      (fsp + 0x9a0#64) (toU8 ekASk)
      (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) st _
      hctrl_c3 htr_c3 hpcm_c3 hlrm_c3 hx0_c3 hx1_c3 (by rw [hctrl_c3.sp]; exact hx8_c3)
      (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hspkLen]) hFit hpanic
      (by (try dsimp only [stage3KeySlotsAt])
          rw [hpool_c3, hctrl_c3.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
          (try dsimp only [fsp]); sep_frame)
      ?_ ?_
    · intro hdh3_zero s_z3 hi u2 hctrl_z3 _ htr_z3
      rw [hctrl_c3.sp]
      obtain ⟨halign_z3, hx29_z3, hfsp_z3⟩ := hctrl_z3.step_ctx fsp
      refine' s3_block_in_vm_placed hh 0x1544
        (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
        hctrl_z3 ?_ ?_; rotate_left 1
      · have hpc : s_z3.pc = (blkPl_521).base + 0x97c#64 := hctrl_z3.pc; have hrun := hctrl_z3.run
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, speWord,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        (try dsimp only [fsp] at *); rw [← hctrl_z3.sp] at *
        by_vm_steps (
          wp_steps
          refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal, by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
      · intro sm_u3 hvm_u3 htr_u3 hctrl_u3 ⟨hx26_u3, hx1_u3⟩
        have hpool_u3 : A.pool lim st s_z3 = A.pool lim st sm_u3 :=
          (A.pool_transport lim st s_z3 sm_u3 hvm_u3).symm
        rw [hctrl_z3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have hdh3_mod :
            (modelPrims X ⟨W.C, W.Q⟩).x25519
              (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
              (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                (padCoins x.coins)).bundle.spkB =
            List.replicate 32 0 :=
          dh3_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk
            hs3.bundleEq hs3.ekPairEq.1 ▸ hdh3_zero
        have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
          x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
          (Or.inr (Or.inr (Or.inl hdh3_mod)))
        have h96 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2)).length = 96 := by
          rw [bytesToBv8_length, List.length_append, List.length_append,
            hdh1_len32, hdh2_len32]; decide
        exact s3_dh_unwind_1544_placed hh (hEnv hdh3_mod) hS hnone hstk hstk64 hekAPkLen hekASkLen
          hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u3
          (htr_u3.trans (htr_z3.trans htr_c3)) hx26_u3 hx1_u3 hpost hpanic
          (hi ++ 3#8) u2 96#64
          (sepConj_mono (sec96_re_placed secretsPtr (F_X25519 ++ dh1 ++ dh2) h96)
            (Entails.of_eq (s3_repack3_placed A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId)))
          (by rw [hpool_u3, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              (try dsimp only [fsp]); cases x.bundle.opk <;> (dsimp only; sep_frame))
    · intro hdh3_nz s_ok3 dh3Ptr hctrl_ok3 hcs_ok3 htr_ok3
      rw [hctrl_c3.sp]
      let st_a3 := M.stepEvents (rustAllocEvents 32 1) st
      have hx20_3 := hcs_ok3.2.1.trans hx20_c3; have hx21_3 := hcs_ok3.2.2.1.trans hx21_c3
      have hx22_3 := hcs_ok3.2.2.2.1.trans hx22_c3
      have hx26_3 := hcs_ok3.2.2.2.2.2.2.2.1.trans hx26_c3
      set dh3 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 ekASk)
        (toU8 x.bundle.spk.bytes.toList)
      have hdh3_len : (bytesToBv8 dh3).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
      obtain ⟨halign_3, hx29_3, hfsp_3⟩ := hctrl_ok3.step_ctx fsp
      refine' s3_block_to_call_vm_placed hh
        (lsρ memcpyName)
        0x9e4 (Φ := fun sm =>
          sm.readReg64 .x0 = secretsPtr + 96#64 ∧ sm.readReg64 .x1 = dh3Ptr ∧
          sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
          sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh3Ptr ∧
          sm.readReg64 (.gpr 26#5) = 96#64)
        hctrl_ok3 ?_ ?_; rotate_left 1
      · have hpc : s_ok3.pc = (blkPl_521).base + 0x97c#64 := hctrl_ok3.pc; have hrun := hctrl_ok3.run
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        (try dsimp only [fsp] at *); rw [← hctrl_ok3.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_3 hx21_3 hx22_3 hx26_3
        by_vm_steps (
          wp_steps
          refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
             by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
             by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
      · intro sm_mc3 hvm_mc3 hctrl_mc3 hpcm_mc3 hlrm_mc3 htrm_mc3
          ⟨hx0_mc3, hx1_mc3, hx2_mc3, hx20_mc3, hx21_mc3, hx22_mc3,
           hx24_mc3, hx25_mc3, hx26_mc3⟩
        have hpool_mc3 : A.pool lim st_a3 s_ok3 = A.pool lim st_a3 sm_mc3 :=
          (A.pool_transport lim st_a3 s_ok3 sm_mc3 hvm_mc3).symm
        rw [hctrl_ok3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        refine s3_memcpy_pool_placed hh (secretsPtr + 96#64) dh3Ptr (bytesToBv8 dh3) st_a3 _
          hctrl_mc3 (htrm_mc3.trans (htr_ok3.trans htr_c3)) hpcm_mc3 hlrm_mc3
          hx0_mc3 hx1_mc3 (by rw [hx2_mc3, hdh3_len]; decide) hpanic
          (by rw [hpool_mc3, hctrl_mc3.sp, hdh3_len]; (try dsimp only [fsp, st_a3]); sep_frame)
          ?_
        intro s_mc3 hctrl_mc3' hcs_mc3 _ htr_mc3
        rw [hctrl_mc3.sp]
        have hx20_m3 := hcs_mc3.2.1.trans hx20_mc3; have hx21_m3 := hcs_mc3.2.2.1.trans hx21_mc3
        have hx22_m3 := hcs_mc3.2.2.2.1.trans hx22_mc3
        have hx24_m3 := hcs_mc3.2.2.2.2.2.1.trans hx24_mc3
        have hx25_m3 := hcs_mc3.2.2.2.2.2.2.1.trans hx25_mc3
        have hx26_m3 := hcs_mc3.2.2.2.2.2.2.2.1.trans hx26_mc3
        obtain ⟨halign_m3, hx29_m3, hfsp_m3⟩ := hctrl_mc3'.step_ctx fsp
        refine' s3_block_to_call_vm_placed hh
          (lsρ lsRustDeallocSymCli)
          0x9fc (Φ := fun sm =>
            sm.readReg64 .x0 = dh3Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_mc3' ?_ ?_; rotate_left 1
        · have hpc : s_mc3.pc = (blkPl_521).base + 0x9e4#64 := hctrl_mc3'.pc; have hrun := hctrl_mc3'.run
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          (try dsimp only [fsp] at *); rw [← hctrl_mc3'.sp] at *
          try simp only [arm64_norm, wp_norm]
            at hx20_m3 hx21_m3 hx22_m3 hx24_m3 hx25_m3 hx26_m3
          by_vm_steps (
            wp_steps
            refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
               by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
               by wp_norm_goal,
               by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
               by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
               by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
               by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm]⟩
              (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
              (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
        · intro sm_da3 hvm_da3 hctrl_da3 hpcm_da3 hlrm_da3 htrm_da3
            ⟨hx0_da3, hx1_da3, hx2_da3, hx20_da3, hx21_da3, hx22_da3, hx26_da3⟩
          have hpool_da3 : A.pool lim st_a3 s_mc3 = A.pool lim st_a3 sm_da3 :=
            (A.pool_transport lim st_a3 s_mc3 sm_da3 hvm_da3).symm
          rw [hctrl_mc3'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine s3_dealloc_stack_placed hh dh3Ptr 32 st_a3 _ hctrl_da3
            hpcm_da3 hlrm_da3 hx0_da3 (by rw [hx1_da3]; decide) (by rw [hx2_da3]; decide)
            lay32
            (by rw [hpool_da3, hctrl_da3.sp]
                exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh3Ptr) hdh3_len)
                  (by (try dsimp only [fsp, st_a3]); sep_frame)
                  (by (try dsimp only [fsp, st_a3]); sep_frame))
            ?_
          intro s_d3 hctrl_d3 hcs_d3 htr_d3
          rw [hctrl_da3.sp]
          have hx20_d3 := hcs_d3.2.1.trans hx20_da3; have hx21_d3 := hcs_d3.2.2.1.trans hx21_da3
          have hx22_d3 := hcs_d3.2.2.2.1.trans hx22_da3
          have hx26_d3 := hcs_d3.2.2.2.2.2.2.2.1.trans hx26_da3
          refine' s3_block_in_vm_placed hh 0xa70 (Φ := fun sm =>
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64) hctrl_d3 ?_ ?_; rotate_left 1
          · have hpc : s_d3.pc = (blkPl_521).base + 0x9fc#64 := hctrl_d3.pc; have hrun := hctrl_d3.run
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            (try dsimp only [fsp] at *); rw [← hctrl_d3.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_d3 hx21_d3 hx22_d3 hx26_d3
            by_vm_steps (
              wp_steps
              refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
                 by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
                 by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
                 by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm]⟩
                (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
          · intro sa hvm_a htr_a hctrl_a ⟨hx20_a, hx21_a, hx22_a, hx26_a⟩
            have hpool_a :
                A.pool lim (M.stepEvents (rustDeallocEvents 32 1) st_a3) s_d3 =
                  A.pool lim (M.stepEvents dh3StepOkEvents st) sa := by
              dsimp only [st_a3]
              rw [stepEvents_dh3StepOkEvents]
              exact (A.pool_transport lim (M.stepEvents dh3StepOkEvents st) s_d3 sa hvm_a).symm
            rw [hctrl_d3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have hdh3_eq := dh3_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk
              hs3.bundleEq hs3.ekPairEq.1
            have htr_fin : sa.trace = s0.trace :=
              htr_a.trans (htr_d3.trans (htrm_da3.trans
                (htr_mc3.trans (htrm_mc3.trans (htr_ok3.trans htr_c3)))))
            have hsret3 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh3Ptr 32#64
            have happ3 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2) dh3 96#64
              (by rw [List.length_append, List.length_append, hdh1_len32, hdh2_len32]; rfl)
            refine sepWPp_conseq_oom ?_
              (hnext sa dh3 hdh3_eq hdh3_nz hctrl_a htr_fin hx20_a hx21_a hx22_a hx26_a)
            rw [hpool_a, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            exact sep_replace
              (sepConj_mono hsret3 (sepConj_mono
                (Entails.of_eq (s3_repack3_placed A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId))
                (Entails.of_eq happ3)))
              (by (try dsimp only [fsp]); cases x.bundle.opk <;> dsimp only <;> sep_frame)
              (by (try dsimp only [fsp]); sep_frame)

theorem dh3_step_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiatePlaced s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh3StepOkEvents st) sa ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  dh3_step_of_ok hh (hLocal.calculateAgreement X) hFit hEnv hS hstk hstk64 hs3 hpost hpanic
    hdh1_len32 hdh2_len32 hsecNonNull hctrl htr hx20 hx21 hx22 hx24 hx26 hnext

theorem dh3_step_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim st
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents 192 1) st) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiatePlaced s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh3StepOkEvents st) sa ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  dh3_step_of_ok hh (calculateAgreement_cli_placed_ok mmpl gh W hh X) hFit hEnv hS hstk hstk64 hs3
    hpost hpanic hdh1_len32 hdh2_len32 hsecNonNull hctrl htr hx20 hx21 hx22 hx24 hx26 hnext

theorem dh3_step_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim (M.stepEvents evs_pre st0) (rustAllocEvents 32 1))
    (hEnv :
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0 →
      InitEnv x (evs_pre ++ unwind1548Events))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiatePlaced s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sa
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (evs_pre ++ dh3StepOkEvents) st0) sa ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool lim (M.stepEvents evs_pre st0) s ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  refine dh3_step_placed_ok hh hLocal (fitsEvents_s3CalcAgreeEvents_of_alloc32 hFit)
    (fun hzero => ⟨evs_pre ++ unwind1548Events, hEnv hzero,
      (stepEvents_unwind1548Events M (M.stepEvents evs_pre st0)).trans
        (M.stepEvents_append evs_pre unwind1548Events st0).symm⟩)
    hS hstk hstk64 hs3 hpost hpanic hdh1_len32 hdh2_len32 hsecNonNull hctrl htr
    hx20 hx21 hx22 hx24 hx26 fun sa dh3 hdh3 hnz hc ha hx20' hx21' hx22' hx26' => ?_
  rw [← M.stepEvents_append evs_pre dh3StepOkEvents st0]
  exact hnext sa dh3 hdh3 hnz hc ha hx20' hx21' hx22' hx26'

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2PlacedBudget
