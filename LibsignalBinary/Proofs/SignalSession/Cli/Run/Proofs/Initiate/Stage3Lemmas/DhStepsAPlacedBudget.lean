/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 PQXDH Step A (`[LibsignalPlacement]`, `+0x0760 → +0x0858`: `secrets` Alloc + `DH1`)

Advances `+0x0760 → +0x0858` under `RustCliAllocBudget M` across `__rust_alloc(192, 1)` and
`DH1 = X25519(ikASk, spkB)` (Block `207`), handling the all-zero `DH1` unwind (`dh1UnwindEvents`)
and writing `F_X25519 ++ dh1` (`len = 64`, `cap = 192`) at `secretsPtr` (`dh1OkEvents`).
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

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsAPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding
  pqxdhCalculateAgreementPlacedBaseSpec pqxdhCalculateAgreementPlacedFrozenSpec
  PqxdhCalculateAgreementPlacedOk PqxdhCalculateAgreementPlacedFrozenOk
  pqxdhCalculateAgreement_placed_ok
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced InitLocalCalleesPlaced initLocalCallees_placed_ok
  pqxdhCalculateAgreementPlacedInnerSpec stage2MemPlaced stage3MemPlaced stage4MemPlaced
  stage5MemPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas hiding
  fp_eq_fsp_add_placed fp_slot_30_placed fp_slot_28_placed fp_slot_20_placed
  fp_slot_50_placed fp_slot_48_placed fp_slot_40_placed fp_slot_38_placed
  S3InvPrefixPlaced Unwind1548MemPlaced fsp_eq_sp_placed unwind_1548_placed_ok
  unwind_1544_placed_ok s3_calc_agree_placed s3_dh_collapse_common_placed s3_dh_unwind_1544_placed
  s3_call_placed s3_call_alloc_placed dh1_step_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage3MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced calculateAgreement_cli_placed_ok pqxdhCalculateAgreementPlacedInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_in_vm_placed s3_block_to_call_vm_placed s3_dealloc_stack_placed s3_done_call_vm
   s3_done_in_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (rustLay192 s3_call_alloc_placed s3_memcpy_pool_placed s3_shim_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced fitsEvents_s3CalcAgreeEvents_of_alloc32 fitsEvents_s3CalcAgreeEvents_of_zero
   s3CalcAgreeEvents s3_calc_agree_of_ok s3_dh_collapse_common_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlacedBudget
  (Unwind1548MemPlaced stepEvents_unwind1548Events unwind1548Events unwind_1548_placed_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## `AllocEvent` Sequences -/

/-- Allocator events for one non-zero `calculate_agreement` + `dealloc` step (`32` B). -/
def dhStepOkEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustDeallocEvents 32 1

/-- Allocator events along `+0x0760 → +0x0858` on non-zero `DH1`. -/
def dh1OkEvents : List AllocEvent :=
  rustAllocEvents 192 1 ++ dhStepOkEvents

/-- Allocator events along `+0x0760 → +0x1548 → ret` when `DH1` is all-zero. -/
def dh1UnwindEvents : List AllocEvent :=
  rustAllocEvents 192 1 ++ unwind1548Events

theorem stepEvents_dhStepOkEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 32 1) (M.stepEvents (rustAllocEvents 32 1) st) =
      M.stepEvents dhStepOkEvents st :=
  (M.stepEvents_append (rustAllocEvents 32 1) (rustDeallocEvents 32 1) st).symm

theorem stepEvents_dh1OkEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 32 1)
      (M.stepEvents (rustAllocEvents 32 1) (M.stepEvents (rustAllocEvents 192 1) st)) =
      M.stepEvents dh1OkEvents st :=
  (stepEvents_dhStepOkEvents M (M.stepEvents (rustAllocEvents 192 1) st)).trans
    (M.stepEvents_append (rustAllocEvents 192 1) dhStepOkEvents st).symm

theorem stepEvents_dh1UnwindEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 1568 1)
      (M.stepEvents (rustDeallocEvents 192 1) (M.stepEvents (rustAllocEvents 192 1) st)) =
      M.stepEvents dh1UnwindEvents st :=
  (stepEvents_unwind1548Events M (M.stepEvents (rustAllocEvents 192 1) st)).trans
    (M.stepEvents_append (rustAllocEvents 192 1) unwind1548Events st).symm

theorem fitsEvents_dh1_of_okEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {ourSk theirPk : SignalPqxdh.Bytes}
    (hFit : FitsEvents M lim st dh1OkEvents) :
    FitsEvents M lim st (rustAllocEvents 192 1) ∧
      FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
        (s3CalcAgreeEvents X W ourSk theirPk) := by
  have ⟨h192, hRest⟩ := (fitsEvents_append M lim (rustAllocEvents 192 1) dhStepOkEvents st).mp hFit
  have ⟨h32, _⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 32 1) (rustDeallocEvents 32 1)
      (M.stepEvents (rustAllocEvents 192 1) st)).mp hRest
  exact ⟨h192, fitsEvents_s3CalcAgreeEvents_of_alloc32 h32⟩

theorem fitsEvents_dh1_of_unwindEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {ourSk theirPk : SignalPqxdh.Bytes}
    (hZero : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk = List.replicate 32 0)
    (hFit : FitsEvents M lim st dh1UnwindEvents) :
    FitsEvents M lim st (rustAllocEvents 192 1) ∧
      FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
        (s3CalcAgreeEvents X W ourSk theirPk) :=
  ⟨((fitsEvents_append M lim (rustAllocEvents 192 1) unwind1548Events st).mp hFit).1,
   fitsEvents_s3CalcAgreeEvents_of_zero hZero⟩

/-! ## Spatial Split and Repack Helpers -/

private theorem s3_loc_split_placed (fsp : BitVec 64) :
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
      memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x48 ∗
      memRegion (fsp + 0x9a0#64) 0x20 ∗ memRegion (fsp + 0x9c0#64) 0xc40 ∗
      memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
      memRegion (fsp + 0x1c60#64) 8 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
      memRegion (fsp + 0x1c70#64) 8 ∗ memRegion (fsp + 0x1c78#64) 0x18 := by
  simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
  rw [← memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 0x1360 (fsp + 0x930#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x930#64) 8 0x1358 (fsp + 0x938#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x938#64) 0x20 0x1338 (fsp + 0x958#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x958#64) 0x48 0x12f0 (fsp + 0x9a0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12d0 (fsp + 0x9c0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x690 (fsp + 0x1600#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1600#64) 24 0x678 (fsp + 0x1618#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1618#64) 0x648 0x30 (fsp + 0x1c60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c60#64) 8 0x28 (fsp + 0x1c68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c68#64) 8 0x20 (fsp + 0x1c70#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]

private theorem s3_sec_split_placed (secretsPtr : BitVec 64) :
    memRegion secretsPtr 192 =
      memRegion secretsPtr 32 ∗ memRegion (secretsPtr + 32#64) 32 ∗
      memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 := by
  rw [← memRegion_merge_at secretsPtr 32 160 (secretsPtr + 32#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 32#64) 32 128 (secretsPtr + 64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 64#64) 32 96 (secretsPtr + 96#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by bv_omega) (by decide)]

private theorem stage3KeySlotsAt_repack_dh1_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗ ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗ memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗ ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A.repAlloc fsp b kp ekASk ekAPk pqspkPtr opkId :=
  stage3KeySlotsAt_repack_dh1 A.repAlloc fsp b kp ekASk ekAPk pqspkPtr opkId

/-! ## `DH1` Step Theorems (`+0x0760 → +0x0858`) -/

set_option maxHeartbeats 1600000 in
/-- Budget-threaded Step A (`+0x0760 → +0x0858`: `secrets` alloc + `DH1`) from a Block `207` witness. -/
theorem dh1_step_of_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCalc : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A lim)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents dh1UnwindEvents st = M.stepEvents evs st0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiatePlaced s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh1OkEvents st) s ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, hspkLen, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  have hikASkLen : kp.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  refine sepWPp_conseq_oom (P' :=
      S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗ A.pool lim st s3 ∗
      stackAt fsp extHookStack ∗ memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ memRegion fsp 0x78 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
      stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
      memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗ memRegion (fsp + 0x1c60#64) 8 ∗
      memRegion (fsp + 0x1c68#64) 8 ∗ memRegion (fsp + 0x1c70#64) 8 ∗
      memRegion (fsp + 0x1c78#64) 0x18)
    (by unfold S3InvPrefixPlaced; dsimp only [stage3MemPlaced]
        rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl,
            stackAt_sub_split_init fsp hsub_ext (stk_sub_le_2pow64 hstk64), s3_loc_split_placed fsp]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine' s3_block_to_call_vm_placed hh
    (lsρ lsRustNoAllocShimSymCli)
    0x764 (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
    hs3.ctrl ?_ ?_; rotate_left 1
  · have hpc : s3.pc = (blkPl_521).base + 0x760#64 := hs3.ctrl.pc; have hrun := hs3.ctrl.run
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_vm_steps (
      wp_steps
      refine s3_done_call_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
        (by wp_norm_lhs) (Entails.refl _)
        ⟨by simpa only [fsp, arm64_norm, wp_norm] using hs3.x20,
         by simpa only [fsp, arm64_norm, wp_norm] using hs3.x21,
         by simpa only [fsp, arm64_norm, wp_norm] using hs3.x22,
         by simpa only [fsp, arm64_norm, wp_norm] using hs3.x24⟩)
  · intro sm0 hvm0 hctrl0 hpcm0 hlrm0 htrm0 ⟨hx20_0, hx21_0, hx22_0, hx24_0⟩
    have hpool0 : A.pool lim st s3 = A.pool lim st sm0 :=
      (A.pool_transport lim st s3 sm0 hvm0).symm
    refine s3_shim_pool_placed hh st _ hctrl0 (htrm0.trans hs3.trace) hpcm0 hlrm0 hpanic
      (by rw [hpool0, hctrl0.sp]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_sh hctrl_sh hcs_sh htr_sh
    rw [hctrl0.sp]
    have hx20_sh := hcs_sh.2.1.trans hx20_0; have hx21_sh := hcs_sh.2.2.1.trans hx21_0
    have hx22_sh := hcs_sh.2.2.2.1.trans hx22_0; have hx24_sh := hcs_sh.2.2.2.2.2.1.trans hx24_0
    refine' s3_block_to_call_vm_placed hh
      (lsρ lsRustAllocSymCli)
      0x770 (Φ := fun sm =>
        sm.readReg64 .x0 = 192#64 ∧ sm.readReg64 .x1 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
      hctrl_sh ?_ ?_; rotate_left 1
    · have hpc : s_sh.pc = (blkPl_521).base + 0x764#64 := hctrl_sh.pc; have hrun := hctrl_sh.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simpa only [arm64_norm, wp_norm] using hx20_sh,
           by simpa only [arm64_norm, wp_norm] using hx21_sh,
           by simpa only [arm64_norm, wp_norm] using hx22_sh,
           by simpa only [arm64_norm, wp_norm] using hx24_sh⟩)
    · intro sm_al hvm_al hctrl_al hpcm_al hlrm_al htrm_al
        ⟨hx0_al, hx1_al, hx20_al, hx21_al, hx22_al, hx24_al⟩
      have htr_al : sm_al.trace = s0.trace :=
        htrm_al.trans (htr_sh.trans (htrm0.trans hs3.trace))
      have hpool_al : A.pool lim st s_sh = A.pool lim st sm_al :=
        (A.pool_transport lim st s_sh sm_al hvm_al).symm
      refine s3_call_alloc_placed hh 192 st _ hctrl_al hpcm_al hlrm_al
        (by rw [hx0_al]; decide) (by rw [hx1_al]; decide) rustLay192 hFit192
        (by rw [hpool_al, hctrl_al.sp]; (try dsimp only [fsp]); sep_frame) ?_
      intro s_ok hctrl_ok hcs_ok hsecNonNull _ htr_ok
      let st1 := M.stepEvents (rustAllocEvents 192 1) st
      set secretsPtr := s_ok.readReg64 .x0
      have hx20_ok := hcs_ok.2.1.trans hx20_al; have hx21_ok := hcs_ok.2.2.1.trans hx21_al
      have hx22_ok := hcs_ok.2.2.2.1.trans hx22_al; have hx24_ok := hcs_ok.2.2.2.2.2.1.trans hx24_al
      rw [hctrl_al.sp, s3_sec_split_placed secretsPtr, memRegion32_cells4 secretsPtr,
          ProofLib.memRegion_eight (fsp + 0x1c60#64), ProofLib.memRegion_eight (fsp + 0x1c68#64),
          ProofLib.memRegion_eight (fsp + 0x1c70#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun sw0 => sepWPp_exists_elim_oom fun sw1 =>
        sepWPp_exists_elim_oom fun sw2 => sepWPp_exists_elim_oom fun sw3 =>
        sepWPp_exists_elim_oom fun c0 => sepWPp_exists_elim_oom fun c1 =>
        sepWPp_exists_elim_oom fun c2 => ?_
      obtain ⟨halign_ok, hx29_ok, hfsp_ok⟩ := hctrl_ok.step_ctx fsp
      refine' s3_block_to_call_vm_placed hh
        (lsmpl.base 207)
        0x7a8 (Φ := fun sm =>
          sm.readReg64 .x0 = fsp + 0x368#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
          sm.readReg64 .x8 = fsp + 0x1600#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
          sm.readReg64 (.gpr 25#5) = secretsPtr)
        hctrl_ok ?_ ?_; rotate_left 1
      · have hpc : s_ok.pc = (blkPl_521).base + 0x770#64 := hctrl_ok.pc; have hrun := hctrl_ok.run
        dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        have hnz0 : s_ok.readReg64 (.gpr 0#5) ≠ 0#64 := by
          simpa only [arm64_norm, wp_norm] using hsecNonNull
        (try dsimp only [fsp] at *); rw [← hctrl_ok.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_ok hx21_ok hx22_ok hx24_ok
        by_vm_steps (
          wp_steps
          have hsec_reg : s_ok.readReg64 (.gpr 0#5) = secretsPtr := rfl
          have hones :
              (secretsPtr ↦₆₄ 0xffffffffffffffff#64) ∗
                ((secretsPtr + 8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                ((secretsPtr + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                ((secretsPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) =
              (secretsPtr ↦ₛ bytesToBv8 F_X25519) := allOnes64_4_eq_F_X25519 secretsPtr
          rw [hones, hsec_reg]
          refine s3_done_call_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by wp_norm_goal,
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [secretsPtr, arm64_norm, wp_norm]⟩)
      · intro sm_c1 hvm_c1 hctrl_c1 hpcm_c1 hlrm_c1 htrm_c1
          ⟨hx0_c1, hx1_c1, hx8_c1, hx20_c1, hx21_c1, hx22_c1, hx24_c1, hx25_c1⟩
        rw [hctrl_ok.sp] at *
        (try iterate 6 rw [BitVec.add_comm _ fsp])
        (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
        have htr_c1 : sm_c1.trace = s0.trace := htrm_c1.trans (htr_ok.trans htr_al)
        have hpool_c1 : A.pool lim st1 s_ok = A.pool lim st1 sm_c1 :=
          (A.pool_transport lim st1 s_ok sm_c1 hvm_c1).symm
        dsimp only [stage3KeySlotsAt, RustCliAllocBudget.repAlloc]
        refine s3_calc_agree_of_ok (X := X) hh hCalc
          (fsp + 0x368#64) (toU8 kp.privateKey.bytes.toList)
          (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) st1 _
          hctrl_c1 htr_c1 hpcm_c1 hlrm_c1 hx0_c1 hx1_c1 (by rw [hctrl_c1.sp]; exact hx8_c1)
          (by rw [toU8_length_eq, hikASkLen]) (by rw [toU8_length_eq, hspkLen])
          hFitDh1 hpanic
          (by
            rw [hpool_c1, hctrl_c1.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            (try dsimp only [fsp, st1]); sep_frame)
          ?_ ?_
        · intro hdh1_zero s_z1 hi u2 hctrl_z1 hcs_z1 htr_z1
          have hx25_z1 := hcs_z1.2.2.2.2.2.2.1.trans hx25_c1
          rw [hctrl_c1.sp]
          obtain ⟨halign_z1, hx29_z1, hfsp_z1⟩ := hctrl_z1.step_ctx fsp
          refine' s3_block_in_vm_placed hh 0x1548
            (Φ := fun sm => sm.readReg64 (.gpr 25#5) = secretsPtr ∧
              sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
            hctrl_z1 ?_ ?_; rotate_left 1
          · have hpc : s_z1.pc = (blkPl_521).base + 0x7a8#64 := hctrl_z1.pc; have hrun := hctrl_z1.run
            dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, speWord, BitVec.ofNat_eq_ofNat] at hpc ⊢
            (try dsimp only [fsp] at *); rw [← hctrl_z1.sp] at *
            by_vm_steps (
              wp_steps
              refine s3_done_in_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (by wp_norm_lhs) (Entails.refl _)
                ⟨by simpa only [arm64_norm, wp_norm] using hx25_z1,
                 by wp_norm_goal, by wp_norm_goal⟩)
          · intro sm_u1 hvm_u1 htr_u1 hctrl_u1 ⟨hx25_u1, hx26_u1, hx1_u1⟩
            rw [hctrl_z1.sp] at *
            (try iterate 6 rw [BitVec.add_comm _ fsp])
            (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
            have hdh1_inp_zero :
                (modelPrims X ⟨W.C, W.Q⟩).x25519
                  (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
                  (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB =
                  List.replicate 32 0 :=
              dh1_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq ▸ hdh1_zero
            have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
              x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk (Or.inl hdh1_inp_zero)
            obtain ⟨evs_u, hInitEnv_u, hevsEq_u⟩ := hEnv_dh1 hdh1_inp_zero
            have hEnv1548 : ∃ evs, InitEnv x evs ∧
                M.stepEvents (rustDeallocEvents 1568 1)
                  (M.stepEvents (rustDeallocEvents 192 1) st1) = M.stepEvents evs st0 :=
              ⟨evs_u, hInitEnv_u, (stepEvents_dh1UnwindEvents M st).trans hevsEq_u⟩
            have hpool_u1 : A.pool lim st1 s_z1 = A.pool lim st1 sm_u1 :=
              (A.pool_transport lim st1 s_z1 sm_u1 hvm_u1).symm
            refine sepWPp_conseq_oom ?_
              (unwind_1548_placed_ok hh hEnv1548 hS hnone hstk hstk64 hs3.x8 hsecNonNull
                hs3.pqspkNonNull hctrl_u1 (htr_u1.trans (htr_z1.trans htr_c1))
                hx25_u1 hx26_u1 hx1_u1 hpost hpanic)
            rw [hpool_u1, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            have hbase := s3_dh_collapse_common_placed (A := A) (lim := lim) (st := st1) (B := B)
              (x := x) (kp := kp) (ekASk := ekASk) (ekAPk := ekAPk)
              (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr) (opkId := opkId)
              hstk hstk64 hekAPkLen hekASkLen hkpkLen s0 sm_u1
            have hsec_re :
                (secretsPtr ↦ₛ bytesToBv8 F_X25519) ∗ memRegion (secretsPtr + 32#64) 32 ∗
                  memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
                  memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
                memRegion secretsPtr 192 := by
              refine Entails.trans (sepConj_mono_left
                (pointsToBytes_entails_memRegion_len (n := 32) (by decide))) ?_
              rw [← s3_sec_split_placed secretsPtr]; exact Entails.refl _
            have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 (hi ++ 3#8) u2
            have hloc_re :
                memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
                  memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
                  memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
                memRegion (fsp + 0x958#64) 0x1310 := by
              refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
              rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by clear * -; bv_omega) (by decide)]
              exact Entails.refl _
            have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢
                memRegion fsp 0x80 := by
              refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
              rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by clear * -; bv_omega) (by decide)]
              exact Entails.refl _
            have hc20 : ((fsp + 0x1c70#64) ↦₆₄ 32#64) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
                memRegion (fsp + 0x1c70#64) 0x20 := by
              refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
              rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by clear * -; bv_omega) (by decide)]
              exact Entails.refl _
            have hkeys_back :=
              stage3KeySlotsAt_repack_dh1_budget A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
            have htail1548 :
                ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
                  memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ⊢
                memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
              rw [show s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 from by
                dsimp only [fsp]; clear * -; rw [cliInitiateFrame_eq]; bv_omega]
              refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
              have hm : memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
                  memRegion (fsp + 0x1c70#64) 0x20 =
                  memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
                simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
                rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by clear * -; bv_omega) (by decide)]
              exact Entails.of_eq (by rw [← hm]; sep_ac_rfl)
            refine sep_replace (sepConj_mono hsec_re (sepConj_mono hm78 (sepConj_mono hsret hc20)))
              (by (try dsimp only [fsp, st1]); sep_frame) ?_
            refine sep_replace (sepConj_mono hloc_re (Entails.of_eq hkeys_back))
              (by (try dsimp only [fsp, st1]); cases x.bundle.opk <;> (dsimp only; sep_frame)) ?_
            refine sep_replace hbase (by (try dsimp only [fsp, st1]); sep_frame) ?_
            dsimp only [Unwind1548MemPlaced]
            exact sep_replace htail1548 (by (try dsimp only [fsp, st1]); sep_frame)
              (by (try dsimp only [fsp, st1]); sep_frame)
        · intro hdh1_nz s_ok1 dh1Ptr hctrl_ok1 hcs_ok1 htr_ok1
          let st2 := M.stepEvents (rustAllocEvents 32 1) st1
          have hx20_1 := hcs_ok1.2.1.trans hx20_c1; have hx21_1 := hcs_ok1.2.2.1.trans hx21_c1
          have hx22_1 := hcs_ok1.2.2.2.1.trans hx22_c1
          have hx24_1 := hcs_ok1.2.2.2.2.2.1.trans hx24_c1
          have hx25_1 := hcs_ok1.2.2.2.2.2.2.1.trans hx25_c1
          set dh1 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 kp.privateKey.bytes.toList)
            (toU8 x.bundle.spk.bytes.toList)
          have hdh1_len : (bytesToBv8 dh1).length = 32 := by
            rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
          rw [hctrl_c1.sp]
          obtain ⟨halign_1, hx29_1, hfsp_1⟩ := hctrl_ok1.step_ctx fsp
          refine' s3_block_to_call_vm_placed hh
            (lsρ memcpyName)
            0x808 (Φ := fun sm =>
              sm.readReg64 .x0 = secretsPtr + 32#64 ∧ sm.readReg64 .x1 = dh1Ptr ∧
              sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 22#5) = 32#64 ∧
              sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
              sm.readReg64 (.gpr 25#5) = secretsPtr ∧
              sm.readReg64 (.gpr 27#5) = 32#64 ∧ sm.readReg64 (.gpr 28#5) = dh1Ptr)
            hctrl_ok1 ?_ ?_; rotate_left 1
          · have hpc : s_ok1.pc = (blkPl_521).base + 0x7a8#64 := hctrl_ok1.pc
            have hrun := hctrl_ok1.run
            dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            (try dsimp only [fsp] at *); rw [← hctrl_ok1.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_1 hx21_1 hx22_1 hx24_1 hx25_1
            by_vm_steps (
              wp_steps
              refine s3_done_call_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal⟩)
          · intro sm_mc1 hvm_mc1 hctrl_mc1 hpcm_mc1 hlrm_mc1 htrm_mc1
              ⟨hx0_mc1, hx1_mc1, hx2_mc1, hx20_mc1, hx21_mc1, hx22_mc1, hx23_mc1, hx24_mc1,
               hx25_mc1, hx27_mc1, hx28_mc1⟩
            rw [hctrl_ok1.sp] at *
            (try iterate 6 rw [BitVec.add_comm _ fsp])
            (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
            have hpool_mc1 : A.pool lim st2 s_ok1 = A.pool lim st2 sm_mc1 :=
              (A.pool_transport lim st2 s_ok1 sm_mc1 hvm_mc1).symm
            refine s3_memcpy_pool_placed hh (secretsPtr + 32#64) dh1Ptr (bytesToBv8 dh1) st2 _
              hctrl_mc1 (htrm_mc1.trans (htr_ok1.trans htr_c1)) hpcm_mc1 hlrm_mc1
              hx0_mc1 hx1_mc1 (by rw [hx2_mc1, hdh1_len]; decide) hpanic
              (by rw [hpool_mc1, hctrl_mc1.sp, hdh1_len]; (try dsimp only [fsp, st2]); sep_frame)
              ?_
            intro s_mc1 hctrl_mc1' hcs_mc1 _ htr_mc1; rw [hctrl_mc1.sp]
            have hx20_m := hcs_mc1.2.1.trans hx20_mc1; have hx21_m := hcs_mc1.2.2.1.trans hx21_mc1
            have hx22_m := hcs_mc1.2.2.2.1.trans hx22_mc1
            have hx23_m := hcs_mc1.2.2.2.2.1.trans hx23_mc1
            have hx24_m := hcs_mc1.2.2.2.2.2.1.trans hx24_mc1
            have hx25_m := hcs_mc1.2.2.2.2.2.2.1.trans hx25_mc1
            have hx27_m := hcs_mc1.2.2.2.2.2.2.2.2.1.trans hx27_mc1
            have hx28_m := hcs_mc1.2.2.2.2.2.2.2.2.2.1.trans hx28_mc1
            obtain ⟨halign_m1, hx29_m1, hfsp_m1⟩ := hctrl_mc1'.step_ctx fsp
            refine' s3_block_to_call_vm_placed hh
              (lsρ lsRustDeallocSymCli)
              0x820 (Φ := fun sm =>
                sm.readReg64 .x0 = dh1Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
                sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧
                sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧
                sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
              hctrl_mc1' ?_ ?_; rotate_left 1
            · have hpc : s_mc1.pc = (blkPl_521).base + 0x808#64 := hctrl_mc1'.pc
              have hrun := hctrl_mc1'.run
              dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
                BitVec.ofNat_eq_ofNat] at hpc ⊢
              (try dsimp only [fsp] at *); rw [← hctrl_mc1'.sp] at *
              try simp only [arm64_norm, wp_norm]
                at hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m
              by_vm_steps (
                wp_steps
                refine s3_done_call_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                  (by wp_norm_lhs) (Entails.refl _)
                  ⟨by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by wp_norm_goal,
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm]⟩)
            · intro sm_da1 hvm_da1 hctrl_da1 hpcm_da1 hlrm_da1 htrm_da1
                ⟨hx0_da1, hx1_da1, hx2_da1, hx20_da1, hx21_da1, hx23_da1, hx24_da1,
                 hx25_da1, hx26_da1⟩
              rw [hctrl_mc1'.sp] at *
              (try iterate 6 rw [BitVec.add_comm _ fsp])
              (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
              have hpool_da1 : A.pool lim st2 s_mc1 = A.pool lim st2 sm_da1 :=
                (A.pool_transport lim st2 s_mc1 sm_da1 hvm_da1).symm
              refine s3_dealloc_stack_placed hh dh1Ptr 32 st2 _ hctrl_da1
                hpcm_da1 hlrm_da1 hx0_da1 (by rw [hx1_da1]; decide) (by rw [hx2_da1]; decide) lay32
                (by rw [hpool_da1, hctrl_da1.sp]
                    exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh1Ptr) hdh1_len)
                      (by (try dsimp only [fsp, st2]); sep_frame)
                      (by (try dsimp only [fsp, st2]); sep_frame)) ?_
              intro s_d1 hctrl_d1 hcs_d1 htr_d1; rw [hctrl_da1.sp]
              have hx20_d1 := hcs_d1.2.1.trans hx20_da1; have hx21_d1 := hcs_d1.2.2.1.trans hx21_da1
              have hx23_d1 := hcs_d1.2.2.2.2.1.trans hx23_da1
              have hx24_d1 := hcs_d1.2.2.2.2.2.1.trans hx24_da1
              have hx25_d1 := hcs_d1.2.2.2.2.2.2.1.trans hx25_da1
              have hx26_d1 := hcs_d1.2.2.2.2.2.2.2.1.trans hx26_da1
              refine' s3_block_in_vm_placed hh 0x858 (Φ := fun sm =>
                sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
                sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
                sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
                hctrl_d1 ?_ ?_; rotate_left 1
              · have hpc : s_d1.pc = (blkPl_521).base + 0x820#64 := hctrl_d1.pc
                have hrun := hctrl_d1.run
                dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
                (try dsimp only [fsp] at *); rw [← hctrl_d1.sp] at *
                try simp only [arm64_norm, wp_norm]
                  at hx20_d1 hx21_d1 hx23_d1 hx24_d1 hx25_d1 hx26_d1
                by_vm_steps (
                  wp_steps
                  refine s3_done_in_vm (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
                    (by wp_norm_lhs) (Entails.refl _)
                    ⟨by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm]⟩)
              · intro s858 hvm_858 htr_858 hctrl_858
                  ⟨hx20_858, hx21_858, hx22_858, hx24_858, hx25_858, hx26_858⟩
                rw [hctrl_d1.sp] at *
                (try iterate 6 rw [BitVec.add_comm _ fsp])
                (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
                have hdh1_eq := dh1_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq
                have htr_final : s858.trace = s0.trace :=
                  htr_858.trans (htr_d1.trans (htrm_da1.trans
                    (htr_mc1.trans (htrm_mc1.trans (htr_ok1.trans htr_c1)))))
                have hpool_858 :
                    A.pool lim (M.stepEvents (rustDeallocEvents 32 1) st2) s_d1 =
                      A.pool lim (M.stepEvents dh1OkEvents st) s858 := by
                  dsimp only [st2, st1]
                  rw [stepEvents_dh1OkEvents]
                  exact (A.pool_transport lim (M.stepEvents dh1OkEvents st) s_d1 s858 hvm_858).symm
                have hsret_ok := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh1Ptr 32#64
                have hkeys_ok :=
                  stage3KeySlotsAt_repack_dh1_budget A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
                refine sepWPp_conseq_oom ?_
                  (hnext s858 secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hctrl_858 htr_final
                    hx20_858 hx21_858 hx22_858 hx24_858 hx25_858 hx26_858)
                rw [hpool_858, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
                exact sep_replace
                  (sepConj_mono hsret_ok (sepConj_mono (Entails.of_eq hkeys_ok)
                    (Entails.of_eq (append_bv8_at secretsPtr F_X25519 dh1 32#64 rfl))))
                  (by (try dsimp only [fsp]); cases x.bundle.opk <;> ((try dsimp only); sep_frame))
                  (by (try dsimp only [fsp]); sep_frame)

theorem dh1_step_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents dh1UnwindEvents st = M.stepEvents evs st0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiatePlaced s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh1OkEvents st) s ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  dh1_step_of_ok hh (hLocal.calculateAgreement X) hS hstk hstk64 hs3 hFit192 hFitDh1 hEnv_dh1
    hpost hpanic hnext

theorem dh1_step_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents dh1UnwindEvents st = M.stepEvents evs st0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiatePlaced s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents dh1OkEvents st) s ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  dh1_step_of_ok hh (calculateAgreement_cli_placed_ok mmpl gh W hh X) hS hstk hstk64 hs3
    hFit192 hFitDh1 hEnv_dh1 hpost hpanic hnext

theorem dh1_step_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hFit192 : FitsEvents M lim (M.stepEvents evs_pre st0) (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim
      (M.stepEvents (rustAllocEvents 192 1) (M.stepEvents evs_pre st0))
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList) (toU8 x.bundle.spk.bytes.toList)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ dh1UnwindEvents))
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiatePlaced s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          A.pool lim (M.stepEvents (evs_pre ++ dh1OkEvents) st0) s ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim (M.stepEvents evs_pre st0) x kp ekASk ekAPk pqspkPtr opkId stk s0 s3)
      Q Qp oom :=
  dh1_step_placed_ok hh hLocal hS hstk hstk64 hs3 hFit192 hFitDh1
    (fun h0 => ⟨evs_pre ++ dh1UnwindEvents, hEnv_dh1 h0,
      (M.stepEvents_append evs_pre dh1UnwindEvents st0).symm⟩)
    hpost hpanic
    (fun s secretsPtr dh1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => by
      rw [← M.stepEvents_append evs_pre dh1OkEvents st0]
      exact hnext s secretsPtr dh1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsAPlacedBudget
