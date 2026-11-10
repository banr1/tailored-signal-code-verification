/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2MidPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3

/-!
# Budget-Threaded Relocatable Stage P2 Substages 1–3 Composition

Defines Substages P2.1–P2.3 allocator event lists and `SeqEnv` envelopes, and proves
`RustCliAllocBudget M` / `VmPreserved` placed composition (`+0x0868 → +0x0d5c` or error exit via
Arms 1–2) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord SignedPreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded NoFsEv
  PreKeyStoreSpec PreKeyVtablesPlacedOk
  SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk
  speErrAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (IdentitySelfStoreSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt eq_of_sep_emp
  processPrekeyActive10At sessionRecordEmptyHeaderAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_allocHookStack_le_stageP2
  p2_bytes7_937_to_cells8_930
  p2_cells2_4f8_eq
  p2_cells4_3d8_eq
  p2_cells8_398_to_keyPair64UnalignedAt
  p2_cells8_930_split_7_57
  p2_drop_frame_mid
  p2_envOk_kpk
  p2_envOk_spk
  p2_fsAt_step_kpk
  p2_fsAt_step_spk
  p2_intro_kpk_vt_placed
  p2_intro_pk_vt_placed
  p2_intro_spk_vt_placed
  p2_keyPair64UnalignedAt_eq_bytes32_pair
  p2_keyPair64UnalignedAt_to_memRegion
  p2_kpkPoll_le_stageP2
  p2_kpkShim_le_stageP2
  p2_memRegion7_to_bytes7At
  p2_memRegion_3e0_split_88_280
  p2_memRegion_3e0_split_9_79
  p2_memRegion_a90_65_to_cells6
  p2_processPrekeyActive10At_eq
  p2_pure_le_stageP2
  p2_sepWPp_frame_eq
  p2_sepWPp_weaken_eq
  p2_sessionRecordEmptyHeaderAt_errArm
  p2_spkPoll_le_stageP2
  p2_spkShim_le_stageP2
  p2_stackAt_split_of_le
  stageP1EntryPlaced
  stageP1ProgPlaced
  stageP2CallStack
  stageP2EnvOk
  stageP2PureAndErrStack
  stageP2Quiet
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp (mono_run)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget SeqEnv coarseCostModel coarseStep coarseStepReserve
  fitsEvents_of_step_monotone rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2Arm1ErrEvents
  p2Arm2ErrEvents
  p2_arm1_err_hooks_placed_ok
  p2_arm2_err_hooks_placed_ok
  p2_bind_sepWPp_steps_frame_state
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  P2Sub1Env
  boxAllocEnv_iff_eq
  boxAllocEvents
  p2Sub1Events
  p2_bind_sepWPp_cro_frame_state_nopanic
  stageP2_sub1_kits_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  freeOnlyEvs_rustDeallocEvents
  p2SpkRecFreeEvents
  p2SpkRecFreeEvents_freeOnly
  p2Sub2TailEvents
  stageP2_sub2_kits_ext_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
  p2KpkVecFreeEvents_freeOnly
  p2Sub3TailAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget (
  p2Sub3DetPostPollEvents
  p2Sub3OkPostPollEvents
  p2Sub3PreTailEvents
  stageP2_sub3_kits_ext_placed
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_intro_spk_vt_placed
  p2_intro_kpk_vt_placed
  p2_intro_pk_vt_placed
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [RustCliAllocBudget.repAlloc_live]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Substages P2.1–P2.3 Event Lists, Envelopes & `SeqEnv` Projections -/

/-- Allocator event list along Arm 1 (`+0x0868 -> s0.readReg64 .x30` on `spkKit.getPoll` `.error e`):
Substage P2.1 (`p2Sub1Events spkBoxSize`), `evs_spk` from `spkKit.getPoll`, and Arm 1 teardown
(`p2Arm1ErrEvents spkBoxSize 0#64`). -/
def p2Sub1To3Arm1Events (spkBoxSize : Nat) (evs_spk : List AllocEvent) : List AllocEvent :=
  p2Sub1Events spkBoxSize ++ evs_spk ++ p2Arm1ErrEvents spkBoxSize 0#64

/-- Allocator event list of Substages P2.1–P2.2 along `.ok spkRec` (`+0x0868 -> +0x1460`):
Substage P2.1 (`p2Sub1Events spkBoxSize`), `evs_spk` from `spkKit.getPoll`, and Substage P2.2's
`.ok`-tail (`p2Sub2TailEvents spkBoxSize spkPubCap spkPrivCap spkSigCap kpkBoxSize`). -/
def p2Sub1To2OkEvents (spkBoxSize : Nat) (evs_spk : List AllocEvent)
    (spkPubCap spkPrivCap spkSigCap kpkBoxSize : Nat) : List AllocEvent :=
  p2Sub1Events spkBoxSize ++ evs_spk ++
    p2Sub2TailEvents spkBoxSize spkPubCap spkPrivCap spkSigCap kpkBoxSize

/-- Allocator event list along Arm 2 (`+0x0868 -> s0.readReg64 .x30` on `kpkKit.getPoll` `.error e`):
Substages P2.1–P2.2 `.ok spkRec` (`p2Sub1To2OkEvents`), `evs_kpk` from `kpkKit.getPoll`, and Arm 2
teardown (`p2Arm2ErrEvents kpkBoxSize 0#64`). -/
def p2Sub1To3Arm2Events (spkBoxSize : Nat) (evs_spk : List AllocEvent)
    (spkPubCap spkPrivCap spkSigCap kpkBoxSize : Nat) (evs_kpk : List AllocEvent) :
    List AllocEvent :=
  p2Sub1To2OkEvents spkBoxSize evs_spk spkPubCap spkPrivCap spkSigCap kpkBoxSize ++
    evs_kpk ++ p2Arm2ErrEvents kpkBoxSize 0#64

/-- Allocator event list of Substages P2.1–P2.3 along `.ok spkRec` / `.ok kpkRec`
(`+0x0868 -> +0x0d5c`):
Substages P2.1–P2.2 `.ok spkRec` (`p2Sub1To2OkEvents`), `evs_kpk` from `kpkKit.getPoll`, and
Substage P2.3's post-poll `.ok` events (`p2Sub3OkPostPollEvents`). -/
def p2Sub1To3OkEvents (spkBoxSize : Nat) (evs_spk : List AllocEvent)
    (spkPubCap spkPrivCap spkSigCap kpkBoxSize : Nat) (evs_kpk : List AllocEvent)
    (kpkPubCap kpkPrivCap kpkSigCap : Nat) (evs_drop : List AllocEvent) : List AllocEvent :=
  p2Sub1To2OkEvents spkBoxSize evs_spk spkPubCap spkPrivCap spkSigCap kpkBoxSize ++
    evs_kpk ++
    p2Sub3OkPostPollEvents kpkBoxSize kpkPubCap kpkPrivCap kpkSigCap evs_drop

/-- Deterministic fixed-poll allocator event envelope for Substages P2.1–P2.3 `.ok`
(`+0x0868 -> +0x0d5c`). -/
def P2Sub1To3FixedPollEnv (spkBoxSize : Nat) (evs_spk : List AllocEvent)
    (spkPubCap spkPrivCap spkSigCap kpkBoxSize : Nat) (evs_kpk : List AllocEvent)
    (kpkPubCap kpkPrivCap kpkSigCap : Nat) (evs_drop : List AllocEvent)
    (evs : List AllocEvent) : Prop :=
  evs = p2Sub1To3OkEvents spkBoxSize evs_spk spkPubCap spkPrivCap spkSigCap kpkBoxSize
    evs_kpk kpkPubCap kpkPrivCap kpkSigCap evs_drop

theorem fitsEnv_p2Sub1To3FixedPollEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (spkBoxSize : Nat) (evs_spk : List AllocEvent)
    (spkPubCap spkPrivCap spkSigCap kpkBoxSize : Nat) (evs_kpk : List AllocEvent)
    (kpkPubCap kpkPrivCap kpkSigCap : Nat) (evs_drop : List AllocEvent) :
    FitsEnv M lim st
      (P2Sub1To3FixedPollEnv spkBoxSize evs_spk spkPubCap spkPrivCap spkSigCap kpkBoxSize
        evs_kpk kpkPubCap kpkPrivCap kpkSigCap evs_drop) ↔
    FitsEvents M lim st
      (p2Sub1To3OkEvents spkBoxSize evs_spk spkPubCap spkPrivCap spkSigCap kpkBoxSize
        evs_kpk kpkPubCap kpkPrivCap kpkSigCap evs_drop) :=
  FitsEnv.eq_iff

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub1To3FixedPollEnv` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub1To3FixedPollEnv 64 [.alloc 33, .alloc 32, .alloc 64] 33 32 64 64
        [.alloc 1569, .alloc 3169, .alloc 64] 1569 3169 64 [.free 1 21]) := by
  rw [fitsEnv_p2Sub1To3FixedPollEnv_iff]
  refine fitsEvents_of_step_monotone coarseCostModel _ 40000000 _ [] coarseCostModel.init ?_
  have hevs :
      p2Sub1To3OkEvents 64 [.alloc 33, .alloc 32, .alloc 64] 33 32 64 64
        [.alloc 1569, .alloc 3169, .alloc 64] 1569 3169 64 [.free 1 21] =
      [.alloc 33, .free 1 33, .alloc 64,
       .alloc 33, .alloc 32, .alloc 64,
       .free 8 64, .free 1 33, .free 1 32, .free 1 64, .alloc 64,
       .alloc 1569, .alloc 3169, .alloc 64,
       .free 8 64, .alloc 1568, .alloc 3168, .free 1 1569, .free 1 3169, .free 1 64, .alloc 21,
       .free 1 21] := by decide
  rw [hevs]
  dsimp only [List.append_nil, FitsStep, coarseCostModel]
  decide

/-- Single-`SeqEnv` allocator budget envelope covering Substages P2.1–P2.3 (`+0x0868 -> +0x0d5c`
and Arms 1–2):
`P2Sub1Env spkBoxSize`, `spkEnv.getPollEnv`, `FreeOnlyEvs`, `BoxAllocEnv kpkBoxSize`,
`kpkEnv.getPollEnv`, `FreeOnlyEvs`, `KemKeyPairFromPubPrivEnv`, `FreeOnlyEvs`, and
`P2Sub3TailAllocEnv`. -/
def P2Sub1To3SeqEnv {A : RustAlloc}
    (spkKit : SignedPreKeyStoreSpec A 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (stSpk : spkKit.SpkState) (signedPreKeyId : BitVec 32)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (stKpk : kpkKit.KpkState) (kyberPreKeyId : BitVec 32) :
    List AllocEvent → Prop :=
  SeqEnv (P2Sub1Env spkKit.getBoxSize)
    (SeqEnv (spkEnv.getPollEnv stSpk signedPreKeyId)
      (SeqEnv FreeOnlyEvs
        (SeqEnv (BoxAllocEnv kpkKit.getBoxSize)
          (SeqEnv (kpkEnv.getPollEnv stKpk kyberPreKeyId)
            (SeqEnv FreeOnlyEvs
              (SeqEnv KemKeyPairFromPubPrivEnv
                (SeqEnv FreeOnlyEvs P2Sub3TailAllocEnv)))))))

/-- `SeqEnv` prefix of Substages P2.1–P2.3 chained with a post-`+0x0d5c` continuation envelope
`TailEnv` (after `dropSpe2`'s `FreeOnlyEvs` drop), enabling single-hypothesis composition with
Substage P2.4+. -/
def P2Sub1To3ThenEnv {A : RustAlloc}
    (spkKit : SignedPreKeyStoreSpec A 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (stSpk : spkKit.SpkState) (signedPreKeyId : BitVec 32)
    (kpkKit : KyberPreKeyStoreSpec A 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (stKpk : kpkKit.KpkState) (kyberPreKeyId : BitVec 32)
    (TailEnv : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (P2Sub1Env spkKit.getBoxSize)
    (SeqEnv (spkEnv.getPollEnv stSpk signedPreKeyId)
      (SeqEnv FreeOnlyEvs
        (SeqEnv (BoxAllocEnv kpkKit.getBoxSize)
          (SeqEnv (kpkEnv.getPollEnv stKpk kyberPreKeyId)
            (SeqEnv FreeOnlyEvs
              (SeqEnv KemKeyPairFromPubPrivEnv
                (SeqEnv FreeOnlyEvs
                  (SeqEnv P2Sub3TailAllocEnv
                    (SeqEnv FreeOnlyEvs TailEnv)))))))))

/-- Project the post-`+0x0d5c` continuation `FitsEnv M lim st3 TailEnv` after a valid `.ok`-branch
event list `p2Sub1To3OkEvents` from `FitsEnv M lim st (P2Sub1To3ThenEnv ... TailEnv)`. -/
theorem fitsEnv_tail_of_p2Sub1To3ThenEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A 0#64} {spkEnv : SignedPreKeyStoreBudgetEnv spkKit}
    {stSpk : spkKit.SpkState} {signedPreKeyId : BitVec 32}
    {kpkKit : KyberPreKeyStoreSpec A 0#64} {kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {stKpk : kpkKit.KpkState} {kyberPreKeyId : BitVec 32}
    {TailEnv : List AllocEvent → Prop}
    {evs_spk evs_kpk evs_drop : List AllocEvent}
    {spkPubCap spkPrivCap spkSigCap kpkPubCap kpkPrivCap kpkSigCap : Nat}
    (h : FitsEnv M lim st
      (P2Sub1To3ThenEnv spkKit spkEnv stSpk signedPreKeyId kpkKit kpkEnv stKpk kyberPreKeyId
        TailEnv))
    (hevs_spk : spkEnv.getPollEnv stSpk signedPreKeyId evs_spk)
    (hevs_kpk : kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk)
    (hfree_drop : FreeOnlyEvs evs_drop) :
    FitsEnv M lim
      (M.stepEvents
        (p2Sub1To3OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
          kpkKit.getBoxSize evs_kpk kpkPubCap kpkPrivCap kpkSigCap evs_drop) st)
      TailEnv := by
  have h1 : P2Sub1Env spkKit.getBoxSize (p2Sub1Events spkKit.getBoxSize) := rfl
  have h3 := p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap
  have h4 : BoxAllocEnv kpkKit.getBoxSize (boxAllocEvents kpkKit.getBoxSize) :=
    (boxAllocEnv_iff_eq kpkKit.getBoxSize _).mpr rfl
  have h6 := freeOnlyEvs_rustDeallocEvents kpkKit.getBoxSize 8
  have h7 : KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents := rfl
  have h8 := p2KpkVecFreeEvents_freeOnly kpkPubCap kpkPrivCap kpkSigCap
  have h9 : P2Sub3TailAllocEnv p2Sub3TailAllocEvents := rfl
  have hstep :=
    ((((((((h.seq_right h1).seq_right hevs_spk).seq_right h3).seq_right h4).seq_right
      hevs_kpk).seq_right h6).seq_right h7).seq_right h8).seq_right h9
  have hfinal := hstep.seq_right hfree_drop
  simpa only [p2Sub1To3OkEvents, p2Sub1To2OkEvents, p2Sub2TailEvents, p2Sub3OkPostPollEvents,
    p2Sub3DetPostPollEvents, p2Sub3PreTailEvents, M.stepEvents_append] using hfinal

/-! ## 2. Budget-Threaded Error-Arm & Header Helpers -/

private theorem p2_sessionRecordEmptyHeaderAt_errArm_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (coroPtr : BitVec 64) :
    sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if (0#64 : BitVec 64) = 0 then emp
       else A.live 8#64 ((0#64 : BitVec 64).toNat * 24) 8 ∗
            memRegion 8#64 ((0#64 : BitVec 64).toNat * 24)) ∗
      ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) := by
  simpa only [RustCliAllocBudget.repAlloc_live] using
    (p2_sessionRecordEmptyHeaderAt_errArm (A := A.repAlloc) coroPtr)

/-- State-indexed spatial postcondition variant of `p2_finish_err_arm_drop` for budget-threaded
error arms whose `ArmOut sf` / `Keep sf` carry `A.pool lim st' sf`. -/
theorem p2_finish_err_arm_drop_state {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre Rest Drop : SepProp} {ArmOut Keep : State → SepProp}
    {Q Qp : State → SepProp → Prop} {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut sf) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ∀ sf : State, ArmOut sf ∗ Rest ⊢ Drop ∗ Keep sf)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep sf) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame_state hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  refine weaken_frame (hSplit sf) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  refine p2_drop_frame_mid (Drop := Drop) rfl ?_
  exact SepWPp.done hpcf hrunf (hQ sf (Keep sf) hst hpcf hrunf htrf (Entails.refl _) hΦ)

/-! ## 3. Factored CPS Statement & Proof of Substages P2.1–P2.3 (`+0x0868 -> +0x0d5c`) -/

/-- Residual CPS statement of `stageP2_sub1_to_3_kits_ext_placed` (`+0x0868 -> +0x0d5c` on
`.ok spkRec` / `.ok kpkRec`, or error exit to `s0.readReg64 .x30` via Arms 1–2), factored so `4K`,
non-`4K`, `SeqEnv`, and `ThenEnv` entry points share one definition. -/
abbrev stageP2Sub1To3KitsPlacedProp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) (Qp : State → SepProp → Prop)
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) : Prop :=
  kyberCtCap ≠ 0#64 →
  LibsignalCodeRoLoaded lsmpl s.mem →
  FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
    (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s →
  spkKit.idOk signedPreKeyId →
  (∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
    spkKit.RecOk r →
    ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
      spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes) →
  kpkKit.getIdOk kyberPreKeyId →
  (∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
    kpkKit.RecOk r →
    ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
      kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes) →
  s.pc = stageP1EntryPlaced + 0x868#64 →
  s.status = .Running → s.sp = sp →
  (sp &&& 15#64 == 0#64) = true →
  calleeSavedVRegs s = calleeSavedVRegs s0 →
  s.readReg64 .x8 = kyberStorePtr → s.readReg64 .x9 = msgPtr →
  s.readReg64 .x10 = kpkKit.kpk_vt → s.readReg64 .x11 = preKeyStorePtr →
  s.readReg64 .x12 = remoteAddrPtr → s.readReg64 .x13 = pkKit.pk_vt →
  s.readReg64 .x14 = localAddrPtr → s.readReg64 .x15 = idStorePtr →
  s.readReg64 .x16 = ikit.id_vt → s.readReg64 .x19 = coroPtr →
  s.readReg64 .x22 = spkStorePtr → s.readReg64 .x23 = coroPtr + 0xe0#64 →
  s.readReg64 .x24 = spkKit.spk_vt →
  (∀ (e : spkKit.GetErr) (evs_spk : List AllocEvent) (spkFutPtr : BitVec 64)
     (sf : State) (P_f : SepProp),
    Steps (stageP1ProgPlaced ext) s sf →
    spkKit.getRel stSpk signedPreKeyId (.error e) →
    spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
    sf.pc = s0.readReg64 .x30 → sf.status = .Running →
    sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
    sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    LibsignalCodeRoLoaded lsmpl sf.mem →
    (P_f ⊢
      speErrAt spkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
      kpkKit.storeAt kyberStorePtr stKpk ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
      cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
      ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
      ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
      memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim (M.stepEvents (p2Sub1To3Arm1Events spkKit.getBoxSize evs_spk) st) sf ∗
      stackAt sp stk ∗ Frame) →
    Q sf P_f) →
  (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
     (evs_spk : List AllocEvent) (spkPubCap spkPrivCap spkSigCap : BitVec 64)
     (e : kpkKit.GetErr) (evs_kpk : List AllocEvent) (kyberFutPtr : BitVec 64)
     (sf : State) (P_f : SepProp),
    Steps (stageP1ProgPlaced ext) s sf →
    spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
    spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
    33 ≤ spkPubCap.toNat → 32 ≤ spkPrivCap.toNat →
    spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
    spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
    spkRec.signedPreKey.privateKey = spkPrivBytes →
    kpkKit.getRel stKpk kyberPreKeyId (.error e) →
    kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
    sf.pc = s0.readReg64 .x30 → sf.status = .Running →
    sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
      kpkKit.getEvs kyberPreKeyId (.error e) →
    sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    LibsignalCodeRoLoaded lsmpl sf.mem →
    (P_f ⊢
      speErrAt kpkKit.getErr outPtr e ∗
      spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
      kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
      memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
      ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
      cells (coroPtr + 0x3d8#64) 4 ∗
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
      ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
      ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
      ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
      ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
      ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
      memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim
        (M.stepEvents
          (p2Sub1To3Arm2Events spkKit.getBoxSize evs_spk spkPubCap.toNat spkPrivCap.toNat
            spkSigCap.toNat kpkKit.getBoxSize evs_kpk) st) sf ∗
      stackAt sp stk ∗ Frame) →
    Q sf P_f) →
  (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
     (evs_spk : List AllocEvent) (spkPubCap spkPrivCap spkSigCap : BitVec 64)
     (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
     (evs_kpk evs_drop : List AllocEvent)
     (pkBuf skBuf kyberFutPtr kpkPubCap v90 privCap privPtr : BitVec 64) (s3 : State),
    Steps (stageP1ProgPlaced ext) s s3 →
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s3 →
    spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
    spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
    33 ≤ spkPubCap.toNat → 32 ≤ spkPrivCap.toNat →
    spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
    spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
    spkRec.signedPreKey.privateKey = spkPrivBytes →
    kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
    kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
    FreeOnlyEvs evs_drop →
    1569 ≤ kpkPubCap.toNat → 3169 ≤ privCap.toNat →
    kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
    kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
    kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
    pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
    s3.pc = stageP1EntryPlaced + 0xd5c#64 →
    s3.status = .Running → s3.sp = sp →
    s3.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
      kpkKit.getEvs kyberPreKeyId (.ok kpkRec) →
    s3.readReg64 .x19 = coroPtr → s3.readReg64 .x21 = msgPtr + 0x90#64 →
    s3.readReg64 .x22 = kyberCtCap → s3.readReg64 .x23 = coroPtr + 0x4f2#64 →
    s3.readReg64 .x25 = sp + 0x210#64 → s3.readReg64 .x26 = coroPtr + 0x398#64 →
    s3.readReg64 .x27 = ctxPtr → s3.readReg64 .x28 = sp + 0xa90#64 →
    s3.readReg64 .x29 = s.readReg64 .x29 →
    calleeSavedVRegs s3 = calleeSavedVRegs s0 →
    LibsignalCodeRoLoaded lsmpl s3.mem →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s3
      (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
       kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
       (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
       (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ 3169#64) ∗
       ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ privCap) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗
       memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 88 ∗
       memRegion (sp + 0x438#64) 280 ∗ cells (sp + 0x930#64) 8 ∗
       memRegion (sp + 0xa90#64) 65 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim
         (M.stepEvents
           (p2Sub1To3OkEvents spkKit.getBoxSize evs_spk spkPubCap.toNat spkPrivCap.toNat
             spkSigCap.toNat kpkKit.getBoxSize evs_kpk kpkPubCap.toNat privCap.toNat
             v90.toNat evs_drop) st) s3 ∗
       stackAt sp stk ∗ Frame)
      Q Qp) →
  SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
    (spkKit.storeAt spkStorePtr stSpk ∗
     kpkKit.storeAt kyberStorePtr stKpk ∗
     sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
     memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
     ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
     cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
     cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
     ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
     cells (coroPtr + 0x4f8#64) 2 ∗
     ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
     ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
     ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
     ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
     ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
     ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
     ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
     ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
     memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
     cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
     decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
     memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗ Frame)
    Q Qp

set_option maxHeartbeats 1400000 in
/-- Budget-Threaded Placed Kit-Generic Stage P2 Substages 1–3
(`+0x0868 -> +0x0d5c` or error exit to `s0.readReg64 .x30`):
Composes `stageP2_sub1_kits_ext_placed`, `stageP2_sub2_kits_ext_placed` (discharging Arm 1 via
`p2_arm1_err_hooks_placed_ok`), and `stageP2_sub3_kits_ext_placed` (discharging Arm 2 via
`p2_arm2_err_hooks_placed_ok`), threading `A.pool lim st s`, `FsAt` via `stageP2Quiet`, and
`calleeSavedVRegs` under `StageP2ClosureHooksPlaced` and `StageP2PureCalleesPlaced4KOfEnv`. -/
theorem stageP2_sub1_to_3_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits_sub1 : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hfits_spk_poll : FitsEnv M lim
      (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st)
      (spkEnv.getPollEnv stSpk signedPreKeyId))
    (hfits_kpk_shim : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1Events spkKit.getBoxSize ++ evs_spk ++
            p2SpkRecFreeEvents spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap) st)
        (BoxAllocEnv kpkKit.getBoxSize))
    (hfits_kpk_poll : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize) st)
        (kpkEnv.getPollEnv stKpk kyberPreKeyId))
    (hfits_kem : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat)
      (kpkRec : KyberPreKeyRecord) (evs_kpk : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize ++ evs_kpk ++ rustDeallocEvents kpkKit.getBoxSize 8) st)
        KemKeyPairFromPubPrivEnv)
    (hfits_tail : ∀ (spkRec : SignedPreKeyRecord) (evs_spk : List AllocEvent)
      (spkPubCap spkPrivCap spkSigCap : Nat)
      (kpkRec : KyberPreKeyRecord) (evs_kpk : List AllocEvent)
      (kpkPubCap kpkPrivCap kpkSigCap : Nat),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkEnv.getPollEnv stSpk signedPreKeyId evs_spk →
      33 ≤ spkPubCap → 32 ≤ spkPrivCap →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_kpk →
      1569 ≤ kpkPubCap → 3169 ≤ kpkPrivCap →
      FitsEnv M lim
        (M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk spkPubCap spkPrivCap spkSigCap
            kpkKit.getBoxSize ++ evs_kpk ++
            p2Sub3PreTailEvents kpkKit.getBoxSize kpkPubCap kpkPrivCap kpkSigCap) st)
        P2Sub3TailAllocEnv) :
    stageP2Sub1To3KitsPlacedProp A lim ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 := by
  intro hkyber_nz hCode hfs hid_spk hspk_wf hid_kpk hkpk_wf
    hpc hrun hsp_eq hsp_align hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    hErrSpk hErrKpk hOk
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp_eq ▸ hsp_align
  have hstk_pure : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans (p2_pure_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc : allocHookStack ≤ stk :=
    Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc_split := p2_stackAt_split_of_le sp stk allocHookStack hstk_alloc hstk_lt
  refine p2_intro_spk_vt_placed hspkVt hCode ?_
  refine p2_intro_kpk_vt_placed hkpkVt hCode ?_
  refine weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_9_79 sp)) (by sep_focus) ?_
  have hsub1 := stageP2_sub1_kits_ext_placed (Qp := fun _ _ => False) ext hH hPure
    spkKit spkEnv hspkOk
    stk hstk_pure (Nat.le_trans (p2_spkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
    st s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
    preKeyStorePtr pkKit.pk_vt spkStorePtr kyberStorePtr kpkKit.kpk_vt
    baseKey signedPreKeyId b_4f1 hfits_sub1 hCode hpc hrun hsp_align_s hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  rw [hsp_eq] at hsub1
  refine p2_bind_sepWPp_cro_frame_state_nopanic hCode hsub1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 _hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx19_1, _, _, _, hx25_1, _, _, _, hx29_1, hvregs1, hCode1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hsp_align
  have hfs1 := hfs.of_steps hst01 (evs := []) (by rw [htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  sep_norm
  refine SepWPp.exists_elim fun spkFutPtr => SepWPp.pure_elim fun ⟨hx0_1, hx1_1, _, _⟩ => ?_
  refine weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_9_79 sp).symm) (by sep_focus) ?_
  refine weaken_frame
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_cells2_4f8_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  refine weaken_frame (p2_cells8_398_to_keyPair64UnalignedAt coroPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun c0_i => SepWPp.exists_elim fun c1_i =>
    SepWPp.exists_elim fun c2_i => SepWPp.exists_elim fun c3_i =>
    SepWPp.exists_elim fun c4_i => SepWPp.exists_elim fun c5_i =>
    SepWPp.exists_elim fun c6_i => SepWPp.exists_elim fun c63_i =>
    SepWPp.exists_elim fun cw0_i => SepWPp.exists_elim fun cw1_i =>
    SepWPp.exists_elim fun cw2_i => SepWPp.exists_elim fun cw3_i =>
    SepWPp.exists_elim fun cw4_i => SepWPp.exists_elim fun cw5_i =>
    SepWPp.exists_elim fun cw6_i => ?_
  refine weaken_frame (Entails.of_eq (p2_cells8_930_split_7_57 sp)) (by sep_focus) ?_
  refine weaken_frame (p2_memRegion7_to_bytes7At (sp + 0x930#64)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s6_b => ?_
  let Drop_vt : SepProp :=
    ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
    ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
    ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
    ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
    ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff)) ∗
    ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
    ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
    ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff))
  refine p2_sepWPp_frame_eq
    (stageP2_sub2_kits_ext_placed ext hH hPure
      spkKit spkEnv hspkOk kpkKit kpkEnv hkpkOk stk hstk_pure
      (Nat.le_trans (p2_spkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2)
      (Nat.le_trans (p2_kpkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
      (s0.readReg64 .x30) (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) s0 s1 _ Q (Qp := Qp)
      coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
      (coroPtr + 0x4f2#64) v_b0 u_90 u_b8 u_d0 u_4f8 u_500
      signedPreKeyId kyberPreKeyId stSpk
      s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i
      hfits_spk_poll
      (fun spkRec evs_spk spkPubCap spkPrivCap spkSigCap hrel hrec hevs hpub33 hpriv32 => by
        have hk := hfits_kpk_shim spkRec evs_spk spkPubCap spkPrivCap spkSigCap
          hrel hrec hevs hpub33 hpriv32
        simpa only [M.stepEvents_append] using hk)
      hCode1 (fun sm hst htrm => p2_envOk_spk hfs1 hst htrm) hid_spk hspk_wf hkyber_nz
      hpc1 hrun1 hsp1_align hvregs1 hx0_1 hx1_1 hx19_1 ?_ ?_)
    (by rw [hsp1]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
  · -- Arm 1: spkKit .error e at +0x0f38
    intro e evs_spk s2 hst12 hrel_spk hevs_spk hpc2 hrun2 hsp2 htr2_1
      hx19_2 hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ _ hvregs2 hCode2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine weaken_frame
      (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_errArm_budget A coroPtr)) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq hstk_alloc_split) (by sep_focus) ?_
    refine weaken_frame
      (p2_bytes7_937_to_cells8_930 sp s0_b s1_b s2_b s3_b s4_b s5_b s6_b) (by sep_focus) ?_
    refine weaken_frame
      (Entails.trans (p2_keyPair64UnalignedAt_to_memRegion (coroPtr + 0x398#64)
        c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i)
        (Entails.of_eq (ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide))))
      (by sep_focus) ?_
    refine weaken_frame
      (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
      (by sep_focus) ?_
    have harm1 := p2_arm1_err_hooks_placed_ok
      (st := M.stepEvents evs_spk (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st))
      (Qp := fun _ _ => False) hH hspkOk s0 s2
      sp coroPtr outPtr 0#64 8#64 spkStorePtr spkFutPtr ctxPtr
      v_b0 u_90 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 u_b8 ctxPtr u_d0
      signedPreKeyId b_2c0 b_390 b_4f2 e (by decide) hCode2 hsp2
      hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2 (hx25_2.trans hx25_1) hx26_2 hx27_2 hvregs2
    have hpool_arm1 :
        M.stepEvents (p2Arm1ErrEvents spkKit.getBoxSize 0#64)
          (M.stepEvents evs_spk (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st)) =
        M.stepEvents (p2Sub1To3Arm1Events spkKit.getBoxSize evs_spk) st := by
      dsimp only [p2Sub1To3Arm1Events]
      simp only [M.stepEvents_append]
    refine p2_finish_err_arm_drop_state (Drop := Drop_vt) harm1 (by sep_focus) ?_
      (fun sf P_f hst2f hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef, _⟩ =>
        hErrSpk e evs_spk spkFutPtr sf P_f
          (hst01.trans (hst12.trans hst2f)) hrel_spk hevs_spk
          hpcf hrunf (by rw [htrf, htr2_1, htr1])
          hspf hcsf hvregsf hCodef hent)
    intro sf
    dsimp only [Drop_vt]
    rw [hstk_alloc_split, hpool_arm1]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · -- Substage 2 .ok -> Substage 3: +0x1460 -> +0x0d5c or Arm 2 (+0x0998)
    intro spkRec spkPubBytes spkPrivBytes evs_spk
      spkPubCap spkPrivCap privPtr_2 spkSigCap _ kyberFutPtr
      b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
      w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
      s2 hst12 hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap
      hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
      hpub_words hpriv_words hkp_lo hkp_hi
      hpc2 hrun2 hsp2 htr2_1 hx0_2 hx1_2 _ _
      hx19_2 _ hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ hx29_2
      hvregs2 hCode2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hst02 : Steps (stageP1ProgPlaced ext) s s2 := hst01.trans hst12
    have hfs2 := p2_fsAt_step_spk signedPreKeyId (.ok spkRec) hfs1 hst12 htr2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine weaken_frame
      (Entails.of_eq (p2_keyPair64UnalignedAt_eq_bytes32_pair (coroPtr + 0x398#64)
        spkPubBytes spkPrivBytes
        b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
        w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
        hpub_words hpriv_words hkp_lo hkp_hi))
      (by sep_focus) ?_
    sep_norm
    refine weaken_frame
      (p2_bytes7_937_to_cells8_930 sp b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2)
      (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq (p2_cells4_3d8_eq coroPtr)) (by sep_focus) ?_
    sep_norm
    refine SepWPp.exists_elim fun u_3d8 => SepWPp.exists_elim fun u_3e0 =>
      SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 => ?_
    let st_sub2 :=
      M.stepEvents
        (evs_spk ++ p2Sub2TailEvents spkKit.getBoxSize
          spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat kpkKit.getBoxSize)
        (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st)
    have hst_sub2_eq :
        st_sub2 =
        M.stepEvents
          (p2Sub1To2OkEvents spkKit.getBoxSize evs_spk
            spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat kpkKit.getBoxSize) st := by
      dsimp only [st_sub2, p2Sub1To2OkEvents]
      simp only [M.stepEvents_append]
    refine p2_sepWPp_frame_eq
      (stageP2_sub3_kits_ext_placed ext hH hPure
        kpkKit kpkEnv hkpkOk stk hstk_pure
        (Nat.le_trans (p2_kpkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
        (s0.readReg64 .x30) st_sub2 s0 s2 _ Q (Qp := Qp)
        coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
        (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 spkFutPtr (0#64 + spkKit.getFutVtOff)
        spkSigCap u_a8 spkPrivCap ctxPtr privPtr_2
        u_3d8 u_3e0 u_3e8 u_3f0
        kyberPreKeyId 0#8 stKpk
        (by
          rw [hst_sub2_eq]
          exact hfits_kpk_poll spkRec evs_spk spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat
            hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap)
        (fun kpkRec evs_kpk hrel_kpk hrec_kpk hevs_kpk => by
          have hk := hfits_kem spkRec evs_spk spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat
            kpkRec evs_kpk hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap
            hrel_kpk hrec_kpk hevs_kpk
          rw [hst_sub2_eq]
          simpa only [M.stepEvents_append] using hk)
        (fun kpkRec evs_kpk kpkPubCap kpkPrivCap kpkSigCap
            hrel_kpk hrec_kpk hevs_kpk hpub1569 hpriv3169 => by
          have hk := hfits_tail spkRec evs_spk spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat
            kpkRec evs_kpk kpkPubCap kpkPrivCap kpkSigCap
            hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap
            hrel_kpk hrec_kpk hevs_kpk hpub1569 hpriv3169
          rw [hst_sub2_eq]
          simpa only [M.stepEvents_append] using hk)
        hkyber_nz hCode2 (fun sm hst htrm => p2_envOk_kpk hfs2 hst htrm) hid_kpk hkpk_wf
        hpc2 hrun2 hsp2_align hvregs2 hx0_2 hx1_2 hx19_2 hx21_2 hx23_2 hx26_2 hx27_2 ?_ ?_)
      (by rw [hsp2]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
    · -- Arm 2: kpkKit .error e at +0x0998
      intro e evs_kpk s3 hst23 hrel_kpk hevs_kpk hpc3 hrun3 hsp3 htr3_2
        hx19_3 hx21_3 hx23_3 hx25_3 hx26_3 hx27_3 _ _ hvregs3 hCode3
      try rw [hsp2] at hsp3
      try rw [hsp2]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hsp_align
      refine weaken_frame
        (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_errArm_budget A coroPtr)) (by sep_focus) ?_
      refine weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
      refine weaken_frame (Entails.of_eq hstk_alloc_split) (by sep_focus) ?_
      have h3d8_fold :
          ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ⊢
          cells (coroPtr + 0x3d8#64) 4 := by
        refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _)))) ?_
        rw [← ProofLib.memRegion_split' (b := coroPtr + 0x3e8#64) (n := 8) (k := 8)
              (b' := coroPtr + 0x3f0#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3e0#64) (n := 8) (k := 16)
              (b' := coroPtr + 0x3e8#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3d8#64) (n := 8) (k := 24)
              (b' := coroPtr + 0x3e0#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide)]
        exact Entails.refl _
      refine weaken_frame h3d8_fold (by sep_focus) ?_
      refine weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      have harm2 := p2_arm2_err_hooks_placed_ok (st := M.stepEvents evs_kpk st_sub2)
        (Qp := fun _ _ => False) hH hkpkOk s0 s3
        sp coroPtr outPtr 0#64 8#64 kyberStorePtr kyberFutPtr ctxPtr
        v_b0 spkSigCap (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 spkPrivCap
        ctxPtr privPtr_2
        kyberPreKeyId b_2c0 b_390 0#8 b_4f2 e (by decide) hCode3 hsp3
        hpc3 hrun3 hsp3_align hx19_3 hx21_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1]) hx26_3 hx27_3 hvregs3
      have hpool_arm2 :
          M.stepEvents (p2Arm2ErrEvents kpkKit.getBoxSize 0#64)
            (M.stepEvents evs_kpk st_sub2) =
          M.stepEvents
            (p2Sub1To3Arm2Events spkKit.getBoxSize evs_spk spkPubCap.toNat spkPrivCap.toNat
              spkSigCap.toNat kpkKit.getBoxSize evs_kpk) st := by
        rw [hst_sub2_eq]
        dsimp only [p2Sub1To3Arm2Events]
        simp only [M.stepEvents_append]
      refine p2_finish_err_arm_drop_state (Drop := Drop_vt) harm2 (by sep_focus) ?_
        (fun sf P_f hst3f hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef, _⟩ =>
          hErrKpk spkRec spkPubBytes spkPrivBytes evs_spk spkPubCap spkPrivCap spkSigCap
            e evs_kpk kyberFutPtr sf P_f
            (hst02.trans (hst23.trans hst3f))
            hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap
            hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
            hrel_kpk hevs_kpk
            hpcf hrunf (by rw [htrf, htr3_2, htr2_1, htr1])
            hspf hcsf hvregsf hCodef hent)
      intro sf
      dsimp only [Drop_vt]
      rw [hstk_alloc_split, hpool_arm2]
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    · -- Substage 3 .ok -> hOk at +0x0d5c
      intro kpkRec kyberPubBytes kyberPrivBytes evs_kpk evs_drop
        pkBuf skBuf kpkPubCap v90_3 privCap_3 privPtr_3 s3
        hst23 hrel_kpk hrec_kpk hevs_kpk hfree_drop hkpk_pub_cap hkpk_priv_cap
        hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3 htr3_2
        hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
        hvregs3 hCode3
      try rw [hsp2] at hsp3
      try rw [hsp2] at hx28_3
      try rw [hsp2]
      have hst03 : Steps (stageP1ProgPlaced ext) s s3 := hst02.trans hst23
      have hfs3 := p2_fsAt_step_kpk kyberPreKeyId (.ok kpkRec) hfs2 hst23 htr3_2
      refine weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      refine p2_drop_frame_mid (Drop := Drop_vt) (by dsimp only [Drop_vt]; sep_focus) ?_
      have hpool_ok :
          M.stepEvents
            (evs_kpk ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
              kpkPubCap.toNat privCap_3.toNat v90_3.toNat evs_drop) st_sub2 =
          M.stepEvents
            (p2Sub1To3OkEvents spkKit.getBoxSize evs_spk
              spkPubCap.toNat spkPrivCap.toNat spkSigCap.toNat kpkKit.getBoxSize
              evs_kpk kpkPubCap.toNat privCap_3.toNat v90_3.toNat evs_drop) st := by
        rw [hst_sub2_eq]
        dsimp only [p2Sub1To3OkEvents]
        simp only [M.stepEvents_append]
      rw [hpool_ok]
      have hok := hOk spkRec spkPubBytes spkPrivBytes evs_spk spkPubCap spkPrivCap spkSigCap
        kpkRec kyberPubBytes kyberPrivBytes evs_kpk evs_drop
        pkBuf skBuf kyberFutPtr kpkPubCap v90_3 privCap_3 privPtr_3 s3
        hst03 hfs3 hrel_spk hrec_spk hevs_spk hspk_pub_cap hspk_priv_cap
        hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
        hrel_kpk hrec_kpk hevs_kpk hfree_drop hkpk_pub_cap hkpk_priv_cap
        hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3
        (by rw [htr3_2, htr2_1, htr1])
        hx19_3 hx21_3 hx22_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1])
        hx26_3 hx27_3 hx28_3
        (by rw [hx29_3, hx29_2, hx29_1])
        hvregs3 hCode3
      exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub1_to_3_kits_4k_placed := @stageP2_sub1_to_3_kits_ext_placed
abbrev stageP2_sub1_to_3_kits_hooks_placed := @stageP2_sub1_to_3_kits_ext_placed

abbrev stageP2_sub1_to_3_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub1_to_3_kits_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH hPure.to_4K

theorem stageP2_sub1_to_3_kits_seqEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits : FitsEnv M lim st
      (P2Sub1To3SeqEnv spkKit spkEnv stSpk signedPreKeyId kpkKit kpkEnv stKpk kyberPreKeyId)) :
    stageP2Sub1To3KitsPlacedProp A lim ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 :=
  have h1 : P2Sub1Env spkKit.getBoxSize (p2Sub1Events spkKit.getBoxSize) := rfl
  have h4 : BoxAllocEnv kpkKit.getBoxSize (boxAllocEvents kpkKit.getBoxSize) :=
    (boxAllocEnv_iff_eq kpkKit.getBoxSize _).mpr rfl
  have h6 := freeOnlyEvs_rustDeallocEvents kpkKit.getBoxSize 8
  have h7 : KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents := rfl
  stageP2_sub1_to_3_kits_ext_placed ext hH hPure skit
    spkKit spkEnv hspkVt hspkOk kpkKit kpkEnv hkpkVt hkpkOk pkKit
    stk hstk_p2 hstk_lt st s0 s Frame Q (Qp := Qp)
    sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
    v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
    stSpk stKpk b_2c0 b_390 b_4f1 b_4f2
    hfits.seq_left (hfits.seq_right h1).seq_left
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ _ hevs_spk _ _ => by
      simpa only [M.stepEvents_append] using
        (((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ _ hevs_spk _ _ => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, M.stepEvents_append] using
        ((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ evs_kpk
        _ _ hevs_spk _ _ _ _ hevs_kpk => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, M.stepEvents_append] using
        ((((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_right hevs_kpk).seq_right h6).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ evs_kpk kpkPubCap kpkPrivCap kpkSigCap
        _ _ hevs_spk _ _ _ _ hevs_kpk _ _ => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, p2Sub3PreTailEvents,
        M.stepEvents_append] using
        (((((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_right hevs_kpk).seq_right h6).seq_right h7).seq_right
          (p2KpkVecFreeEvents_freeOnly kpkPubCap kpkPrivCap kpkSigCap))

abbrev stageP2_sub1_to_3_kits_seqEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub1_to_3_kits_seqEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH hPure.to_4K

/-- `P2Sub1To3ThenEnv` specialization of `stageP2_sub1_to_3_kits_ext_placed` for callers composing
Substages P2.1–P2.3 with a post-`+0x0d5c` continuation envelope `TailEnv` (pair with
`fitsEnv_tail_of_p2Sub1To3ThenEnv` inside `hOk`). -/
theorem stageP2_sub1_to_3_kits_thenEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {TailEnv : List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hfits : FitsEnv M lim st
      (P2Sub1To3ThenEnv spkKit spkEnv stSpk signedPreKeyId kpkKit kpkEnv stKpk kyberPreKeyId
        TailEnv)) :
    stageP2Sub1To3KitsPlacedProp A lim ext skit spkKit spkEnv kpkKit kpkEnv pkKit
      stk st s0 s Frame Q Qp
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
      stSpk stKpk b_2c0 b_390 b_4f1 b_4f2 :=
  have h1 : P2Sub1Env spkKit.getBoxSize (p2Sub1Events spkKit.getBoxSize) := rfl
  have h4 : BoxAllocEnv kpkKit.getBoxSize (boxAllocEvents kpkKit.getBoxSize) :=
    (boxAllocEnv_iff_eq kpkKit.getBoxSize _).mpr rfl
  have h6 := freeOnlyEvs_rustDeallocEvents kpkKit.getBoxSize 8
  have h7 : KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents := rfl
  stageP2_sub1_to_3_kits_ext_placed ext hH hPure skit
    spkKit spkEnv hspkVt hspkOk kpkKit kpkEnv hkpkVt hkpkOk pkKit
    stk hstk_p2 hstk_lt st s0 s Frame Q (Qp := Qp)
    sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
    v_b0 u_90 u_a8 u_b8 u_d0 baseKey signedPreKeyId kyberPreKeyId
    stSpk stKpk b_2c0 b_390 b_4f1 b_4f2
    hfits.seq_left (hfits.seq_right h1).seq_left
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ _ hevs_spk _ _ => by
      simpa only [M.stepEvents_append] using
        (((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ _ hevs_spk _ _ => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, M.stepEvents_append] using
        ((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ evs_kpk
        _ _ hevs_spk _ _ _ _ hevs_kpk => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, M.stepEvents_append] using
        ((((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_right hevs_kpk).seq_right h6).seq_left)
    (fun _ evs_spk spkPubCap spkPrivCap spkSigCap _ evs_kpk kpkPubCap kpkPrivCap kpkSigCap
        _ _ hevs_spk _ _ _ _ hevs_kpk _ _ => by
      simpa only [p2Sub1To2OkEvents, p2Sub2TailEvents, p2Sub3PreTailEvents,
        M.stepEvents_append] using
        ((((((((hfits.seq_right h1).seq_right hevs_spk).seq_right
          (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize spkPubCap spkPrivCap spkSigCap)).seq_right
          h4).seq_right hevs_kpk).seq_right h6).seq_right h7).seq_right
          (p2KpkVecFreeEvents_freeOnly kpkPubCap kpkPrivCap kpkSigCap)).seq_left)

abbrev stageP2_sub1_to_3_kits_thenEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {TailEnv : List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub1_to_3_kits_thenEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv TailEnv
    ext hH hPure.to_4K

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudget
