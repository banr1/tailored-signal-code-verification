/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Stage 3 KEM Ciphertext Boxing and Serialization (`0x0fb4 → 0x1044`)

Verifies `derive_keys_a_placed_ok` on `initProgPlaced` over `RustCliAllocBudget M` and
`VmPreserved`, boxing `ss` and `ct`, calling `<kem::Ciphertext>::serialize` (block `71`), freeing
`ctBoxPtr`, and advancing the cost-model state by `deriveKeysAEvents`.
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
open CryptoVerification.E2E (PreKeyBundleFields initiateKemCoins)
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8 pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName tryCloneFromRefStack)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced coinsCursorAtPlaced initEntryPlaced initPcPlaced initProgPlaced
   stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (dhLenWord dhPrefix dhRemAt memRegion_merge_at pointsToBytes_entails_memRegion_len
   sepWPp_conseq_oom sepWPp_exists_elim_oom sepWPp_pure_elim_oom sep_replace stackAt_sub_split_init)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget (kemCiphertextSerializeSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced kemCtSerialize_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (rustLay1568 s3_call_alloc_placed s3_call_placed s3_dealloc_placed s3_memcpy_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1PlacedBudget
  (deriveKeysA1Events derive_keys_a1_placed_nonnull_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-- Allocation prefix of `deriveKeysAEvents` prior to `__rust_dealloc(ctBoxPtr, 1568, 1)`. -/
def deriveKeysAAllocPrefixEvents : List AllocEvent :=
  deriveKeysA1Events ++ rustAllocEvents 1568 1 ++ rustAllocEvents 1569 1

/-- Complete heap `AllocEvent` trace across `0x0fb4 → 0x1044`. -/
def deriveKeysAEvents : List AllocEvent :=
  deriveKeysAAllocPrefixEvents ++ rustDeallocEvents 1568 1

theorem stepEvents_deriveKeysAEvents (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (rustDeallocEvents 1568 1)
      (M.stepEvents (rustAllocEvents 1569 1)
        (M.stepEvents (rustAllocEvents 1568 1)
          (M.stepEvents deriveKeysA1Events st))) =
      M.stepEvents deriveKeysAEvents st := by
  unfold deriveKeysAEvents deriveKeysAAllocPrefixEvents
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]

theorem fitsEvents_deriveKeysAAllocPrefix_of_full {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (hFit : FitsEvents M lim st deriveKeysAEvents) :
    FitsEvents M lim st deriveKeysAAllocPrefixEvents :=
  ((fitsEvents_append M lim deriveKeysAAllocPrefixEvents (rustDeallocEvents 1568 1) st).mp hFit).1

private theorem fitsEvents_deriveKeysAAllocPrefix_elim {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (hFit : FitsEvents M lim st deriveKeysAAllocPrefixEvents) :
    FitsEvents M lim st deriveKeysA1Events ∧
      FitsEvents M lim (M.stepEvents deriveKeysA1Events st) (rustAllocEvents 1568 1) ∧
      FitsEvents M lim
        (M.stepEvents (rustAllocEvents 1568 1) (M.stepEvents deriveKeysA1Events st))
        (rustAllocEvents 1569 1) := by
  unfold deriveKeysAAllocPrefixEvents at hFit
  rcases (fitsEvents_append M lim
    (deriveKeysA1Events ++ rustAllocEvents 1568 1) (rustAllocEvents 1569 1) st).mp hFit with
      ⟨hFit12, hFit1569⟩
  rcases (fitsEvents_append M lim
    deriveKeysA1Events (rustAllocEvents 1568 1) st).mp hFit12 with ⟨hFitA1, hFit1568⟩
  rw [M.stepEvents_append deriveKeysA1Events (rustAllocEvents 1568 1) st] at hFit1569
  exact ⟨hFitA1, hFit1568, hFit1569⟩

private theorem ct1568_split_hdr (p : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 1568) :
    (p ↦ₛ bs) ⊢
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗ memRegion (p + 16#64) 1552 := by
  refine Entails.trans (pointsToBytes_entails_memRegion_len h) ?_
  rw [← memRegion_merge_at p 8 1560 (p + 8#64) (by clear * -; bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 1552 (p + 16#64) (by clear * -; bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem s3_step_1030_1044_vm_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {s : State}
    (kemCtPtr ctBoxPtr ssBoxPtr g60 g68 : BitVec 64) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0x1030)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kemCtPtr)
    (hx1 : s.readReg64 .x1 = 1569#64)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx25 : s.readReg64 (.gpr 25#5) = ctBoxPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = ssBoxPtr) :
    SepWP (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      s (((s.sp + 0x60#64) ↦₆₄ g60) ∗ ((s.sp + 0x68#64) ↦₆₄ g68) ∗ G)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 1569#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 0x1044 ∧
        (sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
          sm.readReg64 .x2 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64 ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)) := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
  try simp only [arm64_norm, wp_norm] at hx0 hx1 hx20 hx21 hx25 hx26
  by_vm_steps (
    wp_steps
    exact s3_done_call_vm (by wp_norm_lhs)
      (by (try simp only [hx0, hx1, arm64_norm, wp_norm]); sep_frame)
      ⟨by simp only [hx25, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
       by simp only [hx26, arm64_norm, wp_norm]⟩
      (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
      (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))

set_option maxHeartbeats 1600000 in
/-- Core budget-threaded KEM `ss`/`ct` boxing and serialization (`0x0fb4 → 0x1044`), exposing `ssBoxPtr ≠ 0#64` and `kemCtPtr ≠ 0#64`. -/
theorem derive_keys_a_placed_core_nonnull_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKemCt : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 71)
      (withLsCodeRoLoaded lsmpl (kemCiphertextSerializeSpec M A lim)))
    (hFit : FitsEvents M lim st deriveKeysAAllocPrefixEvents)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      ssBoxPtr ≠ 0#64 →
      kemCtPtr ≠ 0#64 →
      InInitiatePlaced s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents deriveKeysAEvents st) sg ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗
          ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
          A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf0
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sf0 ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  rcases fitsEvents_deriveKeysAAllocPrefix_elim hFit with ⟨hFitA1, hFit1568, hFit1569⟩
  refine derive_keys_a1_placed_nonnull_ok hh hFitA1 hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr hssNonNull hc8 htr8 hx20_8 hx21_8 hx26_8 => ?_
  try dsimp only at hx20_8 hx21_8 ⊢
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
  let st1 := M.stepEvents deriveKeysA1Events st
  let st2 := M.stepEvents (rustAllocEvents 1568 1) st1
  let st3 := M.stepEvents (rustAllocEvents 1569 1) st2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  obtain ⟨_, _, hfsp8⟩ := hc8.step_ctx fsp
  refine' s3_block_to_call_vm_placed hh
    (lsρ lsRustAllocSymCli)
    0x1004 (Φ := fun sm =>
      sm.readReg64 .x0 = 1568#64 ∧ sm.readReg64 .x1 = 1#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 26#5) = ssBoxPtr)
    hc8 ?_ ?_; rotate_left 1
  · have hpc : s8.pc = (blkPl_521).base + 0xff8#64 := hc8.pc; have hrun := hc8.run
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
    (try dsimp only [fsp] at *); rw [← hc8.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20_8 hx21_8 hx26_8
    by_vm_steps (
      wp_steps
      refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20_8, arm64_norm, wp_norm],
         by simp only [hx21_8, arm64_norm, wp_norm],
         by simp only [hx26_8, arm64_norm, wp_norm]⟩
        (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
        (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
  · intro sm9 hvm9 hc9 hp9 hl9 ht9 ⟨hx0_9, hx1_9, hx20_9, hx21_9, hx26_9⟩
    have hpool9 : A.pool lim st1 s8 = A.pool lim st1 sm9 :=
      (A.pool_transport lim st1 s8 sm9 hvm9).symm
    rw [hc8.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr9 := ht9.trans htr8
    refine s3_call_alloc_placed hh 1568 st1 _ hc9 hp9 hl9
      (by rw [hx0_9]; decide) (by rw [hx1_9]; decide) rustLay1568 hFit1568
      (by dsimp only [st1] at hpool9 ⊢
          rw [hpool9, hc9.sp]; (try dsimp only [fsp]); sep_frame) ?_
    intro s10 hc10 hcs10 hctNonNull _ htr_10
    set ctBoxPtr := s10.readReg64 .x0
    rw [hc9.sp]
    have htr10 := htr_10.trans htr9
    have hx20_10 := hcs10.2.1.trans hx20_9; have hx21_10 := hcs10.2.2.1.trans hx21_9
    have hx26_10 := hcs10.2.2.2.2.2.2.2.1.trans hx26_9
    obtain ⟨_, _, hfsp10⟩ := hc10.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh
      (lsρ memcpyName)
      0x101c (Φ := fun sm =>
        sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
        sm.readReg64 .x2 = 1568#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = 1568#64 ∧
        sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
        sm.readReg64 (.gpr 26#5) = ssBoxPtr)
      hc10 ?_ ?_; rotate_left 1
    · have hpc : s10.pc = (blkPl_521).base + 0x1004#64 := hc10.pc; have hrun := hc10.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
      have hnz10 : s10.readReg64 (.gpr 0#5) ≠ 0#64 := by
        simpa only [ctBoxPtr, arm64_norm, wp_norm] using hctNonNull
      (try dsimp only [fsp] at *); rw [← hc10.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_10 hx21_10 hx26_10
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [ctBoxPtr, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_10, arm64_norm, wp_norm],
           by simp only [hx21_10, arm64_norm, wp_norm],
           by wp_norm_goal, by simp only [ctBoxPtr, arm64_norm, wp_norm],
           by simp only [hx26_10, arm64_norm, wp_norm]⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sm11 hvm11 hc11 hp11 hl11 ht11
        ⟨hx0_11, hx1_11, hx2_11, hx20_11, hx21_11, hx22_11, hx25_11, hx26_11⟩
      have hpool11 : A.pool lim st2 s10 = A.pool lim st2 sm11 :=
        (A.pool_transport lim st2 s10 sm11 hvm11).symm
      rw [hc10.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr11 := ht11.trans htr10
      refine s3_memcpy_pool_placed hh ctBoxPtr (fsp + 0xfe0#64) ct.toList st2 _
        hc11 htr11 hp11 hl11 hx0_11 hx1_11 (by rw [hx2_11, hct_len]; decide) hpanic
        (by dsimp only [st2, st1] at hpool11 ⊢
            rw [hpool11, hc11.sp, hct_len]; (try dsimp only [fsp]); sep_frame) ?_
      intro s12 hc12 hcs12 _ htr_12
      rw [hc11.sp]
      have htr12 := htr_12.trans htr11
      have hx20_12 := hcs12.2.1.trans hx20_11
      have hx21_12 := hcs12.2.2.1.trans hx21_11
      have hx22_12 := hcs12.2.2.2.1.trans hx22_11
      have hx25_12 := hcs12.2.2.2.2.2.2.1.trans hx25_11
      have hx26_12 := hcs12.2.2.2.2.2.2.2.1.trans hx26_11
      have hhdr := ct1568_split_hdr (fsp + 0x1600#64) hct_len
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr
      refine sepWPp_conseq_oom
        (by dsimp only [fsp, ct] at hhdr ⊢; exact sep_replace hhdr (by sep_frame) (Entails.refl _)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun h0 => sepWPp_exists_elim_oom fun h1 => ?_
      obtain ⟨_, _, hfsp12⟩ := hc12.step_ctx fsp
      refine' s3_block_to_call_vm_placed hh
        (lsmpl.base 71)
        0x1030 (Φ := fun sm =>
          sm.readReg64 .x0 = fsp + 0x1600#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)
        hc12 ?_ ?_; rotate_left 1
      · have hpc : s12.pc = (blkPl_521).base + 0x101c#64 := hc12.pc; have hrun := hc12.run
        dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
        (try dsimp only [fsp] at *); rw [← hc12.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_12 hx21_12 hx22_12 hx25_12 hx26_12
        by_vm_steps (
          wp_steps
          refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal,
             by simp only [hx20_12, arm64_norm, wp_norm],
             by simp only [hx21_12, arm64_norm, wp_norm],
             by simp only [hx25_12, arm64_norm, wp_norm],
             by simp only [hx26_12, arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
      · intro sm13 hvm13 hc13 hp13 hl13 ht13 ⟨hx0_13, hx20_13, hx21_13, hx25_13, hx26_13⟩
        have hpool13 : A.pool lim st2 s12 = A.pool lim st2 sm13 :=
          (A.pool_transport lim st2 s12 sm13 hvm13).symm
        rw [hc12.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
        have htr13 := ht13.trans htr12
        have hstk_clone :
            memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                (pqxdhEntryStack - extHookStack) ∗ stackAt fsp extHookStack =
              memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                (pqxdhEntryStack - tryCloneFromRefStack) ∗
                stackAt fsp tryCloneFromRefStack := by
          rw [← hstk_ext, stackAt_sub_split_init fsp
            (by decide : tryCloneFromRefStack ≤ pqxdhEntryStack) (by decide)]
        refine s3_call_placed hh hKemCt
          ((fsp + 0x1600#64, ctBoxPtr, ct.toList), st2) _
          hc13 htr13 hp13 hl13 hpanic
          (by
            have hx25_raw := hx25_12; conv at hx25_raw => lhs; simp only [arm64_norm, wp_norm]
            have hx22_raw := hx22_12; conv at hx22_raw => lhs; simp only [arm64_norm, wp_norm]
            simp only [kemCiphertextSerializeSpec, hc13.sp, hx25_12, hx22_12, hx25_raw, hx22_raw,
              BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            refine Entails.pure_right ⟨hx0_13, hct_len, hFit1569⟩ ?_
            dsimp only [fsp, ct, ctBoxPtr, t, st2, st1] at hstk_clone hpool13 ⊢
            rw [hpool13]
            refine sep_replace (Entails.of_eq hstk_clone) (by sep_frame) ?_
            sep_frame) ?_ ?_ ?_ ?_
        · intro _ _ h; simp [kemCiphertextSerializeSpec, Spec.onPanic] at h
        · intro _ _ _ h; simp [kemCiphertextSerializeSpec, Spec.onExit] at h
        · intro _ _ h; simp [kemCiphertextSerializeSpec, Spec.onOom] at h
        · intro s14 _ _ _ hcs14 _ hof14
          simp only [kemCiphertextSerializeSpec, hc13.sp, BitVec.add_assoc,
            BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
          refine sepWPp_exists_elim_oom fun kemCtPtr => ?_
          refine sepWPp_pure_elim_oom fun ⟨htr_14, hx0_14, hx1_14, hkemNonNull⟩ => ?_
          have hc14 := hof14 htr_14
          have htr14 := htr_14.trans htr13
          have hx20_14 := hcs14.2.1.trans hx20_13
          have hx21_14 := hcs14.2.2.1.trans hx21_13
          have hx25_14 := hcs14.2.2.2.2.2.2.1.trans hx25_13
          have hx26_14 := hcs14.2.2.2.2.2.2.2.1.trans hx26_13
          have hstk_back_ext :
              memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                  (pqxdhEntryStack - tryCloneFromRefStack) ∗
                  stackAt fsp tryCloneFromRefStack =
                memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                  (pqxdhEntryStack - extHookStack) ∗ stackAt fsp extHookStack :=
            hstk_clone.symm
          refine sepWPp_conseq_oom
            (show _ ⊢ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗ _ by
              dsimp only [fsp]; sep_frame) ?_
          rw [ProofLib.memRegion_eight (fsp + 0x60#64),
              ProofLib.memRegion_eight (fsp + 0x68#64)]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          refine sepWPp_exists_elim_oom fun g60 =>
            sepWPp_exists_elim_oom fun g68 => ?_
          obtain ⟨halign14, _, hfsp14⟩ := hc14.step_ctx fsp
          refine' s3_block_to_call_vm_placed hh
            (lsρ lsRustDeallocSymCli)
            0x1044 (Φ := fun sm =>
              sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
              sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 26#5) = ssBoxPtr)
            hc14 ?_ ?_; rotate_left 1
          · have hpc : s14.pc = (blkPl_521).base + BitVec.ofNat 64 0x1030 := hc14.pc
            rw [hfsp14]
            exact s3_step_1030_1044_vm_placed kemCtPtr ctBoxPtr ssBoxPtr _ _ _ halign14 hpc hc14.run
              hx0_14 hx1_14 (by rwa [← hfsp14]) (by rwa [← hfsp14]) hx25_14 hx26_14
          · intro sm15 hvm15 hc15 hp15 hl15 ht15
              ⟨hx0_15, hx1_15, hx2_15, hx20_15, hx21_15, hx26_15⟩
            rw [← hfsp14] at *
            have hpool15 : A.pool lim st3 s14 = A.pool lim st3 sm15 :=
              (A.pool_transport lim st3 s14 sm15 hvm15).symm
            have htr15 := ht15.trans htr14
            have hbox_mem := pointsToBytes_entails_memRegion_len (a := ctBoxPtr) hct_len
            have hmid_collapse :
                ((fsp + 0xfe0#64) ↦ₛ ct.toList) ∗
                  ((fsp + 0x1600#64) ↦₆₄ ctBoxPtr) ∗ ((fsp + 0x1608#64) ↦₆₄ 1568#64) ∗
                  memRegion (fsp + 0x1610#64) 1552 ∗ memRegion (fsp + 0x1c20#64) 64 ⊢
                  memRegion (fsp + 0xfe0#64) 0xc80 := by
              refine Entails.trans
                (sepConj_mono (pointsToBytes_entails_memRegion_len hct_len)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (Entails.refl _)))) ?_
              rw [memRegion_merge_at (fsp + 0x1610#64) 1552 64 (fsp + 0x1c20#64)
                    (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x1608#64) 8 1616 (fsp + 0x1610#64)
                    (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0x1600#64) 8 1624 (fsp + 0x1608#64)
                    (by clear * -; bv_omega) (by decide),
                  memRegion_merge_at (fsp + 0xfe0#64) 1568 1632 (fsp + 0x1600#64)
                    (by clear * -; bv_omega) (by decide)]
              exact Entails.refl _
            refine s3_dealloc_placed hh ctBoxPtr 1568 st3 _
              hc15 hp15 hl15 hx0_15 (by rw [hx1_15]; decide) (by rw [hx2_15]; decide) rustLay1568
              (by rw [hc15.sp]
                  dsimp only [fsp, ct, st3, st2, st1] at hstk_back_ext hbox_mem hpool15 ⊢
                  rw [hpool15]
                  refine sep_replace hbox_mem (by sep_frame) ?_
                  exact sep_replace (Entails.of_eq hstk_back_ext) (by sep_frame) (by sep_frame)) ?_
            intro sg hcg hcsg htr_g
            rw [hc15.sp]
            refine sepWPp_conseq_oom ?_
              (hnext sg ssBoxPtr kemCtPtr hssNonNull hkemNonNull hcg (htr_g.trans htr15)
                (hcsg.2.1.trans hx20_15) (hcsg.2.2.1.trans hx21_15)
                (hcsg.2.2.2.2.2.2.2.1.trans hx26_15))
            dsimp only [fsp, ct, ss, st3, st2, st1] at hstk_ext hmid_collapse ⊢
            rw [stepEvents_deriveKeysAEvents M st]
            refine sep_replace hmid_collapse (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hstk_ext.symm) (by sep_frame) (by sep_frame)

/-- Discharges block `71` directly from `hh` via `kemCtSerialize_cli_placed_ok`. -/
theorem derive_keys_a_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim st deriveKeysAAllocPrefixEvents)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      InInitiatePlaced s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents deriveKeysAEvents st) sg ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗
          ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
          A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf0
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sf0 ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  derive_keys_a_placed_core_nonnull_ok hh (kemCtSerialize_cli_placed_ok mmpl gh W hh) hFit hpanic
    hctrl htr hx20 hx21 fun sg ssBoxPtr kemCtPtr _ hkemNonNull hcg htrg hx20g hx21g hx26g =>
      hnext sg ssBoxPtr kemCtPtr hkemNonNull hcg htrg hx20g hx21g hx26g

/-- Budget-threaded KEM `ss`/`ct` boxing and `<kem::Ciphertext>::serialize` (`0x0fb4 → 0x1044`). -/
theorem derive_keys_a_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st deriveKeysAEvents)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      InInitiatePlaced s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents deriveKeysAEvents st) sg ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗
          ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
          A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf0
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st sf0 ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  derive_keys_a_placed_core_nonnull_ok hh hLocal.kemCtSerialize
    (fitsEvents_deriveKeysAAllocPrefix_of_full hFit) hpanic hctrl htr hx20 hx21
    fun sg ssBoxPtr kemCtPtr _ hkemNonNull hcg htrg hx20g hx21g hx26g =>
      hnext sg ssBoxPtr kemCtPtr hkemNonNull hcg htrg hx20g hx21g hx26g

theorem derive_keys_a_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim (M.stepEvents evs_pre st0) deriveKeysAEvents)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      InInitiatePlaced s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents (evs_pre ++ deriveKeysAEvents) st0) sg ∗
          stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗
          ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
          A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ (8#8 :: ct.toList)) ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf0
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim (M.stepEvents evs_pre st0) sf0 ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  refine derive_keys_a_placed_ok hh hLocal hFit hpanic hctrl htr hx20 hx21
    fun sg ssBoxPtr kemCtPtr hkemNonNull hcg htrg hx20g hx21g hx26g => ?_
  rw [← M.stepEvents_append evs_pre deriveKeysAEvents st0]
  exact hnext sg ssBoxPtr kemCtPtr hkemNonNull hcg htrg hx20g hx21g hx26g

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlacedBudget
