/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Stage 3 KEM Shared-Secret Boxing (`0x0fb4 → 0x0ff8`)

Verifies `derive_keys_a1_placed_ok` on `initProgPlaced` over `RustCliAllocBudget M` and
`VmPreserved`, advancing the cost-model state by `deriveKeysA1Events = rustAllocEvents 32 1`.
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
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (PreKeyBundleFields initiateKemCoins)
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8 pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced coinsCursorAtPlaced initEntryPlaced initPcPlaced initProgPlaced
   stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (bytes32_exists_cells4 cells4_to_memRegion32 dhLenWord dhPrefix dhRemAt memRegion32_cells4
   memRegion_merge_at pointsToBytes_entails_memRegion_len sepWPp_conseq_oom sepWPp_exists_elim_oom
   sep_replace stackAt_sub_split_init)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1PlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (rustLay32 s3_call_alloc_placed s3_memcpy_pool_placed s3_shim_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-- Heap `AllocEvent` trace across `0x0fb4 → 0x0ff8` (`rustAllocEvents 32 1` for `ssBoxPtr`). -/
def deriveKeysA1Events : List AllocEvent := rustAllocEvents 32 1

theorem fitsEvents_deriveKeysA1Events_of_alloc32 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (hFit : FitsEvents M lim st (rustAllocEvents 32 1)) :
    FitsEvents M lim st deriveKeysA1Events :=
  hFit

set_option maxHeartbeats 1200000 in
/-- Budget-threaded KEM `ss` boxing (`0x0fb4 → 0x0ff8`), exposing `ssBoxPtr ≠ 0#64`. -/
theorem derive_keys_a1_placed_nonnull_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim st deriveKeysA1Events)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (s8 : State) (ssBoxPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      ssBoxPtr ≠ 0#64 →
      InInitiatePlaced s0 s8 0xff8 → s8.trace = s0.trace →
      s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s8.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s8
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents deriveKeysA1Events st) s8 ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
          stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          memRegion (fsp + 0x1c20#64) 64 ∗
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
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hss_len : ss.toList.length = 32 := ss.toList_length
  obtain ⟨ss0, ss1, ss2, ss3, hss_cells⟩ := bytes32_exists_cells4 hss_len
  have hfe0_1568 :
      ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗ memRegion (fsp + 0x1000#64) 0x600 ⊢
        memRegion (fsp + 0xfe0#64) 1568 := by
    refine Entails.trans
      (sepConj_mono_left (pointsToBytes_entails_memRegion_len (initiateKemCoins t).toList_length)) ?_
    rw [memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64) (by clear * -; bv_omega) (by decide)]
    exact Entails.refl _
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  refine sepWPp_conseq_oom (by
    rw [hstk_ext]
    exact sep_replace hfe0_1568 (by sep_frame) (Entails.refl _)) ?_
  obtain ⟨_, _, hfsp0⟩ := hctrl.step_ctx fsp
  refine' s3_block_to_call_vm_placed hh
    (lsρ memcpyName)
    0xfc8 (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0xfe0#64 ∧ sm.readReg64 .x1 = fsp + 0x1600#64 ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : sf0.pc = (blkPl_521).base + 0xfb4#64 := hctrl.pc; have hrun := hctrl.run
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21
    by_vm_steps (
      wp_steps
      refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
        (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
        (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
  · intro sm1 hvm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1⟩
    have hpool1 : A.pool lim st sf0 = A.pool lim st sm1 :=
      (A.pool_transport lim st sf0 sm1 hvm1).symm
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr1 := ht1.trans htr
    refine s3_memcpy_pool_placed hh (fsp + 0xfe0#64) (fsp + 0x1600#64) ct.toList st _
      hc1 htr1 hp1 hl1 hx0_1 hx1_1 (by rw [hx2_1, hct_len]; decide) hpanic
      (by rw [hpool1, hc1.sp, hct_len]; (try dsimp only [fsp]); sep_frame) ?_
    intro s2 hc2 hcs2 _ htr_2
    rw [hc1.sp]
    have htr2 := htr_2.trans htr1
    have hx20_2 := hcs2.2.1.trans hx20_1; have hx21_2 := hcs2.2.2.1.trans hx21_1
    rw [hss_cells (fsp + 0x1c20#64), memRegion32_cells4 (fsp + 0x1c40#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun t0 => sepWPp_exists_elim_oom fun t1 =>
      sepWPp_exists_elim_oom fun t2 => sepWPp_exists_elim_oom fun t3 => ?_
    obtain ⟨halign2, hx29_2, hfsp2⟩ := hc2.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh
      (lsρ lsRustNoAllocShimSymCli)
      0xfd8 (Φ := fun sm =>
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hc2 ?_ ?_; rotate_left 1
    · have hpc : s2.pc = (blkPl_521).base + 0xfc8#64 := hc2.pc; have hrun := hc2.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
      (try dsimp only [fsp] at *); rw [← hc2.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm]⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sm3 hvm3 hc3 hp3 hl3 ht3 ⟨hx20_3, hx21_3⟩
      have hpool3 : A.pool lim st s2 = A.pool lim st sm3 :=
        (A.pool_transport lim st s2 sm3 hvm3).symm
      rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr3 := ht3.trans htr2
      refine s3_shim_pool_placed hh st _ hc3 htr3 hp3 hl3 hpanic
        (by rw [hpool3, hc3.sp]; (try dsimp only [fsp]); sep_frame) ?_
      intro s4 hc4 hcs4 htr_4
      rw [hc3.sp]
      have htr4 := htr_4.trans htr3
      have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
      obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
      refine' s3_block_to_call_vm_placed hh
        (lsρ lsRustAllocSymCli)
        0xfe4 (Φ := fun sm =>
          sm.readReg64 .x0 = 32#64 ∧ sm.readReg64 .x1 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
        hc4 ?_ ?_; rotate_left 1
      · have hpc : s4.pc = (blkPl_521).base + 0xfd8#64 := hc4.pc; have hrun := hc4.run
        dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
        (try dsimp only [fsp] at *); rw [← hc4.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4
        by_vm_steps (
          wp_steps
          refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
      · intro sm5 hvm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx20_5, hx21_5⟩
        have hpool5 : A.pool lim st s4 = A.pool lim st sm5 :=
          (A.pool_transport lim st s4 sm5 hvm5).symm
        rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr5 := ht5.trans htr4
        refine s3_call_alloc_placed hh 32 st _ hc5 hp5 hl5
          (by rw [hx0_5]; decide) (by rw [hx1_5]; decide) rustLay32 hFit
          (by rw [hpool5, hc5.sp]; (try dsimp only [fsp]); sep_frame) ?_
        intro s6 hc6 hcs6 hssNonNull _ htr_6
        set ssBoxPtr := s6.readReg64 .x0
        let st1 := M.stepEvents deriveKeysA1Events st
        rw [hc5.sp, memRegion32_cells4 ssBoxPtr]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine sepWPp_exists_elim_oom fun b0 => sepWPp_exists_elim_oom fun b1 =>
          sepWPp_exists_elim_oom fun b2 => sepWPp_exists_elim_oom fun b3 => ?_
        have htr6 := htr_6.trans htr5
        have hx20_6 := hcs6.2.1.trans hx20_5; have hx21_6 := hcs6.2.2.1.trans hx21_5
        obtain ⟨halign6, hx29_6, hfsp6⟩ := hc6.step_ctx fsp
        refine' s3_block_to_call_vm_placed hh
          (lsρ lsRustNoAllocShimSymCli)
          0xff8 (Φ := fun sm =>
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 26#5) = ssBoxPtr)
          hc6 ?_ ?_; rotate_left 1
        · have hpc : s6.pc = (blkPl_521).base + 0xfe4#64 := hc6.pc; have hrun := hc6.run
          dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521,
            BitVec.ofNat_eq_ofNat] at ⊢
          have hnz6 : s6.readReg64 (.gpr 0#5) ≠ 0#64 := by
            simpa only [ssBoxPtr, arm64_norm, wp_norm] using hssNonNull
          (try dsimp only [fsp] at *); rw [← hc6.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_6 hx21_6
          by_vm_steps (
            wp_steps
            refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_6, arm64_norm, wp_norm],
               by simp only [hx21_6, arm64_norm, wp_norm],
               by simp only [ssBoxPtr, arm64_norm, wp_norm]⟩
              (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
              (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
        · intro sm7 hvm7 hc7 hp7 hl7 ht7 ⟨hx20_7, hx21_7, hx26_7⟩
          have hpool7 : A.pool lim st1 s6 = A.pool lim st1 sm7 :=
            (A.pool_transport lim st1 s6 sm7 hvm7).symm
          rw [hc6.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          have htr7 := ht7.trans htr6
          refine s3_shim_pool_placed hh st1 _ hc7 htr7 hp7 hl7 hpanic
            (by dsimp only [st1, deriveKeysA1Events] at hpool7 ⊢
                rw [hpool7, hc7.sp]; (try dsimp only [fsp]); sep_frame) ?_
          intro s8 hc8 hcs8 htr_8
          rw [hc7.sp]
          have htr8 := htr_8.trans htr7
          have hx20_8 := hcs8.2.1.trans hx20_7; have hx21_8 := hcs8.2.2.1.trans hx21_7
          have hx26_8 := hcs8.2.2.2.2.2.2.2.1.trans hx26_7
          have hss_fold :
              (ssBoxPtr ↦₆₄ ss0) ∗ ((ssBoxPtr + 8#64) ↦₆₄ ss1) ∗
                ((ssBoxPtr + 16#64) ↦₆₄ ss2) ∗ ((ssBoxPtr + 24#64) ↦₆₄ ss3) =
                (ssBoxPtr ↦ₛ ss.toList) := (hss_cells ssBoxPtr).symm
          have htail64 :
              ((fsp + 0x1c20#64) ↦₆₄ ss0) ∗ ((fsp + 0x1c28#64) ↦₆₄ ss1) ∗
                ((fsp + 0x1c30#64) ↦₆₄ ss2) ∗ ((fsp + 0x1c38#64) ↦₆₄ ss3) ∗
                ((fsp + 0x1c40#64) ↦₆₄ ss0) ∗ ((fsp + 0x1c48#64) ↦₆₄ ss1) ∗
                ((fsp + 0x1c50#64) ↦₆₄ ss2) ∗ ((fsp + 0x1c58#64) ↦₆₄ ss3) ⊢
                memRegion (fsp + 0x1c20#64) 64 := by
            have hA := cells4_to_memRegion32 (fsp + 0x1c20#64) ss0 ss1 ss2 ss3
            have hB := cells4_to_memRegion32 (fsp + 0x1c40#64) ss0 ss1 ss2 ss3
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at hA hB
            refine sep_replace hA (by sep_frame) ?_
            refine sep_replace hB (by sep_frame) ?_
            rw [← memRegion_merge_at (fsp + 0x1c20#64) 32 32 (fsp + 0x1c40#64)
              (by clear * -; bv_omega) (by decide)]
            dsimp only [fsp]; sep_frame
          refine sepWPp_conseq_oom ?_
            (hnext s8 ssBoxPtr hssNonNull hc8 htr8 hx20_8 hx21_8 hx26_8)
          dsimp only [fsp, ct, ss, st1, deriveKeysA1Events] at htail64 hss_fold ⊢
          refine sep_replace htail64 (by sep_frame) ?_
          exact sep_replace (Entails.of_eq hss_fold) (by sep_frame) (by sep_frame)

/-- Budget-threaded KEM `ss` boxing (`0x0fb4 → 0x0ff8`). -/
theorem derive_keys_a1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim st deriveKeysA1Events)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (s8 : State) (ssBoxPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiatePlaced s0 s8 0xff8 → s8.trace = s0.trace →
      s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s8.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s8
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents deriveKeysA1Events st) s8 ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
          stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          memRegion (fsp + 0x1c20#64) 64 ∗
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
  derive_keys_a1_placed_nonnull_ok hh hFit hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr _ hc8 htr8 hx20_8 hx21_8 hx26_8 =>
      hnext s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8

theorem derive_keys_a1_placed_evs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFit : FitsEvents M lim (M.stepEvents evs_pre st0) deriveKeysA1Events)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (s8 : State) (ssBoxPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiatePlaced s0 s8 0xff8 → s8.trace = s0.trace →
      s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s8.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s8
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim (M.stepEvents (evs_pre ++ deriveKeysA1Events) st0) s8 ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
          stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          memRegion (fsp + 0x1c20#64) 64 ∗
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
  refine derive_keys_a1_placed_ok hh hFit hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8 => ?_
  rw [← M.stepEvents_append evs_pre deriveKeysA1Events st0]
  exact hnext s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1PlacedBudget
