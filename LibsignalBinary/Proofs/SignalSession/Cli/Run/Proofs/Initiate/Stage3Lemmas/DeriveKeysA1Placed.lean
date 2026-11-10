/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 3 KEM Shared-Secret Boxing (`0x0fb4 → 0x0ff8`)

Verifies `derive_keys_a1_placed_ok` on `initProgPlaced` under `[LibsignalPlacement]`: copies `ct`
to `fsp + 0xfe0`, allocates `ssBoxPtr` (32 bytes), and stores `ss`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
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
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

set_option maxHeartbeats 1200000 in
theorem derive_keys_a1_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
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
          A.pool ∗
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
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          memRegion (fsp + 0x1c20#64) 64 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf0
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
        ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
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
  refine' s3_block_to_call_placed hh
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
    wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
  · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr1 := ht1.trans htr
    refine s3_memcpy_placed hh (fsp + 0xfe0#64) (fsp + 0x1600#64) ct.toList _
      hc1 htr1 hp1 hl1 hx0_1 hx1_1 (by rw [hx2_1, hct_len]; decide) hpanic
      (by rw [hc1.sp, hct_len]; (try dsimp only [fsp]); sep_frame) ?_
    intro s2 hc2 hcs2 _ htr_2
    rw [hc1.sp]
    have htr2 := htr_2.trans htr1
    have hx20_2 := hcs2.2.1.trans hx20_1; have hx21_2 := hcs2.2.2.1.trans hx21_1
    rw [hss_cells (fsp + 0x1c20#64), memRegion32_cells4 (fsp + 0x1c40#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun t0 => sepWPp_exists_elim_oom fun t1 =>
      sepWPp_exists_elim_oom fun t2 => sepWPp_exists_elim_oom fun t3 => ?_
    obtain ⟨halign2, hx29_2, hfsp2⟩ := hc2.step_ctx fsp
    refine' s3_block_to_call_placed hh
      (lsρ lsRustNoAllocShimSymCli)
      0xfd8 (Φ := fun sm =>
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hc2 ?_ ?_; rotate_left 1
    · have hpc : s2.pc = (blkPl_521).base + 0xfc8#64 := hc2.pc; have hrun := hc2.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
      (try dsimp only [fsp] at *); rw [← hc2.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2
      wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm]⟩
    · intro sm3 hc3 hp3 hl3 ht3 ⟨hx20_3, hx21_3⟩
      rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr3 := ht3.trans htr2
      refine s3_shim_placed hh _ hc3 htr3 hp3 hl3 hpanic (by rw [hc3.sp]; (try dsimp only [fsp]); sep_frame) ?_
      intro s4 hc4 hcs4 htr_4
      rw [hc3.sp]
      have htr4 := htr_4.trans htr3
      have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
      obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
      refine' s3_block_to_call_placed hh
        (lsρ lsRustAllocSymCli)
        0xfe4 (Φ := fun sm =>
          sm.readReg64 .x0 = 32#64 ∧ sm.readReg64 .x1 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
        hc4 ?_ ?_; rotate_left 1
      · have hpc : s4.pc = (blkPl_521).base + 0xfd8#64 := hc4.pc; have hrun := hc4.run
        dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
        (try dsimp only [fsp] at *); rw [← hc4.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4
        wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm]⟩
      · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx20_5, hx21_5⟩
        rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr5 := ht5.trans htr4
        refine s3_call_alloc_placed hh 32 _ hc5 hp5 hl5
          (by rw [hx0_5]; decide) (by rw [hx1_5]; decide) lay32
          (by rw [hc5.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
        · intro sm_oom1 hp_oom1 hrun_oom1 hnull1 htr_oom1
          refine sepWPp_oom_jmp (mid := (blkPl_521).base + 0x1930#64) ?_ fun s' hpc' hrun' htr' =>
            oom_1930_placed_ok hh hpc' hrun' (allocFailedIn_of_append (htr5 ▸ htr' ▸ htr_oom1)) hpanic
          have hp_oom1' : sm_oom1.pc = (blkPl_521).base + 0xfe4#64 := hp_oom1
          dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
            BitVec.ofNat_eq_ofNat] at hp_oom1' ⊢
          try simp only [arm64_norm, wp_norm] at hnull1
          wp_steps
          exact SepWP.done (by wp_norm_goal) hrun_oom1 ⟨rfl, by wp_norm_goal, hrun_oom1, rfl⟩
        · intro s6 hc6 hcs6 hssNonNull htr_6
          set ssBoxPtr := s6.readReg64 .x0
          rw [hc5.sp, memRegion32_cells4 ssBoxPtr]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          refine sepWPp_exists_elim_oom fun b0 => sepWPp_exists_elim_oom fun b1 =>
            sepWPp_exists_elim_oom fun b2 => sepWPp_exists_elim_oom fun b3 => ?_
          have htr6 := htr_6.trans htr5
          have hx20_6 := hcs6.2.1.trans hx20_5; have hx21_6 := hcs6.2.2.1.trans hx21_5
          obtain ⟨halign6, hx29_6, hfsp6⟩ := hc6.step_ctx fsp
          refine' s3_block_to_call_placed hh
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
            wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (Entails.refl _)
              ⟨by simp only [hx20_6, arm64_norm, wp_norm], by simp only [hx21_6, arm64_norm, wp_norm],
               by simp only [ssBoxPtr, arm64_norm, wp_norm]⟩
          · intro sm7 hc7 hp7 hl7 ht7 ⟨hx20_7, hx21_7, hx26_7⟩
            rw [hc6.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr7 := ht7.trans htr6
            refine s3_shim_placed hh _ hc7 htr7 hp7 hl7 hpanic
              (by rw [hc7.sp]; (try dsimp only [fsp]); sep_frame) ?_
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
            refine sepWPp_conseq_oom ?_ (hnext s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8)
            dsimp only [fsp, ct, ss] at htail64 hss_fold ⊢
            refine sep_replace htail64 (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hss_fold) (by sep_frame) (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
