/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 3 KEM Ciphertext Boxing and Serialization (`0x0ff8 → 0x1044`)

Verifies `derive_keys_a_placed_ok` on `initProgPlaced` under `[LibsignalPlacement]`: boxes `ss` and
`ct`, invokes `<kem::Ciphertext>::serialize` (block `71`), stores `(kemCtPtr, 1569)` at
`[fsp + 0x60 .. 0x70)`, and frees `ctBoxPtr`.
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

private theorem ct1568_split_hdr (p : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 1568) :
    (p ↦ₛ bs) ⊢
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗ memRegion (p + 16#64) 1552 := by
  refine Entails.trans (pointsToBytes_entails_memRegion_len h) ?_
  rw [← memRegion_merge_at p 8 1560 (p + 8#64) (by clear * -; bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 1552 (p + 16#64) (by clear * -; bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  exact Entails.of_eq (by ac_rfl)

private theorem s3_step_1030_1044_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {s : State}
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
  wp_steps
  exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
    (by (try simp only [hx0, hx1, arm64_norm, wp_norm]); sep_frame)
    ⟨by simp only [hx25, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
     by simp only [hx26, arm64_norm, wp_norm]⟩
set_option maxHeartbeats 1200000 in
theorem derive_keys_a_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
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
          A.pool ∗ stackAt fsp pqxdhEntryStack ∗
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
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
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
  refine derive_keys_a1_placed_ok hh hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8 => ?_
  try dsimp only at hx20_8 hx21_8 ⊢
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  obtain ⟨_, _, hfsp8⟩ := hc8.step_ctx fsp
  refine' s3_block_to_call_placed hh
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
    wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20_8, arm64_norm, wp_norm], by simp only [hx21_8, arm64_norm, wp_norm],
       by simp only [hx26_8, arm64_norm, wp_norm]⟩
  · intro sm9 hc9 hp9 hl9 ht9 ⟨hx0_9, hx1_9, hx20_9, hx21_9, hx26_9⟩
    rw [hc8.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr9 := ht9.trans htr8
    refine s3_call_alloc_placed hh 1568 _ hc9 hp9 hl9
      (by rw [hx0_9]; decide) (by rw [hx1_9]; decide) lay1568
      (by rw [hc9.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
    · intro sm_oom2 hp_oom2 hrun_oom2 hnull2 htr_oom2
      refine sepWPp_oom_jmp (mid := (blkPl_521).base + 0x193c#64) ?_ fun s' hpc' hrun' htr' =>
        oom_193c_placed_ok hh hpc' hrun' (allocFailedIn_of_append (htr9 ▸ htr' ▸ htr_oom2)) hpanic
      have hp_oom2' : sm_oom2.pc = (blkPl_521).base + 0x1004#64 := hp_oom2
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521,
        BitVec.ofNat_eq_ofNat] at hp_oom2' ⊢
      try simp only [arm64_norm, wp_norm] at hnull2
      wp_steps
      exact SepWP.done (by wp_norm_goal) hrun_oom2 ⟨rfl, by wp_norm_goal, hrun_oom2, rfl⟩
    · intro s10 hc10 hcs10 hctNonNull htr_10
      set ctBoxPtr := s10.readReg64 .x0
      rw [hc9.sp]
      have htr10 := htr_10.trans htr9
      have hx20_10 := hcs10.2.1.trans hx20_9; have hx21_10 := hcs10.2.2.1.trans hx21_9
      have hx26_10 := hcs10.2.2.2.2.2.2.2.1.trans hx26_9
      obtain ⟨_, _, hfsp10⟩ := hc10.step_ctx fsp
      refine' s3_block_to_call_placed hh
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
        wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [ctBoxPtr, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_10, arm64_norm, wp_norm], by simp only [hx21_10, arm64_norm, wp_norm],
           by wp_norm_goal, by simp only [ctBoxPtr, arm64_norm, wp_norm],
           by simp only [hx26_10, arm64_norm, wp_norm]⟩
      · intro sm11 hc11 hp11 hl11 ht11
          ⟨hx0_11, hx1_11, hx2_11, hx20_11, hx21_11, hx22_11, hx25_11, hx26_11⟩
        rw [hc10.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr11 := ht11.trans htr10
        refine s3_memcpy_placed hh ctBoxPtr (fsp + 0xfe0#64) ct.toList _
          hc11 htr11 hp11 hl11 hx0_11 hx1_11 (by rw [hx2_11, hct_len]; decide) hpanic
          (by rw [hc11.sp, hct_len]; (try dsimp only [fsp]); sep_frame) ?_
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
        refine sepWPp_conseq_oom (by dsimp only [fsp, ct] at hhdr ⊢; exact sep_replace hhdr (by sep_frame) (Entails.refl _)) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine sepWPp_exists_elim_oom fun h0 => sepWPp_exists_elim_oom fun h1 => ?_
        obtain ⟨halign12, _, hfsp12⟩ := hc12.step_ctx fsp
        refine' s3_block_to_call_placed hh
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
          wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal,
             by simp only [hx20_12, arm64_norm, wp_norm], by simp only [hx21_12, arm64_norm, wp_norm],
             by simp only [hx25_12, arm64_norm, wp_norm], by simp only [hx26_12, arm64_norm, wp_norm]⟩
        · intro sm13 hc13 hp13 hl13 ht13 ⟨hx0_13, hx20_13, hx21_13, hx25_13, hx26_13⟩
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
          refine s3_call_placed hh hLocal.kemCtSerialize
            (fsp + 0x1600#64, ctBoxPtr, ct.toList) _
            hc13 htr13 hp13 hl13 hpanic
            (by
              have hx25_raw := hx25_12; conv at hx25_raw => lhs; simp only [arm64_norm, wp_norm]
              have hx22_raw := hx22_12; conv at hx22_raw => lhs; simp only [arm64_norm, wp_norm]
              simp only [kemCiphertextSerializeSpec, hc13.sp, hx25_12, hx22_12, hx25_raw, hx22_raw,
                BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
              refine Entails.pure_right ⟨hx0_13, hct_len⟩ ?_
              dsimp only [fsp, ct, ctBoxPtr, t] at hstk_clone ⊢
              refine sep_replace (Entails.of_eq hstk_clone) (by sep_frame) ?_
              sep_frame) ?_ ?_ ?_ ?_
          · intro _ _ h
            simp only [kemCiphertextSerializeSpec] at h
            rw [sepConj_assoc, satisfies_pure_sepConj] at h
            exact h.1.1
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
            refine' s3_block_to_call_placed hh
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
              exact s3_step_1030_1044_placed kemCtPtr ctBoxPtr ssBoxPtr g68 g60 _ halign14 hpc hc14.run
                hx0_14 hx1_14 (by rwa [← hfsp14]) (by rwa [← hfsp14]) hx25_14 hx26_14
            · intro sm15 hc15 hp15 hl15 ht15
                ⟨hx0_15, hx1_15, hx2_15, hx20_15, hx21_15, hx26_15⟩
              rw [← hfsp14] at *
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
              refine s3_dealloc_placed hh ctBoxPtr 1568 _
                hc15 htr15 hp15 hl15 hx0_15 (by rw [hx1_15]; decide) (by rw [hx2_15]; decide) lay1568 hpanic
                (by rw [hc15.sp]; dsimp only [fsp, ct] at hstk_back_ext hbox_mem ⊢
                    refine sep_replace hbox_mem (by sep_frame) ?_
                    exact sep_replace (Entails.of_eq hstk_back_ext) (by sep_frame) (by sep_frame)) ?_
              intro sg hcg hcsg htr_g
              rw [hc15.sp]
              refine sepWPp_conseq_oom ?_
                (hnext sg ssBoxPtr kemCtPtr hkemNonNull hcg (htr_g.trans htr15)
                  (hcsg.2.1.trans hx20_15) (hcsg.2.2.1.trans hx21_15)
                  (hcsg.2.2.2.2.2.2.2.1.trans hx26_15))
              dsimp only [fsp, ct, ss] at hstk_ext hmid_collapse ⊢
              refine sep_replace hmid_collapse (by sep_frame) ?_
              exact sep_replace (Entails.of_eq hstk_ext.symm) (by sep_frame) (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
