/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysNone
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 3 `HandshakeKeys::derive` (`dh4? = none`, `+0x1044 → +0x10a4`, `[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` proof of the `dh4? = none` branch of `<HandshakeKeys>::derive`.
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
theorem derive_keys_none_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_eq : dh1 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh1_nz : dh1 ≠ List.replicate 32 0) (hdh1_len : dh1.length = 32)
    (hdh2_eq : dh2 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.ikB)
    (hdh2_nz : dh2 ≠ List.replicate 32 0) (hdh2_len : dh2.length = 32)
    (hdh3_eq : dh3 = (modelPrims X ⟨W.C, W.Q⟩).x25519
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh3_nz : dh3 ≠ List.replicate 32 0) (hdh3_len : dh3.length = 32)
    (hdh4_none : ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X ⟨W.C, W.Q⟩).x25519
          (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk) = none)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sg
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool ∗ stackAt fsp pqxdhEntryStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 none)) ∗
        dhRemAt secretsPtr none ∗
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
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord none) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only [dhPrefix, dhRemAt, dhLenWord]
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
  obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have h930_split :
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 =
        memRegion (fsp + 0x930#64) 100 ∗ memRegion (fsp + 0x994#64) 12 := by
    rw [memRegion_merge_at (fsp + 0x938#64) 0x20 0x48 (fsp + 0x958#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x930#64) 8 104 (fsp + 0x938#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x930#64) 100 12 (fsp + 0x994#64) (by clear * -; bv_omega) (by decide)]
  have hss_bv : bytesToBv8 (E2E.vecU8 ss) = ss.toList := bytesToBv8_toU8_eq ss.toList
  have hss_u8_len : (E2E.vecU8 ss).length = 32 := Pqxdh.Initiator.e2e_vecU8_length ss
  obtain ⟨ss0, ss1, ss2, ss3, hss_cells⟩ := bytes32_exists_cells4 ss.toList_length
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  obtain ⟨hkeysOk, hctEq, hhkEq, hctLen1569, hhkLen100⟩ :=
    stage4_keysOk_of_parts X ⟨W.C, W.Q⟩ kp be x.coins hs3.signaturesVerify
      (hdh1_eq ▸ hdh1_nz) (hdh2_eq ▸ hdh2_nz) (hdh3_eq ▸ hdh3_nz)
      (by rw [hdh4_none]; rfl)
  have hsec_len : (buildSecrets dh1 dh2 dh3 none (E2E.vecU8 ss)).length = 160 := by
    simp [buildSecrets, F_X25519, hdh1_len, hdh2_len, hdh3_len, hss_u8_len]
  have htake32 := buildSecrets_take32_eq dh1 dh2 dh3 none (E2E.vecU8 ss)
  rw [hstk_ext, hss_cells ssBoxPtr, memRegion32_cells4 (secretsPtr + 128#64)]
  refine sepWPp_conseq_oom (by
    dsimp only [fsp] at h930_split ⊢
    exact sep_replace (Entails.of_eq h930_split) (by sep_frame) (Entails.refl _)) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim_oom fun d0 => sepWPp_exists_elim_oom fun d1 =>
    sepWPp_exists_elim_oom fun d2 => sepWPp_exists_elim_oom fun d3 => ?_
  obtain ⟨halign0, hx29_0, hfsp0⟩ := hctrl.step_ctx fsp
  refine' s3_block_to_call_placed hh
    (lsρ lsRustDeallocSymCli)
    0x107c (Φ := fun sm =>
      sm.readReg64 .x0 = ssBoxPtr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
      sm.readReg64 (.gpr 27#5) = 192#64 ∧ sm.readReg64 (.gpr 28#5) = 128#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : sg.pc = (blkPl_521).base + 0x1044#64 := hctrl.pc; have hrun := hctrl.run
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx26
    wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by simp only [hx26, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1, hx25_1, hx27_1, hx28_1⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr1 := ht1.trans htr
    have hbox32 := cells4_to_memRegion32 ssBoxPtr ss0 ss1 ss2 ss3
    have hss_fold128 :
        ((secretsPtr + 128#64) ↦₆₄ ss0) ∗ ((secretsPtr + 136#64) ↦₆₄ ss1) ∗
          ((secretsPtr + 144#64) ↦₆₄ ss2) ∗ ((secretsPtr + 152#64) ↦₆₄ ss3) =
          ((secretsPtr + 128#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, hss_bv] using
        (hss_cells (secretsPtr + 128#64)).symm
    have happ128 :
        (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
          ((secretsPtr + 128#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) =
          (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 none (E2E.vecU8 ss))) :=
      append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) (E2E.vecU8 ss) 128#64
        (by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len])
    refine s3_dealloc_placed hh ssBoxPtr 32 _
      hc1 htr1 hp1 hl1 hx0_1 (by rw [hx1_1]; decide) (by rw [hx2_1]; decide) lay32 hpanic
      (by rw [hc1.sp]; (try dsimp only [fsp]); exact sep_replace hbox32 (by sep_frame) (by sep_frame)) ?_
    intro s2 hc2 hcs2 htr_2
    rw [hc1.sp]
    have htr2 := htr_2.trans htr1
    have hx20_2 := hcs2.2.1.trans hx20_1; have hx21_2 := hcs2.2.2.1.trans hx21_1
    have hx22_2 := hcs2.2.2.2.1.trans hx22_1
    have hx25_2 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have hx27_2 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    dsimp only [fsp, ss] at hstk_ext hss_fold128 happ128 ⊢
    rw [pack_cells4_append _ _ _ _ _ _ _ _ _ _ _ _ hss_fold128 happ128,
        repack_pqxdh_stk _ _ _ _ _ _ _ _ _ hstk_ext.symm]
    obtain ⟨_, _, hfsp2⟩ := hc2.step_ctx fsp
    refine' s3_block_to_call_placed hh
      (lsmpl.base 59)
      0x1090 (Φ := fun sm =>
        sm.readReg64 .x8 = fsp + 0x930#64 ∧ sm.readReg64 .x0 = secretsPtr ∧
        sm.readReg64 .x1 = 160#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
        sm.readReg64 (.gpr 27#5) = 192#64)
      hc2 ?_ ?_; rotate_left 1
    · have hpc : s2.pc = (blkPl_521).base + 0x107c#64 := hc2.pc; have hrun := hc2.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
      (try dsimp only [fsp] at *); rw [← hc2.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2
      wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by simp only [hx25_2, arm64_norm, wp_norm],
         by simp only [hx28_2, arm64_norm, wp_norm],
         by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm],
         by simp only [hx22_2, arm64_norm, wp_norm], by simp only [hx25_2, arm64_norm, wp_norm],
         by simp only [hx27_2, arm64_norm, wp_norm]⟩
    · intro sm3 hc3 hp3 hl3 ht3 ⟨hx8_3, hx0_3, hx1_3, hx20_3, hx21_3, hx22_3, hx25_3, hx27_3⟩
      rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr3 := ht3.trans htr2
      refine s3_call_placed hh (hLocal.handshakeDerive X)
        ⟨secretsPtr, buildSecrets dh1 dh2 dh3 none (E2E.vecU8 ss), fsp + 0x930#64⟩ _
        hc3 htr3 hp3 hl3 hpanic
        (by
          simp only [handshakeKeysDerivePlacedBaseSpec, hc3.sp, sepConj_assoc]
          refine Entails.pure_right ⟨hx8_3, hx0_3, by rw [hx1_3, hsec_len]; decide,
            Or.inl hsec_len, htake32⟩ ?_
          dsimp only [fsp, ss, t] at *
          sep_frame) ?_ ?_ ?_ ?_
      · intro _ _ h
        simp only [handshakeKeysDerivePlacedBaseSpec, sepConj_assoc,
          satisfies_pure_sepConj] at h
        exact h.1.1
      · intro _ _ _ h; simp [handshakeKeysDerivePlacedBaseSpec, Spec.onExit] at h
      · intro _ _ h; simp [handshakeKeysDerivePlacedBaseSpec, Spec.onOom] at h
      · intro s4a _ _ _ hcs4 _ hof4
        simp only [handshakeKeysDerivePlacedBaseSpec, hc3.sp, sepConj_assoc]
        refine sepWPp_pure_elim_oom fun htr_4 => ?_
        have hc4 := hof4 htr_4
        have htr4 := htr_4.trans htr3
        have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
        have hx22_4 := hcs4.2.2.2.1.trans hx22_3
        have hx25_4 := hcs4.2.2.2.2.2.2.1.trans hx25_3
        have hx27_4 := hcs4.2.2.2.2.2.2.2.2.1.trans hx27_3
        obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
        refine' s3_block_to_call_placed hh
          (lsρ lsRustDeallocSymCli)
          0x10a4 (Φ := fun sm =>
            sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧ sm.readReg64 .x2 = 1#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x900#64)
          hc4 ?_ ?_; rotate_left 1
        · have hpc : s4a.pc = (blkPl_521).base + 0x1090#64 := hc4.pc; have hrun := hc4.run
          dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at ⊢
          (try dsimp only [fsp] at *); rw [← hc4.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx25_4 hx27_4
          wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx25_4, arm64_norm, wp_norm], by simp only [hx27_4, arm64_norm, wp_norm],
             by wp_norm_goal,
             by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm],
             by simp only [hx22_4, arm64_norm, wp_norm]⟩
        · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx2_5, hx20_5, hx21_5, hx22_5⟩
          rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          have htr5 := ht5.trans htr4
          have hsec192 :
              (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 none (E2E.vecU8 ss))) ∗
                memRegion (secretsPtr + 160#64) 32 ⊢ memRegion secretsPtr 192 := by
            refine Entails.trans
              (sepConj_mono_left
                (pointsToBytes_entails_memRegion_len
                  ((bytesToBv8_length _).trans hsec_len))) ?_
            rw [memRegion_merge_at secretsPtr 160 32 (secretsPtr + 160#64)
              (by clear * -; bv_omega) (by decide)]
            exact Entails.refl _
          refine s3_dealloc_placed hh secretsPtr 192 _
            hc5 htr5 hp5 hl5 hx0_5 (by rw [hx1_5]; decide) (by rw [hx2_5]; decide) lay192 hpanic
            (by rw [hc5.sp, hstk_ext]; dsimp only [fsp, ss, t] at *
                exact sep_replace hsec192 (by sep_frame) (by sep_frame)) ?_
          intro s_end hc_end hcs_end htr_end
          rw [hc5.sp]
          have htr_final := htr_end.trans htr5
          have hfs_final : s_end.fs.files = x.F :=
            hc_end.files0.trans hs3.ctrl.files0.symm |>.trans hs3.files
          have hstk_full :
              memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
                stackAt fsp extHookStack ∗
                memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                  (stk - cliInitiateFrame - pqxdhEntryStack) =
                stackAt fsp (stk - cliInitiateFrame) := by
            rw [← sepConj_assoc, ← hstk_ext, sepConj_comm,
                ← stackAt_sub_split_init fsp hsub_pq (stk_sub_le_2pow64 hstk64)]
          have htail := tail_locals_collapse fsp hekASkLen hkpkLen secretsPtr 128#64
          subst hdh1_eq hdh2_eq hdh3_eq
          dsimp only [t] at hdh4_none
          conv at hhkEq => lhs; rw [hdh4_none]
          refine sepWPp_conseq_oom ?_
            (hnext s_end _ _ (8#8 :: ct.toList) _ kemCtPtr
              { ctrl := hc_end, trace := htr_final, files := hfs_final, x8 := hs3.x8,
                bundleEq := hs3.bundleEq, trustedOk := hs3.trustedOk, kpOk := hs3.kpOk,
                ekPairEq := hs3.ekPairEq, opkIdEq := hs3.opkIdEq,
                keysOk := hkeysOk, kemCtEq := hctEq, hkSlotEq := rfl,
                pqspkNonNull := hs3.pqspkNonNull, kemCtNonNull := hkemNonNull,
                x20 := hcs_end.2.1.trans hx20_5, x21 := hcs_end.2.2.1.trans hx21_5,
                x22 := hcs_end.2.2.2.1.trans hx22_5 })
          unfold S3InvPrefixPlaced; dsimp only [stage4MemPlaced]
          refine Entails.pure_right ⟨hctLen1569, hhkLen100⟩ ?_
          dsimp only [fsp, ct, ss, t] at hhkEq hstk_full htail ⊢
          rw [hhkEq]
          refine sep_replace htail (by sep_frame) ?_
          exact sep_replace (Entails.of_eq hstk_full) (by sep_frame) (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
