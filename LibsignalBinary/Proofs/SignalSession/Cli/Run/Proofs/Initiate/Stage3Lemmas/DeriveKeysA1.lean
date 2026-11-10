/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Shared-Secret Boxing (`0x0fb4 → 0x0ff8`)

Copies `ct` (1568 bytes) to `fsp + 0xfe0`, allocates `ssBoxPtr` (32 bytes, OOM → `0x1930`), stores
`ss` into `ssBoxPtr`, and collapses `[fsp + 0x1c20 .. 0x1c60)` to `memRegion (fsp + 0x1c20) 64`
(`derive_keys_a1_ok` and `derive_keys_a1_ok_ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefix coinsCursorAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

set_option maxHeartbeats 1200000 in
theorem derive_keys_a1_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiate img W s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (s8 : State) (ssBoxPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiate img W s0 s8 0xff8 → s8.trace = s0.trace →
      s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s8.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (initProg img W) (s0.readReg64 .lr) s8
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
    SepWPp (initProg img W) (s0.readReg64 .lr) sf0
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
  refine' s3_block_to_call hh
    (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    0xfc8 (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0xfe0#64 ∧ sm.readReg64 .x1 = fsp + 0x1600#64 ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfb4 20
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
  · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr1 := ht1.trans htr
    refine s3_memcpy hh (fsp + 0xfe0#64) (fsp + 0x1600#64) ct.toList _
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
    refine' s3_block_to_call hh
      (initEntry img W + bv% (ls_rel%
        "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      0xfd8 (Φ := fun sm =>
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hc2 ?_ ?_; rotate_left 1
    · have hpc := hc2.pc; have hrun := hc2.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfc8 16
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hc2.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm]⟩
    · intro sm3 hc3 hp3 hl3 ht3 ⟨hx20_3, hx21_3⟩
      rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr3 := ht3.trans htr2
      refine s3_shim hh _ hc3 htr3 hp3 hl3 hpanic (by rw [hc3.sp]; (try dsimp only [fsp]); sep_frame) ?_
      intro s4 hc4 hcs4 htr_4
      rw [hc3.sp]
      have htr4 := htr_4.trans htr3
      have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
      obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
      refine' s3_block_to_call hh
        (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
        0xfe4 (Φ := fun sm =>
          sm.readReg64 .x0 = 32#64 ∧ sm.readReg64 .x1 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
        hc4 ?_ ?_; rotate_left 1
      · have hpc := hc4.pc; have hrun := hc4.run
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfd8 12
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hc4.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm]⟩
      · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx20_5, hx21_5⟩
        rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr5 := ht5.trans htr4
        refine s3_call_alloc hh 32 _ hc5 hp5 hl5
          (by rw [hx0_5]; decide) (by rw [hx1_5]; decide) lay32
          (by rw [hc5.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
        · intro sm_oom1 hp_oom1 hrun_oom1 hnull1 htr_oom1
          refine sepWPp_oom_jmp (mid := initPc img W 0x1930) ?_ fun s' hpc' hrun' htr' =>
            oom_1930_ok hpc' hrun' (allocFailedIn_of_append (htr5 ▸ htr' ▸ htr_oom1)) hpanic
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfe4 4
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hp_oom1 ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          try simp only [arm64_norm, wp_norm] at hnull1
          examples_hide_fetches; wp_steps
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
          refine' s3_block_to_call hh
            (initEntry img W + bv% (ls_rel%
              "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
            0xff8 (Φ := fun sm =>
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 26#5) = ssBoxPtr)
            hc6 ?_ ?_; rotate_left 1
          · have hpc := hc6.pc; have hrun := hc6.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfe4 20
            dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            have hnz6 : s6.readReg64 (.gpr 0#5) ≠ 0#64 := by
              simpa only [ssBoxPtr, arm64_norm, wp_norm] using hssNonNull
            (try dsimp only [fsp] at *); rw [← hc6.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_6 hx21_6
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (Entails.refl _)
              ⟨by simp only [hx20_6, arm64_norm, wp_norm], by simp only [hx21_6, arm64_norm, wp_norm],
               by simp only [ssBoxPtr, arm64_norm, wp_norm]⟩
          · intro sm7 hc7 hp7 hl7 ht7 ⟨hx20_7, hx21_7, hx26_7⟩
            rw [hc6.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr7 := ht7.trans htr6
            refine s3_shim hh _ hc7 htr7 hp7 hl7 hpanic
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

/-! ## Extern-parameterized `derive_keys_a1_ok_ext` -/

private abbrev s3ProgExt (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt img.base (cliExternsWith ext)

private abbrev s3EntryExt (img : Obj.Image) (ext : String → Option (State → State)) : BitVec 64 :=
  (s3ProgExt img ext).fnAddr cliInitiateName

private abbrev s3PcExt (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    BitVec 64 :=
  s3EntryExt img ext + BitVec.ofNat 64 k

/-- Control-state invariant at relative offset `k` on `tripleRatchetProgAtExt img.base (cliExternsWith ext)`. -/
abbrev s3DkCtrlExt (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop :=
  let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
  s.pc = prog.fnAddr cliInitiateName + BitVec.ofNat 64 k ∧
  s.status = .Running ∧
  s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
  s.readReg64 .fp = s0.sp - 0x60#64 ∧
  s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
  s.fs.files = s0.fs.files ∧
  ImgCallInv img s ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s0.spAligned = true

private structure S3Ctrl (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = s3PcExt img ext k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  files0 : s.fs.files = s0.fs.files
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

private theorem S3Ctrl.of_prop {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : s3DkCtrlExt img ext s0 s k) : S3Ctrl img ext s0 s k := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem S3Ctrl.to_prop {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s3DkCtrlExt img ext s0 s k := by
  exact ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

private theorem S3Ctrl.spAligned_cur {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

private theorem S3Ctrl.step_ctx {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧
      s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧
      fsp = s.sp := by
  have ha := h.spAligned_cur; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

private theorem s3_withPanics_cliExternsWith (ext : String → Option (State → State)) :
    Rust.withPanics (cliExternsWith ext) = cliExternsWith ext :=
  withPanics_withCliPanics ext

private theorem s3_quietEv_false_of_isFsChange (e : TraceEvent)
    (h : e.isFsChange = true) : ¬ QuietEv e := by
  cases e with
  | writeByte st _ => cases st <;> simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢
  | _ => simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢

private theorem s3_externAt_fsTraced {prog : Program}
    (hX : ∀ n f, prog.externs n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hO : ∀ n f, prog.overrides n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    {pc : BitVec 64} {f : State → State} (h : prog.externAt? pc = some f) :
    HookFsTraced (fun e => e.isFsChange = true) f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, _⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno; split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, _⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno; split at hno
    · exact hO n f hno
    · cases hno

private theorem rebase_traceFsSound (C : Program) (b : BitVec 64) (hsvc : C.svc = execSyscall)
    {P0 : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext) :
    TraceFsSound (C.rebase b (Rust.withPanics (cliExternsWith ext))) := by
  refine TraceFsSound.of_isFs s3_quietEv_false_of_isFsChange fun s s' hst => ?_
  refine hst.files_eq_of_noFs (fun _ h => h)
    (fun _ _ h => s3_externAt_fsTraced ?_ (fun _ _ hn => by cases C; cases hn) h) (by cases C; exact hsvc)
  intro name f hf; cases C; change (Rust.withPanics (cliExternsWith ext)) name = some f at hf
  rw [s3_withPanics_cliExternsWith] at hf
  simp only [cliExternsWith, withCliPanics] at hf
  cases hpan : isCliPanicSymbol name
  · rw [hpan] at hf; exact hOk.fsTraced name f hf
  · rw [hpan] at hf; cases hf; exact fun _ => ⟨[], by simp [Rust.panicked], fun _ => rfl⟩

private theorem s3_traceFsSound (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    TraceFsSound (s3ProgExt img ext) := by
  exact rebase_traceFsSound libsignalSessionCode img.base rfl hOk

private theorem S3Ctrl.of_call {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    {s0 s sm : State} {k_in k_out : Nat}
    (h : S3Ctrl img ext s0 s k_in)
    (hsteps : Steps (s3ProgExt img ext) s sm)
    (hpcm : sm.pc = s3PcExt img ext k_out)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp)
    (hcsm : CalleeSavedPreserved s sm)
    (htrm : sm.trace = s.trace) :
    S3Ctrl img ext s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq : sm.fs.files = s.fs.files :=
    TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps
      (evs := []) (by simpa using htrm) NoFsEv.nil
  exact
    { pc := hpcm
      run := hrunm
      sp := hspm.trans h.sp
      fp := hfp.trans h.fp
      x19 := hx19.trans h.x19
      files0 := hfs_eq.trans h.files0
      inv := h.inv.of_steps hsteps
      vregs := hvregs.trans h.vregs
      spAligned := h.spAligned }

private theorem s3_pc_sub_entry (a b : BitVec 64) :
    a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

private theorem s3_block_to_call_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat)
    {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (hwp : SepWP (s3ProgExt img ext) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧
      sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = s3PcExt img ext k_out ∧ Φ sm))
    (hcont : ∀ sm : State,
      S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) →
      sm.pc = callee →
      sm.readReg64 .lr = s3PcExt img ext k_out →
      sm.trace = s.trace →
      Φ sm →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  intro R hm hL
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq : sm.fs.files = s.fs.files :=
      TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps
        (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' : S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) :=
      { pc := s3_pc_sub_entry sm.pc (s3EntryExt img ext)
        run := hrunm
        sp := hsp.trans hctrl.sp
        fp := hfp.trans hctrl.fp
        x19 := hx19.trans hctrl.x19
        files0 := hfs_eq.trans hctrl.files0
        inv := hctrl.inv.of_steps hsteps
        vregs := hvregs.trans hctrl.vregs
        spAligned := hctrl.spAligned }
    have hmm' : sm.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont sm hctrl' hpcm hlrm htrm hphi R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_call_ext {α : Type} {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (s3ProgExt img ext) callee spec)
    (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee)
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State,
      sm.pc = s3PcExt img ext k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (sm.trace = s.trace → S3Ctrl img ext s0 sm k_out) →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine sepWPp_conseq_oom hpre ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre g s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome g (F ∗ R') s hpc hctrl.run hm_pre
      (S3Ctrl.spAligned_cur hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hctrl.inv.of_steps hsteps)
        (S3Ctrl.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic g s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by
      simpa only [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan,
      hpanic sm _ (initPanicPost_of_allocFailed _ halloc0)⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

private theorem s3_hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)}
    {sym : String} {spec : Spec α}
    (hnp : E2E.isImagePanicSymbol sym = false) (h : HookSat ext sym spec) :
    HookSat (cliExternsWith ext) sym spec := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnp).trans hf, hok⟩

private theorem shim_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      CliExt.shimSpec := by
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (stub := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by simp [Rust.isPanicSymbol])
    (s3_hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
      hOk.shim)

private theorem memcpy_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      CliExt.memcpySpec := by
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "memcpy")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (stub := num% (ls_off% "memcpy"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "memcpy")
    (by simp [Rust.isPanicSymbol])
    (s3_hookSat_cliExternsWith
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
      hOk.memcpy)

private theorem alloc_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      (rustAllocSpecWithStack A extHookStack) := by
  obtain ⟨f, hf, hok⟩ := hOk.alloc.alloc
  have hsat : HookSat (cliExternsWith ext) allocName (rustAllocSpecWithStack A extHookStack) :=
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext
          (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, allocName])).trans hf,
     hookOk_rustAllocWithStack hok (by decide) (by decide)⟩
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := allocName)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (stub := num% (ls_off% "__rustc::__rust_alloc"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "__rustc::__rust_alloc")
    (by simp [Rust.isPanicSymbol, allocName])
    hsat

private theorem panic_alloc_error_at_init_ext (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (s3ProgExt img ext).externAt?
      (s3EntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate"
          "alloc::alloc::handle_alloc_error")) =
      some Rust.panicked := by
  exact panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "alloc::alloc::handle_alloc_error")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate"
      "alloc::alloc::handle_alloc_error"))
    (stub := num% (ls_off% "alloc::alloc::handle_alloc_error"))
    cliInitiate_fnOff rfl (by decide)
    (ls_hook% "alloc::alloc::handle_alloc_error")
    (by simp [Rust.isPanicSymbol])

private theorem oom_1930_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = s3PcExt img ext 0x1930) (hrun : s.status = .Running)
    (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init_ext img ext
  refine sepWP_bind_oom (mid := s3EntryExt img ext +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1930 12
  dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
    BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P)
      (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

private theorem s3_shim_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = s3EntryExt img ext + bv% (ls_rel%
      "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, S3Ctrl img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.trace = s.trace → SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        (stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ CliExt.shimSpec.pre () s ∗ (stackAt s.sp extHookStack ∗ F) :=
    Entails.trans hpre (by simp only [CliExt.shimSpec, emp_sepConj]; exact Entails.refl _)
  refine s3_call_ext hOk (shim_ok_at_init_ext img hOk) () (stackAt s.sp extHookStack ∗ F)
    hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [CliExt.shimSpec] at h
  · intro _ _ _ h; simp [CliExt.shimSpec] at h
  · intro _ _ h; simp [CliExt.shimSpec] at h
  · intro sm _ _ _ hcsm _ hof
    simp only [CliExt.shimSpec, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

private theorem s3_memcpy_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, S3Ctrl img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hstk_split := stackAt_sub_split_init s.sp
    (by decide : CliExt.memHookStack ≤ extHookStack) (by decide)
  let F' := memRegion (s.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - CliExt.memHookStack) ∗ F
  have hpre' : P ⊢ CliExt.memcpySpec.pre (dst, src, bs) s ∗ F' := by
    refine Entails.trans hpre ?_
    rw [hstk_split]
    simp only [CliExt.memcpySpec, libcMemcpySpec, F', sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by ac_rfl))
  refine s3_call_ext hOk (memcpy_ok_at_init_ext img hOk) (dst, src, bs) F'
    hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [CliExt.memcpySpec] at h
  · intro _ _ _ h; simp [CliExt.memcpySpec] at h
  · intro _ _ h; simp [CliExt.memcpySpec] at h
  · intro sm _ _ _ hcsm _ hof
    simp only [CliExt.memcpySpec, F', sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ => ?_
    refine sepWPp_conseq_oom ?_ (hnext sm (hof htrm) hcsm hx0m htrm)
    rw [hstk_split]
    exact Entails.of_eq (by ac_rfl)

private theorem s3_call_alloc_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (hpc : s.pc = s3EntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_null : ∀ sm : State,
      sm.pc = s3PcExt img ext k_out → sm.status = .Running →
      sm.readReg64 .x0 = 0#64 →
      sm.trace = s.trace ++ [allocFailedEvent] →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0))
    (hnext_ok : ∀ sm : State,
      S3Ctrl img ext s0 sm k_out →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.trace = s.trace →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗
          A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have halloc := alloc_ok_at_init_ext img hOk
  have hpre' : P ⊢ (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [rustAllocSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlay⟩ (Entails.of_eq (by ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨
      (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    halloc.no_fault_before_outcome (sz, 1) (F ∗ R') s hpc hctrl.run hm_pre
      (S3Ctrl.spAligned_cur hctrl) hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [hlr] at hpcm
    dsimp only [rustAllocSpecWithStack] at hpost
    by_cases hnull : sm.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨
          ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s.sp extHookStack ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      obtain ⟨htrm, hmem_null'⟩ := hpost'
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_null sm hpcm hrunm hnull htrm R' hmem_null' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨
          ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            ((A.pool ∗ stackAt s.sp extHookStack ∗
              A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'
      obtain ⟨⟨_, htrm⟩, hmem_ok'⟩ := hpost'
      have hctrl' := S3Ctrl.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ :=
        hnext_ok sm hctrl' hcsm hnull htrm R' hmem_ok' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · simp only [rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [rustAllocSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

set_option maxHeartbeats 1200000 in
/-- KEM `ss` boxing (`0x0fb4 → 0x0ff8`) under `CliExternsOk P0 A ext`. -/
theorem derive_keys_a1_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl_in : s3DkCtrlExt img ext s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (s8 : State) (ssBoxPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
      s3DkCtrlExt img ext s0 s8 0xff8 → s8.trace = s0.trace →
      s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s8.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) s8
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
    let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) sf0
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
        memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  have hctrl : S3Ctrl img ext s0 sf0 0xfb4 := S3Ctrl.of_prop hctrl_in
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hss_len : ss.toList.length = 32 := ss.toList_length
  obtain ⟨ss0, ss1, ss2, ss3, hss_cells⟩ := bytes32_exists_cells4 hss_len
  have hfe0_1568 :
      memRegion (fsp + 0xfe0#64) 32 ∗ memRegion (fsp + 0x1000#64) 0x600 ⊢
        memRegion (fsp + 0xfe0#64) 1568 := by
    rw [memRegion_merge_at (fsp + 0xfe0#64) 32 0x600 (fsp + 0x1000#64)
      (by clear * -; bv_omega) (by decide)]
    exact Entails.refl _
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  refine sepWPp_conseq_oom (by
    rw [hstk_ext]
    exact sep_replace hfe0_1568 (by sep_frame) (Entails.refl _)) ?_
  obtain ⟨_, _, hfsp0⟩ := hctrl.step_ctx fsp
  refine' s3_block_to_call_ext hOk
    (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    0xfc8 (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0xfe0#64 ∧ sm.readReg64 .x1 = fsp + 0x1600#64 ∧
      sm.readReg64 .x2 = 1568#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfb4 20
    dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
  · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr1 := ht1.trans htr
    refine s3_memcpy_ext hOk (fsp + 0xfe0#64) (fsp + 0x1600#64) ct.toList _
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
    refine' s3_block_to_call_ext hOk
      (s3EntryExt img ext + bv% (ls_rel%
        "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      0xfd8 (Φ := fun sm =>
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hc2 ?_ ?_; rotate_left 1
    · have hpc := hc2.pc; have hrun := hc2.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfc8 16
      dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hc2.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm]⟩
    · intro sm3 hc3 hp3 hl3 ht3 ⟨hx20_3, hx21_3⟩
      rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr3 := ht3.trans htr2
      refine s3_shim_ext hOk _ hc3 htr3 hp3 hl3 hpanic
        (by rw [hc3.sp]; (try dsimp only [fsp]); sep_frame) ?_
      intro s4 hc4 hcs4 htr_4
      rw [hc3.sp]
      have htr4 := htr_4.trans htr3
      have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
      obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
      refine' s3_block_to_call_ext hOk
        (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
        0xfe4 (Φ := fun sm =>
          sm.readReg64 .x0 = 32#64 ∧ sm.readReg64 .x1 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
        hc4 ?_ ?_; rotate_left 1
      · have hpc := hc4.pc; have hrun := hc4.run
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfd8 12
        dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hc4.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm]⟩
      · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx20_5, hx21_5⟩
        rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr5 := ht5.trans htr4
        refine s3_call_alloc_ext hOk 32 _ hc5 hp5 hl5
          (by rw [hx0_5]; decide) (by rw [hx1_5]; decide) lay32
          (by rw [hc5.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
        · intro sm_oom1 hp_oom1 hrun_oom1 hnull1 htr_oom1
          refine sepWPp_oom_jmp (mid := s3PcExt img ext 0x1930) ?_ fun s' hpc' hrun' htr' =>
            oom_1930_ok_ext hpc' hrun' (allocFailedIn_of_append (htr5 ▸ htr' ▸ htr_oom1)) hpanic
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfe4 4
          dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hp_oom1 ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          try simp only [arm64_norm, wp_norm] at hnull1
          examples_hide_fetches; wp_steps
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
          refine' s3_block_to_call_ext hOk
            (s3EntryExt img ext + bv% (ls_rel%
              "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
            0xff8 (Φ := fun sm =>
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 26#5) = ssBoxPtr)
            hc6 ?_ ?_; rotate_left 1
          · have hpc := hc6.pc; have hrun := hc6.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xfe4 20
            dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
            have hnz6 : s6.readReg64 (.gpr 0#5) ≠ 0#64 := by
              simpa only [ssBoxPtr, arm64_norm, wp_norm] using hssNonNull
            (try dsimp only [fsp] at *); rw [← hc6.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_6 hx21_6
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
              (Entails.refl _)
              ⟨by simp only [hx20_6, arm64_norm, wp_norm], by simp only [hx21_6, arm64_norm, wp_norm],
               by simp only [ssBoxPtr, arm64_norm, wp_norm]⟩
          · intro sm7 hc7 hp7 hl7 ht7 ⟨hx20_7, hx21_7, hx26_7⟩
            rw [hc6.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr7 := ht7.trans htr6
            refine s3_shim_ext hOk _ hc7 htr7 hp7 hl7 hpanic
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
            refine sepWPp_conseq_oom ?_ (hnext s8 ssBoxPtr hc8.to_prop htr8 hx20_8 hx21_8 hx26_8)
            dsimp only [fsp, ct, ss] at htail64 hss_fold ⊢
            refine sep_replace htail64 (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hss_fold) (by sep_frame) (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
