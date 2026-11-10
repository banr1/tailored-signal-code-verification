/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysNone
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsB2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncaps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 `HandshakeKeys::derive` (`dh4? = some`) and Full Stage 3 Composition

Verifies the `dh4? = some` (192-byte secrets) branch of `<HandshakeKeys>::derive`, combines it with
`DeriveKeysNone` into `derive_keys_ok`, and composes all Stage 3 segments (`0x0760 → 0x10a4`) into
`stage3_all_ok` and `stage3_all_ok_ext`.
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
theorem derive_keys_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
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
    (hdh4_eq : dh4? = ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X ⟨W.C, W.Q⟩).x25519
          (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk))
    (hdh4_nz : SignalPqxdh.dhOptNonZero dh4? = true)
    (hdh4_len : ∀ d, dh4? = some d → d.length = 32)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4 img W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProg img W) (s0.readReg64 .lr) sg
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
      Q Qp (initOom s0) := by
  dsimp only
  cases dh4? with
  | none =>
    exact derive_keys_none_ok hh hLocal hstk hstk64 hs3 hpanic
      hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
      hdh4_eq.symm hkemNonNull hctrl htr hx20 hx21 hx26 hnext
  | some dh4 =>
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
        (hdh1_eq ▸ hdh1_nz) (hdh2_eq ▸ hdh2_nz) (hdh3_eq ▸ hdh3_nz) (hdh4_eq ▸ hdh4_nz)
    have h4_len : dh4.length = 32 := hdh4_len dh4 rfl
    have hsec_len : (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss)).length = 192 := by
      simp [buildSecrets, F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len, hss_u8_len]
    have htake32 := buildSecrets_take32_eq dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss)
    rw [hstk_ext, hss_cells ssBoxPtr, memRegion32_cells4 (secretsPtr + 160#64)]
    refine sepWPp_conseq_oom
      (by dsimp only [fsp] at h930_split ⊢
          exact sep_replace (Entails.of_eq h930_split) (by sep_frame) (Entails.refl _)) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun d0 => sepWPp_exists_elim_oom fun d1 =>
      sepWPp_exists_elim_oom fun d2 => sepWPp_exists_elim_oom fun d3 => ?_
    obtain ⟨halign0, hx29_0, hfsp0⟩ := hctrl.step_ctx fsp
    refine' s3_block_to_call hh
      (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      0x107c (Φ := fun sm =>
        sm.readReg64 .x0 = ssBoxPtr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
        sm.readReg64 (.gpr 27#5) = 192#64 ∧ sm.readReg64 (.gpr 28#5) = 160#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1044 56
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx26
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx26, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1, hx25_1, hx27_1, hx28_1⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr1 := ht1.trans htr
      have hbox32 := cells4_to_memRegion32 ssBoxPtr ss0 ss1 ss2 ss3
      have hss_fold160 :
          ((secretsPtr + 160#64) ↦₆₄ ss0) ∗ ((secretsPtr + 168#64) ↦₆₄ ss1) ∗
            ((secretsPtr + 176#64) ↦₆₄ ss2) ∗ ((secretsPtr + 184#64) ↦₆₄ ss3) =
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, hss_bv] using
          (hss_cells (secretsPtr + 160#64)).symm
      have happ160 :
          (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4)) ∗
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) =
            (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss))) :=
        append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4) (E2E.vecU8 ss) 160#64
          (by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len])
      refine s3_dealloc hh ssBoxPtr 32 _
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
      dsimp only [fsp, ss] at hstk_ext hss_fold160 happ160 ⊢
      rw [pack_cells4_append _ _ _ _ _ _ _ _ _ _ _ _ hss_fold160 happ160,
          repack_pqxdh_stk _ _ _ _ _ _ _ _ _ hstk_ext.symm]
      obtain ⟨_, _, hfsp2⟩ := hc2.step_ctx fsp
      refine' s3_block_to_call hh
        (initEntry img W - bv% (ls_rel%
          "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"
          "libsignal_cli_handshake::initiate"))
        0x1090 (Φ := fun sm =>
          sm.readReg64 .x8 = fsp + 0x930#64 ∧ sm.readReg64 .x0 = secretsPtr ∧
          sm.readReg64 .x1 = 192#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
          sm.readReg64 (.gpr 27#5) = 192#64)
        hc2 ?_ ?_; rotate_left 1
      · have hpc := hc2.pc; have hrun := hc2.run
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x107c 20
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hc2.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by simp only [hx25_2, arm64_norm, wp_norm],
           by simp only [hx28_2, arm64_norm, wp_norm],
           by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm],
           by simp only [hx22_2, arm64_norm, wp_norm], by simp only [hx25_2, arm64_norm, wp_norm],
           by simp only [hx27_2, arm64_norm, wp_norm]⟩
      · intro sm3 hc3 hp3 hl3 ht3 ⟨hx8_3, hx0_3, hx1_3, hx20_3, hx21_3, hx22_3, hx25_3, hx27_3⟩
        rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr3 := ht3.trans htr2
        refine s3_call hh (hLocal.handshakeDerive X)
          ⟨secretsPtr, buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss), fsp + 0x930#64⟩ _
          hc3 htr3 (hp3.trans (handshakeDerive_fnAddr_eq img W)) hl3 hpanic
          (by
            simp only [handshakeKeysDeriveSpec, Spec.inImage, hc3.sp, sepConj_assoc]
            refine Entails.pure_right hc3.inv
              (Entails.pure_right ⟨hx8_3, hx0_3, by rw [hx1_3, hsec_len]; decide,
                Or.inr hsec_len, htake32⟩ ?_)
            dsimp only [fsp, ss, t] at *
            sep_frame) ?_ ?_ ?_ ?_
        · intro _ _ h
          simp only [handshakeKeysDeriveSpec, Spec.inImage, rustPanicOnOom, sepConj_assoc,
            satisfies_pure_sepConj] at h
          exact h.1.1
        · intro _ _ _ h; simp [handshakeKeysDeriveSpec, Spec.inImage] at h
        · intro _ _ h; simp [handshakeKeysDeriveSpec, Spec.inImage] at h
        · intro s4a _ _ _ hcs4 _ hof4
          simp only [handshakeKeysDeriveSpec, Spec.inImage, hc3.sp, sepConj_assoc]
          refine sepWPp_pure_elim_oom fun htr_4 => ?_
          have hc4 := hof4 htr_4
          have htr4 := htr_4.trans htr3
          have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
          have hx22_4 := hcs4.2.2.2.1.trans hx22_3
          have hx25_4 := hcs4.2.2.2.2.2.2.1.trans hx25_3
          have hx27_4 := hcs4.2.2.2.2.2.2.2.2.1.trans hx27_3
          obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
          refine' s3_block_to_call hh
            (initEntry img W + bv% (ls_rel%
              "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
            0x10a4 (Φ := fun sm =>
              sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x900#64)
            hc4 ?_ ?_; rotate_left 1
          · have hpc := hc4.pc; have hrun := hc4.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1090 20
            dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hc4.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx25_4 hx27_4
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx25_4, arm64_norm, wp_norm], by simp only [hx27_4, arm64_norm, wp_norm],
               by wp_norm_goal,
               by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm],
               by simp only [hx22_4, arm64_norm, wp_norm]⟩
          · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx2_5, hx20_5, hx21_5, hx22_5⟩
            rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr5 := ht5.trans htr4
            have hsec192 :
                (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss))) ⊢
                  memRegion secretsPtr 192 :=
              pointsToBytes_entails_memRegion_len ((bytesToBv8_length _).trans hsec_len)
            refine s3_dealloc hh secretsPtr 192 _
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
            have htail := tail_locals_collapse fsp hekASkLen hkpkLen secretsPtr 160#64
            subst hdh1_eq hdh2_eq hdh3_eq
            dsimp only [t] at hdh4_eq
            conv at hhkEq => lhs; rw [← hdh4_eq]
            refine sepWPp_conseq_oom ?_
              (hnext s_end _ _ (8#8 :: ct.toList) _ kemCtPtr
                { ctrl := hc_end, trace := htr_final, files := hfs_final, x8 := hs3.x8,
                  bundleEq := hs3.bundleEq, trustedOk := hs3.trustedOk, kpOk := hs3.kpOk,
                  ekPairEq := hs3.ekPairEq, opkIdEq := hs3.opkIdEq,
                  keysOk := hkeysOk, kemCtEq := hctEq, hkSlotEq := rfl,
                  pqspkNonNull := hs3.pqspkNonNull, kemCtNonNull := hkemNonNull,
                  x20 := hcs_end.2.1.trans hx20_5, x21 := hcs_end.2.2.1.trans hx21_5,
                  x22 := hcs_end.2.2.2.1.trans hx22_5 })
            unfold S3InvPrefix; dsimp only [stage4Mem]
            refine Entails.pure_right ⟨hctLen1569, hhkLen100⟩ ?_
            dsimp only [fsp, ct, ss, t] at hhkEq hstk_full htail ⊢
            rw [hhkEq]
            refine sep_replace htail (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hstk_full) (by sep_frame) (by sep_frame)

/-- Full Stage 3 composition (`0x0760 → 0x10a4` and early `Err` / OOM exits) on `initProg img W`. -/
theorem stage3_all_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4 img W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) := by
  refine dh1_step_ok hh hLocal hS hstk hstk64 hs3 hpost hpanic
    fun s_a secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hc_a htr_a
      hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a => ?_
  have hdh1_len : dh1.length = 32 := hdh1_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh2_step_ok hh hLocal hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hsecNonNull hc_a htr_a hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a
    fun s_b dh2 hdh2_eq hdh2_nz hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b => ?_
  have hdh2_len : dh2.length = 32 := hdh2_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh3_step_ok hh hLocal hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hdh2_len hsecNonNull hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b
    fun s_c dh3 hdh3_eq hdh3_nz hc_c htr_c hx20_c hx21_c hx22_c hx26_c => ?_
  have hdh3_len : dh3.length = 32 := hdh3_eq ▸ modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
  refine dh4_step_ok hh hLocal hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hdh2_len hdh3_len hsecNonNull hc_c htr_c hx20_c hx21_c hx22_c hx26_c
    fun s_d dh4? hdh4_eq hdh4_nz hdh4_len hc_d htr_d hx20_d hx21_d hx22_d => ?_
  refine kem_coins_a_ok hh hCoins hcoinsLt hstk hstk64 hs3 hpanic
    hc_d htr_d hx20_d hx21_d hx22_d
    fun s_e z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
      hc_e htr_e hx20_e hx21_e => ?_
  refine kem_coins_b_ok hh hCoins hcoinsLt hpanic hc_e htr_e hx20_e hx21_e
    fun s_f hc_f htr_f hx20_f hx21_f => ?_
  refine kem_coins_c_ok hh hCoins hcoinsLt hpanic hc_f htr_f hx20_f hx21_f
    fun s_g hc_g htr_g hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g => ?_
  refine kem_encaps_ok hh hstk hstk64 hs3 hpanic hc_g htr_g
    hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g
    fun s_h hc_h htr_h hx20_h hx21_h => ?_
  refine derive_keys_a_ok hh hLocal hpanic hc_h htr_h hx20_h hx21_h
    fun s_i ssBoxPtr kemCtPtr hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i => ?_
  exact derive_keys_ok hh hLocal hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i hnext

/-! ## Extern-parameterized `derive_keys_ok_ext` and `stage3_all_ok_ext` -/

set_option Elab.async false

attribute [local irreducible] libsignalSessionCode Program.fnOff in
set_option maxHeartbeats 1200000 in
theorem derive_keys_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr kemCtPtr : BitVec 64}
    {opkId : BitVec 32} {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 sg : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hHandshakeDerive : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliHandshakeDeriveName)
      (Pqxdh.Initiator.handshakeKeysDeriveSpecExt (modelPrims X P0) A img))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_eq : dh1 = (modelPrims X P0).x25519
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ikASk
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh1_nz : dh1 ≠ List.replicate 32 0) (hdh1_len : dh1.length = 32)
    (hdh2_eq : dh2 = (modelPrims X P0).x25519
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.ikB)
    (hdh2_nz : dh2 ≠ List.replicate 32 0) (hdh2_len : dh2.length = 32)
    (hdh3_eq : dh3 = (modelPrims X P0).x25519
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
      (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).bundle.spkB)
    (hdh3_nz : dh3 ≠ List.replicate 32 0) (hdh3_len : dh3.length = 32)
    (hdh4_eq : dh4? = ((initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be
      (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
        (modelPrims X P0).x25519
          (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)).ekASk
          opkPk))
    (hdh4_nz : SignalPqxdh.dhOptNonZero dh4? = true)
    (hdh4_len : ∀ d, dh4? = some d → d.length = 32)
    (hkemNonNull : kemCtPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 sg 0x1044) (htr : sg.trace = s0.trace)
    (hx20 : sg.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sg.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Ext img P0 ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
        opkId s0 s4 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sg
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
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
      Q Qp (initOom s0) := by
  dsimp only
  cases dh4? with
  | none =>
    exact derive_keys_none_ok_ext hOk hHandshakeDerive hstk hstk64 hs3 hpanic
      hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
      hdh4_eq.symm hkemNonNull hctrl htr hx20 hx21 hx26 hnext
  | some dh4 =>
    dsimp only [dhPrefix, dhRemAt, dhLenWord]
    set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    set t := padCoins x.coins
    set ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
    set ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
    obtain ⟨_, _, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
    have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
    have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
      Nat.le_trans (by decide) (stk_sub_ge_base hstk)
    have hsub_pqExt : pqxdhEntryStackExt ≤ stk - cliInitiateFrame :=
      Ext.pqxdhEntryStk_le_frame hstk
    have hstk_to_pqExt : ∀ R : SepProp,
        stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗ R =
        stackAt fsp pqxdhEntryStackExt ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStackExt) ∗ R := by
      intro R
      rw [← sepConj_assoc, sepConj_comm (stackAt fsp pqxdhEntryStack),
          ← stackAt_sub_split_init fsp hsub_pq (stk_sub_le_2pow64 hstk64),
          stackAt_sub_split_init fsp hsub_pqExt (stk_sub_le_2pow64 hstk64),
          sepConj_comm _ (stackAt fsp pqxdhEntryStackExt), sepConj_assoc]
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
    have hstk_ext := stackAt_sub_split_init fsp
      (by decide : extHookStack ≤ pqxdhEntryStackExt) (by decide)
    obtain ⟨hkeysOk, hctEq, hhkEq, hctLen1569, hhkLen100⟩ :=
      stage4_keysOk_of_parts X P0 kp be x.coins hs3.signaturesVerify
        (hdh1_eq ▸ hdh1_nz) (hdh2_eq ▸ hdh2_nz) (hdh3_eq ▸ hdh3_nz) (hdh4_eq ▸ hdh4_nz)
    have h4_len : dh4.length = 32 := hdh4_len dh4 rfl
    have hsec_len : (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss)).length = 192 := by
      simp [buildSecrets, F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len, hss_u8_len]
    have htake32 := buildSecrets_take32_eq dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss)
    rw [hstk_to_pqExt, hstk_ext, hss_cells ssBoxPtr, memRegion32_cells4 (secretsPtr + 160#64)]
    refine sepWPp_conseq_oom
      (by dsimp only [fsp] at h930_split ⊢
          exact sep_replace (Entails.of_eq h930_split) (by sep_frame) (Entails.refl _)) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun d0 => sepWPp_exists_elim_oom fun d1 =>
      sepWPp_exists_elim_oom fun d2 => sepWPp_exists_elim_oom fun d3 => ?_
    obtain ⟨halign0, hx29_0, hfsp0⟩ := hctrl.step_ctx fsp
    refine' Ext.s3_block_to_call hOk
      (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      0x107c (Φ := fun sm =>
        sm.readReg64 .x0 = ssBoxPtr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
        sm.readReg64 (.gpr 27#5) = 192#64 ∧ sm.readReg64 (.gpr 28#5) = 160#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1044 56
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx26
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx26, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · intro sm1 hc1 hp1 hl1 ht1 ⟨hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1, hx25_1, hx27_1, hx28_1⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr1 := ht1.trans htr
      have hbox32 := cells4_to_memRegion32 ssBoxPtr ss0 ss1 ss2 ss3
      have hss_fold160 :
          ((secretsPtr + 160#64) ↦₆₄ ss0) ∗ ((secretsPtr + 168#64) ↦₆₄ ss1) ∗
            ((secretsPtr + 176#64) ↦₆₄ ss2) ∗ ((secretsPtr + 184#64) ↦₆₄ ss3) =
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, hss_bv] using
          (hss_cells (secretsPtr + 160#64)).symm
      have happ160 :
          (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4)) ∗
            ((secretsPtr + 160#64) ↦ₛ bytesToBv8 (E2E.vecU8 ss)) =
            (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss))) :=
        append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4) (E2E.vecU8 ss) 160#64
          (by simp [F_X25519, hdh1_len, hdh2_len, hdh3_len, h4_len])
      refine Ext.s3_dealloc hOk ssBoxPtr 32 _
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
      dsimp only [fsp, ss] at hstk_ext hss_fold160 happ160 ⊢
      rw [pack_cells4_append _ _ _ _ _ _ _ _ _ _ _ _ hss_fold160 happ160,
          repack_pqxdh_stk _ _ _ _ _ _ _ _ _ hstk_ext.symm]
      obtain ⟨_, _, hfsp2⟩ := hc2.step_ctx fsp
      refine' Ext.s3_block_to_call hOk
        (initEntryExt img ext - bv% (ls_rel%
          "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"
          "libsignal_cli_handshake::initiate"))
        0x1090 (Φ := fun sm =>
          sm.readReg64 .x8 = fsp + 0x930#64 ∧ sm.readReg64 .x0 = secretsPtr ∧
          sm.readReg64 .x1 = 192#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x900#64 ∧ sm.readReg64 (.gpr 25#5) = secretsPtr ∧
          sm.readReg64 (.gpr 27#5) = 192#64)
        hc2 ?_ ?_; rotate_left 1
      · have hpc := hc2.pc; have hrun := hc2.run
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x107c 20
        dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hc2.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by simp only [hx25_2, arm64_norm, wp_norm],
           by simp only [hx28_2, arm64_norm, wp_norm],
           by simp only [hx20_2, arm64_norm, wp_norm], by simp only [hx21_2, arm64_norm, wp_norm],
           by simp only [hx22_2, arm64_norm, wp_norm], by simp only [hx25_2, arm64_norm, wp_norm],
           by simp only [hx27_2, arm64_norm, wp_norm]⟩
      · intro sm3 hc3 hp3 hl3 ht3 ⟨hx8_3, hx0_3, hx1_3, hx20_3, hx21_3, hx22_3, hx25_3, hx27_3⟩
        rw [hc2.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr3 := ht3.trans htr2
        refine Ext.s3_call hOk (hHandshakeDerive X)
          ⟨secretsPtr, buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss), fsp + 0x930#64⟩ _
          hc3 htr3 (hp3.trans (Ext.handshakeDerive_fnAddr_eq img ext)) hl3 hpanic
          (by
            simp only [handshakeKeysDeriveSpecExt, handshakeKeysDeriveSpecAt,
              Spec.inImage, hc3.sp, sepConj_assoc]
            refine Entails.pure_right hc3.inv
              (Entails.pure_right ⟨hx8_3, hx0_3, by rw [hx1_3, hsec_len]; decide,
                Or.inr hsec_len, htake32⟩ ?_)
            dsimp only [fsp, ss, t] at *
            sep_frame) ?_ ?_ ?_ ?_
        · intro _ _ h
          simp only [handshakeKeysDeriveSpecExt, handshakeKeysDeriveSpecAt,
            Spec.inImage, rustPanicOnOom, sepConj_assoc, satisfies_pure_sepConj] at h
          exact h.1.1
        · intro _ _ _ h; simp [handshakeKeysDeriveSpecExt, handshakeKeysDeriveSpecAt, Spec.inImage] at h
        · intro _ _ h; simp [handshakeKeysDeriveSpecExt, handshakeKeysDeriveSpecAt, Spec.inImage] at h
        · intro s4a _ _ _ hcs4 _ hof4
          simp only [handshakeKeysDeriveSpecExt, handshakeKeysDeriveSpecAt,
            Spec.inImage, hc3.sp, sepConj_assoc]
          refine sepWPp_pure_elim_oom fun htr_4 => ?_
          have hc4 := hof4 htr_4
          have htr4 := htr_4.trans htr3
          have hx20_4 := hcs4.2.1.trans hx20_3; have hx21_4 := hcs4.2.2.1.trans hx21_3
          have hx22_4 := hcs4.2.2.2.1.trans hx22_3
          have hx25_4 := hcs4.2.2.2.2.2.2.1.trans hx25_3
          have hx27_4 := hcs4.2.2.2.2.2.2.2.2.1.trans hx27_3
          obtain ⟨_, _, hfsp4⟩ := hc4.step_ctx fsp
          refine' Ext.s3_block_to_call hOk
            (initEntryExt img ext + bv% (ls_rel%
              "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
            0x10a4 (Φ := fun sm =>
              sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x900#64)
            hc4 ?_ ?_; rotate_left 1
          · have hpc := hc4.pc; have hrun := hc4.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1090 20
            dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hc4.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx25_4 hx27_4
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx25_4, arm64_norm, wp_norm], by simp only [hx27_4, arm64_norm, wp_norm],
               by wp_norm_goal,
               by simp only [hx20_4, arm64_norm, wp_norm], by simp only [hx21_4, arm64_norm, wp_norm],
               by simp only [hx22_4, arm64_norm, wp_norm]⟩
          · intro sm5 hc5 hp5 hl5 ht5 ⟨hx0_5, hx1_5, hx2_5, hx20_5, hx21_5, hx22_5⟩
            rw [hc4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have htr5 := ht5.trans htr4
            have hsec192 :
                (secretsPtr ↦ₛ bytesToBv8 (buildSecrets dh1 dh2 dh3 (some dh4) (E2E.vecU8 ss))) ⊢
                  memRegion secretsPtr 192 :=
              pointsToBytes_entails_memRegion_len ((bytesToBv8_length _).trans hsec_len)
            refine Ext.s3_dealloc hOk secretsPtr 192 _
              hc5 htr5 hp5 hl5 hx0_5 (by rw [hx1_5]; decide) (by rw [hx2_5]; decide) lay192 hpanic
              (by rw [hc5.sp, hstk_ext]; dsimp only [fsp, ss, t] at *
                  exact sep_replace hsec192 (by sep_frame) (by sep_frame)) ?_
            intro s_end hc_end hcs_end htr_end
            rw [hc5.sp]
            have htr_final := htr_end.trans htr5
            have hfs_final : s_end.fs.files = x.F :=
              hc_end.files0.trans hs3.ctrl.files0.symm |>.trans hs3.files
            have hstk_full :
                memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStackExt) (pqxdhEntryStackExt - extHookStack) ∗
                  stackAt fsp extHookStack ∗
                  memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                    (stk - cliInitiateFrame - pqxdhEntryStackExt) =
                  stackAt fsp (stk - cliInitiateFrame) := by
              rw [← sepConj_assoc, ← hstk_ext, sepConj_comm,
                  ← stackAt_sub_split_init fsp hsub_pqExt (stk_sub_le_2pow64 hstk64)]
            have htail := tail_locals_collapse fsp hekASkLen hkpkLen secretsPtr 160#64
            subst hdh1_eq hdh2_eq hdh3_eq
            dsimp only [t] at hdh4_eq
            conv at hhkEq => lhs; rw [← hdh4_eq]
            refine sepWPp_conseq_oom ?_
              (hnext s_end _ _ (8#8 :: ct.toList) _ kemCtPtr
                { ctrl := hc_end, trace := htr_final, files := hfs_final, x8 := hs3.x8,
                  bundleEq := hs3.bundleEq, trustedOk := hs3.trustedOk, kpOk := hs3.kpOk,
                  ekPairEq := hs3.ekPairEq, opkIdEq := hs3.opkIdEq,
                  keysOk := hkeysOk, kemCtEq := hctEq, hkSlotEq := rfl,
                  pqspkNonNull := hs3.pqspkNonNull, kemCtNonNull := hkemNonNull,
                  x20 := hcs_end.2.1.trans hx20_5, x21 := hcs_end.2.2.1.trans hx21_5,
                  x22 := hcs_end.2.2.2.1.trans hx22_5 })
            unfold S3InvPrefix; dsimp only [stage4Mem]
            refine Entails.pure_right ⟨hctLen1569, hhkLen100⟩ ?_
            dsimp only [fsp, ct, ss, t] at hhkEq hstk_full htail ⊢
            rw [hhkEq]
            refine sep_replace htail (by sep_frame) ?_
            exact sep_replace (Entails.of_eq hstk_full) (by sep_frame) (by sep_frame)

/-- Full Stage 3 composition (`0x0760 → 0x10a4` and early `Err` / OOM exits) under `CliExternsOk P0 A ext`. -/
theorem stage3_all_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hCalcAgree : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (Ext.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P0) A img))
    (hKemCtSer : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliKemCtSerializeName)
      (kemCiphertextSerializeExtSpec A))
    (hHandshakeDerive : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliHandshakeDeriveName)
      (Pqxdh.Initiator.handshakeKeysDeriveSpecExt (modelPrims X P0) A img))
    (hS : S.initiate = initDef X P0)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Ext img P0 ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
        opkId s0 s4 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) := by
  refine dh1_step_ok_ext hOk hCalcAgree hS hstk hstk64 hs3 hpost hpanic
    fun s_a secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hc_a htr_a
      hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a => ?_
  have hdh1_len : dh1.length = 32 := hdh1_eq ▸ modelPrims_x25519_len X P0 _ _
  refine dh2_step_ok_ext hOk hCalcAgree hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hsecNonNull hc_a htr_a hx20_a hx21_a hx22_a hx24_a hx25_a hx26_a
    fun s_b dh2 hdh2_eq hdh2_nz hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b => ?_
  have hdh2_len : dh2.length = 32 := hdh2_eq ▸ modelPrims_x25519_len X P0 _ _
  refine dh3_step_ok_ext hOk hCalcAgree hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hdh2_len hsecNonNull hc_b htr_b hx20_b hx21_b hx22_b hx24_b hx26_b
    fun s_c dh3 hdh3_eq hdh3_nz hc_c htr_c hx20_c hx21_c hx22_c hx26_c => ?_
  have hdh3_len : dh3.length = 32 := hdh3_eq ▸ modelPrims_x25519_len X P0 _ _
  refine dh4_step_ok_ext hOk hCalcAgree hS hstk hstk64 hs3 hpost hpanic
    hdh1_len hdh2_len hdh3_len hsecNonNull hc_c htr_c hx20_c hx21_c hx22_c hx26_c
    fun s_d dh4? hdh4_eq hdh4_nz hdh4_len hc_d htr_d hx20_d hx21_d hx22_d => ?_
  refine kem_coins_a_ok_ext hOk hCoins hcoinsLt hstk hstk64 hs3 hpanic
    hc_d htr_d hx20_d hx21_d hx22_d
    fun s_e z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23
      hc_e htr_e hx20_e hx21_e => ?_
  refine kem_coins_b_ok_ext hOk hCoins hcoinsLt hpanic hc_e htr_e hx20_e hx21_e
    fun s_f hc_f htr_f hx20_f hx21_f => ?_
  refine kem_coins_c_ok_ext hOk hCoins hcoinsLt hpanic hc_f htr_f hx20_f hx21_f
    fun s_g hc_g htr_g hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g => ?_
  refine kem_encaps_ok_ext hOk hstk hstk64 hs3.bundleEq hpanic hc_g.to_ctrlTuple htr_g
    hx20_g hx21_g hx25_g hx22_g hx26_g hx23_g hx27_g hx28_g hx24_g
    fun s_h hc_h htr_h hx20_h hx21_h => ?_
  refine derive_keys_a_ok_ext hOk hstk hstk64 hKemCtSer hpanic hc_h htr_h hx20_h hx21_h
    fun s_i ssBoxPtr kemCtPtr hkemNonNull hc_i htr_i hx20_i hx21_i hx26_i => ?_
  exact derive_keys_ok_ext hOk hHandshakeDerive hstk hstk64 hs3 hpanic
    hdh1_eq hdh1_nz hdh1_len hdh2_eq hdh2_nz hdh2_len hdh3_eq hdh3_nz hdh3_len
    hdh4_eq hdh4_nz hdh4_len hkemNonNull (InInitiateExt.of_ctrlTuple hc_i) htr_i
    hx20_i hx21_i hx26_i hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
