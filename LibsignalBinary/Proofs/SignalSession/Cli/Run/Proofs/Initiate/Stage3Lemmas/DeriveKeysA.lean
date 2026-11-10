/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Ciphertext Boxing and Serialization (`0x0ff8 → 0x1044`)

Allocates `ctBoxPtr` (1568 bytes, OOM → `0x193c`), copies `ct`, invokes
`<kem::Ciphertext>::serialize` (`kemCtPtr`, 1569 bytes), stores `(kemCtPtr, 1569)` at
`[fsp + 0x60 .. 0x70)`, and frees `ctBoxPtr` (`derive_keys_a_ok` and `derive_keys_a_ok_ext`).
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

private theorem ct1568_split_hdr (p : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 1568) :
    (p ↦ₛ bs) ⊢
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗ memRegion (p + 16#64) 1552 := by
  refine Entails.trans (pointsToBytes_entails_memRegion_len h) ?_
  rw [← memRegion_merge_at p 8 1560 (p + 8#64) (by clear * -; bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 1552 (p + 16#64) (by clear * -; bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  exact Entails.of_eq (by ac_rfl)

private theorem s3_step_1030_1044 {img : Obj.Image} {W : CliHooks} {s : State}
    (kemCtPtr ctBoxPtr ssBoxPtr g60 g68 : BitVec 64) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0x1030)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = kemCtPtr)
    (hx1 : s.readReg64 .x1 = 1569#64)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx25 : s.readReg64 (.gpr 25#5) = ctBoxPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = ssBoxPtr) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)))
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      s (((s.sp + 0x60#64) ↦₆₄ g60) ∗ ((s.sp + 0x68#64) ↦₆₄ g68) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 1569#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0x1044 ∧
        (sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
          sm.readReg64 .x2 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64 ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1030 20
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx0 hx1 hx20 hx21 hx25 hx26
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
    (by (try simp only [hx0, hx1, arm64_norm, wp_norm]); sep_frame)
    ⟨by simp only [hx25, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
     by simp only [hx26, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 1200000 in
theorem derive_keys_a_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiate img W s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      InInitiate img W s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
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
  refine derive_keys_a1_ok hh hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8 => ?_
  try dsimp only at hx20_8 hx21_8 ⊢
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  obtain ⟨_, _, hfsp8⟩ := hc8.step_ctx fsp
  refine' s3_block_to_call hh
    (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    0x1004 (Φ := fun sm =>
      sm.readReg64 .x0 = 1568#64 ∧ sm.readReg64 .x1 = 1#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 26#5) = ssBoxPtr)
    hc8 ?_ ?_; rotate_left 1
  · have hpc := hc8.pc; have hrun := hc8.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xff8 12
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hc8.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20_8 hx21_8 hx26_8
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20_8, arm64_norm, wp_norm], by simp only [hx21_8, arm64_norm, wp_norm],
       by simp only [hx26_8, arm64_norm, wp_norm]⟩
  · intro sm9 hc9 hp9 hl9 ht9 ⟨hx0_9, hx1_9, hx20_9, hx21_9, hx26_9⟩
    rw [hc8.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr9 := ht9.trans htr8
    refine s3_call_alloc hh 1568 _ hc9 hp9 hl9
      (by rw [hx0_9]; decide) (by rw [hx1_9]; decide) lay1568
      (by rw [hc9.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
    · intro sm_oom2 hp_oom2 hrun_oom2 hnull2 htr_oom2
      refine sepWPp_oom_jmp (mid := initPc img W 0x193c) ?_ fun s' hpc' hrun' htr' =>
        oom_193c_ok hpc' hrun' (allocFailedIn_of_append (htr9 ▸ htr' ▸ htr_oom2)) hpanic
      code_fetches_range libsignalSessionCode initS3 img.base
        (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1004 4
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
        BitVec.ofNat_eq_ofNat] at hp_oom2 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      try simp only [arm64_norm, wp_norm] at hnull2
      examples_hide_fetches; wp_steps
      exact SepWP.done (by wp_norm_goal) hrun_oom2 ⟨rfl, by wp_norm_goal, hrun_oom2, rfl⟩
    · intro s10 hc10 hcs10 hctNonNull htr_10
      set ctBoxPtr := s10.readReg64 .x0
      rw [hc9.sp]
      have htr10 := htr_10.trans htr9
      have hx20_10 := hcs10.2.1.trans hx20_9; have hx21_10 := hcs10.2.2.1.trans hx21_9
      have hx26_10 := hcs10.2.2.2.2.2.2.2.1.trans hx26_9
      obtain ⟨_, _, hfsp10⟩ := hc10.step_ctx fsp
      refine' s3_block_to_call hh
        (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
        0x101c (Φ := fun sm =>
          sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
          sm.readReg64 .x2 = 1568#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = 1568#64 ∧
          sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)
        hc10 ?_ ?_; rotate_left 1
      · have hpc := hc10.pc; have hrun := hc10.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1004 24
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        have hnz10 : s10.readReg64 (.gpr 0#5) ≠ 0#64 := by
          simpa only [ctBoxPtr, arm64_norm, wp_norm] using hctNonNull
        (try dsimp only [fsp] at *); rw [← hc10.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_10 hx21_10 hx26_10
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [ctBoxPtr, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_10, arm64_norm, wp_norm], by simp only [hx21_10, arm64_norm, wp_norm],
           by wp_norm_goal, by simp only [ctBoxPtr, arm64_norm, wp_norm],
           by simp only [hx26_10, arm64_norm, wp_norm]⟩
      · intro sm11 hc11 hp11 hl11 ht11
          ⟨hx0_11, hx1_11, hx2_11, hx20_11, hx21_11, hx22_11, hx25_11, hx26_11⟩
        rw [hc10.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr11 := ht11.trans htr10
        refine s3_memcpy hh ctBoxPtr (fsp + 0xfe0#64) ct.toList _
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
        refine' s3_block_to_call hh
          (initEntry img W - bv% (ls_rel%
            "<libsignal_protocol::kem::Ciphertext>::serialize"
            "libsignal_cli_handshake::initiate"))
          0x1030 (Φ := fun sm =>
            sm.readReg64 .x0 = fsp + 0x1600#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
            sm.readReg64 (.gpr 26#5) = ssBoxPtr)
          hc12 ?_ ?_; rotate_left 1
        · have hpc := hc12.pc; have hrun := hc12.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExterns W))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x101c 20
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hc12.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_12 hx21_12 hx22_12 hx25_12 hx26_12
          examples_hide_fetches; wp_steps
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
          refine s3_call hh hLocal.kemCtSerialize
            (fsp + 0x1600#64, ctBoxPtr, ct.toList) _
            hc13 htr13 (hp13.trans (kemCtSerialize_fnAddr_eq img W)) hl13 hpanic
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
            refine' s3_block_to_call hh
              (initEntry img W + bv% (ls_rel%
                "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
              0x1044 (Φ := fun sm =>
                sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
                sm.readReg64 .x2 = 1#64 ∧
                sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
                sm.readReg64 (.gpr 26#5) = ssBoxPtr)
              hc14 ?_ ?_; rotate_left 1
            · have hpc := hc14.pc
              dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt] at hpc ⊢
              rw [hfsp14]
              exact s3_step_1030_1044 kemCtPtr ctBoxPtr ssBoxPtr g68 g60 _ halign14 hpc hc14.run
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
              refine s3_dealloc hh ctBoxPtr 1568 _
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

/-! ## Extern-parameterized `derive_keys_a2_ok_ext` and `derive_keys_a_ok_ext` -/

private abbrev s3ProgExt (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt img.base (cliExternsWith ext)
private abbrev s3EntryExt (img : Obj.Image) (ext : String → Option (State → State)) : BitVec 64 :=
  (s3ProgExt img ext).fnAddr cliInitiateName
private abbrev s3PcExt (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) :
    BitVec 64 := s3EntryExt img ext + BitVec.ofNat 64 k

/-- Control-state invariant at relative offset `k` on `tripleRatchetProgAtExt img.base (cliExternsWith ext)`. -/
abbrev s3DkACtrlExt (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop :=
  let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
  s.pc = prog.fnAddr cliInitiateName + BitVec.ofNat 64 k ∧ s.status = .Running ∧
  s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧ s.readReg64 .fp = s0.sp - 0x60#64 ∧
  s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧ s.fs.files = s0.fs.files ∧
  ImgCallInv img s ∧ calleeSavedVRegs s = calleeSavedVRegs s0 ∧ s0.spAligned = true

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
    {s0 s : State} {k : Nat} (h : s3DkACtrlExt img ext s0 s k) : S3Ctrl img ext s0 s k := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem S3Ctrl.to_prop {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s3DkACtrlExt img ext s0 s k := by
  exact ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

private theorem S3Ctrl.spAligned_cur {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) : s.spAligned = true := by
  have h0 : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  simp only [State.spAligned, h.sp, cliInitiateFrame_eq, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq; have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢; omega

private theorem S3Ctrl.step_ctx {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (h : S3Ctrl img ext s0 s k) (fsp : BitVec 64)
    (hf : fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by rfl) :
    (s.sp &&& 15#64 == 0#64) = true ∧ s.readReg64 (.gpr 29#5) = s.sp + 7312#64 ∧ fsp = s.sp := by
  have ha := h.spAligned_cur; simp only [State.spAligned] at ha
  have hsp : s.sp = s0.sp - 7408#64 := h.sp
  have hfp : s.readReg64 (.gpr 29#5) = s0.sp - 96#64 := h.fp
  exact ⟨ha, by rw [hfp, hsp]; bv_omega, hf.trans h.sp.symm⟩

private theorem s3_withPanics_cliExternsWith (ext : String → Option (State → State)) :
    Rust.withPanics (cliExternsWith ext) = cliExternsWith ext :=
  withPanics_withCliPanics ext

private theorem s3_quietEv_false_of_isFsChange (e : TraceEvent) (h : e.isFsChange = true) :
    ¬ QuietEv e := by
  cases e with
  | writeByte st _ => cases st <;> simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢
  | _ => simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢

private theorem s3_externAt_fsTraced {prog : Program}
    (hX : ∀ n f, prog.externs n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hO : ∀ n f, prog.overrides n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    {pc : BitVec 64} {f : State → State} (h : prog.externAt? pc = some f) :
    HookFsTraced (fun e => e.isFsChange = true) f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩ <;>
    { obtain ⟨⟨n, _⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
      dsimp only at hno; split at hno; · first | exact hX n f hno | exact hO n f hno
      · cases hno }

private theorem rebase_traceFsSound (C : Program) (b : BitVec 64) (hsvc : C.svc = execSyscall)
    {P0 : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P0 A ext) :
    TraceFsSound (C.rebase b (Rust.withPanics (cliExternsWith ext))) := by
  refine TraceFsSound.of_isFs s3_quietEv_false_of_isFsChange fun s s' hst => ?_
  refine hst.files_eq_of_noFs (fun _ h => h)
    (fun _ _ h => s3_externAt_fsTraced ?_ (fun _ _ hn => by cases C; cases hn) h) (by cases C; exact hsvc)
  intro name f hf; cases C; change (Rust.withPanics (cliExternsWith ext)) name = some f at hf
  rw [s3_withPanics_cliExternsWith] at hf; simp only [cliExternsWith, withCliPanics] at hf
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
    (h : S3Ctrl img ext s0 s k_in) (hsteps : Steps (s3ProgExt img ext) s sm)
    (hpcm : sm.pc = s3PcExt img ext k_out) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s.sp) (hcsm : CalleeSavedPreserved s sm) (htrm : sm.trace = s.trace) :
    S3Ctrl img ext s0 sm k_out := by
  rcases hcsm with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  have hfs_eq := TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
  exact ⟨hpcm, hrunm, hspm.trans h.sp, hfp.trans h.fp, hx19.trans h.x19,
    hfs_eq.trans h.files0, h.inv.of_steps hsteps, hvregs.trans h.vregs, h.spAligned⟩

private theorem s3_pc_sub_entry (a b : BitVec 64) :
    a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

private theorem s3_block_to_call_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext)
    (callee : BitVec 64) {k_in : Nat} (k_out : Nat) {s0 s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {Φ : State → Prop} (hctrl : S3Ctrl img ext s0 s k_in)
    (hwp : SepWP (s3ProgExt img ext) callee s P (fun sm Pm =>
      sm.trace = s.trace ∧ (Pm ⊢ P') ∧ sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
      sm.readReg64 .lr = s3PcExt img ext k_out ∧ Φ sm))
    (hcont : ∀ sm : State, S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) →
      sm.pc = callee → sm.readReg64 .lr = s3PcExt img ext k_out → sm.trace = s.trace → Φ sm →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm P' Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  intro R hm hL
  rcases hwp.elim hm hL with
      ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, htrm, hent, hsp, hfp, hx19, hvregs, hlrm, hphi⟩ | ⟨_, hf⟩⟩
  · have hfs_eq := TraceFsSound.files_eq (s3_traceFsSound img hOk) hsteps (evs := []) (by simpa using htrm) NoFsEv.nil
    have hctrl' : S3Ctrl img ext s0 sm ((sm.pc - s3EntryExt img ext).toNat) :=
      ⟨s3_pc_sub_entry sm.pc (s3EntryExt img ext),
       hrunm, hsp.trans hctrl.sp, hfp.trans hctrl.fp, hx19.trans hctrl.x19,
       hfs_eq.trans hctrl.files0, hctrl.inv.of_steps hsteps, hvregs.trans hctrl.vregs, hctrl.spAligned⟩
    obtain ⟨sf, hsteps', hout⟩ := hcont sm hctrl' hpcm hlrm htrm hphi R
      (Satisfies.mono (sepConj_mono_left hent) hmm) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_call_ext {α : Type} {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext) {callee : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (s3ProgExt img ext) callee spec) (g : α) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = callee) (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ spec.pre g s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp), (sm.mem ⊨ spec.onPanic g s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onExit g code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onOom g s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = s3PcExt img ext k_out → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (sm.trace = s.trace → S3Ctrl img ext s0 sm k_out) →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm (spec.post g s sm ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  refine sepWPp_conseq_oom hpre ?_; intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre g s ∗ (F ∗ R') := by rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome g (F ∗ R') s hpc hctrl.run hm_pre (S3Ctrl.spAligned_cur hctrl) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm (hctrl.inv.of_steps hsteps)
      (S3Ctrl.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic g s sm ∗ F) ∗ R' := by rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by simpa only [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan, hpanic sm _ (initPanicPost_of_allocFailed _ halloc0)⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

private theorem s3_hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)}
    {sym : String} {spec : Spec α} (hnp : E2E.isImagePanicSymbol sym = false) (h : HookSat ext sym spec) :
    HookSat (cliExternsWith ext) sym spec := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnp).trans hf, hok⟩

private theorem fnAddr_initExt_eq (img : Obj.Image) (ext : String → Option (State → State))
    {name : String} {off : Nat} (hoff : libsignalSessionCode.fnOff name = off) :
    (s3ProgExt img ext).fnAddr name = img.base + BitVec.ofNat 64 off := by
  simp only [s3ProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, hoff]

private theorem kemCtSerialize_fnAddr_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    s3EntryExt img ext - bv% (ls_rel% "<libsignal_protocol::kem::Ciphertext>::serialize"
      "libsignal_cli_handshake::initiate") = (s3ProgExt img ext).fnAddr cliKemCtSerializeName := by
  dsimp only [s3EntryExt]
  rw [fnAddr_initExt_eq img ext cliInitiate_fnOff, fnAddr_initExt_eq img ext cliKemCtSerialize_fnOff]; bv_omega

private theorem memcpy_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      CliExt.memcpySpec := by
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "memcpy")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (stub := num% (ls_off% "memcpy")) cliInitiate_fnOff rfl (by decide) (ls_hook% "memcpy")
    (by simp [Rust.isPanicSymbol])
    (s3_hookSat_cliExternsWith (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol]) hOk.memcpy)

private theorem alloc_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      (rustAllocSpecWithStack A extHookStack) := by
  obtain ⟨f, hf, hok⟩ := hOk.alloc.alloc
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := allocName)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (stub := num% (ls_off% "__rustc::__rust_alloc")) cliInitiate_fnOff rfl (by decide)
    (ls_hook% "__rustc::__rust_alloc") (by simp [Rust.isPanicSymbol, allocName])
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext
          (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, allocName])).trans hf,
     hookOk_rustAllocWithStack hok (by decide) (by decide)⟩

private theorem dealloc_ok_at_init_ext (img : Obj.Image) {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) :
    subroutine_ok (s3ProgExt img ext)
      (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      (rustDeallocExternSpecWithStack A extHookStack) := by
  obtain ⟨f, hf, hok⟩ := hOk.alloc.dealloc
  exact hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := deallocName)
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (stub := num% (ls_off% "__rustc::__rust_dealloc")) cliInitiate_fnOff rfl (by decide)
    (ls_hook% "__rustc::__rust_dealloc") (by simp [Rust.isPanicSymbol, deallocName])
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext
          (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, deallocName])).trans hf,
     hookOk_rustDeallocExternWithStack hok (by decide) (by decide)⟩

private theorem panic_alloc_error_at_init_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (s3ProgExt img ext).externAt?
      (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) =
      some Rust.panicked := by
  exact panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := cliInitiateName) (hname := "alloc::alloc::handle_alloc_error")
    (off := num% (ls_off% "libsignal_cli_handshake::initiate"))
    (k := num% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error"))
    (stub := num% (ls_off% "alloc::alloc::handle_alloc_error")) cliInitiate_fnOff rfl (by decide)
    (ls_hook% "alloc::alloc::handle_alloc_error") (by simp [Rust.isPanicSymbol])

private theorem oom_193c_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = s3PcExt img ext 0x193c) (hrun : s.status = .Running) (hfail : allocFailedIn s0 s)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hext := panic_alloc_error_at_init_ext img ext
  refine sepWP_bind_oom (mid := s3EntryExt img ext +
    bv% (ls_rel% "libsignal_cli_handshake::initiate" "alloc::alloc::handle_alloc_error")) ?_
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x193c 12
  dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc hext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr
    cliInitiateName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by rfl) (by simp [State.setPC, State.writeReg64, hrun])
    (SepWPp.panic (P := P) (hrun := by simp [State.setPC, State.writeReg64, hrun]) (hext := hext)
      (hqp := hpanic _ P (initPanicPost_of_allocFailed P
        (by simpa [allocFailedIn, Rust.panicked, State.setPC, State.writeReg64] using hfail))))

private theorem s3_memcpy_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext) (dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F)
    (hnext : ∀ sm : State, S3Ctrl img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = dst → sm.trace = s.trace →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hstk_split := stackAt_sub_split_init s.sp (by decide : CliExt.memHookStack ≤ extHookStack) (by decide)
  let F' := memRegion (s.sp - BitVec.ofNat 64 extHookStack) (extHookStack - CliExt.memHookStack) ∗ F
  have hpre' : P ⊢ CliExt.memcpySpec.pre (dst, src, bs) s ∗ F' := by
    refine Entails.trans hpre ?_; rw [hstk_split]
    simp only [CliExt.memcpySpec, libcMemcpySpec, F', sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.of_eq (by ac_rfl))
  refine s3_call_ext hOk (memcpy_ok_at_init_ext img hOk) (dst, src, bs) F' hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp [CliExt.memcpySpec] at h
  · intro _ _ _ h; simp [CliExt.memcpySpec] at h
  · intro _ _ h; simp [CliExt.memcpySpec] at h
  · intro sm _ _ _ hcsm _ hof; simp only [CliExt.memcpySpec, F', sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨hx0m, htrm⟩ => ?_
    refine sepWPp_conseq_oom ?_ (hnext sm (hof htrm) hcsm hx0m htrm)
    rw [hstk_split]; exact Entails.of_eq (by ac_rfl)

private theorem s3_call_alloc_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P0 A ext) (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in)
    (hpc : s.pc = s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hx0 : (s.readReg64 .x0).toNat = sz) (hx1 : (s.readReg64 .x1).toNat = 1) (hlay : LayoutOk sz 1)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (hnext_null : ∀ sm : State, sm.pc = s3PcExt img ext k_out → sm.status = .Running →
      sm.readReg64 .x0 = 0#64 → sm.trace = s.trace ++ [allocFailedEvent] →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0))
    (hnext_ok : ∀ sm : State, S3Ctrl img ext s0 sm k_out → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 ≠ 0#64 → sm.trace = s.trace →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt s.sp extHookStack ∗ A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have halloc := alloc_ok_at_init_ext img hOk
  have hpre' : P ⊢ (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_; simp only [rustAllocSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hlay⟩ (Entails.of_eq (by ac_rfl))
  refine sepWPp_conseq_oom hpre' ?_; intro R' hm hL
  have hm_pre : s.mem ⊨ (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s ∗ (F ∗ R') := by rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    halloc.no_fault_before_outcome (sz, 1) (F ∗ R') s hpc hctrl.run hm_pre (S3Ctrl.spAligned_cur hctrl) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · rw [hlr] at hpcm; dsimp only [rustAllocSpecWithStack] at hpost
    by_cases hnull : sm.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨ ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗ ((A.pool ∗ stackAt s.sp extHookStack ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'; obtain ⟨htrm, hmem_null'⟩ := hpost'
      obtain ⟨sf, hsteps', hout'⟩ := hnext_null sm hpcm hrunm hnull htrm R' hmem_null' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hnull, ↓reduceIte] at hpost
      have hpost' : sm.mem ⊨ ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
          ((A.pool ∗ stackAt s.sp extHookStack ∗ A.live (sm.readReg64 .x0) sz 1 ∗ memRegion (sm.readReg64 .x0) sz ∗ F) ∗ R') :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      rw [satisfies_pure_sepConj] at hpost'; obtain ⟨⟨_, htrm⟩, hmem_ok'⟩ := hpost'
      have hctrl' := S3Ctrl.of_call hOk hctrl hsteps hpcm hrunm hspm hcsm htrm
      obtain ⟨sf, hsteps', hout'⟩ := hnext_ok sm hctrl' hcsm hnull htrm R' hmem_ok' (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · simp only [rustAllocSpecWithStack] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · simp only [rustAllocSpecWithStack] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · simp only [rustAllocSpecWithStack] at hpost; exact (not_satisfies_false_sepConj hpost).elim

private theorem s3_dealloc_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext) (ptr : BitVec 64) (sz : Nat) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : S3Ctrl img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    (hlr : s.readReg64 .lr = s3PcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = 1) (hlay : LayoutOk sz 1)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ A.pool ∗ stackAt s.sp extHookStack ∗ A.live ptr sz 1 ∗ memRegion ptr sz ∗ F)
    (hnext : ∀ sm : State, S3Ctrl img ext s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) sm (A.pool ∗ stackAt s.sp extHookStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (s3ProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hpre' : P ⊢ (rustDeallocExternSpecWithStack A extHookStack).pre (ptr, sz, 1) s ∗ F := by
    refine Entails.trans hpre ?_; simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.of_eq (by ac_rfl))
  refine s3_call_ext hOk (dealloc_ok_at_init_ext img hOk) (ptr, sz, 1) F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack] at h; exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [rustDeallocExternSpecWithStack] at h; exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [rustDeallocExternSpecWithStack] at h; exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof; simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    exact sepWPp_pure_elim_oom fun htrm =>
      sepWPp_conseq_oom (Entails.of_eq (by ac_rfl)) (hnext sm (hof htrm) hcsm htrm)

private theorem s3_step_1030_1044_ext {img : Obj.Image} {ext : String → Option (State → State)} {s : State}
    (kemCtPtr ctBoxPtr ssBoxPtr g60 g68 : BitVec 64) (G : SepProp) (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0x1030)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = kemCtPtr) (hx1 : s.readReg64 .x1 = 1569#64)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64) (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx25 : s.readReg64 (.gpr 25#5) = ctBoxPtr) (hx26 : s.readReg64 (.gpr 26#5) = ssBoxPtr) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      s (((s.sp + 0x60#64) ↦₆₄ g60) ∗ ((s.sp + 0x68#64) ↦₆₄ g68) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧ (Pm ⊢ ((s.sp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 1569#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0x1044 ∧
        (sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧ sm.readReg64 .x2 = 1#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64 ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1030 20
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx0 hx1 hx20 hx21 hx25 hx26
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by (try simp only [hx0, hx1, arm64_norm, wp_norm]); sep_frame)
    ⟨by simp only [hx25, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
     by simp only [hx26, arm64_norm, wp_norm]⟩

/-- `CliExternsOk`-compatible `<kem::Ciphertext>::serialize` contract (`tryCloneFromRefStackX = 16432` bytes). -/
def kemCiphertextSerializeExtSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrPtr, boxPtr, ctBytes) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568⌝ ∗
    (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
    (boxPtr ↦ₛ ctBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun (hdrPtr, boxPtr, ctBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧ tempPtr ≠ 0#64⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗ (boxPtr ↦ₛ ctBytes) ∗
      (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

attribute [local irreducible] Program.fnOff in
set_option maxHeartbeats 1200000 in
/-- KEM `ct` boxing and `<kem::Ciphertext>::serialize` (`0x0ff8 → 0x1044`) under `CliExternsOk P0 A ext`. -/
theorem derive_keys_a2_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr ssBoxPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s8 : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hKemCtSer : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliKemCtSerializeName)
      (kemCiphertextSerializeExtSpec A))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hc8_in : s3DkACtrlExt img ext s0 s8 0xff8) (htr8 : s8.trace = s0.trace)
    (hx20_8 : s8.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_8 : s8.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx26_8 : s8.readReg64 (.gpr 26#5) = ssBoxPtr)
    (hnext : ∀ (sg : State) (ssBoxPtr' kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      s3DkACtrlExt img ext s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr' →
      SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) sg
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗ A.live ssBoxPtr' 32 1 ∗ (ssBoxPtr' ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗ ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
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
    let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
    let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
    SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) s8
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗ A.pool ∗
        memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack) (pqxdhEntryStack - extHookStack) ∗
        stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - pqxdhEntryStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
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
      Q Qp (initOom s0) := by
  dsimp only
  have hc8 : S3Ctrl img ext s0 s8 0xff8 := S3Ctrl.of_prop hc8_in
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  set ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
  set ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
  have hct_len : ct.toList.length = 1568 := ct.toList_length
  have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub_ct : tryCloneFromRefStackX ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_le64 := stk_sub_le_2pow64 hstk64
  have hstk_ext := stackAt_sub_split_init fsp (by decide : extHookStack ≤ pqxdhEntryStack) (by decide)
  obtain ⟨_, _, hfsp8⟩ := hc8.step_ctx fsp
  refine' s3_block_to_call_ext hOk
    (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
    0x1004 (Φ := fun sm =>
      sm.readReg64 .x0 = 1568#64 ∧ sm.readReg64 .x1 = 1#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 26#5) = ssBoxPtr)
    hc8 ?_ ?_; rotate_left 1
  · have hpc := hc8.pc; have hrun := hc8.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xff8 12
    dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hc8.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20_8 hx21_8 hx26_8
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20_8, arm64_norm, wp_norm], by simp only [hx21_8, arm64_norm, wp_norm],
       by simp only [hx26_8, arm64_norm, wp_norm]⟩
  · intro sm9 hc9 hp9 hl9 ht9 ⟨hx0_9, hx1_9, hx20_9, hx21_9, hx26_9⟩
    rw [hc8.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr9 := ht9.trans htr8
    refine s3_call_alloc_ext hOk 1568 _ hc9 hp9 hl9
      (by rw [hx0_9]; decide) (by rw [hx1_9]; decide) lay1568
      (by rw [hc9.sp]; (try dsimp only [fsp]); sep_frame) ?_ ?_
    · intro sm_oom2 hp_oom2 hrun_oom2 hnull2 htr_oom2
      refine sepWPp_oom_jmp (mid := s3PcExt img ext 0x193c) ?_ fun s' hpc' hrun' htr' =>
        oom_193c_ok_ext hpc' hrun' (allocFailedIn_of_append (htr9 ▸ htr' ▸ htr_oom2)) hpanic
      code_fetches_range libsignalSessionCode initS3 img.base
        (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1004 4
      dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt,
        BitVec.ofNat_eq_ofNat] at hp_oom2 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      try simp only [arm64_norm, wp_norm] at hnull2
      examples_hide_fetches; wp_steps
      exact SepWP.done (by wp_norm_goal) hrun_oom2 ⟨rfl, by wp_norm_goal, hrun_oom2, rfl⟩
    · intro s10 hc10 hcs10 hctNonNull htr_10
      set ctBoxPtr := s10.readReg64 .x0
      rw [hc9.sp]
      have htr10 := htr_10.trans htr9
      have hx20_10 := hcs10.2.1.trans hx20_9; have hx21_10 := hcs10.2.2.1.trans hx21_9
      have hx26_10 := hcs10.2.2.2.2.2.2.2.1.trans hx26_9
      obtain ⟨_, _, hfsp10⟩ := hc10.step_ctx fsp
      refine' s3_block_to_call_ext hOk
        (s3EntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
        0x101c (Φ := fun sm =>
          sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
          sm.readReg64 .x2 = 1568#64 ∧
          sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = 1568#64 ∧
          sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
          sm.readReg64 (.gpr 26#5) = ssBoxPtr)
        hc10 ?_ ?_; rotate_left 1
      · have hpc := hc10.pc; have hrun := hc10.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1004 24
        dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        have hnz10 : s10.readReg64 (.gpr 0#5) ≠ 0#64 := by
          simpa only [ctBoxPtr, arm64_norm, wp_norm] using hctNonNull
        (try dsimp only [fsp] at *); rw [← hc10.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_10 hx21_10 hx26_10
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [ctBoxPtr, arm64_norm, wp_norm], by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_10, arm64_norm, wp_norm], by simp only [hx21_10, arm64_norm, wp_norm],
           by wp_norm_goal, by simp only [ctBoxPtr, arm64_norm, wp_norm],
           by simp only [hx26_10, arm64_norm, wp_norm]⟩
      · intro sm11 hc11 hp11 hl11 ht11
          ⟨hx0_11, hx1_11, hx2_11, hx20_11, hx21_11, hx22_11, hx25_11, hx26_11⟩
        rw [hc10.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have htr11 := ht11.trans htr10
        refine s3_memcpy_ext hOk ctBoxPtr (fsp + 0xfe0#64) ct.toList _
          hc11 htr11 hp11 hl11 hx0_11 hx1_11 (by rw [hx2_11, hct_len]; decide) hpanic
          (by rw [hc11.sp, hct_len]; (try dsimp only [fsp]); sep_frame) ?_
        intro s12 hc12 hcs12 _ htr_12
        rw [hc11.sp]
        have htr12 := htr_12.trans htr11
        have hx20_12 := hcs12.2.1.trans hx20_11; have hx21_12 := hcs12.2.2.1.trans hx21_11
        have hx22_12 := hcs12.2.2.2.1.trans hx22_11; have hx25_12 := hcs12.2.2.2.2.2.2.1.trans hx25_11
        have hx26_12 := hcs12.2.2.2.2.2.2.2.1.trans hx26_11
        have hhdr := ct1568_split_hdr (fsp + 0x1600#64) hct_len
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr
        refine sepWPp_conseq_oom (by dsimp only [fsp, ct] at hhdr ⊢; exact sep_replace hhdr (by sep_frame) (Entails.refl _)) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine sepWPp_exists_elim_oom fun h0 => sepWPp_exists_elim_oom fun h1 => ?_
        obtain ⟨_, _, hfsp12⟩ := hc12.step_ctx fsp
        refine' s3_block_to_call_ext hOk
          (s3EntryExt img ext - bv% (ls_rel%
            "<libsignal_protocol::kem::Ciphertext>::serialize"
            "libsignal_cli_handshake::initiate"))
          0x1030 (Φ := fun sm =>
            sm.readReg64 .x0 = fsp + 0x1600#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 25#5) = ctBoxPtr ∧
            sm.readReg64 (.gpr 26#5) = ssBoxPtr)
          hc12 ?_ ?_; rotate_left 1
        · have hpc := hc12.pc; have hrun := hc12.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExternsWith ext))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x101c 20
          dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hc12.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_12 hx21_12 hx22_12 hx25_12 hx26_12
          examples_hide_fetches; wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal,
             by simp only [hx20_12, arm64_norm, wp_norm], by simp only [hx21_12, arm64_norm, wp_norm],
             by simp only [hx25_12, arm64_norm, wp_norm], by simp only [hx26_12, arm64_norm, wp_norm]⟩
        · intro sm13 hc13 hp13 hl13 ht13 ⟨hx0_13, hx20_13, hx21_13, hx25_13, hx26_13⟩
          rw [hc12.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
          have htr13 := ht13.trans htr12
          have hstk_clone :
              memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                  (pqxdhEntryStack - extHookStack) ∗ stackAt fsp extHookStack ∗
                memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                  (stk - cliInitiateFrame - pqxdhEntryStack) =
              memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                  (stk - cliInitiateFrame - tryCloneFromRefStackX) ∗
                stackAt fsp tryCloneFromRefStackX := by
            rw [← sepConj_assoc, ← hstk_ext, sepConj_comm (stackAt fsp pqxdhEntryStack),
                ← stackAt_sub_split_init fsp hsub_pq hstk_le64,
                stackAt_sub_split_init fsp hsub_ct hstk_le64]
          refine s3_call_ext hOk hKemCtSer
            (fsp + 0x1600#64, ctBoxPtr, ct.toList) _
            hc13 htr13 (hp13.trans (kemCtSerialize_fnAddr_ext_eq img ext)) hl13 hpanic
            (by
              have hx25_raw := hx25_12; conv at hx25_raw => lhs; simp only [arm64_norm, wp_norm]
              have hx22_raw := hx22_12; conv at hx22_raw => lhs; simp only [arm64_norm, wp_norm]
              simp only [kemCiphertextSerializeExtSpec, hc13.sp, hx25_12, hx22_12, hx25_raw, hx22_raw,
                BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
              refine Entails.pure_right ⟨hx0_13, hct_len⟩ ?_
              dsimp only [fsp, ct, ctBoxPtr, t] at hstk_clone ⊢
              refine sep_replace (Entails.of_eq hstk_clone) (by sep_frame) ?_
              sep_frame) ?_ ?_ ?_ ?_
          · intro _ _ h
            simp only [kemCiphertextSerializeExtSpec] at h
            rw [sepConj_assoc, satisfies_pure_sepConj] at h; exact h.1.1
          · intro _ _ _ h; simp [kemCiphertextSerializeExtSpec, Spec.onExit] at h
          · intro _ _ h; simp [kemCiphertextSerializeExtSpec, Spec.onOom] at h
          · intro s14 _ _ _ hcs14 _ hof14
            simp only [kemCiphertextSerializeExtSpec, hc13.sp, BitVec.add_assoc,
              BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
            refine sepWPp_exists_elim_oom fun kemCtPtr => ?_
            refine sepWPp_pure_elim_oom fun ⟨htr_14, hx0_14, hx1_14, hkemNonNull⟩ => ?_
            have hc14 := hof14 htr_14
            have htr14 := htr_14.trans htr13
            have hx20_14 := hcs14.2.1.trans hx20_13; have hx21_14 := hcs14.2.2.1.trans hx21_13
            have hx25_14 := hcs14.2.2.2.2.2.2.1.trans hx25_13; have hx26_14 := hcs14.2.2.2.2.2.2.2.1.trans hx26_13
            have hstk_back_ext := hstk_clone.symm
            refine sepWPp_conseq_oom
              (show _ ⊢ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗ _ by
                dsimp only [fsp]; sep_frame) ?_
            rw [ProofLib.memRegion_eight (fsp + 0x60#64),
                ProofLib.memRegion_eight (fsp + 0x68#64)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine sepWPp_exists_elim_oom fun g60 =>
              sepWPp_exists_elim_oom fun g68 => ?_
            obtain ⟨halign14, _, hfsp14⟩ := hc14.step_ctx fsp
            refine' s3_block_to_call_ext hOk
              (s3EntryExt img ext + bv% (ls_rel%
                "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
              0x1044 (Φ := fun sm =>
                sm.readReg64 .x0 = ctBoxPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
                sm.readReg64 .x2 = 1#64 ∧
                sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
                sm.readReg64 (.gpr 26#5) = ssBoxPtr)
              hc14 ?_ ?_; rotate_left 1
            · have hpc := hc14.pc
              dsimp only [s3PcExt, s3EntryExt, s3ProgExt, tripleRatchetProgAtExt] at hpc ⊢
              rw [hfsp14]
              exact s3_step_1030_1044_ext kemCtPtr ctBoxPtr ssBoxPtr g68 g60 _ halign14 hpc hc14.run
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
                rw [memRegion_merge_at (fsp + 0x1610#64) 1552 64 (fsp + 0x1c20#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x1608#64) 8 1616 (fsp + 0x1610#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x1600#64) 8 1624 (fsp + 0x1608#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0xfe0#64) 1568 1632 (fsp + 0x1600#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              refine s3_dealloc_ext hOk ctBoxPtr 1568 _
                hc15 htr15 hp15 hl15 hx0_15 (by rw [hx1_15]; decide) (by rw [hx2_15]; decide) lay1568 hpanic
                (by rw [hc15.sp]; dsimp only [fsp, ct] at hstk_back_ext hbox_mem ⊢
                    refine sep_replace hbox_mem (by sep_frame) ?_
                    exact sep_replace (Entails.of_eq hstk_back_ext) (by sep_frame) (by sep_frame)) ?_
              intro sg hcg hcsg htr_g
              rw [hc15.sp]
              refine sepWPp_conseq_oom ?_
                (hnext sg ssBoxPtr kemCtPtr hkemNonNull hcg.to_prop (htr_g.trans htr15)
                  (hcsg.2.1.trans hx20_15) (hcsg.2.2.1.trans hx21_15)
                  (hcsg.2.2.2.2.2.2.2.1.trans hx26_15))
              dsimp only [fsp, ct, ss] at hstk_ext hmid_collapse ⊢
              refine sep_replace hmid_collapse (by sep_frame) ?_
              exact sep_replace (Entails.of_eq hstk_ext.symm) (by sep_frame) (by sep_frame)

set_option maxHeartbeats 1200000 in
/-- Combined KEM `ss` and `ct` boxing and `<kem::Ciphertext>::serialize` (`0x0fb4 → 0x1044`) under `CliExternsOk P0 A ext`. -/
theorem derive_keys_a_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 sf0 : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hKemCtSer : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliKemCtSerializeName)
      (kemCiphertextSerializeExtSpec A))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : s3DkACtrlExt img ext s0 sf0 0xfb4) (htr : sf0.trace = s0.trace)
    (hx20 : sf0.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sf0.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ (sg : State) (ssBoxPtr kemCtPtr : BitVec 64),
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (P0.Q.encaps be.kpkPub (initiateKemCoins t)).2
      kemCtPtr ≠ 0#64 →
      s3DkACtrlExt img ext s0 sg 0x1044 → sg.trace = s0.trace →
      sg.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sg.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sg.readReg64 (.gpr 26#5) = ssBoxPtr →
      SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .lr) sg
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗ A.live ssBoxPtr 32 1 ∗ (ssBoxPtr ↦ₛ ss.toList) ∗
          memRegion fsp 0x60 ∗ ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
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
        memRegion (fsp + 0xfe0#64) 32 ∗ memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
        memRegion (fsp + 0x1c40#64) 32 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  exact derive_keys_a1_ok_ext hOk hpanic hctrl htr hx20 hx21
    fun s8 ssBoxPtr hc8 htr8 hx20_8 hx21_8 hx26_8 =>
      derive_keys_a2_ok_ext hOk hstk hstk64 hKemCtSer hpanic hc8 htr8 hx20_8 hx21_8 hx26_8 hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
