/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 PQXDH Step C (`+0x0a70 → +0x0b6c`: Optional `DH4`)

Advances from `+0x0a70` across optional `DH4 = X25519(ekASk, opkPk)` (`none` short-circuit jump to
`+0x0b6c` vs `some` `calculate_agreement` + zero-DH unwind via `s3_dh_unwind_1544` + `memcpy` +
`__rust_dealloc`) into a unified post-state at `+0x0b6c` parameterized by `dh4?`.
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
  libsignalSessionCode Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem sec128_re (secretsPtr : BitVec 64) (bs : SignalPqxdh.Bytes)
    (h128 : (bytesToBv8 bs).length = 128) :
    (secretsPtr ↦ₛ bytesToBv8 bs) ∗ memRegion (secretsPtr + 128#64) 32 ∗
      memRegion (secretsPtr + 160#64) 32 ⊢ memRegion secretsPtr 192 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion_len h128)) ?_
  rw [memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at secretsPtr 128 64 (secretsPtr + 128#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

private theorem s3_repack4 (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64)
    (opkId oid : BitVec 32) (ok : PublicKey) (hopk : b.opk = some (oid, ok)) :
    ((fsp + 0x439#64) ↦ₛ ok.bytes.toList) ∗
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ 1#32) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
       memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
       ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
       ((fsp + 0x438#64) ↦₈ 1#8) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]
  simp only [hopk, Option.isSome_some, ↓reduceIte,
    show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
  ac_rfl

set_option maxHeartbeats 1600000 in
theorem dh4_step_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiate img W s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sb
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
          A.pool ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, _, hkpkLen, hopkLen, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  rcases hopk : x.bundle.opk with _ | ⟨oid, ok⟩
  · -- Case `x.bundle.opk = none`: `ldrb w8, [sp, #0x438]` = `0#8 ≠ 1` jumps directly to `+0x0b6c`
    obtain ⟨halign_n, _, hfsp_n⟩ := hctrl.step_ctx fsp
    refine' s3_block_in hh 0xb6c (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa70 12
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, stage3KeySlotsAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
      examples_hide_fetches; wp_steps
      refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, arm64_norm, wp_norm]⟩
    · intro sb htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have hnone_opt := dh4_none_opt ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq hopk
      have hdh4_eq :
          (none : Option SignalPqxdh.Bytes) =
            ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
              (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                (modelPrims X ⟨W.C, W.Q⟩).x25519
                  (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                    (padCoins x.coins)).ekASk opkPk) := by
        rw [hnone_opt]; rfl
      refine sepWPp_conseq_oom ?_
        (hnext sb none hdh4_eq rfl (by intro _ h; nomatch h) hctrl_b (htr_b.trans htr)
          hx20_b hx21_b hx22_b)
      dsimp only [dhPrefix, dhRemAt, dhLenWord, stage3KeySlotsAt]
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      (try dsimp only [fsp]); sep_frame
  · -- Case `x.bundle.opk = some (oid, ok)`: runs `calculate_agreement` on `ekASk` and `ok`
    have hokLen : ok.bytes.toList.length = 32 := hopkLen oid ok hopk
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl.step_ctx fsp
    refine' s3_block_to_call hh
      (initEntry img W - bv% (ls_rel%
        "<libsignal_core::curve::PrivateKey>::calculate_agreement"
        "libsignal_cli_handshake::initiate"))
      0xa94 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x439#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 128#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa70 36
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, stage3KeySlotsAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      try simp only [hopk, Option.isSome_some, ↓reduceIte,
        show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx26
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm]⟩
    · intro sm_c4 hctrl_c4 hpcm_c4 hlrm_c4 htrm_c4
        ⟨hx0_c4, hx1_c4, hx8_c4, hx20_c4, hx21_c4, hx22_c4, hx26_c4⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr_c4 : sm_c4.trace = s0.trace := htrm_c4.trans htr
      have hsome_opt := dh4_some_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk oid ok
        hs3.bundleEq hopk hs3.ekPairEq.1
      refine s3_calc_agree (X := X) hh hLocal
        (fsp + 0x9a0#64) (toU8 ekASk)
        (fsp + 0x439#64) (toU8 ok.bytes.toList) _
        hctrl_c4 htr_c4 hpcm_c4 hlrm_c4 hx0_c4 hx1_c4 (by rw [hctrl_c4.sp]; exact hx8_c4)
        (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hokLen]) hpanic
        (by (try dsimp only [stage3KeySlotsAt])
            try simp only [hopk, Option.isSome_some, ↓reduceIte,
              show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
            rw [hctrl_c4.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            (try dsimp only [fsp]); sep_frame)
        ?_ ?_
      · intro hdh4_zero s_z4 hi u2 hctrl_z4 _ htr_z4
        rw [hctrl_c4.sp, ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
        obtain ⟨halign_z4, hx29_z4, hfsp_z4⟩ := hctrl_z4.step_ctx fsp
        refine' s3_block_in hh 0x1544
          (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
          hctrl_z4 ?_ ?_; rotate_left 1
        · have hpc := hctrl_z4.pc; have hrun := hctrl_z4.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa94 28
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb48 8
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x151c 40
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, speWord,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_z4.sp] at *
          examples_hide_fetches; wp_steps
          refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal, by wp_norm_goal⟩
        · intro sm_u4 htr_u4 hctrl_u4 ⟨hx26_u4, hx1_u4⟩
          rw [hctrl_z4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          have hbad4 : SignalPqxdh.dhOptNonZero
              ((initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                  (modelPrims X ⟨W.C, W.Q⟩).x25519
                    (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be
                      (padCoins x.coins)).ekASk opkPk) = false := by
            dsimp only [ofSignalPqxdhPrimitives]; rw [hsome_opt]
            dsimp only [ofSignalPqxdhPrimitives]; rw [hdh4_zero]; rfl
          have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
            x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
            (Or.inr (Or.inr (Or.inr hbad4)))
          have h128 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)).length = 128 := by
            rw [bytesToBv8_length, List.length_append, List.length_append, List.length_append,
              hdh1_len32, hdh2_len32, hdh3_len32]; decide
          exact s3_dh_unwind_1544 hh hS hnone hstk hstk64 hekAPkLen hekASkLen
            hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u4
            (htr_u4.trans (htr_z4.trans htr_c4)) hx26_u4 hx1_u4 hpost hpanic
            (hi ++ 3#8) u2 128#64
            (sepConj_mono (sec128_re secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) h128)
              (Entails.of_eq (s3_repack4 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk)))
            (by rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]; (try dsimp only [fsp]); cases x.bundle.opk <;> ((try dsimp only); sep_frame))
      · intro hdh4_nz s_ok4 dh4Ptr hctrl_ok4 hcs_ok4 htr_ok4
        rw [hctrl_c4.sp, ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
        have hx20_4 := hcs_ok4.2.1.trans hx20_c4; have hx21_4 := hcs_ok4.2.2.1.trans hx21_c4
        have hx22_4 := hcs_ok4.2.2.2.1.trans hx22_c4
        have hx26_4 := hcs_ok4.2.2.2.2.2.2.2.1.trans hx26_c4
        set dh4 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 ekASk) (toU8 ok.bytes.toList)
        have hdh4_len32 : dh4.length = 32 := modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
        have hdh4_len : (bytesToBv8 dh4).length = 32 := by rw [bytesToBv8_length, hdh4_len32]
        obtain ⟨halign_4, hx29_4, hfsp_4⟩ := hctrl_ok4.step_ctx fsp
        refine' s3_block_to_call hh
          (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
          0xb2c (Φ := fun sm =>
            sm.readReg64 .x0 = secretsPtr + 128#64 ∧ sm.readReg64 .x1 = dh4Ptr ∧
            sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh4Ptr ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_ok4 ?_ ?_; rotate_left 1
        · have hpc := hctrl_ok4.pc; have hrun := hctrl_ok4.run
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa94 16
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb04 40
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_ok4.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx26_4
          examples_hide_fetches; wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm]⟩
        · intro sm_mc4 hctrl_mc4 hpcm_mc4 hlrm_mc4 htrm_mc4
            ⟨hx0_mc4, hx1_mc4, hx2_mc4, hx20_mc4, hx21_mc4, hx22_mc4,
             hx24_mc4, hx25_mc4, hx26_mc4⟩
          rw [hctrl_ok4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine s3_memcpy hh (secretsPtr + 128#64) dh4Ptr (bytesToBv8 dh4) _
            hctrl_mc4 (htrm_mc4.trans (htr_ok4.trans htr_c4)) hpcm_mc4 hlrm_mc4
            hx0_mc4 hx1_mc4 (by rw [hx2_mc4, hdh4_len]; decide) hpanic
            (by rw [hctrl_mc4.sp, hdh4_len]; (try dsimp only [fsp]); sep_frame)
            ?_
          intro s_mc4 hctrl_mc4' hcs_mc4 _ htr_mc4
          rw [hctrl_mc4.sp]
          have hx20_m4 := hcs_mc4.2.1.trans hx20_mc4; have hx21_m4 := hcs_mc4.2.2.1.trans hx21_mc4
          have hx22_m4 := hcs_mc4.2.2.2.1.trans hx22_mc4
          have hx24_m4 := hcs_mc4.2.2.2.2.2.1.trans hx24_mc4
          have hx25_m4 := hcs_mc4.2.2.2.2.2.2.1.trans hx25_mc4
          have hx26_m4 := hcs_mc4.2.2.2.2.2.2.2.1.trans hx26_mc4
          obtain ⟨halign_m4, hx29_m4, hfsp_m4⟩ := hctrl_mc4'.step_ctx fsp
          refine' s3_block_to_call hh
            (initEntry img W +
              bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
            0xb44 (Φ := fun sm =>
              sm.readReg64 .x0 = dh4Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64)
            hctrl_mc4' ?_ ?_; rotate_left 1
          · have hpc := hctrl_mc4'.pc; have hrun := hctrl_mc4'.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb2c 24
            dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hctrl_mc4'.sp] at *
            try simp only [arm64_norm, wp_norm]
              at hx20_m4 hx21_m4 hx22_m4 hx24_m4 hx25_m4 hx26_m4
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by wp_norm_goal,
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm]⟩
          · intro sm_da4 hctrl_da4 hpcm_da4 hlrm_da4 htrm_da4
              ⟨hx0_da4, hx1_da4, hx2_da4, hx20_da4, hx21_da4, hx22_da4⟩
            rw [hctrl_mc4'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            refine s3_dealloc hh dh4Ptr 32 _ hctrl_da4
              (htrm_da4.trans (htr_mc4.trans (htrm_mc4.trans (htr_ok4.trans htr_c4))))
              hpcm_da4 hlrm_da4 hx0_da4 (by rw [hx1_da4]; decide) (by rw [hx2_da4]; decide)
              lay32 hpanic
              (by rw [hctrl_da4.sp]
                  exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh4Ptr) hdh4_len)
                    (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame))
              ?_
            intro s_d4 hctrl_d4 hcs_d4 htr_d4
            rw [hctrl_da4.sp]
            have hx20_d4 := hcs_d4.2.1.trans hx20_da4; have hx21_d4 := hcs_d4.2.2.1.trans hx21_da4
            have hx22_d4 := hcs_d4.2.2.2.1.trans hx22_da4
            refine' s3_block_in hh 0xb6c (Φ := fun sm =>
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl_d4 ?_ ?_; rotate_left 1
            · have hpc := hctrl_d4.pc; have hrun := hctrl_d4.run
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb44 4
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb68 4
              dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
                BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_d4.sp] at *
              try simp only [arm64_norm, wp_norm] at hx20_d4 hx21_d4 hx22_d4
              examples_hide_fetches; wp_steps
              refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                 by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                 by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm]⟩
            · intro sb htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
              rw [hctrl_d4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
              have hdh4_ok : SignalPqxdh.dhOptNonZero (some dh4) = true := by
                simp [SignalPqxdh.dhOptNonZero]; exact hdh4_nz
              have hlen_fn : ∀ d, some dh4 = some d → d.length = 32 := by
                intro d hd; cases hd; exact hdh4_len32
              have htr_fin : sb.trace = s0.trace :=
                htr_b.trans (htr_d4.trans (htrm_da4.trans
                  (htr_mc4.trans (htrm_mc4.trans (htr_ok4.trans htr_c4)))))
              have hsret4 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh4Ptr 32#64
              have happ4 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) dh4 128#64
                (by rw [List.length_append, List.length_append, List.length_append,
                      hdh1_len32, hdh2_len32, hdh3_len32]; rfl)
              refine sepWPp_conseq_oom ?_
                (hnext sb (some dh4) hsome_opt.symm hdh4_ok hlen_fn hctrl_b htr_fin
                  hx20_b hx21_b hx22_b)
              dsimp only [dhPrefix, dhRemAt, dhLenWord]
              rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              exact sep_replace
                (sepConj_mono hsret4 (sepConj_mono
                  (Entails.of_eq (s3_repack4 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk))
                  (Entails.of_eq happ4)))
                (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)

/-! ## `CliExternsOk` Generalization (`dh4_step_ok_ext`) -/

set_option Elab.async false

set_option maxHeartbeats 1600000 in
theorem dh4_step_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCalcAgree : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (Ext.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P0) A img))
    (hS : S.initiate = initDef X P0)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32) (hdh3_len32 : dh3.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 s 0xa70) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 128#64)
    (hnext : ∀ (sb : State) (dh4? : Option SignalPqxdh.Bytes),
      let P := modelPrims X P0
      let inp := initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh4? = (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) →
      SignalPqxdh.dhOptNonZero dh4? = true →
      (∀ d, dh4? = some d → d.length = 32) →
      InInitiateExt img ext s0 sb 0xb6c → sb.trace = s0.trace →
      sb.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sb.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sb.readReg64 (.gpr 22#5) = fsp + 0x408#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sb
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
          A.pool ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp ResponderCore.calculateAgreementStackExt ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)) ∗
        memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 128#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hstk_ca := stackAt_sub_split_init fsp
    (by decide : extHookStack ≤ ResponderCore.calculateAgreementStackExt) (by decide)
  have hstk_to_ext :
      stackAt fsp ResponderCore.calculateAgreementStackExt ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) =
      stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) := by
    rw [sepConj_comm (stackAt fsp ResponderCore.calculateAgreementStackExt),
        ← stackAt_sub_split_init fsp (Ext.calcAgreeSubStk_le_frame hstk) (stk_sub_le_2pow64 hstk64),
        stackAt_sub_split_init fsp (Nat.le_trans (by decide : extHookStack ≤ 516880) (stk_sub_ge_base hstk)) (stk_sub_le_2pow64 hstk64),
        sepConj_comm]
  obtain ⟨_, _, hkpkLen, hopkLen, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  rcases hopk : x.bundle.opk with _ | ⟨oid, ok⟩
  · -- Case `x.bundle.opk = none`: `ldrb w8, [sp, #0x438]` = `0#8 ≠ 1` jumps directly to `+0x0b6c`
    obtain ⟨halign_n, _, hfsp_n⟩ := hctrl.step_ctx fsp
    refine' Ext.s3_block_in hOk 0xb6c (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa70 12
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, stage3KeySlotsAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
      examples_hide_fetches; wp_steps
      refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, arm64_norm, wp_norm]⟩
    · intro sb htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have hnone_opt := dh4_none_opt P0 kp x.bundle be x.coins hs3.bundleEq hopk
      have hdh4_eq :
          (none : Option SignalPqxdh.Bytes) =
            ((initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be
              (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                (modelPrims X P0).x25519
                  (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be
                    (padCoins x.coins)).ekASk opkPk) := by
        rw [hnone_opt]; rfl
      refine sepWPp_conseq_oom ?_
        (hnext sb none hdh4_eq rfl (by intro _ h; nomatch h) hctrl_b (htr_b.trans htr)
          hx20_b hx21_b hx22_b)
      dsimp only [dhPrefix, dhRemAt, dhLenWord, stage3KeySlotsAt]
      try simp only [hopk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        show (0#32 : BitVec 32).truncate 8 = 0#8 from rfl]
      exact sep_replace (Entails.of_eq hstk_to_ext)
        (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)
  · -- Case `x.bundle.opk = some (oid, ok)`: runs `calculate_agreement` on `ekASk` and `ok`
    have hokLen : ok.bytes.toList.length = 32 := hopkLen oid ok hopk
    obtain ⟨halign_0, _, hfsp_0⟩ := hctrl.step_ctx fsp
    refine' Ext.s3_block_to_call hOk
      (initEntryExt img ext - bv% (ls_rel%
        "<libsignal_core::curve::PrivateKey>::calculate_agreement"
        "libsignal_cli_handshake::initiate"))
      0xa94 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x439#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 128#64)
      hctrl ?_ ?_; rotate_left 1
    · have hpc := hctrl.pc; have hrun := hctrl.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa70 36
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, stage3KeySlotsAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      try simp only [hopk, Option.isSome_some, ↓reduceIte,
        show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
      (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
      try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx26
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm],
         by simp only [hx20, hx21, hx22, hx26, arm64_norm, wp_norm]⟩
    · intro sm_c4 hctrl_c4 hpcm_c4 hlrm_c4 htrm_c4
        ⟨hx0_c4, hx1_c4, hx8_c4, hx20_c4, hx21_c4, hx22_c4, hx26_c4⟩
      rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
      have htr_c4 : sm_c4.trace = s0.trace := htrm_c4.trans htr
      have hsome_opt := dh4_some_eq X P0 kp x.bundle be x.coins ekASk oid ok
        hs3.bundleEq hopk hs3.ekPairEq.1
      refine Ext.s3_calc_agree (X := X)
        (calcStk := ResponderCore.calculateAgreementStackExt)
        (subStk := ResponderCore.calculateAgreementStackExt)
        hOk (hCalcAgree X)
        (fsp + 0x9a0#64) (toU8 ekASk)
        (fsp + 0x439#64) (toU8 ok.bytes.toList) _
        hctrl_c4 htr_c4 hpcm_c4 hlrm_c4 hx0_c4 hx1_c4 (by rw [hctrl_c4.sp]; exact hx8_c4)
        (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hokLen]) hpanic
        (by (try dsimp only [stage3KeySlotsAt])
            try simp only [hopk, Option.isSome_some, ↓reduceIte,
              show (1#32 : BitVec 32).truncate 8 = 1#8 from rfl]
            rw [hctrl_c4.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            (try dsimp only [fsp]); sep_frame)
        ?_ ?_
      · intro hdh4_zero s_z4 hi u2 hctrl_z4 _ htr_z4
        rw [hctrl_c4.sp, ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
        obtain ⟨halign_z4, hx29_z4, hfsp_z4⟩ := hctrl_z4.step_ctx fsp
        refine' Ext.s3_block_in hOk 0x1544
          (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
          hctrl_z4 ?_ ?_; rotate_left 1
        · have hpc := hctrl_z4.pc; have hrun := hctrl_z4.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa94 28
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb48 8
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x151c 40
          dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, speWord,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_z4.sp] at *
          examples_hide_fetches; wp_steps
          refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by wp_norm_goal, by wp_norm_goal⟩
        · intro sm_u4 htr_u4 hctrl_u4 ⟨hx26_u4, hx1_u4⟩
          rw [hctrl_z4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 1#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          have hbad4 : SignalPqxdh.dhOptNonZero
              ((initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be
                (padCoins x.coins)).bundle.opkB?.map fun (_, opkPk) =>
                  (modelPrims X P0).x25519
                    (initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be
                      (padCoins x.coins)).ekASk opkPk) = false := by
            dsimp only [ofSignalPqxdhPrimitives]; rw [hsome_opt]
            dsimp only [ofSignalPqxdhPrimitives]; rw [hdh4_zero]; rfl
          have hnone := initDef_some_none_of_dh_bad X P0 x.F x.peer.val x.me.val
            x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
            (Or.inr (Or.inr (Or.inr hbad4)))
          have h128 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2 ++ dh3)).length = 128 := by
            rw [bytesToBv8_length, List.length_append, List.length_append, List.length_append,
              hdh1_len32, hdh2_len32, hdh3_len32]; decide
          exact Ext.s3_dh_unwind_1544 (subStk := ResponderCore.calculateAgreementStackExt)
            hOk hS hnone hstk hstk64 hekAPkLen hekASkLen
            hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u4
            (htr_u4.trans (htr_z4.trans htr_c4)) hx26_u4 hx1_u4 hpost hpanic
            (hi ++ 3#8) u2 128#64
            (sepConj_mono (sec128_re secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) h128)
              (Entails.of_eq (s3_repack4 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk)))
            (by rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]; (try dsimp only [fsp]); cases x.bundle.opk <;> ((try dsimp only); sep_frame))
            (Ext.calcAgreeSubStk_le_frame hstk)
      · intro hdh4_nz s_ok4 dh4Ptr hctrl_ok4 hcs_ok4 htr_ok4
        rw [hctrl_c4.sp, hstk_ca, ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
        have hx20_4 := hcs_ok4.2.1.trans hx20_c4; have hx21_4 := hcs_ok4.2.2.1.trans hx21_c4
        have hx22_4 := hcs_ok4.2.2.2.1.trans hx22_c4
        have hx26_4 := hcs_ok4.2.2.2.2.2.2.2.1.trans hx26_c4
        set dh4 := (modelPrims X P0).x25519 (toU8 ekASk) (toU8 ok.bytes.toList)
        have hdh4_len32 : dh4.length = 32 := modelPrims_x25519_len X P0 _ _
        have hdh4_len : (bytesToBv8 dh4).length = 32 := by rw [bytesToBv8_length, hdh4_len32]
        obtain ⟨halign_4, hx29_4, hfsp_4⟩ := hctrl_ok4.step_ctx fsp
        refine' Ext.s3_block_to_call hOk
          (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
          0xb2c (Φ := fun sm =>
            sm.readReg64 .x0 = secretsPtr + 128#64 ∧ sm.readReg64 .x1 = dh4Ptr ∧
            sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh4Ptr ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_ok4 ?_ ?_; rotate_left 1
        · have hpc := hctrl_ok4.pc; have hrun := hctrl_ok4.run
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa94 16
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb04 40
          dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_ok4.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_4 hx21_4 hx22_4 hx26_4
          examples_hide_fetches; wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm],
             by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_4, hx21_4, hx22_4, hx26_4, arm64_norm, wp_norm]⟩
        · intro sm_mc4 hctrl_mc4 hpcm_mc4 hlrm_mc4 htrm_mc4
            ⟨hx0_mc4, hx1_mc4, hx2_mc4, hx20_mc4, hx21_mc4, hx22_mc4,
             hx24_mc4, hx25_mc4, hx26_mc4⟩
          rw [hctrl_ok4.sp] at *; rw [← ProofLib.pointsTo64_split32_at fsp 0x1600#64 0#64]
          try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine Ext.s3_memcpy hOk (secretsPtr + 128#64) dh4Ptr (bytesToBv8 dh4) _
            hctrl_mc4 (htrm_mc4.trans (htr_ok4.trans htr_c4)) hpcm_mc4 hlrm_mc4
            hx0_mc4 hx1_mc4 (by rw [hx2_mc4, hdh4_len]; decide) hpanic
            (by rw [hctrl_mc4.sp, hdh4_len]; (try dsimp only [fsp]); sep_frame)
            ?_
          intro s_mc4 hctrl_mc4' hcs_mc4 _ htr_mc4
          rw [hctrl_mc4.sp]
          have hx20_m4 := hcs_mc4.2.1.trans hx20_mc4; have hx21_m4 := hcs_mc4.2.2.1.trans hx21_mc4
          have hx22_m4 := hcs_mc4.2.2.2.1.trans hx22_mc4
          have hx24_m4 := hcs_mc4.2.2.2.2.2.1.trans hx24_mc4
          have hx25_m4 := hcs_mc4.2.2.2.2.2.2.1.trans hx25_mc4
          have hx26_m4 := hcs_mc4.2.2.2.2.2.2.2.1.trans hx26_mc4
          obtain ⟨halign_m4, hx29_m4, hfsp_m4⟩ := hctrl_mc4'.step_ctx fsp
          refine' Ext.s3_block_to_call hOk
            (initEntryExt img ext +
              bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
            0xb44 (Φ := fun sm =>
              sm.readReg64 .x0 = dh4Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64)
            hctrl_mc4' ?_ ?_; rotate_left 1
          · have hpc := hctrl_mc4'.pc; have hrun := hctrl_mc4'.run
            code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
              cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb2c 24
            dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hctrl_mc4'.sp] at *
            try simp only [arm64_norm, wp_norm]
              at hx20_m4 hx21_m4 hx22_m4 hx24_m4 hx25_m4 hx26_m4
            examples_hide_fetches; wp_steps
            refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by wp_norm_goal,
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm],
               by simp only [hx20_m4, hx21_m4, hx22_m4, hx24_m4, hx25_m4, hx26_m4, arm64_norm, wp_norm]⟩
          · intro sm_da4 hctrl_da4 hpcm_da4 hlrm_da4 htrm_da4
              ⟨hx0_da4, hx1_da4, hx2_da4, hx20_da4, hx21_da4, hx22_da4⟩
            rw [hctrl_mc4'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            refine Ext.s3_dealloc hOk dh4Ptr 32 _ hctrl_da4
              (htrm_da4.trans (htr_mc4.trans (htrm_mc4.trans (htr_ok4.trans htr_c4))))
              hpcm_da4 hlrm_da4 hx0_da4 (by rw [hx1_da4]; decide) (by rw [hx2_da4]; decide)
              lay32 hpanic
              (by rw [hctrl_da4.sp]
                  exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh4Ptr) hdh4_len)
                    (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame))
              ?_
            intro s_d4 hctrl_d4 hcs_d4 htr_d4
            rw [hctrl_da4.sp]
            have hx20_d4 := hcs_d4.2.1.trans hx20_da4; have hx21_d4 := hcs_d4.2.2.1.trans hx21_da4
            have hx22_d4 := hcs_d4.2.2.2.1.trans hx22_da4
            refine' Ext.s3_block_in hOk 0xb6c (Φ := fun sm =>
              sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
              sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
              sm.readReg64 (.gpr 22#5) = fsp + 0x408#64) hctrl_d4 ?_ ?_; rotate_left 1
            · have hpc := hctrl_d4.pc; have hrun := hctrl_d4.run
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb44 4
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb68 4
              dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
                BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_d4.sp] at *
              try simp only [arm64_norm, wp_norm] at hx20_d4 hx21_d4 hx22_d4
              examples_hide_fetches; wp_steps
              refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                 by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm],
                 by simp only [hx20_d4, hx21_d4, hx22_d4, arm64_norm, wp_norm]⟩
            · intro sb htr_b hctrl_b ⟨hx20_b, hx21_b, hx22_b⟩
              rw [hctrl_d4.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
              have hdh4_ok : SignalPqxdh.dhOptNonZero (some dh4) = true := by
                simp [SignalPqxdh.dhOptNonZero]; exact hdh4_nz
              have hlen_fn : ∀ d, some dh4 = some d → d.length = 32 := by
                intro d hd; cases hd; exact hdh4_len32
              have htr_fin : sb.trace = s0.trace :=
                htr_b.trans (htr_d4.trans (htrm_da4.trans
                  (htr_mc4.trans (htrm_mc4.trans (htr_ok4.trans htr_c4)))))
              have hsret4 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh4Ptr 32#64
              have happ4 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2 ++ dh3) dh4 128#64
                (by rw [List.length_append, List.length_append, List.length_append,
                      hdh1_len32, hdh2_len32, hdh3_len32]; rfl)
              have hstk_ca_to_ext :
                  (memRegion (fsp - BitVec.ofNat 64 ResponderCore.calculateAgreementStackExt)
                      (ResponderCore.calculateAgreementStackExt - extHookStack) ∗
                    stackAt fsp extHookStack) ∗
                    memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                      (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) =
                  stackAt fsp extHookStack ∗
                    memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                      (stk - cliInitiateFrame - extHookStack) := by
                rw [← hstk_ca, hstk_to_ext]
              refine sepWPp_conseq_oom ?_
                (hnext sb (some dh4) hsome_opt.symm hdh4_ok hlen_fn hctrl_b htr_fin
                  hx20_b hx21_b hx22_b)
              dsimp only [dhPrefix, dhRemAt, dhLenWord]
              rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              exact sep_replace
                (sepConj_mono hsret4 (sepConj_mono
                  (Entails.of_eq (s3_repack4 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId oid ok hopk))
                  (sepConj_mono (Entails.of_eq happ4) (Entails.of_eq hstk_ca_to_ext))))
                (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
