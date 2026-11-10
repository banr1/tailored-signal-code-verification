/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Stage 3 PQXDH Step B2 (`+0x0968 → +0x0a70`: `DH3`)

Advances from `+0x0968` (`F_X25519 ++ dh1 ++ dh2` at `secretsPtr`, `len = 96`) across
`DH3 = X25519(ekASk, spkB)` to `+0x0a70` with `F_X25519 ++ dh1 ++ dh2 ++ dh3` at `secretsPtr`
(`len = 128`).
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

private theorem sec96_re (secretsPtr : BitVec 64) (bs : SignalPqxdh.Bytes) (h96 : (bytesToBv8 bs).length = 96) :
    (secretsPtr ↦ₛ bytesToBv8 bs) ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
    memRegion secretsPtr 192 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion_len h96)) ?_
  rw [memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at secretsPtr 96 96 (secretsPtr + 96#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

private theorem s3_repack3 (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
       memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
       ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
       ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]; ac_rfl

set_option maxHeartbeats 1600000 in
theorem dh3_step_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiate img W s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sa
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
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, hspkLen, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  obtain ⟨halign_0, hx29_0, hfsp_0⟩ := hctrl.step_ctx fsp
  refine' s3_block_to_call hh
    (initEntry img W - bv% (ls_rel%
      "<libsignal_core::curve::PrivateKey>::calculate_agreement"
      "libsignal_cli_handshake::initiate"))
    0x97c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
      sm.readReg64 .x8 = fsp + 0x1600#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 96#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x968 20
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx24 hx26
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal,
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by wp_norm_goal,
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm]⟩
  · intro sm_c3 hctrl_c3 hpcm_c3 hlrm_c3 htrm_c3
      ⟨hx0_c3, hx1_c3, hx8_c3, hx20_c3, hx21_c3, hx22_c3, hx26_c3⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr_c3 : sm_c3.trace = s0.trace := htrm_c3.trans htr
    refine s3_calc_agree (X := X) hh hLocal
      (fsp + 0x9a0#64) (toU8 ekASk)
      (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) _
      hctrl_c3 htr_c3 hpcm_c3 hlrm_c3 hx0_c3 hx1_c3 (by rw [hctrl_c3.sp]; exact hx8_c3)
      (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hspkLen]) hpanic
      (by (try dsimp only [stage3KeySlotsAt])
          rw [hctrl_c3.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
          (try dsimp only [fsp]); sep_frame)
      ?_ ?_
    · intro hdh3_zero s_z3 hi u2 hctrl_z3 _ htr_z3
      rw [hctrl_c3.sp]
      obtain ⟨halign_z3, hx29_z3, hfsp_z3⟩ := hctrl_z3.step_ctx fsp
      refine' s3_block_in hh 0x1544
        (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
        hctrl_z3 ?_ ?_; rotate_left 1
      · have hpc := hctrl_z3.pc; have hrun := hctrl_z3.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x97c 32
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa40 8
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xae4 28
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, speWord,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hctrl_z3.sp] at *
        examples_hide_fetches; wp_steps
        refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal⟩
      · intro sm_u3 htr_u3 hctrl_u3 ⟨hx26_u3, hx1_u3⟩
        rw [hctrl_z3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
          x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
          (Or.inr (Or.inr (Or.inl (dh3_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk
            hs3.bundleEq hs3.ekPairEq.1 ▸ hdh3_zero))))
        have h96 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2)).length = 96 := by
          rw [bytesToBv8_length, List.length_append, List.length_append,
            hdh1_len32, hdh2_len32]; decide
        exact s3_dh_unwind_1544 hh hS hnone hstk hstk64 hekAPkLen hekASkLen
          hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u3
          (htr_u3.trans (htr_z3.trans htr_c3)) hx26_u3 hx1_u3 hpost hpanic
          (hi ++ 3#8) u2 96#64
          (sepConj_mono (sec96_re secretsPtr (F_X25519 ++ dh1 ++ dh2) h96)
            (Entails.of_eq (s3_repack3 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId)))
          (by rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]; (try dsimp only [fsp]); cases x.bundle.opk <;> (dsimp only; sep_frame))
    · intro hdh3_nz s_ok3 dh3Ptr hctrl_ok3 hcs_ok3 htr_ok3
      rw [hctrl_c3.sp]
      have hx20_3 := hcs_ok3.2.1.trans hx20_c3; have hx21_3 := hcs_ok3.2.2.1.trans hx21_c3
      have hx22_3 := hcs_ok3.2.2.2.1.trans hx22_c3
      have hx26_3 := hcs_ok3.2.2.2.2.2.2.2.1.trans hx26_c3
      set dh3 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 ekASk)
        (toU8 x.bundle.spk.bytes.toList)
      have hdh3_len : (bytesToBv8 dh3).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
      obtain ⟨halign_3, hx29_3, hfsp_3⟩ := hctrl_ok3.step_ctx fsp
      refine' s3_block_to_call hh
        (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
        0x9e4 (Φ := fun sm =>
          sm.readReg64 .x0 = secretsPtr + 96#64 ∧ sm.readReg64 .x1 = dh3Ptr ∧
          sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
          sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh3Ptr ∧
          sm.readReg64 (.gpr 26#5) = 96#64)
        hctrl_ok3 ?_ ?_; rotate_left 1
      · have hpc := hctrl_ok3.pc; have hrun := hctrl_ok3.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x97c 20
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9bc 40
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hctrl_ok3.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_3 hx21_3 hx22_3 hx26_3
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm]⟩
      · intro sm_mc3 hctrl_mc3 hpcm_mc3 hlrm_mc3 htrm_mc3
          ⟨hx0_mc3, hx1_mc3, hx2_mc3, hx20_mc3, hx21_mc3, hx22_mc3,
           hx24_mc3, hx25_mc3, hx26_mc3⟩
        rw [hctrl_ok3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        refine s3_memcpy hh (secretsPtr + 96#64) dh3Ptr (bytesToBv8 dh3) _
          hctrl_mc3 (htrm_mc3.trans (htr_ok3.trans htr_c3)) hpcm_mc3 hlrm_mc3
          hx0_mc3 hx1_mc3 (by rw [hx2_mc3, hdh3_len]; decide) hpanic
          (by rw [hctrl_mc3.sp, hdh3_len]; (try dsimp only [fsp]); sep_frame)
          ?_
        intro s_mc3 hctrl_mc3' hcs_mc3 _ htr_mc3
        rw [hctrl_mc3.sp]
        have hx20_m3 := hcs_mc3.2.1.trans hx20_mc3; have hx21_m3 := hcs_mc3.2.2.1.trans hx21_mc3
        have hx22_m3 := hcs_mc3.2.2.2.1.trans hx22_mc3
        have hx24_m3 := hcs_mc3.2.2.2.2.2.1.trans hx24_mc3
        have hx25_m3 := hcs_mc3.2.2.2.2.2.2.1.trans hx25_mc3
        have hx26_m3 := hcs_mc3.2.2.2.2.2.2.2.1.trans hx26_mc3
        obtain ⟨halign_m3, hx29_m3, hfsp_m3⟩ := hctrl_mc3'.step_ctx fsp
        refine' s3_block_to_call hh
          (initEntry img W +
            bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
          0x9fc (Φ := fun sm =>
            sm.readReg64 .x0 = dh3Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_mc3' ?_ ?_; rotate_left 1
        · have hpc := hctrl_mc3'.pc; have hrun := hctrl_mc3'.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9e4 24
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_mc3'.sp] at *
          try simp only [arm64_norm, wp_norm]
            at hx20_m3 hx21_m3 hx22_m3 hx24_m3 hx25_m3 hx26_m3
          examples_hide_fetches; wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by wp_norm_goal,
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm]⟩
        · intro sm_da3 hctrl_da3 hpcm_da3 hlrm_da3 htrm_da3
            ⟨hx0_da3, hx1_da3, hx2_da3, hx20_da3, hx21_da3, hx22_da3, hx26_da3⟩
          rw [hctrl_mc3'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine s3_dealloc hh dh3Ptr 32 _ hctrl_da3
            (htrm_da3.trans (htr_mc3.trans (htrm_mc3.trans (htr_ok3.trans htr_c3))))
            hpcm_da3 hlrm_da3 hx0_da3 (by rw [hx1_da3]; decide) (by rw [hx2_da3]; decide)
            lay32 hpanic
            (by rw [hctrl_da3.sp]
                exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh3Ptr) hdh3_len)
                  (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame))
            ?_
          intro s_d3 hctrl_d3 hcs_d3 htr_d3
          rw [hctrl_da3.sp]
          have hx20_d3 := hcs_d3.2.1.trans hx20_da3; have hx21_d3 := hcs_d3.2.2.1.trans hx21_da3
          have hx22_d3 := hcs_d3.2.2.2.1.trans hx22_da3
          have hx26_d3 := hcs_d3.2.2.2.2.2.2.2.1.trans hx26_da3
          refine' s3_block_in hh 0xa70 (Φ := fun sm =>
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64) hctrl_d3 ?_ ?_; rotate_left 1
          · have hpc := hctrl_d3.pc; have hrun := hctrl_d3.run
            code_fetches_range libsignalSessionCode initS3 img.base
              (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
              (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9fc 4
            dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hctrl_d3.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_d3 hx21_d3 hx22_d3 hx26_d3
            examples_hide_fetches; wp_steps
            refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm]⟩
          · intro sa htr_a hctrl_a ⟨hx20_a, hx21_a, hx22_a, hx26_a⟩
            rw [hctrl_d3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have hdh3_eq := dh3_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins ekASk
              hs3.bundleEq hs3.ekPairEq.1
            have htr_fin : sa.trace = s0.trace :=
              htr_a.trans (htr_d3.trans (htrm_da3.trans
                (htr_mc3.trans (htrm_mc3.trans (htr_ok3.trans htr_c3)))))
            have hsret3 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh3Ptr 32#64
            have happ3 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2) dh3 96#64
              (by rw [List.length_append, List.length_append, hdh1_len32, hdh2_len32]; rfl)
            refine sepWPp_conseq_oom ?_
              (hnext sa dh3 hdh3_eq hdh3_nz hctrl_a htr_fin hx20_a hx21_a hx22_a hx26_a)
            rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            exact sep_replace
              (sepConj_mono hsret3 (sepConj_mono
                (Entails.of_eq (s3_repack3 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId))
                (Entails.of_eq happ3)))
              (by (try dsimp only [fsp]); cases x.bundle.opk <;> dsimp only <;> sep_frame)
              (by (try dsimp only [fsp]); sep_frame)

/-! ## `CliExternsOk` Generalization (`dh3_step_ok_ext`) -/

set_option Elab.async false

set_option maxHeartbeats 1600000 in
theorem dh3_step_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 : SignalPqxdh.Bytes} {stk : Nat} {s0 s3 s : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCalcAgree : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (Ext.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P0) A img))
    (hS : S.initiate = initDef X P0)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hdh1_len32 : dh1.length = 32) (hdh2_len32 : dh2.length = 32)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 s 0x968) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64)
    (hx24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 96#64)
    (hnext : ∀ (sa : State) (dh3 : SignalPqxdh.Bytes),
      let P := modelPrims X P0
      let inp := initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh3 = P.x25519 inp.ekASk inp.bundle.spkB → dh3 ≠ List.replicate 32 0 →
      InInitiateExt img ext s0 sa 0xa70 → sa.trace = s0.trace →
      sa.readReg64 (.gpr 20#5) = fsp + 0x348#64 → sa.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      sa.readReg64 (.gpr 22#5) = fsp + 0x408#64 → sa.readReg64 (.gpr 26#5) = 128#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sa
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
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp ResponderCore.calculateAgreementStackExt ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1 ++ dh2)) ∗
        memRegion (secretsPtr + 96#64) 32 ∗ memRegion (secretsPtr + 128#64) 32 ∗
        memRegion (secretsPtr + 160#64) 32 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ 96#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hstk_ca := stackAt_sub_split_init fsp
    (by decide : extHookStack ≤ ResponderCore.calculateAgreementStackExt) (by decide)
  obtain ⟨_, hspkLen, hkpkLen, _, _, _, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  obtain ⟨halign_0, hx29_0, hfsp_0⟩ := hctrl.step_ctx fsp
  refine' Ext.s3_block_to_call hOk
    (initEntryExt img ext - bv% (ls_rel%
      "<libsignal_core::curve::PrivateKey>::calculate_agreement"
      "libsignal_cli_handshake::initiate"))
    0x97c (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9a0#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
      sm.readReg64 .x8 = fsp + 0x1600#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 26#5) = 96#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x968 20
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22 hx24 hx26
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by wp_norm_goal,
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by wp_norm_goal,
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm],
       by simp only [hx20, hx21, hx22, hx24, hx26, arm64_norm, wp_norm]⟩
  · intro sm_c3 hctrl_c3 hpcm_c3 hlrm_c3 htrm_c3
      ⟨hx0_c3, hx1_c3, hx8_c3, hx20_c3, hx21_c3, hx22_c3, hx26_c3⟩
    rw [hctrl.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
    have htr_c3 : sm_c3.trace = s0.trace := htrm_c3.trans htr
    refine Ext.s3_calc_agree (X := X)
      (calcStk := ResponderCore.calculateAgreementStackExt)
      (subStk := ResponderCore.calculateAgreementStackExt)
      hOk (hCalcAgree X)
      (fsp + 0x9a0#64) (toU8 ekASk)
      (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) _
      hctrl_c3 htr_c3 hpcm_c3 hlrm_c3 hx0_c3 hx1_c3 (by rw [hctrl_c3.sp]; exact hx8_c3)
      (by rw [toU8_length_eq, hekASkLen]) (by rw [toU8_length_eq, hspkLen]) hpanic
      (by (try dsimp only [stage3KeySlotsAt])
          rw [hctrl_c3.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
          (try dsimp only [fsp]); sep_frame)
      ?_ ?_
    · intro hdh3_zero s_z3 hi u2 hctrl_z3 _ htr_z3
      rw [hctrl_c3.sp]
      obtain ⟨halign_z3, hx29_z3, hfsp_z3⟩ := hctrl_z3.step_ctx fsp
      refine' Ext.s3_block_in hOk 0x1544
        (Φ := fun sm => sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
        hctrl_z3 ?_ ?_; rotate_left 1
      · have hpc := hctrl_z3.pc; have hrun := hctrl_z3.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x97c 32
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xa40 8
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xae4 28
        dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, speWord,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hctrl_z3.sp] at *
        examples_hide_fetches; wp_steps
        refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by wp_norm_goal, by wp_norm_goal⟩
      · intro sm_u3 htr_u3 hctrl_u3 ⟨hx26_u3, hx1_u3⟩
        rw [hctrl_z3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        have hnone := initDef_some_none_of_dh_bad X P0 x.F x.peer.val x.me.val
          x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
          (Or.inr (Or.inr (Or.inl (dh3_model_eq X P0 kp x.bundle be x.coins ekASk
            hs3.bundleEq hs3.ekPairEq.1 ▸ hdh3_zero))))
        have h96 : (bytesToBv8 (F_X25519 ++ dh1 ++ dh2)).length = 96 := by
          rw [bytesToBv8_length, List.length_append, List.length_append,
            hdh1_len32, hdh2_len32]; decide
        exact Ext.s3_dh_unwind_1544 (subStk := ResponderCore.calculateAgreementStackExt)
          hOk hS hnone hstk hstk64 hekAPkLen hekASkLen
          hkpkLen hs3.x8 hsecNonNull hs3.pqspkNonNull hctrl_u3
          (htr_u3.trans (htr_z3.trans htr_c3)) hx26_u3 hx1_u3 hpost hpanic
          (hi ++ 3#8) u2 96#64
          (sepConj_mono (sec96_re secretsPtr (F_X25519 ++ dh1 ++ dh2) h96)
            (Entails.of_eq (s3_repack3 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId)))
          (by rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]; (try dsimp only [fsp]); cases x.bundle.opk <;> (dsimp only; sep_frame))
          (Ext.calcAgreeSubStk_le_frame hstk)
    · intro hdh3_nz s_ok3 dh3Ptr hctrl_ok3 hcs_ok3 htr_ok3
      rw [hctrl_c3.sp, hstk_ca]
      have hx20_3 := hcs_ok3.2.1.trans hx20_c3; have hx21_3 := hcs_ok3.2.2.1.trans hx21_c3
      have hx22_3 := hcs_ok3.2.2.2.1.trans hx22_c3
      have hx26_3 := hcs_ok3.2.2.2.2.2.2.2.1.trans hx26_c3
      set dh3 := (modelPrims X P0).x25519 (toU8 ekASk)
        (toU8 x.bundle.spk.bytes.toList)
      have hdh3_len : (bytesToBv8 dh3).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X P0 _ _
      obtain ⟨halign_3, hx29_3, hfsp_3⟩ := hctrl_ok3.step_ctx fsp
      refine' Ext.s3_block_to_call hOk
        (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
        0x9e4 (Φ := fun sm =>
          sm.readReg64 .x0 = secretsPtr + 96#64 ∧ sm.readReg64 .x1 = dh3Ptr ∧
          sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
          sm.readReg64 (.gpr 24#5) = 32#64 ∧ sm.readReg64 (.gpr 25#5) = dh3Ptr ∧
          sm.readReg64 (.gpr 26#5) = 96#64)
        hctrl_ok3 ?_ ?_; rotate_left 1
      · have hpc := hctrl_ok3.pc; have hrun := hctrl_ok3.run
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x97c 20
        code_fetches_range libsignalSessionCode initS3 img.base
          (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9bc 40
        dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
          BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        (try dsimp only [fsp] at *); rw [← hctrl_ok3.sp] at *
        try simp only [arm64_norm, wp_norm] at hx20_3 hx21_3 hx22_3 hx26_3
        examples_hide_fetches; wp_steps
        refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm],
           by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_3, hx21_3, hx22_3, hx26_3, arm64_norm, wp_norm]⟩
      · intro sm_mc3 hctrl_mc3 hpcm_mc3 hlrm_mc3 htrm_mc3
          ⟨hx0_mc3, hx1_mc3, hx2_mc3, hx20_mc3, hx21_mc3, hx22_mc3,
           hx24_mc3, hx25_mc3, hx26_mc3⟩
        rw [hctrl_ok3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
        refine Ext.s3_memcpy hOk (secretsPtr + 96#64) dh3Ptr (bytesToBv8 dh3) _
          hctrl_mc3 (htrm_mc3.trans (htr_ok3.trans htr_c3)) hpcm_mc3 hlrm_mc3
          hx0_mc3 hx1_mc3 (by rw [hx2_mc3, hdh3_len]; decide) hpanic
          (by rw [hctrl_mc3.sp, hdh3_len]; (try dsimp only [fsp]); sep_frame)
          ?_
        intro s_mc3 hctrl_mc3' hcs_mc3 _ htr_mc3
        rw [hctrl_mc3.sp]
        have hx20_m3 := hcs_mc3.2.1.trans hx20_mc3; have hx21_m3 := hcs_mc3.2.2.1.trans hx21_mc3
        have hx22_m3 := hcs_mc3.2.2.2.1.trans hx22_mc3
        have hx24_m3 := hcs_mc3.2.2.2.2.2.1.trans hx24_mc3
        have hx25_m3 := hcs_mc3.2.2.2.2.2.2.1.trans hx25_mc3
        have hx26_m3 := hcs_mc3.2.2.2.2.2.2.2.1.trans hx26_mc3
        obtain ⟨halign_m3, hx29_m3, hfsp_m3⟩ := hctrl_mc3'.step_ctx fsp
        refine' Ext.s3_block_to_call hOk
          (initEntryExt img ext +
            bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
          0x9fc (Φ := fun sm =>
            sm.readReg64 .x0 = dh3Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64)
          hctrl_mc3' ?_ ?_; rotate_left 1
        · have hpc := hctrl_mc3'.pc; have hrun := hctrl_mc3'.run
          code_fetches_range libsignalSessionCode initS3 img.base
            (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9e4 24
          dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
            BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          (try dsimp only [fsp] at *); rw [← hctrl_mc3'.sp] at *
          try simp only [arm64_norm, wp_norm]
            at hx20_m3 hx21_m3 hx22_m3 hx24_m3 hx25_m3 hx26_m3
          examples_hide_fetches; wp_steps
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by wp_norm_goal,
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm],
             by simp only [hx20_m3, hx21_m3, hx22_m3, hx24_m3, hx25_m3, hx26_m3, arm64_norm, wp_norm]⟩
        · intro sm_da3 hctrl_da3 hpcm_da3 hlrm_da3 htrm_da3
            ⟨hx0_da3, hx1_da3, hx2_da3, hx20_da3, hx21_da3, hx22_da3, hx26_da3⟩
          rw [hctrl_mc3'.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
          refine Ext.s3_dealloc hOk dh3Ptr 32 _ hctrl_da3
            (htrm_da3.trans (htr_mc3.trans (htrm_mc3.trans (htr_ok3.trans htr_c3))))
            hpcm_da3 hlrm_da3 hx0_da3 (by rw [hx1_da3]; decide) (by rw [hx2_da3]; decide)
            lay32 hpanic
            (by rw [hctrl_da3.sp]
                exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh3Ptr) hdh3_len)
                  (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame))
            ?_
          intro s_d3 hctrl_d3 hcs_d3 htr_d3
          rw [hctrl_da3.sp]
          have hx20_d3 := hcs_d3.2.1.trans hx20_da3; have hx21_d3 := hcs_d3.2.2.1.trans hx21_da3
          have hx22_d3 := hcs_d3.2.2.2.1.trans hx22_da3
          have hx26_d3 := hcs_d3.2.2.2.2.2.2.2.1.trans hx26_da3
          refine' Ext.s3_block_in hOk 0xa70 (Φ := fun sm =>
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧
            sm.readReg64 (.gpr 26#5) = 128#64) hctrl_d3 ?_ ?_; rotate_left 1
          · have hpc := hctrl_d3.pc; have hrun := hctrl_d3.run
            code_fetches_range libsignalSessionCode initS3 img.base
              (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
              (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x9fc 4
            dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
              BitVec.ofNat_eq_ofNat] at hpc ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
            (try dsimp only [fsp] at *); rw [← hctrl_d3.sp] at *
            try simp only [arm64_norm, wp_norm] at hx20_d3 hx21_d3 hx22_d3 hx26_d3
            examples_hide_fetches; wp_steps
            refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
              ⟨by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm],
               by simp only [hx20_d3, hx21_d3, hx22_d3, hx26_d3, arm64_norm, wp_norm]⟩
          · intro sa htr_a hctrl_a ⟨hx20_a, hx21_a, hx22_a, hx26_a⟩
            rw [hctrl_d3.sp] at *; try iterate 6 rw [BitVec.add_comm _ fsp]; try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)]
            have hdh3_eq := dh3_model_eq X P0 kp x.bundle be x.coins ekASk
              hs3.bundleEq hs3.ekPairEq.1
            have htr_fin : sa.trace = s0.trace :=
              htr_a.trans (htr_d3.trans (htrm_da3.trans
                (htr_mc3.trans (htrm_mc3.trans (htr_ok3.trans htr_c3)))))
            have hsret3 := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh3Ptr 32#64
            have happ3 := append_bv8_at secretsPtr (F_X25519 ++ dh1 ++ dh2) dh3 96#64
              (by rw [List.length_append, List.length_append, hdh1_len32, hdh2_len32]; rfl)
            refine sepWPp_conseq_oom ?_
              (hnext sa dh3 hdh3_eq hdh3_nz hctrl_a htr_fin hx20_a hx21_a hx22_a hx26_a)
            rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
            exact sep_replace
              (sepConj_mono hsret3 (sepConj_mono
                (Entails.of_eq (s3_repack3 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId))
                (sepConj_mono (Entails.of_eq happ3) (Entails.of_eq hstk_ca.symm))))
              (by (try dsimp only [fsp]); cases x.bundle.opk <;> dsimp only <;> sep_frame)
              (by (try dsimp only [fsp]); sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
