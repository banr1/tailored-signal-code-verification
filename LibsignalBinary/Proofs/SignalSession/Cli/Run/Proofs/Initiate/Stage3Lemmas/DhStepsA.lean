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
# Stage 3 PQXDH Step A (`+0x0760 → +0x0858`: `secrets` Alloc + `DH1`)

Advances from `AtStage3` (`+0x0760`) + `stage3Mem` across `__rust_alloc(192, 1)` (handling OOM via
`oom_1918_ok`) and `DH1 = X25519(ikASk, spkB)` (handling zero-DH via `unwind_1548_ok`) to `+0x0858`
with `F_X25519 ++ dh1` written at `secretsPtr` (`len = 64`, `cap = 192`).
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

private theorem dh1_oom_jmp {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s emp
      (fun s' q => q = emp ∧ s'.pc = mid ∧ s'.status = .Running ∧ s'.trace = s.trace))
    (hoom : ∀ s' : State, s'.pc = mid → s'.status = .Running → s'.trace = s.trace →
      SepWPp prog ret s' P Q Qp Qoom) : SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim (by rwa [emp_sepConj] : s.mem ⊨ emp ∗ (P ∗ R)) hL with
    ⟨s', hst, ⟨-, -, _, hq, rfl, hpc', hrun', htr'⟩ | ⟨_, hf⟩⟩
  · rw [emp_sepConj] at hq
    obtain ⟨sf, hst', hout⟩ := hoom s' hpc' hrun' htr' R hq (hst.codeLoaded hL)
    exact ⟨sf, hst.trans hst', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

private theorem s3_loc_split (fsp : BitVec 64) :
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
      memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x48 ∗
      memRegion (fsp + 0x9a0#64) 0x20 ∗ memRegion (fsp + 0x9c0#64) 0xc40 ∗
      memRegion (fsp + 0x1600#64) 24 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
      memRegion (fsp + 0x1c60#64) 8 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
      memRegion (fsp + 0x1c70#64) 8 ∗ memRegion (fsp + 0x1c78#64) 0x18 := by
  simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
  rw [← memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 0x1360 (fsp + 0x930#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x930#64) 8 0x1358 (fsp + 0x938#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x938#64) 0x20 0x1338 (fsp + 0x958#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x958#64) 0x48 0x12f0 (fsp + 0x9a0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12d0 (fsp + 0x9c0#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x690 (fsp + 0x1600#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1600#64) 24 0x678 (fsp + 0x1618#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1618#64) 0x648 0x30 (fsp + 0x1c60#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c60#64) 8 0x28 (fsp + 0x1c68#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c68#64) 8 0x20 (fsp + 0x1c70#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]

private theorem s3_sec_split (secretsPtr : BitVec 64) :
    memRegion secretsPtr 192 =
      memRegion secretsPtr 32 ∗ memRegion (secretsPtr + 32#64) 32 ∗
      memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 := by
  rw [← memRegion_merge_at secretsPtr 32 160 (secretsPtr + 32#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 32#64) 32 128 (secretsPtr + 64#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 64#64) 32 96 (secretsPtr + 96#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by bv_omega) (by decide)]

set_option maxHeartbeats 1600000 in
theorem dh1_step_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop} (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk) (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X ⟨W.C, W.Q⟩
      let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiate img W s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
          A.pool ∗ stackAt fsp extHookStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, hspkLen, hkpkLen, _, _, hbe_spk, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  have hikASkLen : kp.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  refine sepWPp_conseq_oom (P' :=
      S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗ A.pool ∗
      stackAt fsp extHookStack ∗ memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ memRegion fsp 0x78 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗ stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x48 ∗
      memRegion (fsp + 0x9a0#64) 0x20 ∗ memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗ memRegion (fsp + 0x1c60#64) 8 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
      memRegion (fsp + 0x1c70#64) 8 ∗ memRegion (fsp + 0x1c78#64) 0x18)
    (by unfold S3InvPrefix; dsimp only [stage3Mem]
        rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl,
            stackAt_sub_split_init fsp hsub_ext (stk_sub_le_2pow64 hstk64), s3_loc_split fsp]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine' s3_block_to_call hh
    (initEntry img W + bv% (ls_rel%
      "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    0x764 (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
    hs3.ctrl ?_ ?_; rotate_left 1
  · have hpc := hs3.ctrl.pc; have hrun := hs3.ctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x760 4
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by simpa only [fsp, arm64_norm, wp_norm] using hs3.x20,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x21,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x22,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x24⟩
  · intro sm0 hctrl0 hpcm0 hlrm0 htrm0 ⟨hx20_0, hx21_0, hx22_0, hx24_0⟩
    refine s3_shim hh _ hctrl0 (htrm0.trans hs3.trace) hpcm0 hlrm0 hpanic
      (by rw [hctrl0.sp]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_sh hctrl_sh hcs_sh htr_sh
    rw [hctrl0.sp]
    have hx20_sh := hcs_sh.2.1.trans hx20_0; have hx21_sh := hcs_sh.2.2.1.trans hx21_0
    have hx22_sh := hcs_sh.2.2.2.1.trans hx22_0; have hx24_sh := hcs_sh.2.2.2.2.2.1.trans hx24_0
    refine' s3_block_to_call hh
      (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      0x770 (Φ := fun sm =>
        sm.readReg64 .x0 = 192#64 ∧ sm.readReg64 .x1 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
      hctrl_sh ?_ ?_; rotate_left 1
    · have hpc := hctrl_sh.pc; have hrun := hctrl_sh.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x764 12
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal,
         by simpa only [arm64_norm, wp_norm] using hx20_sh,
         by simpa only [arm64_norm, wp_norm] using hx21_sh,
         by simpa only [arm64_norm, wp_norm] using hx22_sh,
         by simpa only [arm64_norm, wp_norm] using hx24_sh⟩
    · intro sm_al hctrl_al hpcm_al hlrm_al htrm_al ⟨hx0_al, hx1_al, hx20_al, hx21_al, hx22_al, hx24_al⟩
      have htr_al : sm_al.trace = s0.trace :=
        htrm_al.trans (htr_sh.trans (htrm0.trans hs3.trace))
      refine s3_call_alloc hh 192 _ hctrl_al hpcm_al hlrm_al
        (by rw [hx0_al]; decide) (by rw [hx1_al]; decide) lay192
        (by rw [hctrl_al.sp]; (try dsimp only [fsp]); sep_frame)
        ?_ ?_
      · intro sm_null hpcm_null hrun_null hnull htr_null
        refine dh1_oom_jmp (mid := initPc img W 0x1918) ?_ fun s' hpc' hrun' htr' =>
          oom_1918_ok hpc' hrun' (allocFailedIn_of_append (htr_al ▸ htr' ▸ htr_null)) hpanic
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x770 4
        dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
          BitVec.ofNat_eq_ofNat] at hpcm_null ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hnull
        examples_hide_fetches; wp_steps
        exact SepWP.done (by wp_norm_goal) hrun_null ⟨rfl, by wp_norm_goal, hrun_null, rfl⟩
      · intro s_ok hctrl_ok hcs_ok hsecNonNull htr_ok
        set secretsPtr := s_ok.readReg64 .x0
        have hx20_ok := hcs_ok.2.1.trans hx20_al; have hx21_ok := hcs_ok.2.2.1.trans hx21_al
        have hx22_ok := hcs_ok.2.2.2.1.trans hx22_al; have hx24_ok := hcs_ok.2.2.2.2.2.1.trans hx24_al
        rw [hctrl_al.sp, s3_sec_split secretsPtr, memRegion32_cells4 secretsPtr,
            ProofLib.memRegion_eight (fsp + 0x1c60#64), ProofLib.memRegion_eight (fsp + 0x1c68#64),
            ProofLib.memRegion_eight (fsp + 0x1c70#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine sepWPp_exists_elim_oom fun sw0 => sepWPp_exists_elim_oom fun sw1 =>
          sepWPp_exists_elim_oom fun sw2 => sepWPp_exists_elim_oom fun sw3 =>
          sepWPp_exists_elim_oom fun c0 => sepWPp_exists_elim_oom fun c1 =>
          sepWPp_exists_elim_oom fun c2 => ?_
        obtain ⟨halign_ok, hx29_ok, hfsp_ok⟩ := hctrl_ok.step_ctx fsp
        refine' s3_block_to_call hh
          (initEntry img W - bv% (ls_rel%
            "<libsignal_core::curve::PrivateKey>::calculate_agreement"
            "libsignal_cli_handshake::initiate"))
          0x7a8 (Φ := fun sm =>
            sm.readReg64 .x0 = fsp + 0x368#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
            sm.readReg64 .x8 = fsp + 0x1600#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
            sm.readReg64 (.gpr 25#5) = secretsPtr)
          hctrl_ok ?_ ?_; rotate_left 1
        · have hpc := hctrl_ok.pc; have hrun := hctrl_ok.run
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x770 56
          dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
          have hnz0 : s_ok.readReg64 (.gpr 0#5) ≠ 0#64 := by simpa only [arm64_norm, wp_norm] using hsecNonNull
          (try dsimp only [fsp] at *); rw [← hctrl_ok.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_ok hx21_ok hx22_ok hx24_ok
          examples_hide_fetches; wp_steps
          have hsec_reg : s_ok.readReg64 (.gpr 0#5) = secretsPtr := rfl
          have hones : (secretsPtr ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) = (secretsPtr ↦ₛ bytesToBv8 F_X25519) := allOnes64_4_eq_F_X25519 secretsPtr
          rw [hones, hsec_reg]
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm], by wp_norm_goal,
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [secretsPtr, arm64_norm, wp_norm]⟩
        · intro sm_c1 hctrl_c1 hpcm_c1 hlrm_c1 htrm_c1 ⟨hx0_c1, hx1_c1, hx8_c1, hx20_c1, hx21_c1, hx22_c1, hx24_c1, hx25_c1⟩
          rw [hctrl_ok.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
          have htr_c1 : sm_c1.trace = s0.trace := htrm_c1.trans (htr_ok.trans htr_al)
          refine s3_calc_agree (X := X) hh hLocal
            (fsp + 0x368#64) (toU8 kp.privateKey.bytes.toList)
            (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) _
            hctrl_c1 htr_c1 hpcm_c1 hlrm_c1 hx0_c1 hx1_c1 (by rw [hctrl_c1.sp]; exact hx8_c1)
            (by rw [toU8_length_eq, hikASkLen]) (by rw [toU8_length_eq, hspkLen]) hpanic
            (by
              (try dsimp only [stage3KeySlotsAt])
              rw [hctrl_c1.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              (try dsimp only [fsp]); sep_frame)
            ?_ ?_
          · intro hdh1_zero s_z1 hi u2 hctrl_z1 hcs_z1 htr_z1
            have hx25_z1 := hcs_z1.2.2.2.2.2.2.1.trans hx25_c1
            rw [hctrl_c1.sp]
            obtain ⟨halign_z1, hx29_z1, hfsp_z1⟩ := hctrl_z1.step_ctx fsp
            refine' s3_block_in hh 0x1548
              (Φ := fun sm => sm.readReg64 (.gpr 25#5) = secretsPtr ∧
                sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
              hctrl_z1 ?_ ?_; rotate_left 1
            · have hpc := hctrl_z1.pc; have hrun := hctrl_z1.run
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7a8 36
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x834 8
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x914 36
              dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, speWord, BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_z1.sp] at *
              examples_hide_fetches; wp_steps
              refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simpa only [arm64_norm, wp_norm] using hx25_z1, by wp_norm_goal, by wp_norm_goal⟩
            · intro sm_u1 htr_u1 hctrl_u1 ⟨hx25_u1, hx26_u1, hx1_u1⟩
              rw [hctrl_z1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
              have hnone := initDef_some_none_of_dh_bad X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
                x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
                (Or.inl (dh1_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq ▸ hdh1_zero))
              refine sepWPp_conseq_oom ?_
                (unwind_1548_ok hh hS hnone hstk hstk64 hs3.x8 hsecNonNull hs3.pqspkNonNull
                  hctrl_u1 (htr_u1.trans (htr_z1.trans htr_c1)) hx25_u1 hx26_u1 hx1_u1 hpost hpanic)
              rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              have hbase := s3_dh_collapse_common (img := img) (A := A) (B := B)
                (kp := kp) (ekASk := ekASk) (ekAPk := ekAPk)
                (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr) (opkId := opkId)
                hstk hstk64 hekAPkLen hekASkLen hkpkLen s0
              have hsec_re :
                  (secretsPtr ↦ₛ bytesToBv8 F_X25519) ∗ memRegion (secretsPtr + 32#64) 32 ∗
                    memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
                    memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
                  memRegion secretsPtr 192 := by
                refine Entails.trans (sepConj_mono_left
                  (pointsToBytes_entails_memRegion_len (n := 32) (by decide))) ?_
                rw [← s3_sec_split secretsPtr]; exact Entails.refl _
              have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 (hi ++ 3#8) u2
              have hloc_re :
                  memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
                    memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
                    memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
                  memRegion (fsp + 0x958#64) 0x1310 := by
                refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
                rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢
                  memRegion fsp 0x80 := by
                refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
                rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hc20 : ((fsp + 0x1c70#64) ↦₆₄ 32#64) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
                  memRegion (fsp + 0x1c70#64) 0x20 := by
                refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
                rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hkeys_back := stage3KeySlotsAt_repack_dh1 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
              have htail1548 :
                  ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
                    memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ⊢
                  memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
                rw [show s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 from by
                  dsimp only [fsp]; clear * -; rw [cliInitiateFrame_eq]; bv_omega]
                refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
                have hm : memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
                    memRegion (fsp + 0x1c70#64) 0x20 =
                    memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
                  simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
                  rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by clear * -; bv_omega) (by decide),
                      memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.of_eq (by rw [← hm]; ac_rfl)
              refine sep_replace (sepConj_mono hsec_re (sepConj_mono hm78 (sepConj_mono hsret hc20)))
                (by (try dsimp only [fsp]); sep_frame) ?_
              refine sep_replace (sepConj_mono hloc_re (Entails.of_eq hkeys_back))
                (by (try dsimp only [fsp]); cases x.bundle.opk <;> (dsimp only; sep_frame)) ?_
              refine sep_replace hbase (by (try dsimp only [fsp]); sep_frame) ?_
              dsimp only [Unwind1548Mem]
              exact sep_replace htail1548 (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)
          · intro hdh1_nz s_ok1 dh1Ptr hctrl_ok1 hcs_ok1 htr_ok1
            have hx20_1 := hcs_ok1.2.1.trans hx20_c1; have hx21_1 := hcs_ok1.2.2.1.trans hx21_c1
            have hx22_1 := hcs_ok1.2.2.2.1.trans hx22_c1
            have hx24_1 := hcs_ok1.2.2.2.2.2.1.trans hx24_c1
            have hx25_1 := hcs_ok1.2.2.2.2.2.2.1.trans hx25_c1
            set dh1 := (modelPrims X ⟨W.C, W.Q⟩).x25519 (toU8 kp.privateKey.bytes.toList)
              (toU8 x.bundle.spk.bytes.toList)
            have hdh1_len : (bytesToBv8 dh1).length = 32 := by
              rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ _ _
            rw [hctrl_c1.sp]
            obtain ⟨halign_1, hx29_1, hfsp_1⟩ := hctrl_ok1.step_ctx fsp
            refine' s3_block_to_call hh
              (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
              0x808 (Φ := fun sm =>
                sm.readReg64 .x0 = secretsPtr + 32#64 ∧ sm.readReg64 .x1 = dh1Ptr ∧
                sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 22#5) = 32#64 ∧
                sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                sm.readReg64 (.gpr 25#5) = secretsPtr ∧
                sm.readReg64 (.gpr 27#5) = 32#64 ∧ sm.readReg64 (.gpr 28#5) = dh1Ptr)
              hctrl_ok1 ?_ ?_; rotate_left 1
            · have hpc := hctrl_ok1.pc; have hrun := hctrl_ok1.run
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7a8 24
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7dc 44
              dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
                BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_ok1.sp] at *
              try simp only [arm64_norm, wp_norm] at hx20_1 hx21_1 hx22_1 hx24_1 hx25_1
              examples_hide_fetches; wp_steps
              refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal⟩
            · intro sm_mc1 hctrl_mc1 hpcm_mc1 hlrm_mc1 htrm_mc1
                ⟨hx0_mc1, hx1_mc1, hx2_mc1, hx20_mc1, hx21_mc1, hx22_mc1, hx23_mc1, hx24_mc1,
                 hx25_mc1, hx27_mc1, hx28_mc1⟩
              rw [hctrl_ok1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
              refine s3_memcpy hh (secretsPtr + 32#64) dh1Ptr (bytesToBv8 dh1) _
                hctrl_mc1 (htrm_mc1.trans (htr_ok1.trans htr_c1)) hpcm_mc1 hlrm_mc1
                hx0_mc1 hx1_mc1 (by rw [hx2_mc1, hdh1_len]; decide) hpanic
                (by rw [hctrl_mc1.sp, hdh1_len]; (try dsimp only [fsp]); sep_frame)
                ?_
              intro s_mc1 hctrl_mc1' hcs_mc1 _ htr_mc1; rw [hctrl_mc1.sp]
              have hx20_m := hcs_mc1.2.1.trans hx20_mc1; have hx21_m := hcs_mc1.2.2.1.trans hx21_mc1
              have hx22_m := hcs_mc1.2.2.2.1.trans hx22_mc1
              have hx23_m := hcs_mc1.2.2.2.2.1.trans hx23_mc1; have hx24_m := hcs_mc1.2.2.2.2.2.1.trans hx24_mc1
              have hx25_m := hcs_mc1.2.2.2.2.2.2.1.trans hx25_mc1
              have hx27_m := hcs_mc1.2.2.2.2.2.2.2.2.1.trans hx27_mc1
              have hx28_m := hcs_mc1.2.2.2.2.2.2.2.2.2.1.trans hx28_mc1
              obtain ⟨halign_m1, hx29_m1, hfsp_m1⟩ := hctrl_mc1'.step_ctx fsp
              refine' s3_block_to_call hh
                (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
                0x820 (Φ := fun sm =>
                  sm.readReg64 .x0 = dh1Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
                  sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧
                  sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                  sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
                hctrl_mc1' ?_ ?_; rotate_left 1
              · have hpc := hctrl_mc1'.pc; have hrun := hctrl_mc1'.run
                code_fetches_range libsignalSessionCode initS3 img.base
                  (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                  (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x808 24
                dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
                generalize_entry (libsignalSessionCode.rebase img.base
                  (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
                (try dsimp only [fsp] at *); rw [← hctrl_mc1'.sp] at *
                try simp only [arm64_norm, wp_norm] at hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m
                examples_hide_fetches; wp_steps
                refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                  ⟨by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by wp_norm_goal,
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm]⟩
              · intro sm_da1 hctrl_da1 hpcm_da1 hlrm_da1 htrm_da1
                  ⟨hx0_da1, hx1_da1, hx2_da1, hx20_da1, hx21_da1, hx23_da1, hx24_da1, hx25_da1, hx26_da1⟩
                rw [hctrl_mc1'.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
                refine s3_dealloc hh dh1Ptr 32 _ hctrl_da1
                  (htrm_da1.trans (htr_mc1.trans (htrm_mc1.trans (htr_ok1.trans htr_c1))))
                  hpcm_da1 hlrm_da1 hx0_da1 (by rw [hx1_da1]; decide) (by rw [hx2_da1]; decide) lay32 hpanic
                  (by rw [hctrl_da1.sp]
                      exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh1Ptr) hdh1_len)
                        (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)) ?_
                intro s_d1 hctrl_d1 hcs_d1 htr_d1; rw [hctrl_da1.sp]
                have hx20_d1 := hcs_d1.2.1.trans hx20_da1; have hx21_d1 := hcs_d1.2.2.1.trans hx21_da1
                have hx23_d1 := hcs_d1.2.2.2.2.1.trans hx23_da1; have hx24_d1 := hcs_d1.2.2.2.2.2.1.trans hx24_da1
                have hx25_d1 := hcs_d1.2.2.2.2.2.2.1.trans hx25_da1
                have hx26_d1 := hcs_d1.2.2.2.2.2.2.2.1.trans hx26_da1
                refine' s3_block_in hh 0x858 (Φ := fun sm =>
                  sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
                  sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                  sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
                  hctrl_d1 ?_ ?_; rotate_left 1
                · have hpc := hctrl_d1.pc; have hrun := hctrl_d1.run
                  code_fetches_range libsignalSessionCode initS3 img.base
                    (Rust.withPanics (cliExterns W)) cliInitiate_fnOff
                    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x820 20
                  dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
                  generalize_entry (libsignalSessionCode.rebase img.base
                    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
                  (try dsimp only [fsp] at *); rw [← hctrl_d1.sp] at *
                  try simp only [arm64_norm, wp_norm] at hx20_d1 hx21_d1 hx23_d1 hx24_d1 hx25_d1 hx26_d1
                  examples_hide_fetches; wp_steps
                  refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                    ⟨by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm]⟩
                · intro s858 htr_858 hctrl_858 ⟨hx20_858, hx21_858, hx22_858, hx24_858, hx25_858, hx26_858⟩
                  rw [hctrl_d1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
                  have hdh1_eq := dh1_model_eq X ⟨W.C, W.Q⟩ kp x.bundle be x.coins hs3.bundleEq
                  have htr_final : s858.trace = s0.trace :=
                    htr_858.trans (htr_d1.trans (htrm_da1.trans (htr_mc1.trans (htrm_mc1.trans (htr_ok1.trans htr_c1)))))
                  have hsret_ok := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh1Ptr 32#64
                  have hkeys_ok := stage3KeySlotsAt_repack_dh1 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
                  refine sepWPp_conseq_oom ?_
                    (hnext s858 secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hctrl_858 htr_final
                      hx20_858 hx21_858 hx22_858 hx24_858 hx25_858 hx26_858)
                  rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
                  exact sep_replace
                    (sepConj_mono hsret_ok (sepConj_mono (Entails.of_eq hkeys_ok)
                      (Entails.of_eq (append_bv8_at secretsPtr F_X25519 dh1 32#64 rfl))))
                    (by (try dsimp only [fsp]); cases x.bundle.opk <;> ((try dsimp only); sep_frame))
                    (by (try dsimp only [fsp]); sep_frame)

/-! ## `CliExternsOk` Generalization (`dh1_step_ok_ext`) -/

set_option Elab.async false

set_option maxHeartbeats 1600000 in
theorem dh1_step_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s3 : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCalcAgree : ∀ X, subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (Ext.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P0) A img))
    (hS : S.initiate = initDef X P0)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Ext img P0 ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s : State) (secretsPtr : BitVec 64) (dh1 : SignalPqxdh.Bytes),
      let P := modelPrims X P0
      let inp := initiateInput P0 ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      dh1 = P.x25519 inp.ikASk inp.bundle.spkB → dh1 ≠ List.replicate 32 0 → secretsPtr ≠ 0#64 →
      InInitiateExt img ext s0 s 0x858 → s.trace = s0.trace →
      s.readReg64 (.gpr 20#5) = fsp + 0x348#64 → s.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s.readReg64 (.gpr 22#5) = fsp + 0x408#64 → s.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 →
      s.readReg64 (.gpr 25#5) = secretsPtr → s.readReg64 (.gpr 26#5) = 64#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗
          A.pool ∗ stackAt fsp ResponderCore.calculateAgreementStackExt ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) ∗
          A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (F_X25519 ++ dh1)) ∗
          memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
          memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ∗
          memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
          memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
          memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨_, hspkLen, hkpkLen, _, _, hbe_spk, _, _⟩ := bundleEOf_props hs3.bundleEq
  have hekASkLen : ekASk.length = 32 := by rw [hs3.ekPairEq.1]; exact List.Vector.toList_length _
  have hekAPkLen : ekAPk.length = 32 := by rw [hs3.ekPairEq.2]; exact List.Vector.toList_length _
  have hikASkLen : kp.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have hsub_ca : ResponderCore.calculateAgreementStackExt ≤ stk - cliInitiateFrame :=
    Ext.calcAgreeSubStk_le_frame hstk
  have hstk_ca := stackAt_sub_split_init fsp
    (by decide : extHookStack ≤ ResponderCore.calculateAgreementStackExt) (by decide)
  refine sepWPp_conseq_oom (P' :=
      S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 32 ∗ A.pool ∗
      stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 ResponderCore.calculateAgreementStackExt)
        (ResponderCore.calculateAgreementStackExt - extHookStack) ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - ResponderCore.calculateAgreementStackExt) ∗
      memRegion fsp 0x78 ∗
      ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗ stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x48 ∗
      memRegion (fsp + 0x9a0#64) 0x20 ∗ memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
      memRegion (fsp + 0x1618#64) 0x648 ∗ memRegion (fsp + 0x1c60#64) 8 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
      memRegion (fsp + 0x1c70#64) 8 ∗ memRegion (fsp + 0x1c78#64) 0x18)
    (by unfold S3InvPrefix; dsimp only [stage3Mem]
        rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl,
            stackAt_sub_split_init fsp hsub_ca (stk_sub_le_2pow64 hstk64), hstk_ca, s3_loc_split fsp]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine' Ext.s3_block_to_call hOk
    (initEntryExt img ext + bv% (ls_rel%
      "libsignal_cli_handshake::initiate" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    0x764 (Φ := fun sm =>
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
    hs3.ctrl ?_ ?_; rotate_left 1
  · have hpc := hs3.ctrl.pc; have hrun := hs3.ctrl.run
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x760 4
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
      ⟨by simpa only [fsp, arm64_norm, wp_norm] using hs3.x20,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x21,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x22,
       by simpa only [fsp, arm64_norm, wp_norm] using hs3.x24⟩
  · intro sm0 hctrl0 hpcm0 hlrm0 htrm0 ⟨hx20_0, hx21_0, hx22_0, hx24_0⟩
    refine Ext.s3_shim hOk _ hctrl0 (htrm0.trans hs3.trace) hpcm0 hlrm0 hpanic
      (by rw [hctrl0.sp]; (try dsimp only [fsp]); sep_frame) ?_
    intro s_sh hctrl_sh hcs_sh htr_sh
    rw [hctrl0.sp]
    have hx20_sh := hcs_sh.2.1.trans hx20_0; have hx21_sh := hcs_sh.2.2.1.trans hx21_0
    have hx22_sh := hcs_sh.2.2.2.1.trans hx22_0; have hx24_sh := hcs_sh.2.2.2.2.2.1.trans hx24_0
    refine' Ext.s3_block_to_call hOk
      (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_alloc"))
      0x770 (Φ := fun sm =>
        sm.readReg64 .x0 = 192#64 ∧ sm.readReg64 .x1 = 1#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64)
      hctrl_sh ?_ ?_; rotate_left 1
    · have hpc := hctrl_sh.pc; have hrun := hctrl_sh.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x764 12
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      examples_hide_fetches; wp_steps
      refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal,
         by simpa only [arm64_norm, wp_norm] using hx20_sh,
         by simpa only [arm64_norm, wp_norm] using hx21_sh,
         by simpa only [arm64_norm, wp_norm] using hx22_sh,
         by simpa only [arm64_norm, wp_norm] using hx24_sh⟩
    · intro sm_al hctrl_al hpcm_al hlrm_al htrm_al ⟨hx0_al, hx1_al, hx20_al, hx21_al, hx22_al, hx24_al⟩
      have htr_al : sm_al.trace = s0.trace :=
        htrm_al.trans (htr_sh.trans (htrm0.trans hs3.trace))
      refine Ext.s3_call_alloc hOk 192 _ hctrl_al hpcm_al hlrm_al
        (by rw [hx0_al]; decide) (by rw [hx1_al]; decide) lay192
        (by rw [hctrl_al.sp]; (try dsimp only [fsp]); sep_frame)
        ?_ ?_
      · intro sm_null hpcm_null hrun_null hnull htr_null
        refine dh1_oom_jmp (mid := initPcExt img ext 0x1918) ?_ fun s' hpc' hrun' htr' =>
          Ext.oom_1918_ok hpc' hrun' (allocFailedIn_of_append (htr_al ▸ htr' ▸ htr_null)) hpanic
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x770 4
        dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
          BitVec.ofNat_eq_ofNat] at hpcm_null ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hnull
        examples_hide_fetches; wp_steps
        exact SepWP.done (by wp_norm_goal) hrun_null ⟨rfl, by wp_norm_goal, hrun_null, rfl⟩
      · intro s_ok hctrl_ok hcs_ok hsecNonNull htr_ok
        set secretsPtr := s_ok.readReg64 .x0
        have hx20_ok := hcs_ok.2.1.trans hx20_al; have hx21_ok := hcs_ok.2.2.1.trans hx21_al
        have hx22_ok := hcs_ok.2.2.2.1.trans hx22_al; have hx24_ok := hcs_ok.2.2.2.2.2.1.trans hx24_al
        rw [hctrl_al.sp, s3_sec_split secretsPtr, memRegion32_cells4 secretsPtr,
            ProofLib.memRegion_eight (fsp + 0x1c60#64), ProofLib.memRegion_eight (fsp + 0x1c68#64),
            ProofLib.memRegion_eight (fsp + 0x1c70#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine sepWPp_exists_elim_oom fun sw0 => sepWPp_exists_elim_oom fun sw1 =>
          sepWPp_exists_elim_oom fun sw2 => sepWPp_exists_elim_oom fun sw3 =>
          sepWPp_exists_elim_oom fun c0 => sepWPp_exists_elim_oom fun c1 =>
          sepWPp_exists_elim_oom fun c2 => ?_
        obtain ⟨halign_ok, hx29_ok, hfsp_ok⟩ := hctrl_ok.step_ctx fsp
        refine' Ext.s3_block_to_call hOk
          (initEntryExt img ext - bv% (ls_rel%
            "<libsignal_core::curve::PrivateKey>::calculate_agreement"
            "libsignal_cli_handshake::initiate"))
          0x7a8 (Φ := fun sm =>
            sm.readReg64 .x0 = fsp + 0x368#64 ∧ sm.readReg64 .x1 = fsp + 0x3e8#64 ∧
            sm.readReg64 .x8 = fsp + 0x1600#64 ∧
            sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
            sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
            sm.readReg64 (.gpr 25#5) = secretsPtr)
          hctrl_ok ?_ ?_; rotate_left 1
        · have hpc := hctrl_ok.pc; have hrun := hctrl_ok.run
          code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
            cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x770 56
          dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
          have hnz0 : s_ok.readReg64 (.gpr 0#5) ≠ 0#64 := by simpa only [arm64_norm, wp_norm] using hsecNonNull
          (try dsimp only [fsp] at *); rw [← hctrl_ok.sp] at *
          try simp only [arm64_norm, wp_norm] at hx20_ok hx21_ok hx22_ok hx24_ok
          examples_hide_fetches; wp_steps
          have hsec_reg : s_ok.readReg64 (.gpr 0#5) = secretsPtr := rfl
          have hones : (secretsPtr ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((secretsPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) = (secretsPtr ↦ₛ bytesToBv8 F_X25519) := allOnes64_4_eq_F_X25519 secretsPtr
          rw [hones, hsec_reg]
          refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
            ⟨by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm], by wp_norm_goal,
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [hx20_ok, hx21_ok, hx22_ok, hx24_ok, arm64_norm, wp_norm],
             by simp only [secretsPtr, arm64_norm, wp_norm]⟩
        · intro sm_c1 hctrl_c1 hpcm_c1 hlrm_c1 htrm_c1 ⟨hx0_c1, hx1_c1, hx8_c1, hx20_c1, hx21_c1, hx22_c1, hx24_c1, hx25_c1⟩
          rw [hctrl_ok.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
          have htr_c1 : sm_c1.trace = s0.trace := htrm_c1.trans (htr_ok.trans htr_al)
          refine Ext.s3_calc_agree (X := X)
            (calcStk := ResponderCore.calculateAgreementStackExt)
            (subStk := ResponderCore.calculateAgreementStackExt)
            hOk (hCalcAgree X)
            (fsp + 0x368#64) (toU8 kp.privateKey.bytes.toList)
            (fsp + 0x3e8#64) (toU8 x.bundle.spk.bytes.toList) _
            hctrl_c1 htr_c1 hpcm_c1 hlrm_c1 hx0_c1 hx1_c1 (by rw [hctrl_c1.sp]; exact hx8_c1)
            (by rw [toU8_length_eq, hikASkLen]) (by rw [toU8_length_eq, hspkLen]) hpanic
            (by
              (try dsimp only [stage3KeySlotsAt])
              rw [hctrl_c1.sp, bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              dsimp only [fsp] at hstk_ca ⊢
              exact sep_replace (Entails.of_eq hstk_ca.symm) (by sep_frame) (by sep_frame))
            ?_ ?_
          · intro hdh1_zero s_z1 hi u2 hctrl_z1 hcs_z1 htr_z1
            have hx25_z1 := hcs_z1.2.2.2.2.2.2.1.trans hx25_c1
            rw [hctrl_c1.sp]
            obtain ⟨halign_z1, hx29_z1, hfsp_z1⟩ := hctrl_z1.step_ctx fsp
            refine' Ext.s3_block_in hOk 0x1548
              (Φ := fun sm => sm.readReg64 (.gpr 25#5) = secretsPtr ∧
                sm.readReg64 (.gpr 26#5) = speWord 10 ∧ sm.readReg64 .x1 = 192#64)
              hctrl_z1 ?_ ?_; rotate_left 1
            · have hpc := hctrl_z1.pc; have hrun := hctrl_z1.run
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7a8 36
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x834 8
              code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x914 36
              dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, speWord, BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_z1.sp] at *
              examples_hide_fetches; wp_steps
              refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simpa only [arm64_norm, wp_norm] using hx25_z1, by wp_norm_goal, by wp_norm_goal⟩
            · intro sm_u1 htr_u1 hctrl_u1 ⟨hx25_u1, hx26_u1, hx1_u1⟩
              rw [hctrl_z1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
              have hnone := initDef_some_none_of_dh_bad X P0 x.F x.peer.val x.me.val
                x.bundle be kp x.coins hs3.bundleEq hs3.trustedOk hs3.kpOk
                (Or.inl (dh1_model_eq X P0 kp x.bundle be x.coins hs3.bundleEq ▸ hdh1_zero))
              refine sepWPp_conseq_oom ?_
                (Ext.unwind_1548_ok hOk hS hnone hstk hstk64 hs3.x8 hsecNonNull hs3.pqspkNonNull
                  hctrl_u1 (htr_u1.trans (htr_z1.trans htr_c1)) hx25_u1 hx26_u1 hx1_u1 hpost hpanic)
              rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
              have hbase := Ext.s3_dh_collapse_common (A := A) (img := img) (x := x)
                (kp := kp) (ekASk := ekASk) (ekAPk := ekAPk)
                (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr) (opkId := opkId)
                hsub_ca hstk64 hekAPkLen hekASkLen hkpkLen s0
              have hsec_re :
                  (secretsPtr ↦ₛ bytesToBv8 F_X25519) ∗ memRegion (secretsPtr + 32#64) 32 ∗
                    memRegion (secretsPtr + 64#64) 32 ∗ memRegion (secretsPtr + 96#64) 32 ∗
                    memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
                  memRegion secretsPtr 192 := by
                refine Entails.trans (sepConj_mono_left
                  (pointsToBytes_entails_memRegion_len (n := 32) (by decide))) ?_
                rw [← s3_sec_split secretsPtr]; exact Entails.refl _
              have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 (hi ++ 3#8) u2
              have hloc_re :
                  memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
                    memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
                    memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
                  memRegion (fsp + 0x958#64) 0x1310 := by
                refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
                rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by clear * -; bv_omega) (by decide),
                    memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢
                  memRegion fsp 0x80 := by
                refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
                rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hc20 : ((fsp + 0x1c70#64) ↦₆₄ 32#64) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
                  memRegion (fsp + 0x1c70#64) 0x20 := by
                refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
                rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.refl _
              have hkeys_back := stage3KeySlotsAt_repack_dh1 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
              have htail1548 :
                  ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
                    memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ⊢
                  memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
                rw [show s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 from by
                  dsimp only [fsp]; clear * -; rw [cliInitiateFrame_eq]; bv_omega]
                refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
                have hm : memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
                    memRegion (fsp + 0x1c70#64) 0x20 =
                    memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
                  simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
                  rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by clear * -; bv_omega) (by decide),
                      memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by clear * -; bv_omega) (by decide)]
                exact Entails.of_eq (by rw [← hm]; ac_rfl)
              refine sep_replace (sepConj_mono hsec_re (sepConj_mono hm78 (sepConj_mono hsret hc20)))
                (by (try dsimp only [fsp]); sep_frame) ?_
              refine sep_replace (sepConj_mono hloc_re (Entails.of_eq hkeys_back))
                (by (try dsimp only [fsp]); cases x.bundle.opk <;> (dsimp only; sep_frame)) ?_
              refine sep_replace hbase (by (try dsimp only [fsp]); sep_frame) ?_
              dsimp only [Unwind1548Mem]
              exact sep_replace htail1548 (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)
          · intro hdh1_nz s_ok1 dh1Ptr hctrl_ok1 hcs_ok1 htr_ok1
            have hx20_1 := hcs_ok1.2.1.trans hx20_c1; have hx21_1 := hcs_ok1.2.2.1.trans hx21_c1
            have hx22_1 := hcs_ok1.2.2.2.1.trans hx22_c1
            have hx24_1 := hcs_ok1.2.2.2.2.2.1.trans hx24_c1
            have hx25_1 := hcs_ok1.2.2.2.2.2.2.1.trans hx25_c1
            set dh1 := (modelPrims X P0).x25519 (toU8 kp.privateKey.bytes.toList)
              (toU8 x.bundle.spk.bytes.toList)
            have hdh1_len : (bytesToBv8 dh1).length = 32 := by
              rw [bytesToBv8_length]; exact modelPrims_x25519_len X P0 _ _
            rw [hctrl_c1.sp, hstk_ca]
            obtain ⟨halign_1, hx29_1, hfsp_1⟩ := hctrl_ok1.step_ctx fsp
            refine' Ext.s3_block_to_call hOk
              (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
              0x808 (Φ := fun sm =>
                sm.readReg64 .x0 = secretsPtr + 32#64 ∧ sm.readReg64 .x1 = dh1Ptr ∧
                sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧
                sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 22#5) = 32#64 ∧
                sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                sm.readReg64 (.gpr 25#5) = secretsPtr ∧
                sm.readReg64 (.gpr 27#5) = 32#64 ∧ sm.readReg64 (.gpr 28#5) = dh1Ptr)
              hctrl_ok1 ?_ ?_; rotate_left 1
            · have hpc := hctrl_ok1.pc; have hrun := hctrl_ok1.run
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7a8 24
              code_fetches_range libsignalSessionCode initS3 img.base
                (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x7dc 44
              dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
                BitVec.ofNat_eq_ofNat] at hpc ⊢
              generalize_entry (libsignalSessionCode.rebase img.base
                (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
              (try dsimp only [fsp] at *); rw [← hctrl_ok1.sp] at *
              try simp only [arm64_norm, wp_norm] at hx20_1 hx21_1 hx22_1 hx24_1 hx25_1
              examples_hide_fetches; wp_steps
              refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                ⟨by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal,
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by simp only [hx20_1, hx21_1, hx22_1, hx24_1, hx25_1, arm64_norm, wp_norm],
                 by wp_norm_goal, by wp_norm_goal⟩
            · intro sm_mc1 hctrl_mc1 hpcm_mc1 hlrm_mc1 htrm_mc1
                ⟨hx0_mc1, hx1_mc1, hx2_mc1, hx20_mc1, hx21_mc1, hx22_mc1, hx23_mc1, hx24_mc1,
                 hx25_mc1, hx27_mc1, hx28_mc1⟩
              rw [hctrl_ok1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
              refine Ext.s3_memcpy hOk (secretsPtr + 32#64) dh1Ptr (bytesToBv8 dh1) _
                hctrl_mc1 (htrm_mc1.trans (htr_ok1.trans htr_c1)) hpcm_mc1 hlrm_mc1
                hx0_mc1 hx1_mc1 (by rw [hx2_mc1, hdh1_len]; decide) hpanic
                (by rw [hctrl_mc1.sp, hdh1_len]; (try dsimp only [fsp]); sep_frame)
                ?_
              intro s_mc1 hctrl_mc1' hcs_mc1 _ htr_mc1; rw [hctrl_mc1.sp]
              have hx20_m := hcs_mc1.2.1.trans hx20_mc1; have hx21_m := hcs_mc1.2.2.1.trans hx21_mc1
              have hx22_m := hcs_mc1.2.2.2.1.trans hx22_mc1
              have hx23_m := hcs_mc1.2.2.2.2.1.trans hx23_mc1; have hx24_m := hcs_mc1.2.2.2.2.2.1.trans hx24_mc1
              have hx25_m := hcs_mc1.2.2.2.2.2.2.1.trans hx25_mc1
              have hx27_m := hcs_mc1.2.2.2.2.2.2.2.2.1.trans hx27_mc1
              have hx28_m := hcs_mc1.2.2.2.2.2.2.2.2.2.1.trans hx28_mc1
              obtain ⟨halign_m1, hx29_m1, hfsp_m1⟩ := hctrl_mc1'.step_ctx fsp
              refine' Ext.s3_block_to_call hOk
                (initEntryExt img ext + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
                0x820 (Φ := fun sm =>
                  sm.readReg64 .x0 = dh1Ptr ∧ sm.readReg64 .x1 = 32#64 ∧ sm.readReg64 .x2 = 1#64 ∧
                  sm.readReg64 (.gpr 20#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x348#64 ∧
                  sm.readReg64 (.gpr 23#5) = fsp + 0x388#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                  sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
                hctrl_mc1' ?_ ?_; rotate_left 1
              · have hpc := hctrl_mc1'.pc; have hrun := hctrl_mc1'.run
                code_fetches_range libsignalSessionCode initS3 img.base
                  (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                  (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x808 24
                dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
                generalize_entry (libsignalSessionCode.rebase img.base
                  (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
                (try dsimp only [fsp] at *); rw [← hctrl_mc1'.sp] at *
                try simp only [arm64_norm, wp_norm] at hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m
                examples_hide_fetches; wp_steps
                refine s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                  ⟨by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by wp_norm_goal,
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm],
                   by simp only [hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx27_m, hx28_m, arm64_norm, wp_norm]⟩
              · intro sm_da1 hctrl_da1 hpcm_da1 hlrm_da1 htrm_da1
                  ⟨hx0_da1, hx1_da1, hx2_da1, hx20_da1, hx21_da1, hx23_da1, hx24_da1, hx25_da1, hx26_da1⟩
                rw [hctrl_mc1'.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
                refine Ext.s3_dealloc hOk dh1Ptr 32 _ hctrl_da1
                  (htrm_da1.trans (htr_mc1.trans (htrm_mc1.trans (htr_ok1.trans htr_c1))))
                  hpcm_da1 hlrm_da1 hx0_da1 (by rw [hx1_da1]; decide) (by rw [hx2_da1]; decide) lay32 hpanic
                  (by rw [hctrl_da1.sp]
                      exact sep_replace (pointsToBytes_entails_memRegion_len (a := dh1Ptr) hdh1_len)
                        (by (try dsimp only [fsp]); sep_frame) (by (try dsimp only [fsp]); sep_frame)) ?_
                intro s_d1 hctrl_d1 hcs_d1 htr_d1; rw [hctrl_da1.sp]
                have hx20_d1 := hcs_d1.2.1.trans hx20_da1; have hx21_d1 := hcs_d1.2.2.1.trans hx21_da1
                have hx23_d1 := hcs_d1.2.2.2.2.1.trans hx23_da1; have hx24_d1 := hcs_d1.2.2.2.2.2.1.trans hx24_da1
                have hx25_d1 := hcs_d1.2.2.2.2.2.2.1.trans hx25_da1
                have hx26_d1 := hcs_d1.2.2.2.2.2.2.2.1.trans hx26_da1
                refine' Ext.s3_block_in hOk 0x858 (Φ := fun sm =>
                  sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
                  sm.readReg64 (.gpr 22#5) = fsp + 0x408#64 ∧ sm.readReg64 (.gpr 24#5) = fsp + 0x3e8#64 ∧
                  sm.readReg64 (.gpr 25#5) = secretsPtr ∧ sm.readReg64 (.gpr 26#5) = 64#64)
                  hctrl_d1 ?_ ?_; rotate_left 1
                · have hpc := hctrl_d1.pc; have hrun := hctrl_d1.run
                  code_fetches_range libsignalSessionCode initS3 img.base
                    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
                    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x820 20
                  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc ⊢
                  generalize_entry (libsignalSessionCode.rebase img.base
                    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
                  (try dsimp only [fsp] at *); rw [← hctrl_d1.sp] at *
                  try simp only [arm64_norm, wp_norm] at hx20_d1 hx21_d1 hx23_d1 hx24_d1 hx25_d1 hx26_d1
                  examples_hide_fetches; wp_steps
                  refine s3_done_in (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs) (Entails.refl _)
                    ⟨by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm],
                     by simp only [hx20_d1, hx21_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, arm64_norm, wp_norm]⟩
                · intro s858 htr_858 hctrl_858 ⟨hx20_858, hx21_858, hx22_858, hx24_858, hx25_858, hx26_858⟩
                  rw [hctrl_d1.sp] at *; (try iterate 6 rw [BitVec.add_comm _ fsp]); (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
                  have hdh1_eq := dh1_model_eq X P0 kp x.bundle be x.coins hs3.bundleEq
                  have htr_final : s858.trace = s0.trace :=
                    htr_858.trans (htr_d1.trans (htrm_da1.trans (htr_mc1.trans (htrm_mc1.trans (htr_ok1.trans htr_c1)))))
                  have hsret_ok := cells3_to_memRegion24 (fsp + 0x1600#64) 0#64 dh1Ptr 32#64
                  have hkeys_ok := stage3KeySlotsAt_repack_dh1 A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
                  refine sepWPp_conseq_oom ?_
                    (hnext s858 secretsPtr dh1 hdh1_eq hdh1_nz hsecNonNull hctrl_858 htr_final
                      hx20_858 hx21_858 hx22_858 hx24_858 hx25_858 hx26_858)
                  rw [bytesToBv8_toU8_eq, bytesToBv8_toU8_eq]
                  dsimp only [fsp] at hstk_ca ⊢
                  refine sep_replace (Entails.of_eq hstk_ca.symm) (by sep_frame) ?_
                  exact sep_replace
                    (sepConj_mono hsret_ok (sepConj_mono (Entails.of_eq hkeys_ok)
                      (Entails.of_eq (append_bv8_at secretsPtr F_X25519 dh1 32#64 rfl))))
                    (by cases x.bundle.opk <;> ((try dsimp only); sep_frame))
                    (by sep_frame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
