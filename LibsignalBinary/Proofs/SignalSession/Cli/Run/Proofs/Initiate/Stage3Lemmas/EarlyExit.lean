/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Shared Non-Contributory Zero-DH Unwind Exit

Verifies the shared zero-DH unwind tail (`+0x1544` / `+0x1548 → +0x0350 → ret`) freeing
`secretsPtr` (`192` B) and `pqspkPtr` (`1568` B), writing `SpeOwned.plain 10` at `x.ret`,
restoring callee-saved registers, and reassembling `InitExitPost`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

theorem s3_done_in {prog : Program} {target : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = target := by wp_norm_goal)
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm]) :
    SepWP prog target sm P (fun s' P'' =>
      s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htr, hent, hsp, hfp, hx19, hvregs, hphi⟩

theorem s3_done_call {prog : Program} {callee lr_out : BitVec 64} {s sm : State}
    {P P' : SepProp} {Φ : State → Prop}
    (hrun : sm.status = .Running) (hent : P ⊢ P') (hphi : Φ sm)
    (hpc : sm.pc = callee := by wp_norm_goal)
    (htr : sm.trace = s.trace := by simp only [arm64_norm, wp_norm])
    (hsp : sm.sp = s.sp := by wp_norm_goal)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp := by wp_norm_goal)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by wp_norm_goal)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, arm64_norm, wp_norm])
    (hlr : sm.readReg64 .lr = lr_out := by wp_norm_goal) :
    SepWP prog callee sm P (fun s' P'' =>
      s'.trace = s.trace ∧ (P'' ⊢ P') ∧ s'.sp = s.sp ∧
      s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧ s'.readReg64 .lr = lr_out ∧ Φ s') :=
  SepWP.done hpc hrun ⟨htr, hent, hsp, hfp, hx19, hvregs, hlr, hphi⟩

/-- Exact spatial footprint entering the shared zero-DH unwind tail at `+0x1548`. -/
def Unwind1548Mem (A : RustAlloc) (img : Obj.Image) (x : InitGhost)
    (pqspkPtr secretsPtr : BitVec 64) (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ A.pool ∗ initSaved s0 ∗
    A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
    A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
    memRegion fsp 0x128 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x2e0 ∗
    ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
    memRegion (fsp + 0x438#64) 0x181 ∗
    ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) 0x37e ∗
    memRegion (fsp + 0x938#64) 0x20 ∗
    memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) ∗
    stackAt fsp (stk - cliInitiateFrame) ∗
    coinsCursorAt img x.coinsP x.coins 32 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img

private theorem unwind_locals_collapse {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (pqspkPtr : BitVec 64) (u0 u1 u2 u3 : BitVec 64) (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    initSaved s0 ∗
      memRegion fsp 0x128 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x2e0 ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      memRegion (fsp + 0x438#64) 0x181 ∗
      ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 0x37e ∗
      ((fsp + 0x938#64) ↦₆₄ u0) ∗ ((fsp + 0x940#64) ↦₆₄ u1) ∗
      ((fsp + 0x948#64) ↦₆₄ u2) ∗ ((fsp + 0x950#64) ↦₆₄ u3) ∗
      memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  dsimp only
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine Entails.trans
    (sepConj_mono (initSaved_entails_memRegion96 s0)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (initFreshRecAt_collapse fsp)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (Entails.refl _)))))))))))))) ?_
  have hloc :
      memRegion fsp 0x128 ∗ memRegion (fsp + 0x128#64) 0x20 ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗ memRegion (fsp + 0x428#64) 8 ∗
        memRegion (fsp + 0x430#64) 8 ∗ memRegion (fsp + 0x438#64) 0x181 ∗
        memRegion (fsp + 0x5b9#64) 1 ∗ memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
        memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 ∗
        memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) =
      memRegion fsp initLocalsSize := by
    simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
    rw [memRegion_merge_at (fsp + 0x950#64) 8 4920 (fsp + 0x958#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x948#64) 8 4928 (fsp + 0x950#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x940#64) 8 4936 (fsp + 0x948#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x938#64) 8 4944 (fsp + 0x940#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5ba#64) 0x37e 4952 (fsp + 0x938#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x5b9#64) 1 5846 (fsp + 0x5ba#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x438#64) 0x181 5847 (fsp + 0x5b9#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x430#64) 8 6232 (fsp + 0x438#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x428#64) 8 6240 (fsp + 0x430#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x148#64) 0x2e0 6248 (fsp + 0x428#64) (by bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x128#64) 0x20 6984 (fsp + 0x148#64) (by bv_omega) (by decide),
      memRegion_merge_at fsp 0x128 7016 (fsp + 0x128#64) (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq ?_) (stack_frame_reassemble hstk hstk64 s0)
  dsimp only [fsp] at hloc ⊢
  rw [← hloc]
  ac_rfl

theorem fsp_eq_sp {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    s0.sp - BitVec.ofNat 64 cliInitiateFrame = s.sp :=
  h.sp.symm

theorem sep_replace {P R A B F : SepProp}
    (h : A ⊢ B) (h1 : P ⊢ A ∗ F) (h2 : B ∗ F ⊢ R) : P ⊢ R :=
  Entails.trans h1 (Entails.trans (sepConj_mono h (Entails.refl F)) h2)

set_option maxHeartbeats 800000 in
theorem unwind_1548_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 s 0x1548)
    (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 (.gpr 25#5) = secretsPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (Unwind1548Mem A img x pqspkPtr secretsPtr stk s0) Q Qp (initOom s0) := by
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub64 : stk - cliInitiateFrame ≤ 2 ^ 64 := stk_sub_le_2pow64 hstk64
  dsimp only [Unwind1548Mem]
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  rw [stackAt_sub_split_init fsp hsub_ext hsub64]
  refine' s3_block_to_call hh
    (initEntry img W + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    0x1554
    (Φ := fun sm =>
      sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧
      sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx25 hx26 hx1
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1548 12
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [*, arm64_norm, wp_norm], Entails.refl _,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [calleeSavedVRegs, arm64_norm, wp_norm], by wp_norm_goal,
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by wp_norm_goal,
       by simp only [*, arm64_norm, wp_norm]⟩
  · intro sm1 hctrl1 hpcm1 hlrm1 htrm1 ⟨hx0_1, hx1_1, hx2_1, hx26_1⟩
    refine s3_dealloc hh secretsPtr 192 _ hctrl1 (htrm1.trans htr) hpcm1 hlrm1
      hx0_1 (by rw [hx1_1]; decide) (by rw [hx2_1]; decide) lay192 hpanic
      (by rw [hctrl1.sp]; try dsimp only [fsp] at *; sep_frame) ?_
    intro s1 hctrl2 hcs1 htr1
    rw [hctrl1.sp]
    have hx26_2 : s1.readReg64 (.gpr 26#5) = speWord 10 := hcs1.2.2.2.2.2.2.2.1.trans hx26_1
    have h938 :
        memRegion (fsp + 0x938#64) 0x20 =
          memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
          memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 := by
      rw [memRegion_merge_at (fsp + 0x948#64) 8 8 (fsp + 0x950#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x940#64) 8 16 (fsp + 0x948#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x938#64) 8 24 (fsp + 0x940#64) (by bv_omega) (by decide)]
    rw [h938, ProofLib.memRegion_eight (fsp + 0x938#64), ProofLib.memRegion_eight (fsp + 0x940#64),
      ProofLib.memRegion_eight (fsp + 0x948#64), ProofLib.memRegion_eight (fsp + 0x950#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
      sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 => ?_
    obtain ⟨halign, _, hfsp⟩ := hctrl2.step_ctx fsp
    refine' s3_block_to_call hh
      (initEntry img W +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      0x157c
      (Φ := fun sm =>
        sm.readReg64 .x0 = pqspkPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
        sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
      hctrl2 ?_ ?_; rotate_left 1
    · have hpc := hctrl2.pc; have hrun := hctrl2.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1554 40
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      try dsimp only [fsp] at hfsp ⊢
      rw [hfsp]
      examples_hide_fetches; wp_steps
      refine s3_done_call (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by simp only [*, arm64_norm, wp_norm]⟩
    · intro sm2 hctrl3 hpcm2 hlrm2 htrm2 ⟨hx0_2, hx1_2, hx2_2, hx26_3⟩
      rw [← hfsp]
      refine s3_dealloc hh pqspkPtr 1568 _ hctrl3
        (htrm2.trans (htr1.trans (htrm1.trans htr))) hpcm2 hlrm2
        hx0_2 (by rw [hx1_2]; decide) (by rw [hx2_2]; decide) lay1568 hpanic
        (by rw [hctrl3.sp]; try dsimp only [fsp] at *; sep_frame) ?_
      intro s3 hctrl4 hcs3 htr3
      rw [hctrl3.sp]
      have hx26_4 : s3.readReg64 (.gpr 26#5) = speWord 10 :=
        hcs3.2.2.2.2.2.2.2.1.trans hx26_3
      have hret48 :
          memRegion x.ret 48 =
            memRegion x.ret 8 ∗ memRegion (x.ret + 8#64) 8 ∗
            memRegion (x.ret + 16#64) 8 ∗ memRegion (x.ret + 24#64) 8 ∗
            memRegion (x.ret + 32#64) 8 ∗ memRegion (x.ret + 40#64) 8 := by
        rw [memRegion_merge_at (x.ret + 32#64) 8 8 (x.ret + 40#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 24#64) 8 16 (x.ret + 32#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 16#64) 8 24 (x.ret + 24#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 8#64) 8 32 (x.ret + 16#64) (by bv_omega) (by decide),
          memRegion_merge_at x.ret 8 40 (x.ret + 8#64) (by bv_omega) (by decide)]
      rw [hret48, ProofLib.memRegion_eight x.ret, ProofLib.memRegion_eight (x.ret + 8#64),
        ProofLib.memRegion_eight (x.ret + 16#64), ProofLib.memRegion_eight (x.ret + 24#64),
        ProofLib.memRegion_eight (x.ret + 32#64), ProofLib.memRegion_eight (x.ret + 40#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun r0 => sepWPp_exists_elim_oom fun r1 =>
        sepWPp_exists_elim_oom fun r2 => sepWPp_exists_elim_oom fun r3 =>
        sepWPp_exists_elim_oom fun r4 => sepWPp_exists_elim_oom fun r5 => ?_
      refine s3_step_to hh hctrl4.inv (mid := s0.readReg64 .lr) ?_
      have halign4 := (hctrl4.step_ctx fsp).1
      have hpc4 := hctrl4.pc; have hrun4 := hctrl4.run
      have hx19_4 : s3.readReg64 (.gpr 19#5) = x.ret := hctrl4.x19.trans hx8
      have hs0sp : s0.sp = s3.sp + 7408#64 := by
        have hsp4 := hctrl4.sp
        dsimp only [cliInitiateFrame, BitVec.ofNat_eq_ofNat] at hsp4
        rw [hsp4]; bv_omega
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x157c 108
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x350 48
      dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt, initFreshRecAt,
        initSaved, speWord, cliInitiateFrame, fsp,
        BitVec.ofNat_eq_ofNat] at hpc4 hx26_4 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
      simp only [arm64_norm, wp_norm] at hx19_4 hx26_4
      conv =>
        arg 4
        simp only [Nat.reduceAdd, hs0sp,
          show s3.sp + 7408#64 - 7408#64 = s3.sp from by bv_omega,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
      examples_hide_fetches; wp_steps
      have hsp_fin : s3.sp + 4096#64 + 3216#64 + 96#64 = s0.sp := by
        rw [hs0sp]; bv_omega
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by simp only [*, arm64_norm, wp_norm], fun _ hfs_fin => ?_⟩
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      apply hpost
      refine ⟨by rw [← hs0sp]; simp only [arm64_norm, wp_norm], ?_, ?_⟩
      · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
        simpa only [calleeSavedVRegs, arm64_norm, wp_norm] using hctrl4.vregs
      · dsimp only [initSlotSpec, Spec.inImage, slotTrace, slotOut]
        refine Entails.sepExists_right StoresGhost.opened
          (Entails.sepExists_right (.error (.untrustedIdentity x.peer.val)) ?_)
        refine Entails.pure_right ?_ ?_
        · exact ⟨⟨by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]; exact List.prefix_refl _,
                  hfs_fin.trans hctrl4.files0,
                  by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]⟩,
                 (fun h => nomatch h), (fun h => nomatch h), by rw [hS, hnone]⟩
        have hres := sret_err_speOwned A x.peer.val x.ret
          (s3.readReg64 (.gpr 27#5))
          (s3.readReg64 (.gpr 25#5)) (s3.readReg64 (.gpr 28#5))
          (s3.readReg64 (.gpr 24#5)) (s3.readReg64 (.gpr 21#5))
        have hstk_re := unwind_locals_collapse hstk hstk64 pqspkPtr u3 u2 u1 u0 s0
        dsimp only at hstk_re
        rw [stackAt_sub_split_init (s0.sp - BitVec.ofNat 64 cliInitiateFrame) hsub_ext hsub64]
          at hstk_re
        have htop :
            coinsCursorAt img x.coinsP x.coins 32 ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ⊢ anyHeap :=
          ProofLib.entails_anyHeap _
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono hres
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hstk_re htop)))))))))
        dsimp only [fsp, speWord, initSaved, initFreshRecAt, cliInitiateFrame,
          State.sp, BitVec.ofNat_eq_ofNat] at hs0sp hres hstk_re ⊢
        rw [hs0sp]
        simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceAdd, BitVec.reduceNeg, BitVec.add_zero]
        ac_rfl

/-- Entry at `+0x1544` (`ldur x25, [x29, #-0x28]`), shared by `DH2`, `DH3`, and `DH4`. -/
theorem unwind_1544_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiate img W s0 s 0x1544)
    (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗
        memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img) Q Qp (initOom s0) := by
  dsimp only
  have hslot : s0.sp - 0x60#64 - 0x28#64 = s.readReg64 (.gpr 29#5) - 0x28#64 := by
    change _ = s.readReg64 .fp - 0x28#64; rw [hctrl.fp]
  rw [hslot]
  refine' s3_block_in hh 0x1548
    (Φ := fun sm =>
      sm.readReg64 (.gpr 25#5) = secretsPtr ∧
      sm.readReg64 (.gpr 26#5) = speWord 10 ∧
      sm.readReg64 .x1 = 192#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx26 hx1
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1544 4
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [*, arm64_norm, wp_norm], Entails.refl _,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [calleeSavedVRegs, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm]⟩
  · intro sm htrm hctrl' ⟨hx25', hx26', hx1'⟩
    rw [← hslot]
    refine sepWPp_conseq_oom ?_
      (unwind_1548_ok hh hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl'
        (htrm.trans htr) hx25' hx26' hx1' hpost hpanic)
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    have haddr : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
      dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
    have htail :
        ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ⊢
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
      rw [haddr]
      refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
      have hmerge :
          memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
            memRegion (fsp + 0x1c70#64) 0x20 =
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
        simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
        rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by bv_omega) (by decide),
          memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by bv_omega) (by decide)]
      exact Entails.of_eq (by rw [← hmerge]; ac_rfl)
    dsimp only [Unwind1548Mem]
    exact sep_replace htail (by dsimp only [fsp]; sep_frame) (by dsimp only [fsp]; sep_frame)

/-! ## Contract-Parameterized Unwind Tail (`Stage3Lemmas.Ext.*`) -/

namespace Ext

theorem fsp_eq_sp {img : Obj.Image} {ext : String → Option (State → State)} {s0 s : State} {k : Nat}
    (h : InInitiateExt img ext s0 s k) :
    s0.sp - BitVec.ofNat 64 cliInitiateFrame = s.sp :=
  h.sp.symm

set_option maxHeartbeats 800000 in
theorem unwind_1548_ok {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hS : S.initiate = initDef X P0)
    (hnone : initDef X P0 x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 s 0x1548)
    (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 (.gpr 25#5) = secretsPtr)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (Unwind1548Mem A img x pqspkPtr secretsPtr stk s0) Q Qp (initOom s0) := by
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hsub64 : stk - cliInitiateFrame ≤ 2 ^ 64 := stk_sub_le_2pow64 hstk64
  dsimp only [Unwind1548Mem]
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  rw [stackAt_sub_split_init fsp hsub_ext hsub64]
  refine' s3_block_to_call hOk
    (initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    0x1554
    (Φ := fun sm =>
      sm.readReg64 .x0 = secretsPtr ∧ sm.readReg64 .x1 = 192#64 ∧
      sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx25 hx26 hx1
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1548 12
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [*, arm64_norm, wp_norm], Entails.refl _,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [calleeSavedVRegs, arm64_norm, wp_norm], by wp_norm_goal,
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by wp_norm_goal,
       by simp only [*, arm64_norm, wp_norm]⟩
  · intro sm1 hctrl1 hpcm1 hlrm1 htrm1 ⟨hx0_1, hx1_1, hx2_1, hx26_1⟩
    refine s3_dealloc hOk secretsPtr 192 _ hctrl1 (htrm1.trans htr) hpcm1 hlrm1
      hx0_1 (by rw [hx1_1]; decide) (by rw [hx2_1]; decide) lay192 hpanic
      (by rw [hctrl1.sp]; try dsimp only [fsp] at *; sep_frame) ?_
    intro s1 hctrl2 hcs1 htr1
    rw [hctrl1.sp]
    have hx26_2 : s1.readReg64 (.gpr 26#5) = speWord 10 := hcs1.2.2.2.2.2.2.2.1.trans hx26_1
    have h938 :
        memRegion (fsp + 0x938#64) 0x20 =
          memRegion (fsp + 0x938#64) 8 ∗ memRegion (fsp + 0x940#64) 8 ∗
          memRegion (fsp + 0x948#64) 8 ∗ memRegion (fsp + 0x950#64) 8 := by
      rw [memRegion_merge_at (fsp + 0x948#64) 8 8 (fsp + 0x950#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x940#64) 8 16 (fsp + 0x948#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x938#64) 8 24 (fsp + 0x940#64) (by bv_omega) (by decide)]
    rw [h938, ProofLib.memRegion_eight (fsp + 0x938#64), ProofLib.memRegion_eight (fsp + 0x940#64),
      ProofLib.memRegion_eight (fsp + 0x948#64), ProofLib.memRegion_eight (fsp + 0x950#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
      sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 => ?_
    obtain ⟨halign, _, hfsp⟩ := hctrl2.step_ctx fsp
    refine' s3_block_to_call hOk
      (initEntryExt img ext +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      0x157c
      (Φ := fun sm =>
        sm.readReg64 .x0 = pqspkPtr ∧ sm.readReg64 .x1 = 1568#64 ∧
        sm.readReg64 .x2 = 1#64 ∧ sm.readReg64 (.gpr 26#5) = speWord 10)
      hctrl2 ?_ ?_; rotate_left 1
    · have hpc := hctrl2.pc; have hrun := hctrl2.run
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1554 40
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      try dsimp only [fsp] at hfsp ⊢
      rw [hfsp]
      examples_hide_fetches; wp_steps
      refine s3_done_call (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
         by simp only [*, arm64_norm, wp_norm]⟩
    · intro sm2 hctrl3 hpcm2 hlrm2 htrm2 ⟨hx0_2, hx1_2, hx2_2, hx26_3⟩
      rw [← hfsp]
      refine s3_dealloc hOk pqspkPtr 1568 _ hctrl3
        (htrm2.trans (htr1.trans (htrm1.trans htr))) hpcm2 hlrm2
        hx0_2 (by rw [hx1_2]; decide) (by rw [hx2_2]; decide) lay1568 hpanic
        (by rw [hctrl3.sp]; try dsimp only [fsp] at *; sep_frame) ?_
      intro s3 hctrl4 hcs3 htr3
      rw [hctrl3.sp]
      have hx26_4 : s3.readReg64 (.gpr 26#5) = speWord 10 :=
        hcs3.2.2.2.2.2.2.2.1.trans hx26_3
      have hret48 :
          memRegion x.ret 48 =
            memRegion x.ret 8 ∗ memRegion (x.ret + 8#64) 8 ∗
            memRegion (x.ret + 16#64) 8 ∗ memRegion (x.ret + 24#64) 8 ∗
            memRegion (x.ret + 32#64) 8 ∗ memRegion (x.ret + 40#64) 8 := by
        rw [memRegion_merge_at (x.ret + 32#64) 8 8 (x.ret + 40#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 24#64) 8 16 (x.ret + 32#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 16#64) 8 24 (x.ret + 24#64) (by bv_omega) (by decide),
          memRegion_merge_at (x.ret + 8#64) 8 32 (x.ret + 16#64) (by bv_omega) (by decide),
          memRegion_merge_at x.ret 8 40 (x.ret + 8#64) (by bv_omega) (by decide)]
      rw [hret48, ProofLib.memRegion_eight x.ret, ProofLib.memRegion_eight (x.ret + 8#64),
        ProofLib.memRegion_eight (x.ret + 16#64), ProofLib.memRegion_eight (x.ret + 24#64),
        ProofLib.memRegion_eight (x.ret + 32#64), ProofLib.memRegion_eight (x.ret + 40#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun r0 => sepWPp_exists_elim_oom fun r1 =>
        sepWPp_exists_elim_oom fun r2 => sepWPp_exists_elim_oom fun r3 =>
        sepWPp_exists_elim_oom fun r4 => sepWPp_exists_elim_oom fun r5 => ?_
      refine s3_step_to hOk hctrl4.inv (mid := s0.readReg64 .lr) ?_
      have halign4 := (hctrl4.step_ctx fsp).1
      have hpc4 := hctrl4.pc; have hrun4 := hctrl4.run
      have hx19_4 : s3.readReg64 (.gpr 19#5) = x.ret := hctrl4.x19.trans hx8
      have hs0sp : s0.sp = s3.sp + 7408#64 := by
        have hsp4 := hctrl4.sp
        dsimp only [cliInitiateFrame, BitVec.ofNat_eq_ofNat] at hsp4
        rw [hsp4]; bv_omega
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x157c 108
      code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
        cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x350 48
      dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt, initFreshRecAt,
        initSaved, speWord, cliInitiateFrame, fsp,
        BitVec.ofNat_eq_ofNat] at hpc4 hx26_4 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
      simp only [arm64_norm, wp_norm] at hx19_4 hx26_4
      conv =>
        arg 4
        simp only [Nat.reduceAdd, hs0sp,
          show s3.sp + 7408#64 - 7408#64 = s3.sp from by bv_omega,
          BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
      examples_hide_fetches; wp_steps
      have hsp_fin : s3.sp + 4096#64 + 3216#64 + 96#64 = s0.sp := by
        rw [hs0sp]; bv_omega
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by simp only [*, arm64_norm, wp_norm], fun _ hfs_fin => ?_⟩
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      apply hpost
      refine ⟨by rw [← hs0sp]; simp only [arm64_norm, wp_norm], ?_, ?_⟩
      · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
                by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_⟩
        simpa only [calleeSavedVRegs, arm64_norm, wp_norm] using hctrl4.vregs
      · dsimp only [initSlotSpec, Spec.inImage, slotTrace, slotOut]
        refine Entails.sepExists_right StoresGhost.opened
          (Entails.sepExists_right (.error (.untrustedIdentity x.peer.val)) ?_)
        refine Entails.pure_right ?_ ?_
        · exact ⟨⟨by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]; exact List.prefix_refl _,
                  hfs_fin.trans hctrl4.files0,
                  by simp only [arm64_norm, wp_norm, htr3, htrm2, htr1, htrm1, htr]⟩,
                 (fun h => nomatch h), (fun h => nomatch h), by rw [hS, hnone]⟩
        have hres := sret_err_speOwned A x.peer.val x.ret
          (s3.readReg64 (.gpr 27#5))
          (s3.readReg64 (.gpr 25#5)) (s3.readReg64 (.gpr 28#5))
          (s3.readReg64 (.gpr 24#5)) (s3.readReg64 (.gpr 21#5))
        have hstk_re := unwind_locals_collapse hstk hstk64 pqspkPtr u3 u2 u1 u0 s0
        dsimp only at hstk_re
        rw [stackAt_sub_split_init (s0.sp - BitVec.ofNat 64 cliInitiateFrame) hsub_ext hsub64]
          at hstk_re
        have htop :
            coinsCursorAt img x.coinsP x.coins 32 ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ⊢ anyHeap :=
          ProofLib.entails_anyHeap _
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono hres
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hstk_re htop)))))))))
        dsimp only [fsp, speWord, initSaved, initFreshRecAt, cliInitiateFrame,
          State.sp, BitVec.ofNat_eq_ofNat] at hs0sp hres hstk_re ⊢
        rw [hs0sp]
        simp only [Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.add_assoc,
          BitVec.reduceAdd, BitVec.reduceNeg, BitVec.add_zero]
        ac_rfl

theorem unwind_1544_ok {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {pqspkPtr secretsPtr : BitVec 64} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hS : S.initiate = initDef X P0)
    (hnone : initDef X P0 x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64)
    (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiateExt img ext s0 s 0x1544)
    (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10)
    (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗
        initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗
        ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗
        memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗
        memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img) Q Qp (initOom s0) := by
  dsimp only
  have hslot : s0.sp - 0x60#64 - 0x28#64 = s.readReg64 (.gpr 29#5) - 0x28#64 := by
    change _ = s.readReg64 .fp - 0x28#64; rw [hctrl.fp]
  rw [hslot]
  refine' s3_block_in hOk 0x1548
    (Φ := fun sm =>
      sm.readReg64 (.gpr 25#5) = secretsPtr ∧
      sm.readReg64 (.gpr 26#5) = speWord 10 ∧
      sm.readReg64 .x1 = 192#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc; have hrun := hctrl.run
    simp only [arm64_norm, wp_norm] at hx26 hx1
    code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x1544 4
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt,
      BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
    examples_hide_fetches; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [*, arm64_norm, wp_norm], Entails.refl _,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
       by simp only [calleeSavedVRegs, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm],
       by simp only [*, arm64_norm, wp_norm]⟩
  · intro sm htrm hctrl' ⟨hx25', hx26', hx1'⟩
    rw [← hslot]
    refine sepWPp_conseq_oom ?_
      (unwind_1548_ok hOk hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl'
        (htrm.trans htr) hx25' hx26' hx1' hpost hpanic)
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    have haddr : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
      dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
    have htail :
        ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ⊢
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
      rw [haddr]
      refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
      have hmerge :
          memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c68#64) 8 ∗
            memRegion (fsp + 0x1c70#64) 0x20 =
          memRegion (fsp + 0x958#64) (initLocalsSize - 0x958) := by
        simp only [initLocalsSize, Nat.reduceAdd, Nat.reduceSub]
        rw [memRegion_merge_at (fsp + 0x1c68#64) 8 32 (fsp + 0x1c70#64) (by bv_omega) (by decide),
          memRegion_merge_at (fsp + 0x958#64) 4880 40 (fsp + 0x1c68#64) (by bv_omega) (by decide)]
      exact Entails.of_eq (by rw [← hmerge]; ac_rfl)
    dsimp only [Unwind1548Mem]
    exact sep_replace htail (by dsimp only [fsp]; sep_frame) (by dsimp only [fsp]; sep_frame)

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
