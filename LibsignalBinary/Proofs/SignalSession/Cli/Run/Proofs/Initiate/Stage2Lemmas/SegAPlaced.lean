/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_Step4OkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegB_ErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_FinishPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_PrepPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 Composition (`0x0390 → 0x0760`)

Composes the `[LibsignalPlacement]` Stage 2 steps from `stage2MemPlaced` (`0x0390`) to
`AtStage3Placed` (`0x0760`) and early `Err` / OOM exits on `initProgPlaced`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
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

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16
  symtab_setPC_pre symtab_setMem_pre symtab_setPState_pre
  symtab_writeReg64_pre symtab_writeReg32_pre symtab_writeReg_pre symtab_writeVReg128_pre

private theorem sepWPp_pure_4th {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 Rest : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ Rest) Q Qp oom :=
  sepWPp_weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_pure_left h)

private theorem initArgsAtPlaced_entails_mr88 [LibsignalPlacement] (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) :
    initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 88 := by
  unfold initArgsAtPlaced
  refine mr_fold (fsp + 0xd0#64) (fsp + 0xd8#64) 8 80 88 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xd8#64) (fsp + 0xe0#64) 8 72 80 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xe0#64) (fsp + 0xe8#64) 8 64 72 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xe8#64) (fsp + 0xf0#64) 8 56 64 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xf0#64) (fsp + 0xf8#64) 8 48 56 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xf8#64) (fsp + 0x100#64) 8 40 48 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x100#64) (fsp + 0x108#64) 8 32 40 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x108#64) (fsp + 0x110#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x110#64) (fsp + 0x114#64) 4 20 24 (mr_of_u32 _ _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x114#64) (fsp + 0x118#64) 4 16 20 (Entails.refl _) ?_ rfl (by bv_omega)
  exact mr_fold (fsp + 0x118#64) (fsp + 0x120#64) 8 8 16
    (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)

private theorem stage2_err_locals_placed_fold [LibsignalPlacement] (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) (ekAPk ekASk : List (BitVec 8)) (opkId : BitVec 32)
    (hekPk : ekAPk.length = 32) (hekSk : ekASk.length = 32) :
    initFreshRecAt fsp ∗
      (memRegion fsp 0x78 ∗
        memRegion (fsp + 120#64) 8 ∗
        memRegion (fsp + 0x80#64) 0x50 ∗
        initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        ((fsp + 664#64) ↦ₛ ekAPk) ∗
        ((fsp + 696#64) ↦ₛ ekASk) ∗
        ((fsp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((fsp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((fsp + 772#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 776#64) 344 ∗
        memRegion (fsp + 0x460#64) 0x158 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 1472#64) 16 ∗
        memRegion (fsp + 1864#64) 24 ∗
        memRegion (fsp + 1904#64) 32 ∗
        memRegion (fsp + 2336#64) 32 ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 4096#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗
        scratch5baGaps fsp) ⊢
      memRegion fsp initLocalsSize := by
  have hmFresh : initFreshRecAt fsp ⊢ memRegion (fsp + 296#64) 32 := by
    rw [initFreshRecAt_eq_fsp fsp]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words4_entails_mr32 (fsp + 296#64) 0#64 8#64 0#64 (0#64 - 1#64)
  have hmArgs := initArgsAtPlaced_entails_mr88 fsp x s0
  have hm4064 := mr_fold (fsp + 4064#64) (fsp + 4096#64) 32 32 64
    (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
  have hm5ba :
      memRegion (fsp + 1472#64) 16 ∗
        (memRegion (fsp + 1864#64) 24 ∗
          (memRegion (fsp + 1904#64) 32 ∗
            (memRegion (fsp + 2336#64) 32 ∗
              (memRegion (fsp + 2496#64) 32 ∗
                ((memRegion (fsp + 4064#64) 32 ∗ memRegion (fsp + 4096#64) 32) ∗
                  (memRegion (fsp + 5632#64) 72 ∗ scratch5baGaps fsp)))))) ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    rw [scratch5ba_split fsp]
    simp only [sepConj_assoc] at hm4064 ⊢
    refine entails_by_focus (by sep_frame) hm4064 ?_
    sep_frame
  refine Entails.trans (by
    have h664 := mr_of_bytes (fsp + 664#64) ekAPk 32 hekPk
    have h696 := mr_of_bytes (fsp + 696#64) ekASk 32 hekSk
    have h728 := mr_of_bytes (fsp + 728#64) x.bundle.spk.bytes.toList 32
      x.bundle.spk.bytes.property
    have h760 := mr_of_u64 (fsp + 760#64) (x.bundleA + 88#64)
    have h768 := mr_of_u32 (fsp + 768#64) (if x.bundle.opk.isSome then 1#32 else 0#32)
    have h772 := mr_of_u32 (fsp + 772#64) opkId
    have h5b8 := mr_of_u8 (fsp + 0x5b8#64) 0#8
    have h5b9 := mr_of_u8 (fsp + 0x5b9#64) 0#8
    refine (?_ : _ ⊢
      memRegion fsp 0x78 ∗ memRegion (fsp + 120#64) 8 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
        memRegion (fsp + 0xd0#64) 88 ∗ memRegion (fsp + 296#64) 32 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 664#64) 32 ∗
        memRegion (fsp + 696#64) 32 ∗ memRegion (fsp + 728#64) 32 ∗
        memRegion (fsp + 760#64) 8 ∗ memRegion (fsp + 768#64) 4 ∗ memRegion (fsp + 772#64) 4 ∗
        memRegion (fsp + 776#64) 344 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
        memRegion (fsp + 0x5b8#64) 1 ∗ memRegion (fsp + 0x5b9#64) 1 ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))
    simp only [sepConj_assoc] at hmFresh hmArgs hm5ba h664 h696 h728 h760 h768 h772 h5b8 h5b9 ⊢
    refine entails_by_focus (by sep_frame) hmFresh ?_
    refine entails_by_focus (by sep_frame) hmArgs ?_
    refine entails_by_focus (by sep_frame) hm5ba ?_
    refine entails_by_focus (by sep_frame) h664 ?_
    refine entails_by_focus (by sep_frame) h696 ?_
    refine entails_by_focus (by sep_frame) h728 ?_
    refine entails_by_focus (by sep_frame) h760 ?_
    refine entails_by_focus (by sep_frame) h768 ?_
    refine entails_by_focus (by sep_frame) h772 ?_
    refine entails_by_focus (by sep_frame) h5b8 ?_
    refine entails_by_focus (by sep_frame) h5b9 ?_
    sep_frame) ?_
  refine mr_fold fsp (fsp + 120#64) 0x78 (initLocalsSize - 120) initLocalsSize
    (Entails.refl _) ?_ rfl rfl
  refine mr_fold (fsp + 120#64) (fsp + 0x80#64) 8 (initLocalsSize - 128) (initLocalsSize - 120)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x80#64) (fsp + 0xd0#64) 0x50 (initLocalsSize - 208) (initLocalsSize - 128)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0xd0#64) (fsp + 296#64) 88 (initLocalsSize - 296) (initLocalsSize - 208)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 296#64) (fsp + 0x148#64) 32 (initLocalsSize - 328) (initLocalsSize - 296)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x148#64) (fsp + 664#64) 0x150 (initLocalsSize - 664) (initLocalsSize - 328)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 664#64) (fsp + 696#64) 32 (initLocalsSize - 696) (initLocalsSize - 664)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 696#64) (fsp + 728#64) 32 (initLocalsSize - 728) (initLocalsSize - 696)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 728#64) (fsp + 760#64) 32 (initLocalsSize - 760) (initLocalsSize - 728)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 760#64) (fsp + 768#64) 8 (initLocalsSize - 768) (initLocalsSize - 760)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 768#64) (fsp + 772#64) 4 (initLocalsSize - 772) (initLocalsSize - 768)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 772#64) (fsp + 776#64) 4 (initLocalsSize - 776) (initLocalsSize - 772)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 776#64) (fsp + 0x460#64) 344 (initLocalsSize - 1120) (initLocalsSize - 776)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x460#64) (fsp + 0x5b8#64) 0x158 (initLocalsSize - 1464) (initLocalsSize - 1120)
    (Entails.refl _) ?_ rfl (by bv_omega)
  refine mr_fold (fsp + 0x5b8#64) (fsp + 0x5b9#64) 1 (initLocalsSize - 1465) (initLocalsSize - 1464)
    (Entails.refl _) ?_ rfl (by bv_omega)
  exact mr_fold (fsp + 0x5b9#64) (fsp + 0x5ba#64) 1 (initLocalsSize - 0x5ba) (initLocalsSize - 1465)
    (Entails.refl _) (Entails.refl _) rfl (by bv_omega)

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
/-- Relocatable Stage 2 composition (`0x0390 → 0x0760` and early `Err` / OOM exits) on `initProgPlaced`. -/
theorem segA_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs2 : AtStage2Placed W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
        (stage3MemPlaced A x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
      (stage2MemPlaced A x stk s0) Q Qp (initOom s0) := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  have hfsp : s2.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hs2.ctrl.sp
  have hfiles0 : s0.fs.files = x.F := hs2.ctrl.files0.symm.trans hs2.files
  have hx23_s2 : s2.readReg64 (.gpr 23#5) = s2.sp + 128#64 := by
    rw [hfsp]; exact hs2.x23
  have hx25_s2 : s2.readReg64 (.gpr 25#5) = 0#64 - 1#64 := hs2.x25
  unfold stage2MemPlaced
  dsimp only
  rw [← hfsp,
      cliBundleAt_eq_body x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr,
      mr_split s2.sp (s2.sp + 120#64) 0x78 0x58 0xd0 rfl rfl,
      mr_split (s2.sp + 120#64) (s2.sp + 0x80#64) 8 0x50 0x58 rfl (by bv_omega),
      mr_split (s2.sp + 0x128#64) (s2.sp + 0x148#64) 32 0x470 0x490 rfl (by bv_omega),
      mr_split (s2.sp + 0x148#64) (s2.sp + 664#64) 0x150 0x320 0x470 rfl (by bv_omega),
      mr_split (s2.sp + 664#64) (s2.sp + 696#64) 32 0x300 0x320 rfl (by bv_omega),
      mr_split (s2.sp + 696#64) (s2.sp + 728#64) 32 0x2e0 0x300 rfl (by bv_omega),
      mr_split (s2.sp + 728#64) (s2.sp + 776#64) 48 0x2b0 0x2e0 rfl (by bv_omega),
      mr_split (s2.sp + 776#64) (s2.sp + 0x460#64) 344 0x158 0x2b0 rfl (by bv_omega),
      scratch5ba_split s2.sp,
      mr_split (s2.sp + 4064#64) (s2.sp + 4096#64) 32 32 64 rfl (by bv_omega),
      mr_split (s2.sp + 5632#64) (s2.sp + 5664#64) 32 40 72 rfl (by bv_omega)]
  have h296 : s2.sp + 0x128#64 = s2.sp + 296#64 := rfl
  rw [h296]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepWPp_exists_left; intro opkId
  apply sepWPp_pure_4th; intro hbPure
  refine' sepWPp_weaken_pre ?_
    (segA_step1_coins_placed (A := A) @hCoins hcoinsLt hstk hstk64 hs2.ctrl hs2.trace
      hs2.x22 hx23_s2 hx25_s2 hs2.x26 hs2.x27 hpanic
      fun s_a1 hctrl_a1 htr_a1 hx21_a1 hx23_a1 => ?_)
  · try simp only [sepConj_assoc]
    sep_frame
  have hsp_a1 : s_a1.sp = s2.sp := hctrl_a1.sp.trans hfsp.symm
  rw [← hsp_a1] at hx21_a1 hx23_a1 ⊢
  refine' sepWPp_weaken_pre ?_
    (segA_step2_ek_placed hh hLocal hctrl_a1 htr_a1 hx21_a1 hx23_a1 hpanic
      fun s_a2 ekASk ekAPk hctrl_a2 htr_a2 hekPair hx20_a2 hx21_a2 hx23_a2 => ?_)
  · try simp only [sepConj_assoc]
    sep_frame
  have hsp_a2 : s_a2.sp = s_a1.sp := hctrl_a2.sp.trans hctrl_a1.sp.symm
  rw [← hsp_a2] at hx20_a2 hx21_a2 hx23_a2 ⊢
  refine' sepWPp_weaken_pre ?_
    (segA_step3_poll_placed (opkId := opkId) hStore hinitOk hctrl_a2 htr_a2 hfiles0
      hx20_a2 hx21_a2 hx23_a2 hpanic
      fun s_a3 box ans hctrl_a3 htr_a3 _hbox_ne hans hx20_a3 hx21_a3 => ?_)
  · have hm5632 := mr_fold (s_a2.sp + 5632#64) (s_a2.sp + 5664#64) 32 40 72
      (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
    try simp only [sepConj_assoc] at hm5632 ⊢
    refine entails_by_focus (by sep_frame) hm5632 ?_
    sep_frame
  have hsp_a3 : s_a3.sp = s_a2.sp := hctrl_a3.sp.trans hctrl_a2.sp.symm
  rw [← hsp_a3] at hx20_a3 hx21_a3 ⊢
  cases ans with
  | error u =>
    cases u
    refine' sepWPp_weaken_pre ?_
      (segA_step4_err_placed (box := box) hh hStore hstk hstk64 hctrl_a3 htr_a3
        hx20_a3 hx21_a3 hpanic
        fun sf k w0 w1 w2 w3 w4 w5 R_spe hctrlf htrf hw0_ne3 hspe_move
          hx22f hx26f hx27f hx25f hx28f hx24f hx21f => ?_)
    · rw [show StoreDefs.idOwnFutBoxAt = idOwnFutBoxAt from rfl,
          show StoreDefs.idKeyPairOutAt = idKeyPairOutAt from rfl]
      try simp only [sepConj_assoc]
      sep_frame
    have hfsp_a3 : s_a3.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl_a3.sp
    have hekPkLen : ekAPk.length = 32 := by rw [hekPair.2]; exact List.Vector.toList_length _
    have hekSkLen : ekASk.length = 32 := by rw [hekPair.1]; exact List.Vector.toList_length _
    have hLocals := stage2_err_locals_placed_fold (s0.sp - BitVec.ofNat 64 cliInitiateFrame)
      x s0 ekAPk ekASk opkId hekPkLen hekSkLen
    have hBundle :=
      cliBundleBody_entails x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId hbPure
    rw [hfsp_a3]
    refine' sepWPp_weaken_pre ?_
      (segB_err_placed_ok hS hstk hstk64 hctrlf htrf hs2.x8 hans.symm
        hx22f hx26f hx27f hx25f hx28f hx24f hx21f hw0_ne3 hspe_move hLocals hpost)
    try simp only [sepConj_assoc] at hBundle ⊢
    refine entails_by_focus (by sep_frame) hBundle ?_
    sep_frame
  | ok kp =>
    refine' sepWPp_weaken_pre ?_
      (segA_step4_ok_placed (kp := kp) (box := box) hh hStore hstk hstk64 hctrl_a3 htr_a3
        hx20_a3 hx21_a3 hpanic
        fun sf b0 b1 b2 b3 b4 b5 b6 b63 u1 u2 u3 u4 u5 u6 u7 hctrlf htrf
          hx22f hx26f hx27f hx25f hx28f hx24f hx21f hkpLo hkpHi => ?_)
    · rw [show StoreDefs.idOwnFutBoxAt = idOwnFutBoxAt from rfl,
          show StoreDefs.idKeyPairOutAt = idKeyPairOutAt from rfl]
      try simp only [sepConj_assoc]
      sep_frame
    have hsp_sf : sf.sp = s_a3.sp := hctrlf.sp.trans hctrl_a3.sp.symm
    rw [← hsp_sf]
    refine' sepWPp_weaken_pre ?_
      (segC_placed_ok hh hLocal hinitOk hstk hstk64 hs2 hctrlf htrf hans.symm hekPair hbPure
        hx22f hx26f hx27f hx25f hx28f hx24f hx21f hkpLo hkpHi hpanic hnext)
    have hm4064 := mr_fold (sf.sp + 4064#64) (sf.sp + 4096#64) 32 32 64
      (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
    try simp only [sepConj_assoc] at hm4064 ⊢
    refine entails_by_focus (by sep_frame) hm4064 ?_
    sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
