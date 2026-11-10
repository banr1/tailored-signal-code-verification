/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExitPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 3 PQXDH Helpers (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` frame-pointer slot identities, `S3InvPrefixPlaced`,
`s3_calc_agree_placed`, and shared zero-DH unwind collapses (`s3_dh_collapse_common_placed`,
`s3_dh_unwind_1544_placed`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## Frame-Pointer Slot Identities -/

theorem fp_eq_fsp_add_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (hctrl : InInitiatePlaced s0 s k) :
    s.readReg64 (.gpr 29#5) = s.sp + 0x1c90#64 := by
  change s.readReg64 .fp = _
  have hsp := hctrl.sp
  rw [hctrl.fp, hsp, cliInitiateFrame_eq]; bv_omega

theorem fp_slot_30_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7264#64 = s.readReg64 (.gpr 29#5) - 48#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_28_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7272#64 = s.readReg64 (.gpr 29#5) - 40#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_20_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7280#64 = s.readReg64 (.gpr 29#5) - 32#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_50_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7232#64 = s.readReg64 (.gpr 29#5) - 80#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_48_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7240#64 = s.readReg64 (.gpr 29#5) - 72#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_40_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7248#64 = s.readReg64 (.gpr 29#5) - 64#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega
theorem fp_slot_38_placed [LibsignalPlacement] {s0 s : State} {k : Nat}
    (h : InInitiatePlaced s0 s k) :
    s.sp + 7256#64 = s.readReg64 (.gpr 29#5) - 56#64 := by
  change s.sp + _ = s.readReg64 .fp - _; rw [h.fp, h.sp, cliInitiateFrame_eq]; bv_omega

/-! ## Invariant Bundle, `calculate_agreement`, and Unwind Helpers -/

def S3InvPrefixPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ initSaved s0 ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba)
/-- Call `InitLocalCalleesPlaced.calculateAgreement` under the uniform `stackAt s.sp extHookStack`. -/
theorem s3_calc_agree_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {S : RunSem} {x : InitGhost} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (ourA : BitVec 64) (ourSk : SignalPqxdh.Bytes) (theirA : BitVec 64) (theirPk : SignalPqxdh.Bytes)
    (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 207)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = ourA) (hx1 : s.readReg64 .x1 = theirA)
    (hx8 : s.readReg64 .x8 = s.sp + 0x1600#64)
    (hourLen : ourSk.length = 32) (htheirLen : theirPk.length = 32)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢ (ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
      memRegion (s.sp + 0x1600#64) 24 ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
    (herr : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk = List.replicate 32 0 →
      ∀ (sm : State) (hi : BitVec 56) (u2 : BitVec 64),
        InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ (hi ++ 3#8)) ∗
            ((s.sp + 0x1610#64) ↦₆₄ u2) ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
          Q Qp (initOom s0))
    (hok : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk ≠ List.replicate 32 0 →
      ∀ (sm : State) (dhPtr : BitVec 64),
        InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
        SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
          ((ourA ↦ₛ bytesToBv8 ourSk) ∗ (theirA ↦ₛ bytesToBv8 theirPk) ∗
            ((s.sp + 0x1600#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x1608#64) ↦₆₄ dhPtr) ∗
            ((s.sp + 0x1610#64) ↦₆₄ 32#64) ∗
            (dhPtr ↦ₛ bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)) ∗
            A.live dhPtr 32 1 ∗ A.pool ∗ stackAt s.sp extHookStack ∗ F)
          Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hstk_split := stackAt_sub_split_init s.sp
    (by decide : ResponderCore.calculateAgreementStack ≤ extHookStack) (by decide)
  have hpre' : P ⊢
      (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A).pre
        (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp) s ∗
        (memRegion (s.sp - BitVec.ofNat 64 extHookStack)
          (extHookStack - ResponderCore.calculateAgreementStack) ∗ F) := by
    refine Entails.trans hpre ?_
    rw [hstk_split]
    simp only [pqxdhCalculateAgreementPlacedInnerSpec, sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, hx8, trivial, hourLen, htheirLen⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  refine s3_call_placed hh (hLocal.calculateAgreement X)
    (ourA, ourSk, theirA, theirPk, s.sp + 0x1600#64, s.sp)
    (memRegion (s.sp - BitVec.ofNat 64 extHookStack)
      (extHookStack - ResponderCore.calculateAgreementStack) ∗ F)
    hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro sm _ hpan
    dsimp only [pqxdhCalculateAgreementPlacedInnerSpec, rustPanicOnOomPlaced] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1.1
  · intro _ _ _ hex
    simp [pqxdhCalculateAgreementPlacedInnerSpec] at hex
  · intro _ _ hoom
    simp [pqxdhCalculateAgreementPlacedInnerSpec] at hoom
  · intro sm _ _ _ hcsm _ hof
    dsimp only [pqxdhCalculateAgreementPlacedInnerSpec,
      pqxdhCalculateAgreementResultAt, ofSignalPqxdhPrimitives]
    rw [sepConj_assoc]
    refine sepWPp_pure_elim_oom fun htrm => ?_
    have hctrl' := hof htrm
    by_cases hdh : (modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk = List.replicate 32 0
    · simp only [hdh, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun hi => ?_
      refine sepWPp_conseq_oom ?_ (herr hdh sm hi u2 hctrl' hcsm htrm)
      rw [hstk_split]; exact Entails.of_eq (by ac_rfl)
    · simp only [hdh, ↓reduceIte]
      have hlen : (bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)).length = 32 := by
        rw [bytesToBv8_length]; exact modelPrims_x25519_len X ⟨W.C, W.Q⟩ ourSk theirPk
      have hbox := boxSliceU8_32_entails A (s.sp + 0x1600#64 + 8#64)
        (bytesToBv8 ((modelPrims X ⟨W.C, W.Q⟩).x25519 ourSk theirPk)) hlen
      refine sepWPp_conseq_oom
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (sepConj_mono_right hbox))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine sepWPp_exists_elim_oom fun dhPtr => ?_
      refine sepWPp_conseq_oom ?_ (hok hdh sm dhPtr hctrl' hcsm htrm)
      rw [hstk_split]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq (by ac_rfl)
/-- Shared collapse from active DH Stage-3 state into `unwind_1544_placed_ok` / `unwind_1548_placed_ok`. -/
theorem s3_dh_collapse_common_placed [LibsignalPlacement] {A : RustAlloc} {B : RunBudgets}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (s0 : State) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗ A.pool ∗
      A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗ memRegion fsp 0x80 ∗
      stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
      memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
      memRegion (fsp + 0x958#64) 0x1310 ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      memRegion (fsp + 0x1c70#64) 0x20 ∗ stackAt fsp extHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ⊢
      ((s0.sp - 0x60#64 - 0x28#64) ↦₆₄ secretsPtr) ∗ storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
        A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
        A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
        memRegion fsp 0x128 ∗ initFreshRecAt fsp ∗ memRegion (fsp + 0x148#64) 0x2e0 ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        memRegion (fsp + 0x438#64) 0x181 ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 0x37e ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x1310 ∗ memRegion (fsp + 0x1c70#64) 0x20 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt := by
  dsimp only [S3InvPrefixPlaced]
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hsub_ext : extHookStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_re := (stackAt_sub_split_init fsp hsub_ext (stk_sub_le_2pow64 hstk64)).symm
  have hslot : s0.sp - 0x60#64 - 0x28#64 = fsp + 0x1c68#64 := by
    dsimp only [fsp]; rw [cliInitiateFrame_eq]; bv_omega
  have hkeys := stage3KeySlotsAt_collapse A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId
    hekAPkLen hekASkLen hkpkLen
  have hargs := initArgsAtPlaced_collapse fsp x s0
  have hb58 := pointsTo8_entails_memRegion1 (fsp + 0x5b8#64) 0#8
  refine Entails.trans (Entails.of_eq (P := _) (Q :=
      initArgsAtPlaced fsp x s0 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗
        (memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗ stackAt fsp extHookStack) ∗
        (memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
          memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
          memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 ∗
          ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
          A.live secretsPtr 192 1 ∗ memRegion secretsPtr 192 ∗
          initFreshRecAt fsp ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
          memRegion (fsp + 0x938#64) 0x20 ∗ memRegion (fsp + 0x958#64) 0x1310 ∗
          memRegion (fsp + 0x1c70#64) 0x20 ∗
          coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt))
    (by dsimp only [fsp]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hargs (sepConj_mono hkeys
    (sepConj_mono hb58 (sepConj_mono (Entails.of_eq hstk_re) (Entails.refl _))))) ?_
  have hm128 : memRegion fsp 0x80 ∗ memRegion (fsp + 0x80#64) 0x50 ∗
      memRegion (fsp + 0xd0#64) 0x58 = memRegion fsp 0x128 := by
    rw [memRegion_merge_at (fsp + 0x80#64) 0x50 0x58 (fsp + 0xd0#64) (by bv_omega) (by decide),
        memRegion_merge_at fsp 0x80 0xa8 (fsp + 0x80#64) (by bv_omega) (by decide)]
  have hm2e0 : memRegion (fsp + 0x148#64) 0x150 ∗ memRegion (fsp + 0x298#64) 0x190 =
      memRegion (fsp + 0x148#64) 0x2e0 :=
    memRegion_merge_at (fsp + 0x148#64) 0x150 0x190 (fsp + 0x298#64) (by bv_omega) (by decide)
  have hm181 : memRegion (fsp + 0x438#64) 0x28 ∗ memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 = memRegion (fsp + 0x438#64) 0x181 := by
    rw [memRegion_merge_at (fsp + 0x460#64) 0x158 1 (fsp + 0x5b8#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x438#64) 0x28 0x159 (fsp + 0x460#64) (by bv_omega) (by decide)]
  have hm37e : memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗ memRegion (fsp + 0x930#64) 8 =
      memRegion (fsp + 0x5ba#64) 0x37e :=
    memRegion_merge_at (fsp + 0x5ba#64) (0x930 - 0x5ba) 8 (fsp + 0x930#64) (by bv_omega) (by decide)
  refine Entails.of_eq ?_
  dsimp only [fsp] at hm128 hm2e0 hm181 hm37e hslot ⊢
  rw [hslot, ← hm128, ← hm2e0, ← hm181, ← hm37e]
  ac_rfl
/-- One-shot zero-DH unwind discharge at `+0x1544` for `DH2`, `DH3`, and `DH4`. -/
theorem s3_dh_unwind_1544_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32} {stk : Nat}
    {s0 s : State} {P_in P_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hnone : initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hekAPkLen : ekAPk.length = 32) (hekASkLen : ekASk.length = 32)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hsecNonNull : secretsPtr ≠ 0#64) (hpqNonNull : pqspkPtr ≠ 0#64)
    (hctrl : InInitiatePlaced s0 s 0x1544) (htr : s.trace = s0.trace)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 10) (hx1 : s.readReg64 .x1 = 192#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (w1 w2 lenWord : BitVec 64)
    (hextra : P_extra ⊢
      memRegion secretsPtr 192 ∗ stage3KeySlotsAt A (s0.sp - BitVec.ofNat 64 cliInitiateFrame)
        x.bundle kp ekASk ekAPk pqspkPtr opkId)
    (hsplit : P_in ⊢
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P_extra ∗ S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 32 ∗
        A.pool ∗ stackAt fsp extHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - extHookStack) ∗
        A.live secretsPtr 192 1 ∗
        memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗
        ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗
        ((fsp + 0x1600#64) ↦₆₄ 1#64) ∗ ((fsp + 0x1608#64) ↦₆₄ w1) ∗ ((fsp + 0x1610#64) ↦₆₄ w2) ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P_in Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_conseq_oom (Entails.trans hsplit ?_)
    (unwind_1544_placed_ok hh hS hnone hstk hstk64 hx8 hsecNonNull hpqNonNull hctrl htr
      hx26 hx1 hpost hpanic)
  have hbase := s3_dh_collapse_common_placed (A := A) (x := x) (kp := kp)
    (ekASk := ekASk) (ekAPk := ekAPk) (pqspkPtr := pqspkPtr) (secretsPtr := secretsPtr)
    (opkId := opkId) hstk hstk64 hekAPkLen hekASkLen hkpkLen s0
  have hek_m : ((fsp + 0x9a0#64) ↦ₛ ekASk) ⊢ memRegion (fsp + 0x9a0#64) 0x20 :=
    pointsToBytes_entails_memRegion_len hekASkLen
  have hsret := cells3_to_memRegion24 (fsp + 0x1600#64) 1#64 w1 w2
  have hm78 : memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ⊢ memRegion fsp 0x80 := by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at fsp 0x78 8 (fsp + 0x78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hc20 : ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
      memRegion (fsp + 0x1c70#64) 0x20 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion _ _)) ?_
    rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  have hloc_re :
      memRegion (fsp + 0x958#64) 0x48 ∗ memRegion (fsp + 0x9a0#64) 0x20 ∗
        memRegion (fsp + 0x9c0#64) 0xc40 ∗ memRegion (fsp + 0x1600#64) 24 ∗
        memRegion (fsp + 0x1618#64) 0x648 ∗ ((fsp + 0x1c60#64) ↦₆₄ 192#64) ⊢
      memRegion (fsp + 0x958#64) 0x1310 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))))) ?_
    rw [memRegion_merge_at (fsp + 0x1618#64) 0x648 8 (fsp + 0x1c60#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1600#64) 24 0x650 (fsp + 0x1618#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9c0#64) 0xc40 0x668 (fsp + 0x1600#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x9a0#64) 0x20 0x12a8 (fsp + 0x9c0#64) (by bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x958#64) 0x48 0x12c8 (fsp + 0x9a0#64) (by bv_omega) (by decide)]
    exact Entails.refl _
  refine sep_replace (sepConj_mono hextra (sepConj_mono hek_m
      (sepConj_mono hsret (sepConj_mono hm78 hc20))))
    (by dsimp only [fsp]; sep_frame) ?_
  refine sep_replace hloc_re (by dsimp only [fsp]; sep_frame) ?_
  refine Entails.trans ?_ hbase
  dsimp only [fsp]; sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
