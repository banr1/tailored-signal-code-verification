/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.Common.StringClonePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Stage 1 Direct `BL` Wrappers and Shared Error Epilogue

Provides `[LibsignalPlacement]` Stage 1 direct `BL` callee wrappers at residual stack
`stk - cliInitiateFrame` (`dealloc`, `String::clone`, `PublicKey::serialize`, `verify_signature`,
`kem::Key<Public>::serialize`, `memcpy`) and the shared error epilogue `stage1_epilogue_err_placed_ok`
(`0x0350 → ret`) on `initProgPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
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

/-! ## Direct `BL` callee wrappers at residual stack `stk - cliInitiateFrame` -/

theorem lift_stack_lscro [LibsignalPlacement] {α : Type} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {e : BitVec 64} {spec : Nat → Spec α} {sub full : Nat}
    (hsub : subroutine_ok (initProgPlaced mmpl gh W) e
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (spec sub)))
    (_hle : sub ≤ full) (_hhi : full ≤ 2 ^ 64)
    (hpreEq : ∀ x s, (spec full).pre x s =
      memRegion (s.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).pre x s)
    (hpostEq : ∀ x s0 sf, (spec full).post x s0 sf =
      memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub) ∗ (spec sub).post x s0 sf)
    (hpanEq : ∀ x s0 sf, (spec sub).onPanic x s0 sf ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hpanFull : ∀ x s0 sf,
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ⊢ (spec full).onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, (spec sub).onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, (spec sub).onOom x s0 sf = ⌜False⌝) :
    subroutine_ok (initProgPlaced mmpl gh W) e
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (spec full)) := by
  intro gx R s0 hpc hrun hpre hsp hcl
  obtain ⟨hinv, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  rw [hpreEq gx s0] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 full) (full - sub)
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (spec sub)).pre gx s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [stkRem]
    convert hpre using 1; ac_rfl
  rcases hsub gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    change sf.mem ⊨ (spec full).post gx s0 sf ∗ R
    change sf.mem ⊨ (spec sub).post gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hpostEq gx s0 sf]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    change sf.mem ⊨ (spec sub).onPanic gx s0 sf ∗ (stkRem ∗ R) at hq
    change sf.mem ⊨ (spec full).onPanic gx s0 sf ∗ R
    have h1 : (spec sub).onPanic gx s0 sf ∗ stkRem ⊢ (spec full).onPanic gx s0 sf := by
      refine Entails.trans (sepConj_mono_left (hpanEq gx s0 sf)) ?_
      rw [sepConj_assoc]
      exact Entails.trans (sepConj_mono_right (entails_anyHeap _)) (hpanFull gx s0 sf)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left h1) hq
  · change sf.mem ⊨ (spec sub).onExit gx c s0 sf ∗ (stkRem ∗ R) at hq
    rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · change sf.mem ⊨ (spec sub).onOom gx s0 sf ∗ (stkRem ∗ R) at hq
    rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem init_dealloc_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A (stk - cliInitiateFrame))) := by
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  intro gx R s0 hpc hrun hpre hsp hcl
  obtain ⟨hinv, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [rustDeallocExternSpecWithStack, withStack] at hpre
  rw [stackAt_sub_split_local s0.sp hle hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack, withStack, stkRem]
    convert hpre using 1; ac_rfl
  rcases hbase gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    change sf.mem ⊨ (rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).post gx s0 sf ∗ R
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      rustDeallocExternSpecWithStack, withStack] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_stringClone_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 623)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (stringCloneAtStkSpec A (stk - cliInitiateFrame))) := by
  have hShim : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      LibsignalBinary.Proofs.Common.StringClonePlaced.lsRustNoAllocShimPlacedSym sessionShimSpec := by
    simpa [noAllocShimSpec, sessionShimSpec] using hh.shim
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 623)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalPublicApi.stringCloneSpec A)) :=
    LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_placed_codeLoaded_ok
        (callerProg := initProgPlaced mmpl gh W) (i := 521)
        hShim hh.rawAlloc hh.sessionMemcpyRegion hh.panic_raw (by decide))
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hspecEq : LibsignalPublicApi.stringCloneSpec A = stringCloneAtStkSpec A extHookStack := rfl
  rw [hspecEq] at hbase
  exact lift_stack_lscro hbase hle hhi
    (fun (p, ret, g) s => by
      dsimp only [stringCloneAtStkSpec]
      rw [stackAt_sub_split_local s.sp hle hhi]
      ac_rfl)
    (fun (p, ret, g) s0 sf => by
      dsimp only [stringCloneAtStkSpec]
      rw [stackAt_sub_split_local s0.sp hle hhi]
      ac_rfl)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

theorem init_pubKeySerialize_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 205)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pubKeySerializeAtStkSpec A (stk - cliInitiateFrame))) := by
  have h205 : subroutine_ok (CryptoVerification.lsProg_205 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 205) (publicKeySerializeSpecX A) :=
    public_key_serialize_placed_ok_x hh.shim hh.rawAlloc hh.panic_raw
  have hbase : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 205)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain h205)
  have hle : publicKeySerializeStackX ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : publicKeySerializeStackX ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hspecEq : publicKeySerializeSpecX A = pubKeySerializeAtStkSpec A publicKeySerializeStackX :=
    rfl
  rw [hspecEq] at hbase
  exact lift_stack_lscro hbase hle hhi
    (fun gx s => by
      dsimp only [pubKeySerializeAtStkSpec]
      rw [stackAt_sub_split_local s.sp hle hhi]
      ac_rfl)
    (fun gx s0 sf => by
      dsimp only [pubKeySerializeAtStkSpec]
      rw [stackAt_sub_split_local s0.sp hle hhi]
      ac_rfl)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

theorem init_verifySig_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {stk : Nat}
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame))) := by
  have hbase := hLocal.verifySignature X
  have hle : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hp : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hspecEq : verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩) =
      verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
        (Pqxdh.Shared.pqxdhHookStack + 1280) := rfl
  rw [hspecEq] at hbase
  intro gx R s0 hpc hrun hpre hsp hcl
  obtain ⟨hinv, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [verifySigAtStkSpec] at hpre
  rw [stackAt_sub_split_local s0.sp hle hhi] at hpre
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - (Pqxdh.Shared.pqxdhHookStack + 1280))
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
          (Pqxdh.Shared.pqxdhHookStack + 1280))).pre gx s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    dsimp only [verifySigAtStkSpec, stkRem]
    convert hpre using 1; ac_rfl
  rcases hbase gx (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    change sf.mem ⊨
      (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame)).post gx s0 sf ∗ R
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, verifySigAtStkSpec] at hq ⊢
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem init_kemPubSerialize_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {stk : Nat} (hLocal : InitLocalCalleesPlaced A mmpl gh W stk) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (kemPubSerializeInnerSpec A (stk - cliInitiateFrame))) :=
  hLocal.kemPubSerialize

theorem initArgsAtPlaced_entails_memRegion [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  unfold initArgsAtPlaced
  have m64 : ∀ p v, (p ↦₆₄ v) ⊢ memRegion p 8 := pointsTo64_entails_memRegion
  have m32 : ∀ p v, (p ↦₃₂ v) ⊢ memRegion p 4 := pointsTo32_entails_memRegion
  refine Entails.trans (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m32 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _) (m64 _ _)))))))))))) ?_
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xd8#64) 8 8 16 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xe0#64) 16 8 24 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xe8#64) 24 8 32 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xf0#64) 32 8 40 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0xf8#64) 40 8 48 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x100#64) 48 8 56 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x108#64) 56 8 64 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x110#64) 64 4 68 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x114#64) 68 4 72 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0xd0#64) (fsp + 0x118#64) 72 8 80 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge (fsp + 0xd0#64) (fsp + 0x120#64) 80 8 88 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem stage2LocalsPlaced_entails_memRegion [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ⊢
      memRegion fsp initLocalsSize := by
  have h16 : ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ⊢
      memRegion (fsp + 0x5b8#64) 2 := by
    have hadd : (fsp + 0x5b8#64) + 1#64 = fsp + 0x5b9#64 := by bv_omega
    rw [← hadd, ← pointsTo16_zero_eq (fsp + 0x5b8#64)]
    exact pointsTo16_entails_memRegion _ _
  have h5ba :
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ (((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ⊢
      memRegion (fsp + 0x5b8#64) (initLocalsSize - 0x5b8) := by
    rw [← sepConj_assoc]
    refine Entails.trans (sepConj_mono_left h16) ?_
    rw [memRegion_merge (fsp + 0x5b8#64) (fsp + 0x5ba#64) 2 (initLocalsSize - 0x5ba)
      (initLocalsSize - 0x5b8) (by bv_omega) (by decide) (by decide)]
    exact Entails.refl _
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (initArgsAtPlaced_entails_memRegion fsp x s0)
        (sepConj_mono_right h5ba))) ?_
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xd0#64) 0xd0 0x58 0x128
    (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x128#64) 0x128 0x490 0x5b8
    (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge fsp (fsp + 0x5b8#64) 0x5b8 (initLocalsSize - 0x5b8) initLocalsSize
    (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

theorem init_memcpyScratch_placed_ok_at [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {n stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hn : n ≤ 2 ^ 64 := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (memcpyScratchSpec n (stk - cliInitiateFrame))) := by
  have hmc : subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack sessionMemcpyRegionSpec extHookStack)) :=
    transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hh.alloc.session_memcpy_region extHookStack (by decide) (by decide))
  have hle : extHookStack ≤ stk - cliInitiateFrame := by
    have h1 := stk_sub_ge_base hstk
    have hext : extHookStack ≤ 65536 := by decide
    omega
  have hhi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  intro ⟨dst, src⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hinv, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [memcpyScratchSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  rw [ProofLib.memRegion_eq_exists_bytes src n hn] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs, hmem⟩
  rw [show memRegion dst n ∗ ((⌜bs.length = n⌝ ∗ (src ↦ₛ bs)) ∗
        stackAt s0.sp (stk - cliInitiateFrame) ∗ R) =
      ⌜bs.length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (stk - cliInitiateFrame) ∗ R) by ac_rfl,
      satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨hlen, hmem⟩
  subst hlen
  rw [stackAt_sub_split_local s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    ((stk - cliInitiateFrame) - extHookStack)
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack sessionMemcpyRegionSpec extHookStack)).pre
        (dst, src, bs) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hinv ?_
    simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hmc (dst, src, bs) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    change sf.mem ⊨ (memcpyScratchSpec bs.length (stk - cliInitiateFrame)).post (dst, src) s0 sf ∗ R
    simp only [withStack, sessionMemcpyRegionSpec,
      memcpyScratchSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨_hx0f, htr⟩, hq⟩
    refine ⟨htr, ?_⟩
    have h1 := pointsToBytes_entails_memRegion dst bs
    have h2 := pointsToBytes_entails_memRegion src bs
    rw [stackAt_sub_split_local s0.sp hle hhi]
    dsimp only [stkRem] at hq
    refine Satisfies.mono ?_ hq
    refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))) ?_
    sep_frame
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## Shared error epilogue (`0x0350 → ret`) -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
theorem stage1_epilogue_err_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State}
    {H_err H_extra : SepProp} {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hres :
      (x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
        ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
        ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
        ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err ⊢
        initResAt A x.ret stage1Err) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
        memRegion x.ret 48 ∗
        initSaved s0 ∗
        memRegion fsp initLocalsSize ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        H_err ∗ H_extra)
      Q Qp (initOom s0) := by
  intro fsp
  have hpc : s.pc = (blkPl_521).base + 848#64 := hctrl.pc
  have hrun := hctrl.run
  have hsp := hctrl.sp
  have hal0 := hctrl.spAligned
  have hx19 : s.readReg64 (.gpr 19#5) = x.ret := hctrl.x19.trans hx8
  have hfs := hctrl.files0
  have hvregs := hctrl.vregs
  dsimp only [initProgPlaced, lsProg_521]
  rw [memRegion_48_words x.ret, initSaved_norm s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun w5 => sepWPp_exists_elim fun w4 =>
    sepWPp_exists_elim fun w3 => sepWPp_exists_elim fun w2 =>
    sepWPp_exists_elim fun w1 => sepWPp_exists_elim fun w0 => ?_
  apply sepWPp_ret_of_sepWP
  wp_steps
  apply SepWP.done
  · simp only [wp_norm, arm64_norm]
  · simp only [wp_norm, arm64_norm, hrun]
  apply hpost
  refine ⟨?_, ?_, ?_⟩
  · simp only [wp_norm, arm64_norm]
  · unfold CalleeSavedPreserved
    simp [wp_norm, arm64_norm, hvregs]
  · have hstkMerge :
        initSaved s0 ∗ memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame) ⊢
          stackAt s0.sp stk := by
      rw [stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
      refine Entails.trans
        (sepConj_mono_left (initSaved_entails_memRegion s0)) ?_
      sep_frame
    dsimp only [initSlotSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    refine Entails.sepExists_right StoresGhost.opened ?_
    refine Entails.sepExists_right stage1Err ?_
    refine pure_sepConj_intro ⟨⟨?_, ?_, ?_⟩, ?_⟩ ?_
    · simp only [wp_norm, arm64_norm, htr]; exact List.prefix_refl _
    · simp only [wp_norm, arm64_norm, hfs]
    · simp only [wp_norm, arm64_norm, htr]
    · simp [slotOut, hans, stage1Err]
    simp only [← initSaved_norm s0]
    have hre :
        storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗
          protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
            ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
            ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
            ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
            ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
            ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5))) ∗
          initSaved s0 ∗
          memRegion fsp initLocalsSize ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ H_err ∗ H_extra =
        ((x.ret ↦₆₄ s.readReg64 (.gpr 26#5)) ∗
          ((x.ret + 8#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
          ((x.ret + 16#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
          ((x.ret + 24#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗
          ((x.ret + 32#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗
          ((x.ret + 40#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ H_err) ∗
        (initSaved s0 ∗ memRegion fsp initLocalsSize ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
        H_extra ∗
        (storesAt A x.stores StoresGhost.opened ∗
          protocolAddressAt A x.peer x.peerA ∗
          protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool) := by ac_rfl
    rw [hre]
    refine Entails.trans (sepConj_mono hres
      (sepConj_mono hstkMerge (sepConj_mono_left (entails_anyHeap H_extra)))) ?_
    sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
