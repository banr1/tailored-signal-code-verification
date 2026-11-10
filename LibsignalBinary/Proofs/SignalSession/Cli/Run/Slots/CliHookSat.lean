/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
public import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiatePostCommon
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Proofs.SpqrV1.Auth.New
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.TripleRatchet.Hooks

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
/-!
# `cliHookTable` Hook Satisfaction Contracts

Establishes `HookSat` on `cliExterns W` for allocator, triple-ratchet, public API, `bcmp`, SPQR,
`PqxdhHookContracts` (including Kyber-1024 KEM hooks), and `duration_since` contracts.

## 1. `cliHookTable` row lookup and panic helpers
-/
theorem allocZeroed_row (W : CliHooks) : (allocZeroedName, E2E.allocZeroedHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 4) rfl)
theorem fmtWrite_row (W : CliHooks) : (fmtWriteName, E2E.fmtWriteHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 16) rfl)
theorem formatInner_row (W : CliHooks) : (formatInnerName, E2E.formatInnerHook0) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 17) rfl)
theorem durationSince_row (W : CliHooks) :
    (E2E.durationSinceName, durationSinceExactHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 18) rfl)
theorem timeAdd_row (W : CliHooks) : (E2E.timeAddName, E2E.timeAddHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 19) rfl)
theorem compress256_row (W : CliHooks) :
    ("sha2::sha256::compress256", LibsignalHmac.compress256Hook W.C.F) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 21) rfl)
theorem aesEnc_row (W : CliHooks) : (aesEncName, E2E.aesEncHook0 W.C.E) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 22) rfl)
theorem aesDec_row (W : CliHooks) : (aesDecName, E2E.aesDecHook0 W.C.D) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 23) rfl)
theorem compress512_row (W : CliHooks) :
    (E2E.compress512Name, E2E.compress512Hook W.Q.F512) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)
theorem toEdwards_row (W : CliHooks) :
    (E2E.toEdwardsName, E2E.toEdwardsHook W.Q.montToEd) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl)
theorem compress_row (W : CliHooks) :
    (E2E.compressName, E2E.compressHook W.Q.compress) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl)
theorem edNeg_row (W : CliHooks) : (E2E.edNegName, E2E.edNegHook W.Q.edNeg) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 3) rfl)
theorem torsionFree_row (W : CliHooks) :
    (E2E.torsionFreeName, E2E.torsionFreeHook W.Q.isTorsionFree) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 4) rfl)
theorem dsmb_row (W : CliHooks) : (E2E.dsmbName, E2E.dsmbHook W.Q.dsmb) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 5) rfl)
theorem scalarMod_row (W : CliHooks) :
    (E2E.scalarModName, E2E.scalarModHook W.Q.scalarMod) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 6) rfl)
theorem scalarWide_row (W : CliHooks) :
    (E2E.scalarWideName, E2E.scalarWideHook W.Q.scalarWide) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 7) rfl)
theorem kemEncaps_row (W : CliHooks) :
    (E2E.kemEncapsName, E2E.kemEncapsHook W.Q.encaps) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 8) rfl)
theorem kemDecaps_row (W : CliHooks) :
    (E2E.kemDecapsName, E2E.kemDecapsHook W.Q.decaps) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 9) rfl)
theorem mlkemFromSeed_row (W : CliHooks) :
    (mlkemFromSeedName, E2E.mlkemFromSeedHook W.Q.K) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 10) rfl)
theorem mlkemPk1_row (W : CliHooks) : (mlkemPk1Name, E2E.mlkemPk1Hook) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl)
theorem mlkemPk2_row (W : CliHooks) : (mlkemPk2Name, E2E.mlkemPk2Hook) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl)
theorem mlkemEncaps1_row (W : CliHooks) :
    (mlkemEncaps1Name, E2E.mlkemEncaps1Hook W.Q.K) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 13) rfl)
theorem mlkemEncaps2_row (W : CliHooks) :
    (mlkemEncaps2Name, E2E.mlkemEncaps2Hook W.Q.K) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 14) rfl)
theorem mlkemDecaps_row (W : CliHooks) :
    (mlkemDecapsName, E2E.mlkemDecapsHook W.Q.K) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 15) rfl)
theorem mlkemValidatePk_row (W : CliHooks) :
    (mlkemValidatePkName, E2E.mlkemValidatePkHook W.Q.K) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 16) rfl)
theorem libcruxHmac_row (W : CliHooks) :
    (libcruxHmacName, E2E.libcruxHmacHook W.C.F) ∈ cliHookTable W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 17) rfl)
/-! ## 2. Allocator, triple-ratchet, public API, `bcmp`, and SPQR contracts -/
theorem cliExterns_allocHooks_of_hooks (W : CliHooks) {A : RustAlloc} (hA : CliAllocHooks A) :
    AllocHooks A (cliExterns W) where
  alloc := ⟨E2E.allocHook0, cliExterns_row W (alloc_row W), hA.alloc⟩
  dealloc := ⟨E2E.deallocHook, cliExterns_row W (dealloc_row W), hA.dealloc⟩
  realloc := ⟨E2E.reallocHook0, cliExterns_row W (realloc_row W), hA.realloc⟩
theorem cliExterns_allocHooks (W : CliHooks) : AllocHooks E2E.HooksE.A0 (cliExterns W) :=
  cliExterns_allocHooks_of_hooks W cliAllocHooks_A0
theorem cliExterns_allocZeroed (W : CliHooks) :
    HookSat (cliExterns W) allocZeroedName (rustAllocZeroedSpec E2E.HooksE.A0) :=
  ⟨E2E.allocZeroedHook0, cliExterns_row W (allocZeroed_row W), E2E.HooksE.allocZeroedHook0_ok⟩
theorem cliExterns_allocNW (W : CliHooks) :
    HookSat (cliExterns W) E2E.rustAllocName (E2E.HooksE.rustAllocNWSpec E2E.HooksE.A0) :=
  ⟨E2E.allocHook0, cliExterns_row W (alloc_row W), E2E.HooksE.allocHook0_nw_ok⟩
theorem cliExterns_aesEnc (W : CliHooks) :
    HookSat (cliExterns W) aesEncName (aesEncSpec W.C.E E2E.HooksE.A0) :=
  ⟨E2E.aesEncHook0 W.C.E, cliExterns_row W (aesEnc_row W), E2E.HooksE.aesEncHook0_ok W.C.E⟩
theorem cliExterns_aesDec (W : CliHooks) :
    HookSat (cliExterns W) aesDecName (aesDecSpec W.C.D E2E.HooksE.A0) :=
  ⟨E2E.aesDecHook0 W.C.D, cliExterns_row W (aesDec_row W), E2E.HooksE.aesDecHook0_ok W.C.D⟩
theorem cliExterns_formatInner (W : CliHooks) :
    HookSat (cliExterns W) formatInnerName (formatInnerSpec E2E.HooksE.A0) :=
  ⟨E2E.formatInnerHook0, cliExterns_row W (formatInner_row W), E2E.HooksE.formatInnerHook0_ok⟩
theorem cliExterns_fmtWrite (W : CliHooks) :
    HookSat (cliExterns W) fmtWriteName (fmtWriteSpec E2E.HooksE.A0) :=
  ⟨E2E.fmtWriteHook0, cliExterns_row W (fmtWrite_row W), E2E.HooksE.fmtWriteHook0_ok⟩
theorem cliExterns_tripleRatchetHooks (W : CliHooks) (Sm : SpqrModel) :
    TripleRatchetHooks W.C E2E.HooksE.A0 Sm (cliExterns W) :=
  ⟨cliExterns_allocHooks W, cliExterns_allocZeroed W, cliExterns_aesEnc W, cliExterns_aesDec W,
    cliExterns_formatInner W, cliExterns_fmtWrite W⟩
structure CliTripleRatchetHooks (W : CliHooks) (A : RustAlloc) : Prop extends CliAllocHooks A where
  allocZeroed : HookOk E2E.allocZeroedHook0 (rustAllocZeroedSpec A)
  aesEnc : HookOk (E2E.aesEncHook0 W.C.E) (aesEncSpec W.C.E A)
  aesDec : HookOk (E2E.aesDecHook0 W.C.D) (aesDecSpec W.C.D A)
  formatInner : HookOk E2E.formatInnerHook0 (formatInnerSpec A)
  fmtWrite : HookOk E2E.fmtWriteHook0 (fmtWriteSpec A)
theorem cliExterns_tripleRatchetHooks_of_hooks (W : CliHooks) (Sm : SpqrModel) {A : RustAlloc}
    (hA : CliTripleRatchetHooks W A) :
    TripleRatchetHooks W.C A Sm (cliExterns W) :=
  ⟨cliExterns_allocHooks_of_hooks W hA.toCliAllocHooks,
    ⟨E2E.allocZeroedHook0, cliExterns_row W (allocZeroed_row W), hA.allocZeroed⟩,
    ⟨E2E.aesEncHook0 W.C.E, cliExterns_row W (aesEnc_row W), hA.aesEnc⟩,
    ⟨E2E.aesDecHook0 W.C.D, cliExterns_row W (aesDec_row W), hA.aesDec⟩,
    ⟨E2E.formatInnerHook0, cliExterns_row W (formatInner_row W), hA.formatInner⟩,
    ⟨E2E.fmtWriteHook0, cliExterns_row W (fmtWrite_row W), hA.fmtWrite⟩⟩
theorem cliExterns_timeAdd (W : CliHooks) :
    HookSat (cliExterns W) E2E.timeAddName timeAddSpec :=
  ⟨E2E.timeAddHook, cliExterns_row W (timeAdd_row W), E2E.HooksE.timeAddHook_ok⟩
theorem cliExterns_bcmp (W : CliHooks) : HookSat (cliExterns W) cliBcmpName cliBcmpSpec :=
  RunGlue.cli_hookSat_bcmp W
theorem cliBcmpHook_vregs_ok (W : CliHooks) :
    HookOk (cliBcmpHook W.bcmp) E2E.HooksE.bcmpVregsSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [E2E.HooksE.bcmpVregsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hreadA : s0.mem.readBytes x.a x.bsA.length = x.bsA :=
    ((IsBlock.pointsToBytes x.a x.bsA).read hmem).2
  have hmemB : s0.mem ⊨ (x.b ↦ₛ x.bsB) ∗ ((x.a ↦ₛ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    ac_nf at hmem ⊢
  have hreadB : s0.mem.readBytes x.b x.bsA.length = x.bsB := by
    rw [← hlen]; exact ((IsBlock.pointsToBytes x.b x.bsB).read hmemB).2
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [E2E.HooksE.bcmpVregsSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  try rw [CryptoVerification.LibsignalSession.NonVacuityWitness.readReg64_setPC_writeReg64_x0]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨W.bcmp_ok x.bsA x.bsB hlen.symm, rfl, rfl⟩, hmem⟩
theorem cliExterns_bcmpVregs (W : CliHooks) :
    HookSat (cliExterns W) E2E.bcmpName E2E.HooksE.bcmpVregsSpec :=
  ⟨cliBcmpHook W.bcmp, cliExterns_row W (RunGlue.bcmp_row W), cliBcmpHook_vregs_ok W⟩
theorem cliExterns_e2eBcmp (W : CliHooks) :
    HookSat (cliExterns W) E2E.bcmpName E2E.HooksE.e2eBcmpSpec :=
  ⟨cliBcmpHook W.bcmp, cliExterns_row W (RunGlue.bcmp_row W),
    E2E.HooksE.hookOk_bcmpSpec_of_vregs (cliBcmpHook_vregs_ok W)⟩
theorem cliExterns_memcpyRegionRO (W : CliHooks) :
    HookSat (cliExterns W) memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  cli_hookSat_memcpy_region_ro W
theorem cliExterns_spqrHooks (W : CliHooks) :
    SpqrHooks W.C E2E.HooksE.A0 W.Q.K (cliExterns W) :=
  ⟨⟨_, cliExterns_row W (mlkemFromSeed_row W), E2E.Pqxdh.mlkemFromSeedHook_ok W.Q.K⟩,
   ⟨_, cliExterns_row W (mlkemPk1_row W), E2E.Pqxdh.mlkemPk1Hook_ok⟩,
   ⟨_, cliExterns_row W (mlkemPk2_row W), E2E.Pqxdh.mlkemPk2Hook_ok⟩,
   ⟨_, cliExterns_row W (mlkemEncaps1_row W), E2E.Pqxdh.mlkemEncaps1Hook_ok W.Q.K⟩,
   ⟨_, cliExterns_row W (mlkemEncaps2_row W), E2E.Pqxdh.mlkemEncaps2Hook_ok W.Q.K⟩,
   ⟨_, cliExterns_row W (mlkemDecaps_row W), E2E.Pqxdh.mlkemDecapsHook_ok W.Q.K⟩,
   ⟨_, cliExterns_row W (mlkemValidatePk_row W), E2E.Pqxdh.mlkemValidatePkHook_ok W.Q.K⟩,
   ⟨_, cliExterns_row W (libcruxHmac_row W), E2E.Pqxdh.libcruxHmacHook_ok W.C.F⟩⟩

theorem allocContracts_cli_of_hooks (W : CliHooks) (img : Obj.Image) {A : RustAlloc}
    (hA : CliAllocHooks A) : AllocContracts img.base A (cliExterns W) where
  alloc := alloc_stub_ok W img hA.alloc
  dealloc := dealloc_stub_ok W img hA.dealloc
  realloc := realloc_stub_ok W img hA.realloc
  shim := shim_stub_ok W img sessionShim_hookOk
  memcpy stk := memcpy_stub_ok W img (hookMemcpy_ok stk)
  session_memcpy stk := memcpy_stub_ok W img (hookMemcpy_trace_ok stk)
  memcpy_region := memcpy_stub_ok W img hookMemcpy_region_ok
  session_memcpy_region := memcpy_stub_ok W img hookMemcpy_region_trace_ok
  memmove stk := memmove_stub_ok W img (hookMemmove_ok stk)
  session_memmove stk := memmove_stub_ok W img (hookMemmove_trace_ok stk)
  memset stk hpos := memset_stub_ok W img (hookMemset_ok stk hpos)
  session_memset stk hpos := memset_stub_ok W img (hookMemset_trace_ok stk hpos)
  memset_region := memset_stub_ok W img hookMemset_region_ok
  session_memset_region := memset_stub_ok W img hookMemset_region_trace_ok

theorem allocContracts_cli (W : CliHooks) (img : Obj.Image) :
    AllocContracts img.base E2E.HooksE.A0 (cliExterns W) :=
  allocContracts_cli_of_hooks W img cliAllocHooks_A0
private theorem hookMemset_eq_memsetHook : hookMemset = LibsignalAesCbc.memsetHook :=
  funext fun s =>
    congrArg
      (fun c => (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
        (List.replicate (s.readReg64 .x2).toNat c))).setPC (s.readReg64 .lr))
      (BitVec.setWidth_setWidth_of_le (s.readReg64 .x1) (by decide : 8 ≤ 32))
instance cliExterns_hkdfHooks (W : CliHooks) : HkdfHooks W.C.F (cliExterns W) where
  compress256 := (congrFun (withPanics_cliExterns W) _).trans (cliExterns_row W (compress256_row W))
  memcpy := (congrFun (withPanics_cliExterns W) _).trans (cliExterns_row W (memcpy_row W))
  memset := (congrFun (withPanics_cliExterns W) _).trans
    ((cliExterns_row W (memset_row W)).trans (congrArg some hookMemset_eq_memsetHook))

theorem cliExterns_sessionExterns_le (W : CliHooks) :
    ∀ n f, Rust.withPanics (sessionExterns W.C.F (cliExterns W)) n = some f →
      Rust.withPanics (cliExterns W) n = some f := by
  intro n f h
  rw [withPanics_cliExterns]
  by_cases hp : Rust.isPanicSymbol n = true
  · simp [Rust.withPanics, hp] at h
    simp [cliExterns, hp] at h ⊢
    exact h
  · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hk : n ∈ ["sha2::sha256::compress256", "memcpy", "memmove", "memset",
        "__rustc::__rust_no_alloc_shim_is_unstable_v2", "subtle::black_box::<u8>",
        "<alloc::vec::Vec<_, _>>::remove::assert_failed"]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sessionExterns] at h <;>
      first
        | (unfold cliExterns withCliPanics
           simp [isCliPanicSymbol, E2E.isImagePanicSymbol, E2E.extraImagePanicNames,
             deadCliHashbrownPanicNames]
           exact h)
        | (refine (cliExterns_row W ?_).trans (congrArg some h)
           simp [cliHookTable])
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      rcases hk with ⟨h1, h2, h3, h4, h5, h6, h7⟩
      simp only [sessionExterns, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte] at h
      split at h
      · exact h
      · cases h

theorem hkdfToSliceSpqr_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    SpqrV1.Kdf.HkdfToSliceSpqrOkX img (spqrHkdfWith W.C.F) (cliExterns W) :=
  SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext img W.C himg
    (cliExterns_sessionExterns_le W)

theorem authNewOkX_cli_of_hooks {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A (cliExterns W))
    (hZero : HookSat (cliExterns W) allocZeroedName (rustAllocZeroedSpec A)) :
    SpqrV1.Auth.AuthNewOkX img W.C.F A (cliExterns W) := by
  have hhkdf := hkdfToSliceSpqr_cli W himg
  have hRO := cliExterns_memcpyRegionRO W
  have hAX := AllocContractsX.of_AllocContracts hA
  exact SpqrV1.Auth.authNew_ok_of_hook_x himg
    (SpqrV1.Auth.authUpdate_ok_of_hook_x himg (SpqrV1.Alloc.slice_concat_2_ok_x hA hRO)
      hhkdf hAX hZero)
    hAX hZero

theorem authNewOkX_cli {img : Obj.Image} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img) :
    SpqrV1.Auth.AuthNewOkX img W.C.F E2E.HooksE.A0 (cliExterns W) :=
  authNewOkX_cli_of_hooks W himg (allocContracts_cli W img) (cliExterns_allocZeroed W)

/-! ## 3. `PqxdhHookContracts` and Kyber KEM hooks -/

section PqxdhContracts
open E2E E2E.Pqxdh

private theorem ofU8_length (bs : List UInt8) : (ofU8 bs).length = bs.length := by simp [ofU8]
private theorem toU8_length (bs : List (BitVec 8)) : (toU8 bs).length = bs.length := by simp [toU8]
private theorem ofU8_toU8 : ∀ bs : List (BitVec 8), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8 rest)
private theorem toU8_ofU8 : ∀ bs : List UInt8, toU8 (ofU8 bs) = bs
  | [] => rfl
  | ⟨_⟩ :: rest => congrArg₂ List.cons rfl (toU8_ofU8 rest)
private theorem shared_bytesToBv8_eq_ofU8 : ∀ bs : List UInt8, Shared.bytesToBv8 bs = ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (shared_bytesToBv8_eq_ofU8 rest)
private theorem vecU8_len {n : Nat} (v : List.Vector (BitVec 8) n) :
    (E2E.vecU8 v).length = n := by
  rw [E2E.vecU8, toU8_length, v.toList_length]
private theorem bytesToBv8_vecU8_eq {n : Nat} (v : List.Vector (BitVec 8) n) :
    Shared.bytesToBv8 (E2E.vecU8 v) = v.toList := by
  rw [shared_bytesToBv8_eq_ofU8, E2E.vecU8, ofU8_toU8]
private theorem fitBv8_vecU8_eq {n : Nat} (v : List.Vector (BitVec 8) n) :
    Shared.fitBv8 n (E2E.vecU8 v) = v.toList := by
  rw [Shared.fitBv8_eq_bytesToBv8 (vecU8_len v)]
  exact bytesToBv8_vecU8_eq v

private theorem readVecN_of_pointsToBytes_std3 {m : Memory} {a : BitVec 64} {n : Nat}
    {bs : List UInt8} {R : SepProp}
    (hlen : bs.length = n) (h : m ⊨ (a ↦ₛ Shared.bytesToBv8 bs) ∗ R) :
    readVecN m a n = u8Vec n bs := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes a (Shared.bytesToBv8 bs)).read h
  have hlen' : (Shared.bytesToBv8 bs).length = n := by simp [Shared.bytesToBv8, hlen]
  have hof : (ofU8 bs).length = n := by simp [hlen]
  rw [hlen'] at hread
  apply Subtype.ext
  dsimp only [readVecN, u8Vec, fitVec]
  rw [hread, shared_bytesToBv8_eq_ofU8,
    List.take_append_of_le_length (Nat.le_of_eq hof.symm),
    List.take_of_length_le (Nat.le_of_eq hof)]

theorem cryptoLeafHook_ok_std3 {inLen outLen : Nat} (hout_le : outLen ≤ 2 ^ 64)
    (f : List.Vector (BitVec 8) inLen → List.Vector (BitVec 8) outLen) :
    HookOk
      (fun s => LibsignalAesCbc.returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
        (f (readVecN s.mem (s.readReg64 .x0) inLen)).toList)))
      (Shared.cryptoLeafStubSpec (fun bs => vecU8 (f (u8Vec inLen bs))) inLen outLen) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (f (readVecN s.mem (s.readReg64 .x0) inLen)).toList)))
    (Shared.cryptoLeafStubSpec (fun bs => vecU8 (f (u8Vec inLen bs))) inLen outLen)
  refine retHook_ok fun ⟨inPtr, inBytes, outPtr⟩ R s0 hrun hpre _ => ?_
  simp only [Shared.cryptoLeafStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hin_len⟩, hmem⟩
  have hvec : readVecN s0.mem inPtr inLen = u8Vec inLen inBytes :=
    readVecN_of_pointsToBytes_std3 hin_len hmem
  let outBv := (f (u8Vec inLen inBytes)).toList
  have hout_len : outBv.length = outLen := (f (u8Vec inLen inBytes)).toList_length
  have hmem_out : s0.mem ⊨ memRegion outPtr outBv.length ∗
      ((inPtr ↦ₛ Shared.bytesToBv8 inBytes) ∗ (stackAt s0.sp Shared.pqxdhHookStack ∗ R)) := by
    rw [hout_len]
    ac_nf at hmem ⊢
  have hlen : outBv.length ≤ 2 ^ 64 := hout_len ▸ hout_le
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0, hx8, hvec]
    exact keepsFrozen_writeBytes_of_memRegion outBv hlen hmem_out
  · dsimp only [Shared.cryptoLeafStubSpec, retHook, State.setMem]
    simp only [State.trace_setPC, hx0, hx8, hvec, fitBv8_vecU8_eq,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    have hw := satisfies_writeBytes outBv hlen hmem_out
    dsimp only [outBv] at hw
    ac_nf at hw ⊢

theorem dsmbHook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) {img : Obj.Image} :
    HookOk (dsmbHook P0.Q.dsmb) (Shared.dalekDoubleMulStubSpec (modelPrims X P0) img) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (P0.Q.dsmb (readVecN s.mem (s.readReg64 .x0) 32)
        (readVecN s.mem (s.readReg64 .x1) 160)
        (readVecN s.mem (s.readReg64 .x2) 32)).toList)))
    (Shared.dalekDoubleMulStubSpec (modelPrims X P0) img)
  refine retHook_ok
    fun ⟨hBytes, negABytes, sBytes, hPtr, negAPtr, sPtr, outPtr⟩ R s0 hrun hpre _ => ?_
  simp only [Shared.dalekDoubleMulStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, hh_len, ha_len, hs_len⟩, hmem⟩
  have hh : readVecN s0.mem hPtr 32 = u8Vec 32 hBytes :=
    readVecN_of_pointsToBytes_std3 hh_len hmem
  have hmem_a : s0.mem ⊨ (negAPtr ↦ₛ Shared.bytesToBv8 negABytes) ∗
      ((hPtr ↦ₛ Shared.bytesToBv8 hBytes) ∗ (sPtr ↦ₛ Shared.bytesToBv8 sBytes) ∗
       memRegion outPtr 160 ∗ stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have ha : readVecN s0.mem negAPtr 160 = u8Vec 160 negABytes :=
    readVecN_of_pointsToBytes_std3 ha_len hmem_a
  have hmem_s : s0.mem ⊨ (sPtr ↦ₛ Shared.bytesToBv8 sBytes) ∗
      ((hPtr ↦ₛ Shared.bytesToBv8 hBytes) ∗ (negAPtr ↦ₛ Shared.bytesToBv8 negABytes) ∗
       memRegion outPtr 160 ∗ stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hs : readVecN s0.mem sPtr 32 = u8Vec 32 sBytes :=
    readVecN_of_pointsToBytes_std3 hs_len hmem_s
  let outBv := (P0.Q.dsmb (u8Vec 32 hBytes) (u8Vec 160 negABytes) (u8Vec 32 sBytes)).toList
  have hout_len : outBv.length = 160 :=
    (P0.Q.dsmb (u8Vec 32 hBytes) (u8Vec 160 negABytes) (u8Vec 32 sBytes)).toList_length
  have hmem_out : s0.mem ⊨ memRegion outPtr outBv.length ∗
      ((hPtr ↦ₛ Shared.bytesToBv8 hBytes) ∗ (negAPtr ↦ₛ Shared.bytesToBv8 negABytes) ∗
       (sPtr ↦ₛ Shared.bytesToBv8 sBytes) ∗ stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
    rw [hout_len]
    ac_nf at hmem ⊢
  have hlen : outBv.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0, hx1, hx2, hx8, hh, ha, hs]
    exact keepsFrozen_writeBytes_of_memRegion outBv hlen hmem_out
  · dsimp only [Shared.dalekDoubleMulStubSpec, retHook, State.setMem]
    have hdsmb : (modelPrims X P0).doubleScalarMulBasepoint hBytes negABytes sBytes =
        vecU8 (P0.Q.dsmb (u8Vec 32 hBytes) (u8Vec 160 negABytes) (u8Vec 32 sBytes)) := rfl
    simp only [State.trace_setPC, hx0, hx1, hx2, hx8, hh, ha, hs, hdsmb, fitBv8_vecU8_eq,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    have hw := satisfies_writeBytes outBv hlen hmem_out
    dsimp only [outBv] at hw
    ac_nf at hw ⊢

theorem torsionFreeHook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) {img : Obj.Image} :
    HookOk (torsionFreeHook P0.Q.isTorsionFree)
      (Shared.cryptoBoolRegStubSpec (modelPrims X P0).isTorsionFree 160 img) := by
  change HookOk
    (retHook (fun s => s.writeReg64 .x0
      (if P0.Q.isTorsionFree (readVecN s.mem (s.readReg64 .x0) 160) then 1#64 else 0#64)))
    (Shared.cryptoBoolRegStubSpec (modelPrims X P0).isTorsionFree 160 img)
  refine retHook_ok fun ⟨inPtr, inBytes⟩ R s0 hrun hpre _ => ?_
  simp only [Shared.cryptoBoolRegStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hin_len⟩, hmem⟩
  have hvec : readVecN s0.mem inPtr 160 = u8Vec 160 inBytes :=
    readVecN_of_pointsToBytes_std3 hin_len hmem
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [Shared.cryptoBoolRegStubSpec, retHook]
  have htf : (modelPrims X P0).isTorsionFree inBytes = P0.Q.isTorsionFree (u8Vec 160 inBytes) := rfl
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · rw [hx0, hvec, htf,
      CryptoVerification.LibsignalSession.NonVacuityWitness.readReg64_setPC_writeReg64_x0]
    cases P0.Q.isTorsionFree (u8Vec 160 inBytes) <;> rfl
  · change s0.mem ⊨ _
    ac_nf at hmem ⊢

theorem toEdwardsHook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) {img : Obj.Image} :
    HookOk (toEdwardsHook P0.Q.montToEd)
      (Shared.dalekMontToEdStubSpec (modelPrims X P0) img) := by
  change HookOk
    (retHook (fun s =>
      let r := s.readReg64 .x8
      let m := match P0.Q.montToEd (readVecN s.mem (s.readReg64 .x0) 32)
          ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
        | some p => (s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList
        | none => s.mem.write64 r 0#64
      s.setMem m))
    (Shared.dalekMontToEdStubSpec (modelPrims X P0) img)
  refine retHook_ok fun ⟨inBytes, signBit, inPtr, outPtr⟩ R s0 hrun hpre _ => ?_
  simp only [Shared.dalekMontToEdStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hin_len⟩, hmem⟩
  have hin : readVecN s0.mem inPtr 32 = u8Vec 32 inBytes :=
    readVecN_of_pointsToBytes_std3 hin_len hmem
  have hsb : BitVec.ofNat 8 signBit.toNat = signBit.toBitVec := by
    rcases signBit with ⟨v⟩
    simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsb1 : (signBit &&& 1).toBitVec = signBit.toBitVec &&& 1#8 := by
    simp only [UInt8.toBitVec_and]; rfl
  have hsplit : memRegion outPtr 168 =
      (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗ memRegion (outPtr + 8#64) 160 := by
    rw [memRegion_split' (b := outPtr) (n := 8) (k := 160) (b' := outPtr + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_eight outPtr]
  rw [hsplit] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, hcells⟩
  have hc0 : s0.mem ⊨ (outPtr ↦₆₄ w0) ∗
      (memRegion (outPtr + 8#64) 160 ∗ (inPtr ↦ₛ Shared.bytesToBv8 inBytes) ∗
       stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by ac_nf at hcells ⊢
  have hmte : (modelPrims X P0).montToEd inBytes (signBit &&& 1) =
      (P0.Q.montToEd (u8Vec 32 inBytes) (signBit.toBitVec &&& 1#8)).map E2E.vecU8 := by
    dsimp only [modelPrims, blockLevelPrims]
    rw [hsb1]
  cases hres : P0.Q.montToEd (u8Vec 32 inBytes) (signBit.toBitVec &&& 1#8) with
  | none =>
    have hkf := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 0#64 hc0
    have hw := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 0#64 hc0
    refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simp only [hx0, hx1, hsb, hx8, hin, hres]; exact hkf
    · dsimp only [Shared.dalekMontToEdStubSpec, retHook, State.setMem]
      simp only [State.trace_setPC, hx0, hx1, hsb, hx8, hin, hres,
        Shared.dalekMontToEdOutAt, hmte, Option.map,
        sepConj_assoc, satisfies_pure_sepConj, true_and]
      ac_nf at hw ⊢
  | some p =>
    have hkf1 := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 1#64 hc0
    have hw1 := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 1#64 hc0
    have hplen : p.toList.length = 160 := p.toList_length
    have hple : p.toList.length ≤ 2 ^ 64 := by rw [hplen]; decide
    have hm160 : s0.mem.write64 outPtr 1#64 ⊨ memRegion (outPtr + 8#64) p.toList.length ∗
        ((outPtr ↦₆₄ 1#64) ∗ (inPtr ↦ₛ Shared.bytesToBv8 inBytes) ∗
         stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
      rw [hplen]; ac_nf at hw1 ⊢
    have hkf2 := keepsFrozen_writeBytes_of_memRegion p.toList hple hm160
    have hw2 := satisfies_writeBytes p.toList hple hm160
    refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simp only [hx0, hx1, hsb, hx8, hin, hres]; exact hkf1.trans hkf2
    · dsimp only [Shared.dalekMontToEdStubSpec, retHook, State.setMem]
      have hu : Shared.u64le 1#64 = unpack64 1#64 := rfl
      simp only [State.trace_setPC, hx0, hx1, hsb, hx8, hin, hres,
        Shared.dalekMontToEdOutAt, hmte, Option.map, fitBv8_vecU8_eq,
        hu, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
        sepConj_assoc, satisfies_pure_sepConj, true_and]
      ac_nf at hw2 ⊢

private theorem sha512State_toList_std3 (h : Sha512State) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem sha512StateBytesLE_len_std3 (h : Sha512State) :
    (sha512StateBytesLE h).length = 64 := by
  rw [sha512StateBytesLE, sha512State_toList_std3]
  rfl

private theorem sha512StateBytesBE_len_std3 (h : Sha512State) :
    (sha512StateBytesBE h).length = 64 := by
  rw [sha512StateBytesBE, toU8_length, sha512State_toList_std3]
  rfl

private theorem toLEBytes8_read64_std3 (m : Memory) (a : BitVec 64) :
    LibsignalAesCbc.toLEBytes 8 (m.read64 a) = m.readBytes a 8 := by
  have h1 : LibsignalAesCbc.toLEBytes 8 (m.read64 a) = unpack64 (m.read64 a) := rfl
  have hrd : m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  rw [h1, hrd]
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero]
  exact unpack64_pack64 (m.read8 a) (m.read8 (a + 1#64)) (m.read8 (a + 2#64)) (m.read8 (a + 3#64))
    (m.read8 (a + 4#64)) (m.read8 (a + 5#64)) (m.read8 (a + 6#64)) (m.read8 (a + 7#64))

private theorem sha512StateBytesLE_readSha512State_std3 (m : Memory) (a : BitVec 64) :
    sha512StateBytesLE (readSha512State m a) = m.readBytes a 64 := by
  have hget (i : Fin 8) :
      LibsignalAesCbc.toLEBytes 8 ((readSha512State m a).get i) =
        m.readBytes (a + BitVec.ofNat 64 (8 * i.val)) 8 := by
    simp only [readSha512State, List.Vector.get_ofFn, toLEBytes8_read64_std3]
  rw [sha512StateBytesLE, sha512State_toList_std3 (readSha512State m a)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hget]
  change
    m.readBytes (a + 0#64) 8 ++
    (m.readBytes (a + 8#64) 8 ++
    (m.readBytes (a + 16#64) 8 ++
    (m.readBytes (a + 24#64) 8 ++
    (m.readBytes (a + 32#64) 8 ++
    (m.readBytes (a + 40#64) 8 ++
    (m.readBytes (a + 48#64) 8 ++
     m.readBytes (a + 56#64) 8)))))) = m.readBytes a 64
  simp only [Memory.readBytes, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    List.cons_append, List.nil_append]

private theorem ofU8_revWords64_toU8_sha512StateBytesLE_std3 (h : Sha512State) :
    Shared.revWords64 (toU8 (sha512StateBytesLE h)) = sha512StateBytesBE h := by
  rw [← toU8_ofU8 (Shared.revWords64 (toU8 (sha512StateBytesLE h)))]
  congr 1
  simp only [Shared.revWords64, ofU8, List.map_append, List.map_reverse,
    List.map_take, List.map_drop]
  change
    (((ofU8 (toU8 (sha512StateBytesLE h))).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 8).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 16).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 24).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 32).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 40).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 48).take 8).reverse ++
     (((ofU8 (toU8 (sha512StateBytesLE h))).drop 56).take 8).reverse) =
    (h.toList.flatMap (toBEBytes 8))
  rw [ofU8_toU8, sha512StateBytesLE, sha512State_toList_std3 h]
  rfl

private theorem ofU8_revWords64_sha512StateBytesBE_std3 (h : Sha512State) :
    ofU8 (Shared.revWords64 (sha512StateBytesBE h)) = sha512StateBytesLE h := by
  simp only [Shared.revWords64, ofU8, List.map_append, List.map_reverse,
    List.map_take, List.map_drop]
  change
    (((ofU8 (sha512StateBytesBE h)).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 8).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 16).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 24).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 32).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 40).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 48).take 8).reverse ++
     (((ofU8 (sha512StateBytesBE h)).drop 56).take 8).reverse) = sha512StateBytesLE h
  rw [sha512StateBytesBE, ofU8_toU8, sha512StateBytesLE, sha512State_toList_std3 h]
  rfl

private theorem beWord64_toBEBytes8_std3 (w : BitVec 64) :
    beWord 64 (toBEBytes 8 w) 0 = w := by
  change
    ((((((((0#64 <<< 8 ||| (w.extractLsb' 56 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 48 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 40 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 32 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 24 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 16 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 8 8).zeroExtend 64) <<< 8 |||
      (w.extractLsb' 0 8).zeroExtend 64) = w
  bv_bits

private theorem sha512StateOf_sha512StateBytesBE_std3 (h : Sha512State) :
    sha512StateOf (sha512StateBytesBE h) = h := by
  apply List.Vector.ext
  intro i
  simp only [sha512StateOf, List.Vector.get_ofFn]
  have hslice :
      beWord 64 (ofU8 (sha512StateBytesBE h)) i.val =
        beWord 64 (toBEBytes 8 (h.get i)) 0 := by
    rw [sha512StateBytesBE, ofU8_toU8, sha512State_toList_std3 h]
    fin_cases i <;> rfl
  rw [hslice, beWord64_toBEBytes8_std3]

private theorem list_ofFn_eq_range_map_std3 {α : Type} (n : Nat) (f : Nat → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    rw [ih (fun i => f (i + 1)), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

private theorem chunks128_ofU8_std3 (bs : SignalPqxdh.Bytes) :
    chunks128 (ofU8 bs) = (SignalPqxdh.chunkBlocks 128 bs).map ofU8 := by
  unfold chunks128 SignalPqxdh.chunkBlocks
  rw [list_ofFn_eq_range_map_std3 ((ofU8 bs).length / 128)
      (fun i => ((ofU8 bs).drop (128 * i)).take 128),
    ofU8_length, List.map_map]
  congr 1; funext i
  simp only [Function.comp_def, ofU8, ← List.map_drop, ← List.map_take, Nat.mul_comm 128 i]

private theorem foldl_sha512Step_modelPrims_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams)
    (blks : List SignalPqxdh.Bytes) (st : Sha512State) :
    blks.foldl (SignalPqxdh.sha512Step (modelPrims X P0)) (sha512StateBytesBE st) =
      sha512StateBytesBE ((blks.map ofU8).foldl P0.Q.F512 st) := by
  induction blks generalizing st with
  | nil => rfl
  | cons blk rest ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hstep :
        SignalPqxdh.sha512Step (modelPrims X P0) (sha512StateBytesBE st) blk =
          sha512StateBytesBE (P0.Q.F512 st (ofU8 blk)) := by
      unfold SignalPqxdh.sha512Step
      change SignalPqxdh.fitBytes 64
        (sha512StateBytesBE
          (P0.Q.F512 (sha512StateOf (SignalPqxdh.fitBytes 64 (sha512StateBytesBE st))) (ofU8 blk))) =
        sha512StateBytesBE (P0.Q.F512 st (ofU8 blk))
      rw [Shared.fitBytes_of_length_eq (sha512StateBytesBE_len_std3 st),
        sha512StateOf_sha512StateBytesBE_std3,
        Shared.fitBytes_of_length_eq (sha512StateBytesBE_len_std3 _)]
    rw [hstep, ih]

theorem compress512Hook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) {img : Obj.Image} :
    HookOk (compress512Hook P0.Q.F512)
      (Shared.compressInPlaceStubSpec
        (Shared.sha512CompressOutBytes (modelPrims X P0)) 64 128 img) := by
  change HookOk
    (retHook (fun s =>
      let st := readSha512State s.mem (s.readReg64 .x0)
      let bs := s.mem.readBytes (s.readReg64 .x1) (128 * (s.readReg64 .x2).toNat)
      s.setMem (s.mem.writeBytes (s.readReg64 .x0)
        (sha512StateBytesLE ((chunks128 bs).foldl P0.Q.F512 st)))))
    (Shared.compressInPlaceStubSpec
      (Shared.sha512CompressOutBytes (modelPrims X P0)) 64 128 img)
  refine retHook_ok
    fun ⟨statePtr, stateBytes, blocksPtr, blockBytes, nBlocks⟩ R s0 hrun hpre _ => ?_
  simp only [Shared.compressInPlaceStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn_lt, hst_len, hblk_len⟩, hmem⟩
  have hx2_nat : (s0.readReg64 .x2).toNat = nBlocks := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt]
  have hst_read : s0.mem.readBytes statePtr 64 = ofU8 stateBytes := by
    have hlen' : (Shared.bytesToBv8 stateBytes).length = 64 := by simp [Shared.bytesToBv8, hst_len]
    have hrd := ((IsBlock.pointsToBytes statePtr (Shared.bytesToBv8 stateBytes)).read hmem).2
    rw [hlen', shared_bytesToBv8_eq_ofU8] at hrd
    exact hrd
  have hmem_blk : s0.mem ⊨ (blocksPtr ↦ₛ Shared.bytesToBv8 blockBytes) ∗
      ((statePtr ↦ₛ Shared.bytesToBv8 stateBytes) ∗ stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hblk_read : s0.mem.readBytes blocksPtr (128 * nBlocks) = ofU8 blockBytes := by
    have hlen' : (Shared.bytesToBv8 blockBytes).length = 128 * nBlocks := by
      simp [Shared.bytesToBv8, hblk_len]
    have hrd := ((IsBlock.pointsToBytes blocksPtr (Shared.bytesToBv8 blockBytes)).read hmem_blk).2
    rw [hlen', shared_bytesToBv8_eq_ofU8] at hrd
    exact hrd
  let st0 := readSha512State s0.mem statePtr
  have hrev_st : Shared.revWords64 stateBytes = sha512StateBytesBE st0 := by
    have hle : sha512StateBytesLE st0 = ofU8 stateBytes :=
      (sha512StateBytesLE_readSha512State_std3 s0.mem statePtr).trans hst_read
    have hst_eq : stateBytes = toU8 (sha512StateBytesLE st0) := by
      rw [hle, toU8_ofU8]
    rw [hst_eq, ofU8_revWords64_toU8_sha512StateBytesLE_std3]
  let stFinal := (chunks128 (ofU8 blockBytes)).foldl P0.Q.F512 st0
  let outBv := sha512StateBytesLE stFinal
  have hout_eq :
      Shared.fitBv8 64
        (Shared.sha512CompressOutBytes (modelPrims X P0) stateBytes blockBytes) = outBv := by
    unfold Shared.sha512CompressOutBytes
    rw [hrev_st, foldl_sha512Step_modelPrims_std3, ← chunks128_ofU8_std3,
      Shared.fitBytes_of_length_eq (sha512StateBytesBE_len_std3 stFinal)]
    have hrev_len : (Shared.revWords64 (sha512StateBytesBE stFinal)).length = 64 := by
      rw [← ofU8_length, ofU8_revWords64_sha512StateBytesBE_std3, sha512StateBytesLE_len_std3]
    rw [Shared.fitBv8_eq_bytesToBv8 hrev_len, shared_bytesToBv8_eq_ofU8,
      ofU8_revWords64_sha512StateBytesBE_std3]
  have hout_len : outBv.length = (Shared.bytesToBv8 stateBytes).length := by
    simp [outBv, sha512StateBytesLE_len_std3, Shared.bytesToBv8, hst_len]
  have hmem_reg : s0.mem ⊨ memRegion statePtr outBv.length ∗
      ((blocksPtr ↦ₛ Shared.bytesToBv8 blockBytes) ∗ stackAt s0.sp Shared.pqxdhHookStack ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion statePtr _)) hmem
  have hlen64 : outBv.length ≤ 2 ^ 64 := by
    simp only [outBv, sha512StateBytesLE_len_std3]; decide
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [hx0, hx1, hx2_nat, hblk_read]
    exact keepsFrozen_writeBytes_of_memRegion outBv hlen64 hmem_reg
  · dsimp only [Shared.compressInPlaceStubSpec, retHook, State.setMem]
    simp only [State.trace_setPC, hx0, hx1, hx2_nat, hblk_read, hout_eq,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes outBv hlen64 hmem_reg

/-- `PqxdhHookContracts (modelPrims X ⟨W.C, W.Q⟩) A img (cliExterns W)` on `cliExterns W`. -/
theorem cliExterns_pqxdhHookContracts (W : CliHooks) (X : E2E.UnreachedPqxdhPrimitives) {A : RustAlloc}
    (img : Obj.Image) :
    Shared.PqxdhHookContracts (modelPrims X ⟨W.C, W.Q⟩) A img (cliExterns W) where
  dalekMontToEd :=
    ⟨toEdwardsHook W.Q.montToEd, cliExterns_row W (toEdwards_row W),
      toEdwardsHook_ok_std3 X ⟨W.C, W.Q⟩⟩
  dalekTorsionFree :=
    ⟨torsionFreeHook W.Q.isTorsionFree, cliExterns_row W (torsionFree_row W),
      torsionFreeHook_ok_std3 X ⟨W.C, W.Q⟩⟩
  sha512Compress :=
    ⟨compress512Hook W.Q.F512, cliExterns_row W (compress512_row W),
      compress512Hook_ok_std3 X ⟨W.C, W.Q⟩⟩
  dalekScalarWide :=
    ⟨scalarWideHook W.Q.scalarWide, cliExterns_row W (scalarWide_row W),
      cryptoLeafHook_ok_std3 (by decide) W.Q.scalarWide⟩
  dalekScalarMod :=
    ⟨scalarModHook W.Q.scalarMod, cliExterns_row W (scalarMod_row W),
      cryptoLeafHook_ok_std3 (by decide) W.Q.scalarMod⟩
  dalekCompress :=
    ⟨compressHook W.Q.compress, cliExterns_row W (compress_row W),
      cryptoLeafHook_ok_std3 (by decide) W.Q.compress⟩
  dalekEdNeg :=
    ⟨edNegHook W.Q.edNeg, cliExterns_row W (edNeg_row W),
      cryptoLeafHook_ok_std3 (by decide) W.Q.edNeg⟩
  dalekDoubleMul :=
    ⟨dsmbHook W.Q.dsmb, cliExterns_row W (dsmb_row W),
      dsmbHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem kemEncapsHook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) :
    HookOk (kemEncapsHook P0.Q.encaps)
      (Initiator.kyberEncapsStubSpec (modelPrims X P0)) := by
  unfold E2E.kemEncapsHook
  refine retHook_ok fun ⟨pkPtr, pk1568, coinsPtr, coins32, outPtr⟩ R s0 hrun hpre _ => ?_
  simp only [Initiator.kyberEncapsStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hpk_len, hcoins_len, _⟩, hmem⟩
  have heq_bv : ∀ bs, Initiator.bytesToBv8 bs = Shared.bytesToBv8 bs := fun _ => rfl
  rw [heq_bv, heq_bv] at hmem
  have hpk : readVecN s0.mem pkPtr 1568 = u8Vec 1568 pk1568 :=
    readVecN_of_pointsToBytes_std3 hpk_len hmem
  have hmem_coins : s0.mem ⊨ (coinsPtr ↦ₛ Shared.bytesToBv8 coins32) ∗
      ((pkPtr ↦ₛ Shared.bytesToBv8 pk1568) ∗
       memRegion outPtr 1600 ∗ stackAt s0.sp Initiator.pqxdhHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hcoins : readVecN s0.mem coinsPtr 32 = u8Vec 32 coins32 :=
    readVecN_of_pointsToBytes_std3 hcoins_len hmem_coins
  let o := P0.Q.encaps (u8Vec 1568 pk1568) (u8Vec 32 coins32)
  have hsplit : memRegion outPtr 1600 = memRegion outPtr 1568 ∗ memRegion (outPtr + 0x620#64) 32 :=
    ProofLib.memRegion_split' (b := outPtr) (n := 1568) (k := 32) (b' := outPtr + 0x620#64)
      rfl (by bv_omega) (by decide)
  rw [hsplit] at hmem
  have hmem1 : s0.mem ⊨ memRegion outPtr o.1.toList.length ∗
      (memRegion (outPtr + 0x620#64) 32 ∗ (pkPtr ↦ₛ Shared.bytesToBv8 pk1568) ∗
       (coinsPtr ↦ₛ Shared.bytesToBv8 coins32) ∗ stackAt s0.sp Initiator.pqxdhHookStack ∗ R) := by
    rw [o.1.toList_length]; ac_nf at hmem ⊢
  have hlen1 : o.1.toList.length ≤ 2 ^ 64 := by rw [o.1.toList_length]; decide
  have hkf1 := keepsFrozen_writeBytes_of_memRegion o.1.toList hlen1 hmem1
  have hw1 := satisfies_writeBytes o.1.toList hlen1 hmem1
  have hmem2 : s0.mem.writeBytes outPtr o.1.toList ⊨ memRegion (outPtr + 0x620#64) o.2.toList.length ∗
      ((outPtr ↦ₛ o.1.toList) ∗ (pkPtr ↦ₛ Shared.bytesToBv8 pk1568) ∗
       (coinsPtr ↦ₛ Shared.bytesToBv8 coins32) ∗ stackAt s0.sp Initiator.pqxdhHookStack ∗ R) := by
    rw [o.2.toList_length]; ac_nf at hw1 ⊢
  have hlen2 : o.2.toList.length ≤ 2 ^ 64 := by rw [o.2.toList_length]; decide
  have hkf2 := hkf1.trans (keepsFrozen_writeBytes_of_memRegion o.2.toList hlen2 hmem2)
  have hw2 := satisfies_writeBytes o.2.toList hlen2 hmem2
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0, hx1, hx8, hpk, hcoins]; exact hkf2
  · dsimp only [Initiator.kyberEncapsStubSpec, Initiator.kyberEncapsOutBytes, retHook,
      LibsignalAesCbc.returnToLinkRegister, State.setMem]
    have henc : (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P0)).kemEncaps pk1568 coins32 =
        some (vecU8 o.2, vecU8 o.1) := by
      simp only [ResponderCore.ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
        SignalPqxdh.kyberPkLen, hpk_len, beq_self_eq_true, ↓reduceIte]
      rfl
    have hfit : Initiator.fitBv8 1600 (vecU8 o.1 ++ vecU8 o.2) = o.1.toList ++ o.2.toList := by
      unfold Initiator.fitBv8
      rw [Initiator.bytesToBv8_append, Initiator.e2e_bytesToBv8_vecU8,
        Initiator.e2e_bytesToBv8_vecU8]
      have hlen : (o.1.toList ++ o.2.toList).length = 1600 := by
        rw [List.length_append, o.1.toList_length, o.2.toList_length]
      rw [hlen, List.take_of_length_le (by rw [hlen]), Nat.sub_self, List.replicate_zero,
        List.append_nil]
    rw [hx0, hx1, hx8, hpk, hcoins, State.trace_setPC, henc]
    dsimp only
    rw [hfit]
    have hmerge : (outPtr ↦ₛ (o.1.toList ++ o.2.toList)) =
        (outPtr ↦ₛ o.1.toList) ∗ ((outPtr + 0x620#64) ↦ₛ o.2.toList) := by
      rw [pointsToBytes_append, o.1.toList_length]
    rw [hmerge, heq_bv, heq_bv]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and]
    ac_nf at hw2 ⊢

/-- Kyber-1024 encapsulation hook contract at `cliExterns W`. -/
theorem cliExterns_kemEncaps (W : CliHooks) (X : E2E.UnreachedPqxdhPrimitives) :
    HookSat (cliExterns W) kemEncapsName
      (Initiator.kyberEncapsStubSpec (modelPrims X ⟨W.C, W.Q⟩)) :=
  ⟨kemEncapsHook W.Q.encaps, cliExterns_row W (kemEncaps_row W),
    kemEncapsHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem kemDecapsHook_ok_std3 (X : UnreachedPqxdhPrimitives) (P0 : PEParams) :
    HookOk (kemDecapsHook P0.Q.decaps)
      (Initiator.kyberDecapsStubSpec (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P0))) := by
  change HookOk
    (retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (P0.Q.decaps (readVecN s.mem (s.readReg64 .x0) 3168)
        (readVecN s.mem (s.readReg64 .x1) 1568)).toList)))
    (Initiator.kyberDecapsStubSpec (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P0)))
  refine retHook_ok fun ⟨skPtr, skBytes, ctPtr, ctBytes, outPtr⟩ R s0 hrun hpre _ => ?_
  simp only [Initiator.kyberDecapsStubSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsk_len, hct_len, _⟩, hmem⟩
  have heq_bv : ∀ bs, Initiator.bytesToBv8 bs = Shared.bytesToBv8 bs := fun _ => rfl
  rw [heq_bv, heq_bv] at hmem
  have hsk : readVecN s0.mem skPtr 3168 = u8Vec 3168 skBytes :=
    readVecN_of_pointsToBytes_std3 hsk_len hmem
  have hmem_ct : s0.mem ⊨ (ctPtr ↦ₛ Shared.bytesToBv8 ctBytes) ∗
      ((skPtr ↦ₛ Shared.bytesToBv8 skBytes) ∗
       memRegion outPtr 32 ∗ stackAt s0.sp Initiator.pqxdhHookStack ∗ R) := by
    ac_nf at hmem ⊢
  have hct : readVecN s0.mem ctPtr 1568 = u8Vec 1568 ctBytes :=
    readVecN_of_pointsToBytes_std3 hct_len hmem_ct
  let outBv := (P0.Q.decaps (u8Vec 3168 skBytes) (u8Vec 1568 ctBytes)).toList
  have hout_len : outBv.length = 32 :=
    (P0.Q.decaps (u8Vec 3168 skBytes) (u8Vec 1568 ctBytes)).toList_length
  have hmem_out : s0.mem ⊨ memRegion outPtr outBv.length ∗
      ((skPtr ↦ₛ Shared.bytesToBv8 skBytes) ∗
       (ctPtr ↦ₛ Shared.bytesToBv8 ctBytes) ∗
       stackAt s0.sp Initiator.pqxdhHookStack ∗ R) := by
    rw [hout_len]
    ac_nf at hmem ⊢
  have hlen : outBv.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0, hx1, hx8, hsk, hct]
    exact keepsFrozen_writeBytes_of_memRegion outBv hlen hmem_out
  · dsimp only [Initiator.kyberDecapsStubSpec, Initiator.kyberDecapsOutBytes, retHook, State.setMem]
    have hdec : (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P0)).kemDecaps skBytes ctBytes =
        some (vecU8 (P0.Q.decaps (u8Vec 3168 skBytes) (u8Vec 1568 ctBytes))) := by
      simp only [ResponderCore.ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
        SignalPqxdh.kyberCtLen, hct_len, beq_self_eq_true, ↓reduceIte]
    have hfit : Initiator.fitBv8 32 (vecU8 (P0.Q.decaps (u8Vec 3168 skBytes) (u8Vec 1568 ctBytes))) =
        outBv := fitBv8_vecU8_eq _
    simp only [State.trace_setPC, hx0, hx1, hx8, hsk, hct, hdec, Option.getD_some, hfit,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    have hw := satisfies_writeBytes outBv hlen hmem_out
    dsimp only [outBv] at hw
    rw [heq_bv, heq_bv]
    ac_nf at hw ⊢

/-- Kyber-1024 decapsulation hook contract at `cliExterns W`. -/
theorem cliExterns_kemDecaps (W : CliHooks) (X : E2E.UnreachedPqxdhPrimitives) :
    HookSat (cliExterns W) kemDecapsName
      (Initiator.kyberDecapsStubSpec
        (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) :=
  ⟨kemDecapsHook W.Q.decaps, cliExterns_row W (kemDecaps_row W),
    kemDecapsHook_ok_std3 X ⟨W.C, W.Q⟩⟩

end PqxdhContracts

/-! ## 4. `duration_since` contracts -/

theorem timespecAt_entails_memRegion12_pair (p : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) :
    ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec)) ⊢ memRegion p 12 := by
  rw [memRegion_split p 8 4 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p tvSec)
    (pointsTo32_entails_memRegion (p + 8#64) tvNsec)

theorem timespecAt_entails_memRegion16 (p : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) :
    ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ⊢
      memRegion p 16 := by
  have h8 : memRegion (p + 8#64) 8 = memRegion (p + 8#64) 4 ∗ memRegion (p + 12#64) 4 :=
    memRegion_split' (b := p + 8#64) (n := 4) (k := 4) (b' := p + 12#64) rfl
      (by bv_omega) (by decide)
  rw [memRegion_split p 8 8 (by decide), h8]
  exact sepConj_mono (pointsTo64_entails_memRegion p tvSec)
    (sepConj_mono_left (pointsTo32_entails_memRegion (p + 8#64) tvNsec))

private theorem keepsFrozen_write32_of_pointsTo32 {m : Memory} {a : BitVec 64} {v₀ : BitVec 32}
    {R : SepProp} (v : BitVec 32) (h : m ⊨ (a ↦₃₂ v₀) ∗ R) :
    m.KeepsFrozen (m.write32 a v) :=
  Memory.keepsFrozen_write32 ((IsBlock.pointsTo32 a v₀).canWrite (by decide) h) v

private theorem satisfies_write32_of_pointsTo32 {m : Memory} {a : BitVec 64} {v₀ : BitVec 32}
    {R : SepProp} (v : BitVec 32) (h : m ⊨ (a ↦₃₂ v₀) ∗ R) :
    m.write32 a v ⊨ (a ↦₃₂ v) ∗ R :=
  IsBlock.write32 (IsBlock.pointsTo32 a v₀) h v

/-- Stack-parameterized `UNIX_EPOCH` `duration_since` contract: `self` has `tv_sec = 0` (`u64` @0),
`tv_nsec = 0` (`u32` @8), arbitrary 4-byte padding @12, and `earlier` has `x1 = 0 ∧ w2 = 0`. -/
def durationSinceEpochAtSpec (stk : Nat) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      s.readReg64 .x1 = 0#64 ∧ (s.readReg64 .x2).setWidth 32 = 0#32⌝ ∗
      (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s.sp stk
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗
      ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
      stackAt s0.sp stk

def durationSinceEpochSpec : Spec (BitVec 64 × BitVec 64) := durationSinceEpochAtSpec extHookStack
def durationSinceEpochAllocSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceEpochAtSpec allocHookStack

def durationSinceBoundedSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      ((s.readReg64 .x2).setWidth 32).toNat < 1000000000⌝ ∗
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        (p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗
      memRegion ret 24 ∗ stackAt s.sp extHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s0.sp extHookStack

theorem durationSinceBounded_self_intro (p : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) (hns : tvNsec.toNat < 1000000000) :
    ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ⊢
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        (p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) :=
  Entails.sepExists_right tvSec (Entails.sepExists_right tvNsec
    (Entails.pure_right hns (Entails.refl _)))

theorem satisfies_durationSinceBounded_self_of_memRegion {m : Memory} {p : BitVec 64}
    {R : SepProp} (hm : m ⊨ memRegion p 16 ∗ R)
    (hns : (m.read32 (p + 8#64)).toNat < 1000000000) :
    m ⊨ (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
      ⌜tvNsec.toNat < 1000000000⌝ ∗
      (p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗ R := by
  have h8 : memRegion (p + 8#64) 8 = memRegion (p + 8#64) 4 ∗ memRegion (p + 12#64) 4 :=
    memRegion_split' (b := p + 8#64) (n := 4) (k := 4) (b' := p + 12#64) rfl
      (by bv_omega) (by decide)
  rw [memRegion_split p 8 8 (by decide), h8, ProofLib.memRegion_eight p,
      ProofLib.memRegion_four (p + 8#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hm
  rcases hm with ⟨tvNsec, tvSec, hm⟩
  have hm_ns : m ⊨ ((p + 8#64) ↦₃₂ tvNsec) ∗
      ((p ↦₆₄ tvSec) ∗ memRegion (p + 12#64) 4 ∗ R) := by ac_nf at hm ⊢
  have hread : m.read32 (p + 8#64) = tvNsec := (IsBlock.pointsTo32 (p + 8#64) tvNsec).read hm_ns
  rw [hread] at hns
  have hm_grp : m ⊨ ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗ R := by
    ac_nf at hm ⊢
  exact Satisfies.mono
    (sepConj_mono_left (durationSinceBounded_self_intro p tvSec tvNsec hns)) hm_grp

private theorem durationSinceExactHook_step {p ret : BitVec 64} {tvSec : BitVec 64}
    {tvNsec : BitVec 32} {stk : Nat} {R : SepProp} {s0 : State}
    (hx0 : s0.readReg64 .x0 = p) (hx8 : s0.readReg64 .x8 = ret)
    (hns1 : tvNsec.toNat < 1000000000)
    (hns2 : ((s0.readReg64 .x2).setWidth 32).toNat < 1000000000)
    (hmem : s0.mem ⊨ (p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) :
    let d := (tvSec.toInt * 1000000000 + ↑tvNsec.toNat -
      ((s0.readReg64 .x1).toInt * 1000000000 + ↑((s0.readReg64 .x2).setWidth 32).toNat)).natAbs
    let tag : BitVec 64 :=
      if (s0.readReg64 .x1).toInt * 1000000000 + ↑((s0.readReg64 .x2).setWidth 32).toNat ≤
         tvSec.toInt * 1000000000 + ↑tvNsec.toNat
      then 0#64 else 1#64
    ∃ w2 : BitVec 64,
      durationSinceExactHook s0 =
        retHook (fun s => s.setMem (((s.mem.write64 ret tag).write64 (ret + 8#64)
          (BitVec.ofNat 64 (d / 1000000000))).write32 (ret + 16#64)
          (BitVec.ofNat 32 (d % 1000000000)))) s0 ∧
      s0.mem.KeepsFrozen (durationSinceExactHook s0).mem ∧
      (durationSinceExactHook s0).mem ⊨
        memRegion p 16 ∗ (ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 1000000000)) ∗
        ((ret + 16#64) ↦₆₄ w2) ∗ stackAt s0.sp stk ∗ R := by
  intro d tag
  have hmem_p64 : s0.mem ⊨ (p ↦₆₄ tvSec) ∗ (((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem ⊢
  have hrd64 : s0.mem.read64 p = tvSec := (IsBlock.pointsTo64 p tvSec).read hmem_p64
  have hmem_p32 : s0.mem ⊨ ((p + 8#64) ↦₃₂ tvNsec) ∗ ((p ↦₆₄ tvSec) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem ⊢
  have hrd32 : s0.mem.read32 (p + 8#64) = tvNsec :=
    (IsBlock.pointsTo32 (p + 8#64) tvNsec).read hmem_p32
  have hmem_self16 : s0.mem ⊨ memRegion p 16 ∗ (memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by
    have hgrp : s0.mem ⊨ ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗
        (memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem ⊢
    exact Satisfies.mono (sepConj_mono_left (timespecAt_entails_memRegion16 p tvSec tvNsec)) hgrp
  have hmem_p12 : s0.mem ⊨ memRegion p 12 ∗
      (memRegion (p + 12#64) 4 ∗ memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by
    rw [memRegion_split' (b := p) (n := 12) (k := 4) (b' := p + 12#64) rfl rfl (by decide)]
      at hmem_self16
    ac_nf at hmem_self16 ⊢
  have hcanR : s0.mem.canRead p 12 = true := (IsBlock.memRegion p 12).canRead (by decide) hmem_p12
  have hmem_ret24 : s0.mem ⊨ memRegion ret 24 ∗ (memRegion p 16 ∗ stackAt s0.sp stk ∗ R) := by
    ac_nf at hmem_self16 ⊢
  have hcanW : s0.mem.canWrite ret 24 = true :=
    (IsBlock.memRegion ret 24).canWrite (by decide) hmem_ret24
  have h_split_ret : memRegion ret 24 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ lo : BitVec 32, (ret + 16#64) ↦₃₂ lo) ∗ (∃∗ hi : BitVec 32, (ret + 20#64) ↦₃₂ hi) := by
    have h8 : memRegion (ret + 16#64) 8 = memRegion (ret + 16#64) 4 ∗ memRegion (ret + 20#64) 4 :=
      memRegion_split' (b := ret + 16#64) (n := 4) (k := 4) (b' := ret + 20#64) rfl
        (by bv_omega) (by decide)
    rw [memRegion_split' (b := ret) (n := 8) (k := 16) (b' := ret + 8#64) rfl rfl (by decide),
        memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64) rfl
          (by bv_omega) (by decide),
        h8, ProofLib.memRegion_eight ret, ProofLib.memRegion_eight (ret + 8#64),
        ProofLib.memRegion_four (ret + 16#64), ProofLib.memRegion_four (ret + 20#64)]
  rw [h_split_ret] at hmem_ret24
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem_ret24
  rcases hmem_ret24 with ⟨hi, lo, w1, w0, hcells⟩
  have hc0 : s0.mem ⊨ (ret ↦₆₄ w0) ∗ (((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₃₂ lo) ∗
      ((ret + 20#64) ↦₃₂ hi) ∗ memRegion p 16 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hcells ⊢
  have hkf1 := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 tag hc0
  have hw1 := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 tag hc0
  let secs := BitVec.ofNat 64 (d / 1000000000)
  let nanos := BitVec.ofNat 32 (d % 1000000000)
  have hc1 : s0.mem.write64 ret tag ⊨ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret ↦₆₄ tag) ∗
      ((ret + 16#64) ↦₃₂ lo) ∗ ((ret + 20#64) ↦₃₂ hi) ∗
      memRegion p 16 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hw1 ⊢
  have hkf2 := E2E.HooksE.HooksOkAux.keepsFrozen_write64_of_pointsTo64 secs hc1
  have hw2 := E2E.HooksE.HooksOkAux.satisfies_write64_of_pointsTo64 secs hc1
  have hc2 : (s0.mem.write64 ret tag).write64 (ret + 8#64) secs ⊨ ((ret + 16#64) ↦₃₂ lo) ∗
      ((ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ secs) ∗ ((ret + 20#64) ↦₃₂ hi) ∗
       memRegion p 16 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hw2 ⊢
  have hkf3 := keepsFrozen_write32_of_pointsTo32 nanos hc2
  have hw3 := satisfies_write32_of_pointsTo32 nanos hc2
  have h20 : ret + 16#64 + 4#64 = ret + 20#64 := by bv_omega
  have hw_pair : (((s0.mem.write64 ret tag).write64 (ret + 8#64) secs).write32 (ret + 16#64) nanos) ⊨
      (((ret + 16#64) ↦₃₂ nanos) ∗ ((ret + 16#64 + 4#64) ↦₃₂ hi)) ∗
      (memRegion p 16 ∗ (ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ secs) ∗ stackAt s0.sp stk ∗ R) := by
    rw [h20]; ac_nf at hw3 ⊢
  rw [pointsTo32_pair (ret + 16#64) nanos hi] at hw_pair
  have heval : durationSinceExactHook s0 =
      retHook (fun s => s.setMem (((s.mem.write64 ret tag).write64 (ret + 8#64) secs).write32
        (ret + 16#64) nanos)) s0 := by
    unfold durationSinceExactHook
    simp only [hx0, hx8, hcanR, hcanW, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hrd32, hrd64, hns1, hns2, and_self]
    rfl
  refine ⟨hi ++ nanos, heval, ?_, ?_⟩
  · rw [heval]; exact hkf1.trans (hkf2.trans hkf3)
  · rw [heval]; dsimp only [retHook, State.setMem]; ac_nf at hw_pair ⊢

theorem durationSinceExactHook_epoch_at_ok (stk : Nat) :
    HookOk durationSinceExactHook (durationSinceEpochAtSpec stk) := by
  intro ⟨p, ret⟩ R s0 hrun hpre _hsp
  simp only [durationSinceEpochAtSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hx1, hx2⟩, hmem⟩
  have hns1 : (0#32 : BitVec 32).toNat < 1000000000 := by decide
  have hns2 : ((s0.readReg64 .x2).setWidth 32).toNat < 1000000000 := by rw [hx2]; decide
  obtain ⟨w2, heval, hkf, hpost_mem⟩ := durationSinceExactHook_step hx0 hx8 hns1 hns2 hmem
  have hd0 : ((0#64 : BitVec 64).toInt * 1000000000 + ↑(0#32 : BitVec 32).toNat -
      ((s0.readReg64 .x1).toInt * 1000000000 +
        ↑((s0.readReg64 .x2).setWidth 32).toNat)).natAbs = 0 := by rw [hx1, hx2]; decide
  have htag0 : (if (s0.readReg64 .x1).toInt * 1000000000 + ↑((s0.readReg64 .x2).setWidth 32).toNat ≤
       (0#64 : BitVec 64).toInt * 1000000000 + ↑(0#32 : BitVec 32).toNat
      then (0#64 : BitVec 64) else 1#64) = 0#64 := by rw [hx1, hx2]; decide
  rw [hd0, htag0] at heval hpost_mem
  have hsecs0 : BitVec.ofNat 64 (0 / 1000000000) = 0#64 := rfl
  rw [hsecs0] at hpost_mem
  refine ⟨hkf, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [heval]; rfl
  · rw [heval]; exact ⟨rfl, rfl, hrun⟩
  · rw [heval]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only [durationSinceEpochAtSpec]
    have htr : (durationSinceExactHook s0).trace = s0.trace := by rw [heval]; rfl
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hent : ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2)) ⊢
        (∃∗ w2' : BitVec 64, ∃∗ w0' : BitVec 64,
          (ret ↦₆₄ w0') ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2')) :=
      Entails.sepExists_right w2 (Entails.sepExists_right 0#64 (Entails.refl _))
    have hgrp : (durationSinceExactHook s0).mem ⊨
        ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2)) ∗
        (memRegion p 16 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hpost_mem ⊢
    have hgrp' := Satisfies.mono (sepConj_mono_left hent) hgrp
    ac_nf at hgrp' ⊢

theorem durationSinceExactHook_epoch_ok : HookOk durationSinceExactHook durationSinceEpochSpec :=
  durationSinceExactHook_epoch_at_ok extHookStack
theorem cliExterns_durationSinceEpoch (W : CliHooks) :
    HookSat (cliExterns W) E2E.durationSinceName durationSinceEpochSpec :=
  ⟨durationSinceExactHook, cliExterns_row W (durationSince_row W), durationSinceExactHook_epoch_ok⟩
theorem durationSinceExactHook_epoch_alloc_ok :
    HookOk durationSinceExactHook durationSinceEpochAllocSpec :=
  durationSinceExactHook_epoch_at_ok allocHookStack
theorem cliExterns_durationSinceEpochAlloc (W : CliHooks) :
    HookSat (cliExterns W) E2E.durationSinceName durationSinceEpochAllocSpec :=
  ⟨durationSinceExactHook, cliExterns_row W (durationSince_row W),
    durationSinceExactHook_epoch_alloc_ok⟩

theorem durationSinceExactHook_bounded_ok :
    HookOk durationSinceExactHook durationSinceBoundedSpec := by
  intro ⟨p, ret⟩ R s0 hrun hpre _hsp
  simp only [durationSinceBoundedSpec, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc, satisfies_sepExists, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨tvSec, tvNsec, ⟨hx0, hx8, hns2⟩, hns1, hmem⟩
  obtain ⟨w2, heval, hkf, hpost_mem⟩ := durationSinceExactHook_step hx0 hx8 hns1 hns2 hmem
  let d := (tvSec.toInt * 1000000000 + ↑tvNsec.toNat -
    ((s0.readReg64 .x1).toInt * 1000000000 + ↑((s0.readReg64 .x2).setWidth 32).toNat)).natAbs
  let tag : BitVec 64 :=
    if (s0.readReg64 .x1).toInt * 1000000000 + ↑((s0.readReg64 .x2).setWidth 32).toNat ≤
       tvSec.toInt * 1000000000 + ↑tvNsec.toNat
    then 0#64 else 1#64
  let secs := BitVec.ofNat 64 (d / 1000000000)
  refine ⟨hkf, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [heval]; rfl
  · rw [heval]; exact ⟨rfl, rfl, hrun⟩
  · rw [heval]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only [durationSinceBoundedSpec]
    have htr : (durationSinceExactHook s0).trace = s0.trace := by rw [heval]; rfl
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hent24 :
        ((ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ secs) ∗ ((ret + 16#64) ↦₆₄ w2)) ⊢ memRegion ret 24 := by
      rw [memRegion_split' (b := ret) (n := 8) (k := 16) (b' := ret + 8#64) rfl rfl (by decide),
          memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64) rfl
            (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion ret tag)
        (sepConj_mono (pointsTo64_entails_memRegion (ret + 8#64) secs)
          (pointsTo64_entails_memRegion (ret + 16#64) w2))
    have hgrp : (durationSinceExactHook s0).mem ⊨
        memRegion p 16 ∗ ((ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ secs) ∗ ((ret + 16#64) ↦₆₄ w2)) ∗
        (stackAt s0.sp extHookStack ∗ R) := by simpa only [sepConj_assoc] using hpost_mem
    simpa only [sepConj_assoc] using
      Satisfies.mono (sepConj_mono_right (sepConj_mono_left hent24)) hgrp

theorem cliExterns_durationSinceBounded (W : CliHooks) :
    HookSat (cliExterns W) E2E.durationSinceName durationSinceBoundedSpec :=
  ⟨durationSinceExactHook, cliExterns_row W (durationSince_row W),
    durationSinceExactHook_bounded_ok⟩

private def durCounterMem : Memory :=
  Memory.ofFn (fun a => if a = 4096#64 then 1#8 else 0#8) (fun _ => some Perm.rw)

private theorem durCounterMem_satisfies (len : Nat) : durCounterMem ⊨ memRegion 4096#64 len :=
  ProofLib.satisfies_memRegion durCounterMem 4096#64 len fun _ _ => rfl

private theorem not_hookOk_zeroTs_at (stk : Nat)
    (hstk : stk ≤ 2 ^ 60)
    (halign : (({ regs := ⟨fun i => if i = 0#5 then 4096#64 else if i = 8#5 then 4112#64 else 0#64⟩
                  sp := 4144#64 + BitVec.ofNat 64 stk, mem := durCounterMem,
                  status := .Running } : State)).spAligned = true) :
    ¬ HookOk durationSinceExactHook
      { pre := fun (p, ret) s =>
          ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗
            memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s.sp stk
        post := fun (p, ret) s0 sf =>
          ⌜sf.trace = s0.trace⌝ ∗
            memRegion p 16 ∗
            ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
              (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
            stackAt s0.sp stk } := by
  intro hok
  let s0 : State :=
    { regs := ⟨fun i => if i = 0#5 then 4096#64 else if i = 8#5 then 4112#64 else 0#64⟩
      sp := 4144#64 + BitVec.ofNat 64 stk, mem := durCounterMem, status := .Running }
  let R : SepProp := memRegion 4136#64 8
  have hmem0 : s0.mem ⊨ memRegion 4096#64 16 ∗ memRegion 4112#64 24 ∗ stackAt s0.sp stk ∗ R := by
    have hbig : s0.mem ⊨ memRegion 4096#64 (16 + (24 + (8 + stk))) :=
      durCounterMem_satisfies (16 + (24 + (8 + stk)))
    rw [memRegion_split 4096#64 16 (24 + (8 + stk)) (by omega),
        show (4096#64 : BitVec 64) + BitVec.ofNat 64 16 = 4112#64 from rfl,
        memRegion_split 4112#64 24 (8 + stk) (by omega),
        show (4112#64 : BitVec 64) + BitVec.ofNat 64 24 = 4136#64 from rfl,
        memRegion_split 4136#64 8 stk (by omega),
        show (4136#64 : BitVec 64) + BitVec.ofNat 64 8 = 4144#64 from rfl] at hbig
    dsimp only [stackAt, s0, R] at hbig ⊢
    rw [BitVec.add_sub_cancel]
    ac_nf at hbig ⊢
  have hpre0 : s0.mem ⊨
      (⌜s0.readReg64 .x0 = 4096#64 ∧ s0.readReg64 .x8 = 4112#64⌝ ∗
        memRegion 4096#64 16 ∗ memRegion 4112#64 24 ∗ stackAt s0.sp stk) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨rfl, rfl⟩, ?_⟩; ac_nf at hmem0 ⊢
  obtain ⟨_, _, hout⟩ := hok (4096#64, 4112#64) R s0 rfl hpre0 halign
  have hmem_cells : s0.mem ⊨ (4096#64 ↦₆₄ 1#64) ∗ ((4096#64 + 8#64) ↦₃₂ 0#32) ∗
      memRegion (4096#64 + 12#64) 4 ∗ memRegion 4112#64 24 ∗ stackAt s0.sp stk ∗ R := by
    have h8 : memRegion (4096#64 + 8#64) 8 =
        memRegion (4096#64 + 8#64) 4 ∗ memRegion (4096#64 + 12#64) 4 :=
      memRegion_split' (b := 4096#64 + 8#64) (n := 4) (k := 4) (b' := 4096#64 + 12#64) rfl
        (by decide) (by decide)
    rw [memRegion_split 4096#64 8 8 (by decide), h8, ProofLib.memRegion_eight 4096#64,
        ProofLib.memRegion_four (4096#64 + 8#64)] at hmem0
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem0
    rcases hmem0 with ⟨ns, sec, hmem0⟩
    have hm_sec : s0.mem ⊨ (4096#64 ↦₆₄ sec) ∗
        (((4096#64 + 8#64) ↦₃₂ ns) ∗ memRegion (4096#64 + 12#64) 4 ∗
         memRegion 4112#64 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem0 ⊢
    have hm_ns : s0.mem ⊨ ((4096#64 + 8#64) ↦₃₂ ns) ∗
        ((4096#64 ↦₆₄ sec) ∗ memRegion (4096#64 + 12#64) 4 ∗
         memRegion 4112#64 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem0 ⊢
    have hsec : sec = 1#64 := by
      have hrd := (IsBlock.pointsTo64 4096#64 sec).read hm_sec
      have hval : s0.mem.read64 4096#64 = 1#64 := by
        dsimp only [s0, durCounterMem, Memory.read64]; simp only [Memory.read8_ofFn]; decide
      exact hrd.symm.trans hval
    have hns : ns = 0#32 := by
      have hrd := (IsBlock.pointsTo32 (4096#64 + 8#64) ns).read hm_ns
      have hval : s0.mem.read32 (4096#64 + 8#64) = 0#32 := by
        dsimp only [s0, durCounterMem, Memory.read32]; simp only [Memory.read8_ofFn]; decide
      exact hrd.symm.trans hval
    subst hsec hns; ac_nf at hmem0 ⊢
  have hx1 : s0.readReg64 .x1 = 0#64 := rfl
  have hx2 : s0.readReg64 .x2 = 0#64 := rfl
  obtain ⟨wReal, heval, _, hpost_real⟩ :=
    durationSinceExactHook_step (p := 4096#64) (ret := 4112#64) (s0 := s0)
      rfl rfl (by decide) (by rw [hx2]; decide) hmem_cells
  have hstat_run : (durationSinceExactHook s0).status = .Running := by rw [heval]; rfl
  rcases hout with ⟨_, _, hpost⟩ | ⟨hpan, _⟩ | ⟨_, htrap, _⟩ | ⟨_, hoom⟩
  · simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨w2, w0, _, hpost_mem⟩
    rw [sepConj_left_comm (4112#64 ↦₆₄ w0), sepConj_left_comm (memRegion 4096#64 16)] at hpost_mem
    have hzero : (durationSinceExactHook s0).mem.read64 (4112#64 + 8#64) = 0#64 :=
      (IsBlock.pointsTo64 (4112#64 + 8#64) 0#64).read hpost_mem
    rw [hx1, hx2] at hpost_real
    have htag0 : (if (0#64 : BitVec 64).toInt * 1000000000 + ↑((0#64 : BitVec 64).setWidth 32).toNat ≤
        (1#64 : BitVec 64).toInt * 1000000000 + ↑(0#32 : BitVec 32).toNat
      then (0#64 : BitVec 64) else 1#64) = 0#64 := by decide
    have hsecs1 : BitVec.ofNat 64 ((((1#64 : BitVec 64).toInt * 1000000000 + ↑(0#32 : BitVec 32).toNat -
        ((0#64 : BitVec 64).toInt * 1000000000 +
          ↑((0#64 : BitVec 64).setWidth 32).toNat)).natAbs) / 1000000000) = 1#64 := by decide
    rw [htag0, hsecs1, sepConj_left_comm (4112#64 ↦₆₄ 0#64),
        sepConj_left_comm (memRegion 4096#64 16)] at hpost_real
    have hone : (durationSinceExactHook s0).mem.read64 (4112#64 + 8#64) = 1#64 :=
      (IsBlock.pointsTo64 (4112#64 + 8#64) 1#64).read hpost_real
    rw [hone] at hzero; exact absurd hzero (by decide)
  · simp [hstat_run] at hpan
  · rw [htrap] at hstat_run; cases hstat_run
  · exact not_satisfies_false_sepConj hoom

theorem cliExterns_not_durationSinceZeroTs (W : CliHooks) :
    ¬ HookSat (cliExterns W) E2E.durationSinceName E2E.Pqxdh.TopLevel.durationSinceZeroTsSpec := by
  rintro ⟨f, hf, hok⟩
  rw [cliExterns_row W (durationSince_row W), Option.some.injEq] at hf
  subst hf; exact not_hookOk_zeroTs_at extHookStack (by decide) (by decide) hok

theorem cliExterns_not_durationSinceZeroTsAlloc (W : CliHooks) :
    ¬ HookSat (cliExterns W) E2E.durationSinceName E2E.Pqxdh.TopLevel.durationSinceZeroTsAllocSpec := by
  rintro ⟨f, hf, hok⟩
  rw [cliExterns_row W (durationSince_row W), Option.some.injEq] at hf
  subst hf; exact not_hookOk_zeroTs_at allocHookStack (by decide) (by decide) hok

end CryptoVerification.SignalSession.Cli.Slots
