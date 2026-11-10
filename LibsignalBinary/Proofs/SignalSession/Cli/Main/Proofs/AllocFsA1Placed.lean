/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.TripleRatchet.Hooks

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Relocatable `AllocContractsFsPlaced` and `AllocContractsXCliPlaced`

Row lookups on `cliHookTablePlaced mmpl W`, Block-`617` (`lsProg_617 H`) stub helpers, and generic
`LibsignalHooks` constructors `AllocContractsFsPlaced.of_hooks` and `AllocContractsXCliPlaced.of_hooks`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed

/-! ## `cliExternsPlaced` Row Lookups (`37` rows) and Block-`617` Stub Plumbing -/

private def mainHookKeysPlaced : List String :=
  ["_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512",
   "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
   "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
   "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
   "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
   "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
   "_RNvCs65XVORQObL2_12libcrux_hmac4hmac",
   "memmove",
   "bcmp",
   "strlen",
   lsWriteFileSym,
   lsWriteStdoutSym,
   lsMemrchrSym,
   lsFromUtf8Sym,
   lsFmtWriteSym,
   lsFormatInnerSym,
   lsDurationSinceSym,
   lsTimeAddSym,
   lsBlackBoxSym,
   lsCompress256Sym,
   lsAesEncSym,
   lsAesDecSym,
   lsPubFromSecretSym,
   lsDiffieHellmanSym,
   lsStaticSecretDropSym,
   lsSharedSecretDropSym]

private theorem mainHookKeysPlaced_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliHookTablePlaced mmpl W).map Prod.fst = mainHookKeysPlaced := rfl

private theorem mainHookKeysPlaced_nodup : mainHookKeysPlaced.Nodup := by
  unfold mainHookKeysPlaced
  decide

private theorem lookup_of_mem_nodup_main {α : Type} :
    ∀ (L : List (String × α)) (n : String) (v : α),
      (L.map Prod.fst).Nodup → (n, v) ∈ L → L.lookup n = some v
  | [], _, _, _, hm => nomatch hm
  | (k, _) :: rest, n, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with hhead | htail
    · cases hhead
      simp [List.lookup]
    · have hne : (n == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(n, v), htail, rfl⟩)
      simp [List.lookup, hne, lookup_of_mem_nodup_main rest n v hnd.2 htail]

theorem main_cliExternsPlaced_row (mmpl : Obj.MultiPlacement) (W : CliHooks) {sym : String}
    {h : State → State} (hm : (sym, h) ∈ cliHookTablePlaced mmpl W)
    (hnp : isCliPanicSymbolPlaced sym = false := by
      simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol,
        lsWriteFileSym, lsWriteStdoutSym, lsMemrchrSym, lsFromUtf8Sym,
        memsetName, memmoveName, memcpyName]) :
    cliExternsPlaced mmpl W sym = some h := by
  unfold cliExternsPlaced
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup_main _ sym h
    (by rw [mainHookKeysPlaced_eq mmpl W]; exact mainHookKeysPlaced_nodup) hm

private theorem lookup_eq_none_of_not_mem_main {α : Type} :
    ∀ (L : List (String × α)) (n : String),
      n ∉ L.map Prod.fst → L.lookup n = none
  | [], _, _ => rfl
  | (k, _) :: rest, n, hnm => by
    rw [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : (n == k) = false := beq_eq_false_iff_ne.mpr hnm.1
    simp [List.lookup, hne, lookup_eq_none_of_not_mem_main rest n hnm.2]

theorem cliExternsPlaced_memset_none (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W memsetName = none := by
  unfold cliExternsPlaced
  have hnp : isCliPanicSymbolPlaced memsetName = false := by
    simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol, memsetName]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_eq_none_of_not_mem_main _ memsetName
    (by rw [mainHookKeysPlaced_eq mmpl W]; decide)

theorem cliExternsPlaced_memmove (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W memmoveName = some hookMemmove :=
  main_cliExternsPlaced_row mmpl W (List.mem_append_right _ (List.mem_of_getElem? (i := 0) rfl))

theorem cliExternsPlaced_memcpy_none (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W memcpyName = none := by
  unfold cliExternsPlaced
  have hnp : isCliPanicSymbolPlaced memcpyName = false := by
    simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol, memcpyName]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_eq_none_of_not_mem_main _ memcpyName
    (by rw [mainHookKeysPlaced_eq mmpl W]; decide)

theorem hook_stub_placed_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {h : State → State} {spec : Spec α}
    (hext : H sym = some h) (hh : HookOk h spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) ⟨h, hext, hh⟩ hmem

theorem cli_stub_placed_ok [LibsignalPlacement] {α : Type} (mmpl : Obj.MultiPlacement)
    (W : CliHooks) {sym : String} {h : State → State} {spec : Spec α}
    (hext : cliExternsPlaced mmpl W sym = some h) (hh : HookOk h spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ sym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  hook_stub_placed_ok hext hh hmem

/-! ## `LibsignalHooks` Constructors and Read-Only `memcpy` -/

/-- Constructs `AllocContractsFsPlaced A H` from `CliAllocHooks A` and canonical hook lookups. -/
theorem AllocContractsFsPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : CliAllocHooks A)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some E2E.allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some E2E.deallocHook)
    (hrealloc : H lsRustReallocSymCli = some E2E.reallocHook0)
    (hmemset : H memsetName = some hookMemset)
    (hmemmove : H memmoveName = some hookMemmove)
    (hmemcpy : H memcpyName = some hookMemcpy) :
    AllocContractsFsPlaced A H where
  alloc := hook_stub_placed_ok halloc <|
    (hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le).keepsFs allocHook0_fs
  dealloc := hook_stub_placed_ok hdealloc <|
    (hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs deallocHook_fs
  realloc := hook_stub_placed_ok hrealloc <|
    (hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le).keepsFs reallocHook0_fs
  shim stk _ _ := hook_stub_placed_ok hshim <|
    (hookOk_withStack sessionShim_hookOk stk).keepsFs hookNoop_fs
  memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookMemcpy_ok stk).keepsFs hookMemcpy_fs
  session_memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookMemcpy_trace_ok stk).keepsFs hookMemcpy_fs
  memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack hookMemcpy_region_ok stk).keepsFs hookMemcpy_fs
  session_memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack hookMemcpy_region_trace_ok stk).keepsFs hookMemcpy_fs
  memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    (hookMemmove_ok stk).keepsFs hookMemmove_fs
  session_memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    (hookMemmove_trace_ok stk).keepsFs hookMemmove_fs
  memset stk hle _ := hook_stub_placed_ok hmemset <|
    (hookMemset_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  session_memset stk hle _ := hook_stub_placed_ok hmemset <|
    (hookMemset_trace_ok stk (pos_of_extHookStack_le hle)).keepsFs hookMemset_fs
  memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    (hookOk_withStack hookMemset_region_ok stk).keepsFs hookMemset_fs
  session_memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    (hookOk_withStack hookMemset_region_trace_ok stk).keepsFs hookMemset_fs
  session_memcpy_region_ro stk _ _ := hook_stub_placed_ok hmemcpy <|
    (hookOk_withStack CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok stk).keepsFs
      hookMemcpy_fs

/-- Constructs `AllocContractsXCliPlaced A H` (without `.keepsFs`) from `CliAllocHooks A` and canonical hook lookups. -/
theorem AllocContractsXCliPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : CliAllocHooks A)
    (hshim : H lsRustNoAllocShimSymCli = some hookNoop)
    (halloc : H lsRustAllocSymCli = some E2E.allocHook0)
    (hdealloc : H lsRustDeallocSymCli = some E2E.deallocHook)
    (hrealloc : H lsRustReallocSymCli = some E2E.reallocHook0)
    (hmemset : H memsetName = some hookMemset)
    (hmemmove : H memmoveName = some hookMemmove)
    (hmemcpy : H memcpyName = some hookMemcpy) :
    AllocContractsXCliPlaced A H where
  alloc := hook_stub_placed_ok halloc <|
    hookOk_rustAllocWithStack (stk := extHookStack) hA.alloc allocHookStack_le_extHookStack
      extHookStack_le
  dealloc := hook_stub_placed_ok hdealloc <|
    hookOk_rustDeallocExternWithStack (stk := extHookStack) hA.dealloc
      allocHookStack_le_extHookStack extHookStack_le
  realloc := hook_stub_placed_ok hrealloc <|
    hookOk_rustReallocExternWithStack (stk := extHookStack) hA.realloc
      allocHookStack_le_extHookStack extHookStack_le
  shim stk _ _ := hook_stub_placed_ok hshim <|
    hookOk_withStack sessionShim_hookOk stk
  memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    hookMemcpy_ok stk
  session_memcpy stk _ _ := hook_stub_placed_ok hmemcpy <|
    hookMemcpy_trace_ok stk
  memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    hookOk_withStack hookMemcpy_region_ok stk
  session_memcpy_region stk _ _ := hook_stub_placed_ok hmemcpy <|
    hookOk_withStack hookMemcpy_region_trace_ok stk
  memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    hookMemmove_ok stk
  session_memmove stk _ _ := hook_stub_placed_ok hmemmove <|
    hookMemmove_trace_ok stk
  memset stk hle _ := hook_stub_placed_ok hmemset <|
    hookMemset_ok stk (pos_of_extHookStack_le hle)
  session_memset stk hle _ := hook_stub_placed_ok hmemset <|
    hookMemset_trace_ok stk (pos_of_extHookStack_le hle)
  memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    hookOk_withStack hookMemset_region_ok stk
  session_memset_region stk _ _ := hook_stub_placed_ok hmemset <|
    hookOk_withStack hookMemset_region_trace_ok stk

/-- Any extern map mapping `memcpyName` to `hookMemcpy` meets
    `SpqrV1.Alloc.sessionMemcpyRegionROSpec`. -/
theorem cli_hookSat_memcpy_region_ro_placed {H : LibsignalHooks}
    (hmemcpy : H memcpyName = some hookMemcpy) :
    HookSat H memcpyName
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  ⟨hookMemcpy, hmemcpy,
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok⟩

theorem subroutine_ok_withLsCodeRoLoaded_of_keepsFs {α : Type} {P : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok P entry (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec.keepsFs)) :
    subroutine_ok P entry (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

theorem AllocContractsFsPlaced.toAllocContractsX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsFsPlaced A H) : AllocContractsXCliPlaced A H where
  alloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.alloc
  dealloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.dealloc
  realloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.realloc
  shim stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.shim stk h1 h2)
  memcpy stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy stk h1 h2)
  session_memcpy stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy stk h1 h2)
  memcpy_region stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy_region stk h1 h2)
  session_memcpy_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy_region stk h1 h2)
  memmove stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memmove stk h1 h2)
  session_memmove stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memmove stk h1 h2)
  memset stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset stk h1 h2)
  session_memset stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset stk h1 h2)
  memset_region stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset_region stk h1 h2)
  session_memset_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset_region stk h1 h2)

end CryptoVerification.SignalSession.Cli.MainHops
