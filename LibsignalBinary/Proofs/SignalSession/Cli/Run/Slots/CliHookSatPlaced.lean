/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
public import LibsignalBinary.Proofs.TripleRatchet.Hooks
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
public import LibsignalBinary.Proofs.SessionRecordMin.Deserialize
public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.AesCbc.Bytes

/-!
# Relocatable `cliHookTablePlaced`, `cliExternsPlaced`, and `cliGhostExterns` Contracts

Row-membership and `HookSat` contracts for the 39 mangled rows of `cliHookTablePlaced mmpl W` and
18 panic symbols of `cliPanicSymbolsPlaced` under `[LibsignalPlacement]`, together with
`cliGhostExterns` lifts (`CliGhostA0Hooks`, `a0Ghost`) and placed allocator/codec hook bundles.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet hookSat_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)

/-! ## 1. Mangled symbol abbreviations for `cliPqxdhHookTablePlaced` -/

abbrev lsCompress512SymCli : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512"
abbrev lsToEdwardsSymCli : String :=
  "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"
abbrev lsCompressSymCli : String :=
  "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress"
abbrev lsEdNegSymCli : String :=
  "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg"
abbrev lsTorsionFreeSymCli : String :=
  "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free"
abbrev lsDsmbSymCli : String :=
  "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint"
abbrev lsScalarModSymCli : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order"
abbrev lsScalarWideSymCli : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide"
abbrev lsKemEncapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"
abbrev lsKemDecapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"
abbrev lsMlkemFromSeedSymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"
abbrev lsMlkemPk1SymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1"
abbrev lsMlkemPk2SymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2"
abbrev lsMlkemEncaps1SymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"
abbrev lsMlkemEncaps2SymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2"
abbrev lsMlkemDecapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"
abbrev lsMlkemValidatePkSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
abbrev lsLibcruxHmacSymCli : String :=
  "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"
abbrev lsGrowOneU8SymCli : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVechE8grow_oneB7_"
abbrev lsGrowOneVecU8SymCli : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVecINtNtB7_3vec3VechEE8grow_oneCsfr5T3GFabw_3std"

/-! ## 2. Row membership and `cliExternsPlaced` lookups -/

-- Left `18` rows (`cliPqxdhHookTablePlaced mmpl W.C W.Q`):
theorem compress512_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsCompress512SymCli, E2E.compress512Hook W.Q.F512) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)
theorem toEdwards_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsToEdwardsSymCli, E2E.toEdwardsHook W.Q.montToEd) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl)
theorem compress_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsCompressSymCli, E2E.compressHook W.Q.compress) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl)
theorem edNeg_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsEdNegSymCli, E2E.edNegHook W.Q.edNeg) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 3) rfl)
theorem torsionFree_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsTorsionFreeSymCli, E2E.torsionFreeHook W.Q.isTorsionFree) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 4) rfl)
theorem dsmb_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsDsmbSymCli, E2E.dsmbHook W.Q.dsmb) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 5) rfl)
theorem scalarMod_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsScalarModSymCli, E2E.scalarModHook W.Q.scalarMod) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 6) rfl)
theorem scalarWide_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsScalarWideSymCli, E2E.scalarWideHook W.Q.scalarWide) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 7) rfl)
theorem kemEncaps_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsKemEncapsSymCli, E2E.kemEncapsHook W.Q.encaps) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 8) rfl)
theorem kemDecaps_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsKemDecapsSymCli, E2E.kemDecapsHook W.Q.decaps) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 9) rfl)
theorem mlkemFromSeed_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemFromSeedSymCli, E2E.mlkemFromSeedHook W.Q.K) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 10) rfl)
theorem mlkemPk1_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemPk1SymCli, E2E.mlkemPk1Hook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl)
theorem mlkemPk2_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemPk2SymCli, E2E.mlkemPk2Hook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl)
theorem mlkemEncaps1_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemEncaps1SymCli, E2E.mlkemEncaps1Hook W.Q.K) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 13) rfl)
theorem mlkemEncaps2_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemEncaps2SymCli, E2E.mlkemEncaps2Hook W.Q.K) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 14) rfl)
theorem mlkemDecaps_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemDecapsSymCli, E2E.mlkemDecapsHook W.Q.K) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 15) rfl)
theorem mlkemValidatePk_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMlkemValidatePkSymCli, E2E.mlkemValidatePkHook W.Q.K) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 16) rfl)
theorem libcruxHmac_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsLibcruxHmacSymCli, E2E.libcruxHmacHookMallocng mmpl W.C.F) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_left _ (List.mem_of_getElem? (i := 17) rfl)

-- Right `19` rows (`18 + 19 = 37` rows):
theorem memmove_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ("memmove", hookMemmove) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 0) rfl)
-- index 1 is `RunGlue.bcmp_row_placed`
theorem strlen_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ("strlen", strlenHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 2) rfl)
theorem writeFile_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsWriteFileSym, writeFileHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 3) rfl)
theorem writeStdout_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsWriteStdoutSym, writeStdoutHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 4) rfl)
theorem memrchr_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsMemrchrSym, memrchrHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 5) rfl)
theorem fromUtf8_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsFromUtf8Sym, fromUtf8Hook W.utf8Err) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 6) rfl)
theorem fmtWrite_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsFmtWriteSym, E2E.fmtWriteHook0) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 7) rfl)
theorem formatInner_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsFormatInnerSym, E2E.formatInnerHook0) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 8) rfl)
theorem durationSince_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsDurationSinceSym, durationSinceExactHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 9) rfl)
theorem timeAdd_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsTimeAddSym, E2E.timeAddHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 10) rfl)
theorem blackBox_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsBlackBoxSym, LibsignalSession.blackBoxHook) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)
theorem compress256_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsCompress256Sym, LibsignalHmac.compress256Hook W.C.F) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 12) rfl)
theorem aesEnc_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsAesEncSym, E2E.aesEncHookMallocng mmpl W.C.E) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 13) rfl)
theorem aesDec_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsAesDecSym, E2E.aesDecHookMallocng mmpl W.C.D) ∈ cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 14) rfl)
theorem pubFromSecret_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsPubFromSecretSym, LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey) ∈
      cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 15) rfl)
theorem diffieHellman_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsDiffieHellmanSym, LibsignalTripleRatchet.diffieHellmanHook W.C.X) ∈
      cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 16) rfl)
theorem staticSecretDrop_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsStaticSecretDropSym, LibsignalTripleRatchet.zeroizeSecretHook) ∈
      cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 17) rfl)
theorem sharedSecretDrop_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsSharedSecretDropSym, LibsignalTripleRatchet.zeroizeSecretHook) ∈
      cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 18) rfl)

theorem cliExternsPlaced_fromUtf8_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsFromUtf8Sym = some (fromUtf8Hook W.utf8Err) :=
  cliExternsPlaced_row mmpl W (fromUtf8_row_placed mmpl W)

theorem cliExternsPlaced_memrchr_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsMemrchrSym = some memrchrHook :=
  cliExternsPlaced_row mmpl W (memrchr_row_placed mmpl W)

theorem cliGhostExterns_fromUtf8_eq (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsFromUtf8Sym = some (fromUtf8Hook W.utf8Err) :=
  (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_fromUtf8_eq mmpl W)

theorem cliGhostExterns_memrchr_eq (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsMemrchrSym = some memrchrHook :=
  (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_memrchr_eq mmpl W)

/-! ## 3. Panic symbols of `cliPanicSymbolsPlaced` -/

theorem cliExternsPlaced_panic_all (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ sym ∈ cliPanicSymbolsPlaced, cliExternsPlaced mmpl W sym = some Rust.panicked :=
  fun _ hmem => cliExternsPlaced_panic_of_mem mmpl W hmem

theorem cliGhostExterns_panic_all (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    ∀ sym ∈ cliPanicSymbolsPlaced,
      cliGhostExterns g (cliExternsPlaced mmpl W) sym = some Rust.panicked :=
  fun _ hmem => cliGhostExterns_panic_of_mem mmpl g W hmem

theorem cliExternsPlaced_panic_assert_jj (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_assert_yy (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_handle_alloc_error (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_handle_error (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_option_expect_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6option13expect_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_option_unwrap_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_result_unwrap_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_bounds_check (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_assert_failed_inner (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_panic (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking5panic" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_panic_fmt (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_slice_index_fail (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_add_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_mul_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_shl_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_sub_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_async_fn_resumed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_vec_remove_assert_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)

theorem cliGhostExterns_panic_handle_alloc_error (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)
theorem cliGhostExterns_panic_handle_error (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)
theorem cliGhostExterns_panic_option_expect_failed (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCskxtBwYRO61I_4core6option13expect_failed" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)

/-! ## 4. `A0` ghost-hook bundle and `HookSat` contracts -/

/-- `RustAlloc` ghost-hook hypothesis bundle on `g : CliGhostHooks`, including `memset` and `memcpy` consumer contracts on the 37-row `cliHookTablePlaced`. -/
structure CliGhostA0Hooks (A : RustAlloc) (g : CliGhostHooks) : Prop where
  alloc : HookOk g.alloc (rustAllocSpec A)
  allocNW : HookOk g.alloc (E2E.HooksE.rustAllocNWSpec A)
  dealloc : HookOk g.dealloc (rustDeallocSpec A)
  realloc : HookOk g.realloc (rustReallocSpec A)
  allocZeroed : HookOk g.allocZeroed (rustAllocZeroedSpec A)
  alloc_fs : ∀ s : State, (g.alloc s).fs = s.fs
  dealloc_fs : ∀ s : State, (g.dealloc s).fs = s.fs
  realloc_fs : ∀ s : State, (g.realloc s).fs = s.fs
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed
  shim_eq : g.shim = hookNoop := by rfl
  memset : ∃ f, g.memset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy : ∃ f, g.memcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec ∧
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy_exact : ∀ f, g.memcpy = some f → HookExactMemcpy f

/-- Canonical `E2E.HooksE.A0` instantiation of `CliGhostHooks` (no replay obligation). -/
noncomputable def a0Ghost : CliGhostHooks where
  alloc := E2E.allocHook0
  dealloc := E2E.deallocHook
  realloc := E2E.reallocHook0
  allocZeroed := E2E.allocZeroedHook0
  shim := hookNoop
  stringClone := some E2E.stringCloneHook0
  memset := some hookMemset
  memcpy := some hookMemcpy

theorem cliGhostA0Hooks_a0Ghost : CliGhostA0Hooks E2E.HooksE.A0 a0Ghost where
  alloc := E2E.HooksE.allocHook0_ok
  allocNW := E2E.HooksE.allocHook0_nw_ok
  dealloc := E2E.HooksE.deallocHook_ok
  realloc := E2E.HooksE.reallocHook0_ok
  allocZeroed := E2E.HooksE.allocZeroedHook0_ok
  alloc_fs := allocHook0_fs
  dealloc_fs := deallocHook_fs
  realloc_fs := reallocHook0_fs
  alloc_fsT := allocHook0_fsT
  dealloc_fsT := deallocHook_fsT
  realloc_fsT := reallocHook0_fsT
  allocZeroed_fsT := allocZeroedHook0_fsT
  shim_eq := rfl
  memset := ⟨hookMemset, rfl, fun stk hpos => hookMemset_ok stk hpos,
    fun stk hpos => hookMemset_trace_ok stk hpos, hookMemset_region_ok,
    hookMemset_region_trace_ok, hookMemset_fs, hookMemset_fsT⟩
  memcpy := ⟨hookMemcpy, rfl, fun stk => hookMemcpy_ok stk, fun stk => hookMemcpy_trace_ok stk,
    hookMemcpy_region_ok, hookMemcpy_region_trace_ok,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpy_hookOk,
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok, hookMemcpy_fs, hookMemcpy_fsT⟩
  memcpy_exact := fun f hf => by cases hf; exact hookMemcpy_exact

theorem cliGhostExterns_a0_exactMemcpy_sat (baseExt : LibsignalHooks) {A : RustAlloc}
    {g : CliGhostHooks} (hG : CliGhostA0Hooks A g) :
    HookSatExactMemcpy (cliGhostExterns g baseExt) "memcpy" := by
  obtain ⟨f, hf, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hG.memcpy_exact f hf⟩

/-- Post-F3 `A2''` bridge: `CliGhostA0Hooks` discharges `HkdfPlacedHooksExactSat` on
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := by
      obtain ⟨f, hf, _, _, _, hok, _, _⟩ := hG.memset
      exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩
    memcpy := cliGhostExterns_a0_exactMemcpy_sat (cliExternsPlaced mmpl W) hG
    compress256 :=
      (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)) }

/-- `Rust.withPanics` specialization of `HkdfPlacedHooksExactSat.of_a0Hooks`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks_withPanics
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [RunGlue.withPanics_cliGhostExterns mmpl g W]
  exact HkdfPlacedHooksExactSat.of_a0Hooks hG

/-- Variant-extern lift of `HkdfPlacedHooksExactSat.of_a0Hooks` (covers any `H` agreeing with
    `cliGhostExterns g (cliExternsPlaced mmpl W)` outside RNG). -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks_ext
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) {H : LibsignalHooks}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns g (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksExactSat W.C.F H := by
  have hBase : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_a0Hooks hG
  refine { memset := ?_, memcpy := ?_, compress256 := ?_ }
  · obtain ⟨f, hf, hok⟩ := hBase.memset
    exact ⟨f, (hExt lsMemsetSym (by decide)).trans hf, hok⟩
  · obtain ⟨f, hf, hex⟩ := hBase.memcpy
    exact ⟨f, (hExt lsMemcpySym (by decide)).trans hf, hex⟩
  · exact (hExt lsCompress256Sym (by decide)).trans hBase.compress256

theorem cliGhostA0Hooks_to_fs {A : RustAlloc} {g : CliGhostHooks}
    (hG : CliGhostA0Hooks A g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f) :
    CliGhostHooksFs g where
  alloc_fsT := hG.alloc_fsT
  dealloc_fsT := hG.dealloc_fsT
  realloc_fsT := hG.realloc_fsT
  allocZeroed_fsT := hG.allocZeroed_fsT
  shim_fsT := hG.shim_eq ▸ hookNoop_fsT
  stringClone_fsT := hStrFsT
  memset_fsT := by
    obtain ⟨f₀, hf₀, _, _, _, _, _, hfsT⟩ := hG.memset
    intro f hf
    cases hf₀.symm.trans hf
    exact hfsT
  memcpy_fsT := by
    obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, hfsT⟩ := hG.memcpy
    intro f hf
    cases hf₀.symm.trans hf
    exact hfsT

theorem a0Ghost_stringClone_fsT :
    ∀ f, a0Ghost.stringClone = some f → HookFsTraced IsFsC f := by
  intro f hf
  cases hf
  exact stringCloneHook0_fsT

theorem a0Ghost_stringClone_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliGhostExterns a0Ghost (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec E2E.HooksE.A0) :=
  ⟨E2E.stringCloneHook0, cliGhostExterns_stringClone_some a0Ghost _ rfl,
    E2E.HooksE.stringCloneHook0_ok⟩

/-- Lifts `HookSat (cliExternsPlaced mmpl W) sym spec` on a non-ghost symbol `sym` to `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliGhostExterns_sat_of_cliExternsPlaced {α : Type}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {spec : Spec α}
    (hsat : HookSat (cliExternsPlaced mmpl W) sym spec)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) sym spec :=
  hookSat_of_eq (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) hsat

theorem cliGhostExterns_readFile_sat {α : Type} (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {rfh : State → State} {hrfh : HookFsTraced IsFsC rfh} {spec : Spec α}
    (hg : g.readFile = some ⟨rfh, hrfh⟩) (hok : HookOk rfh spec) :
    HookSat (cliGhostExterns g baseExt) lsReadFileSym spec :=
  ⟨rfh, RunGlue.cliGhostExterns_readFile_some g baseExt hg, hok⟩

theorem cliGhostExterns_readStdin_sat {α : Type} (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {rsh : State → State} {hrsh : HookFsTraced IsFsC rsh} {spec : Spec α}
    (hg : g.readStdin = some ⟨rsh, hrsh⟩) (hok : HookOk rsh spec) :
    HookSat (cliGhostExterns g baseExt) lsReadStdinSym spec :=
  ⟨rsh, RunGlue.cliGhostExterns_readStdin_some g baseExt hg, hok⟩

-- Allocator & shim (`cliGhostExterns g (cliExternsPlaced mmpl W)`):
theorem cliExternsPlaced_shim_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli sessionShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim), sessionShim_hookOk⟩

theorem cliExternsPlaced_noAllocShim_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli noAllocShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim), noAllocShim_hookOk⟩

theorem cliExternsPlaced_alloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli (rustAllocSpec A) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.alloc⟩

theorem cliExternsPlaced_allocNW_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli
      (E2E.HooksE.rustAllocNWSpec A) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.allocNW⟩

theorem cliExternsPlaced_dealloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSymCli (rustDeallocSpec A) :=
  ⟨g.dealloc, cliGhostExterns_dealloc g _, hG.dealloc⟩

theorem cliExternsPlaced_realloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustReallocSymCli (rustReallocSpec A) :=
  ⟨g.realloc, cliGhostExterns_realloc g _, hG.realloc⟩

theorem cliExternsPlaced_allocZeroed_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocZeroedSymCli
      (rustAllocZeroedSpec A) :=
  ⟨g.allocZeroed, cliGhostExterns_allocZeroed g _, hG.allocZeroed⟩

-- libc memory & string ops (`cliGhostExterns g` for `memset`/`memcpy`, `cliExternsPlaced` for rest):
theorem cliExternsPlaced_memset_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (libcMemsetSpec stk) := by
  obtain ⟨f, hf, hok, _, _, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok stk hpos⟩

theorem cliExternsPlaced_sessionMemset_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (sessionMemsetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok stk hpos⟩

theorem cliExternsPlaced_memsetRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" memsetRegionSpec := by
  obtain ⟨f, hf, _, _, hok, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩

theorem cliExternsPlaced_sessionMemsetRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩

theorem cliExternsPlaced_memmove_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) "memmove" (libcMemmoveSpec stk) :=
  ⟨hookMemmove, cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W), hookMemmove_ok stk⟩

theorem cliExternsPlaced_sessionMemmove_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) "memmove" (sessionMemmoveSpec stk) :=
  ⟨hookMemmove, cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W), hookMemmove_trace_ok stk⟩

theorem cliExternsPlaced_memcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (libcMemcpySpec stk) := by
  obtain ⟨f, hf, hok, _, _, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok stk⟩

theorem cliExternsPlaced_sessionMemcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (sessionMemcpySpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok stk⟩

theorem cliExternsPlaced_memcpyRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" memcpyRegionSpec := by
  obtain ⟨f, hf, _, _, hok, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_sessionMemcpyRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" sessionMemcpyRegionSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_framelessMemcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec := by
  obtain ⟨f, hf, _, _, _, _, hok, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_memcpyRegionRO_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec := by
  obtain ⟨f, hf, _, _, _, _, _, hok, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_bcmp_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) "bcmp" cliBcmpSpec :=
  RunGlue.cli_hookSat_bcmp_placed mmpl W

theorem cliExternsPlaced_bcmpVregs_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) "bcmp" E2E.HooksE.bcmpVregsSpec :=
  ⟨cliBcmpHook W.bcmp, cliExternsPlaced_bcmp mmpl W, cliBcmpHook_vregs_ok W⟩

theorem cliExternsPlaced_e2eBcmp_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) "bcmp" E2E.HooksE.e2eBcmpSpec :=
  ⟨cliBcmpHook W.bcmp, cliExternsPlaced_bcmp mmpl W,
    E2E.HooksE.hookOk_bcmpSpec_of_vregs (cliBcmpHook_vregs_ok W)⟩

theorem cliExternsPlaced_strlen_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) "strlen" (strlenSpec stk) :=
  ⟨strlenHook, cliExternsPlaced_row mmpl W (strlen_row_placed mmpl W), strlenHook_ok stk⟩

theorem cliExternsPlaced_memrchr_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsMemrchrSym (memrchrSpec stk) :=
  ⟨memrchrHook, cliExternsPlaced_row mmpl W (memrchr_row_placed mmpl W), memrchrHook_ok stk⟩

theorem cliExternsPlaced_fromUtf8_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsFromUtf8Sym (fromUtf8AsciiSpec stk) :=
  ⟨fromUtf8Hook W.utf8Err, cliExternsPlaced_row mmpl W (fromUtf8_row_placed mmpl W),
    fromUtf8Hook_ok stk W.utf8Err⟩

theorem cliExternsPlaced_readFile_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hRead : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  cliReadFilePlaced_hookSat mmpl g W stk hRead

theorem cliWriteStdoutHook_ok_placed (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpecPlaced stk) := by
  intro x R s0 hrun hpre _
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1⟩, hmem⟩ := hpre
  obtain ⟨hlen, hrd⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.buf x.bs).canRead hlen hmem
  rw [← hx0] at hrd hcan
  rw [writeStdoutHook_eq hx1 hcan hrd]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl, List.prefix_append _ _, ?_⟩, hmem⟩
  change Process.ProcessOutcome.traceStreamBytes .stdout
    (s0.trace ++ TraceEvent.ofBytes .stdout x.bs) = _
  rw [MainHops.traceStreamBytes_append, MainHops.traceStreamBytes_ofBytes_stdout]

private theorem cliWriteFile_outcome_placed {stk : Nat} {x : WriteFileGhost} {R : SepProp}
    {s0 : State} {ok : Bool} {fs' : FsState} (hrun : s0.status = .Running)
    (hmem : s0.mem ⊨ (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ R)
    (hpost :
      let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
      match cliIo.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) :
    let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (writeFileSpecPlaced cliIo stk) x R s0 sf := by
  intro sf
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpost, List.prefix_append _ _, ?_⟩, hmem⟩
  change Process.ProcessOutcome.traceStreamBytes .stdout
    (s0.trace ++ [.fileChanged (pathStr x.path)]) = _
  rw [MainHops.traceStreamBytes_append, MainHops.traceStreamBytes_fileChanged, List.append_nil]

theorem cliWriteFileHook_ok_placed (stk : Nat) :
    HookOk writeFileHook (writeFileSpecPlaced cliIo stk) := by
  intro x R s0 hrun hpre _
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemB : s0.mem ⊨ (x.buf ↦ₛ x.bs) ∗ (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ R := by
    rw [sepConj_left_comm]; exact hmem
  obtain ⟨hlenB, hrdB⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmemB
  have hcanB := (IsBlock.pointsToBytes x.buf x.bs).canRead hlenB hmemB
  rw [← hx0] at hrdP hcanP
  rw [← hx2] at hrdB hcanB
  rw [writeFileHook_eq hx1 hx3 (by rw [hcanP, hcanB]; rfl) hrdP hrdB hpok' hpok.2.2]
  simp only
  cases hA : blockingAncestorF s0.fs.files (pathStr x.path) with
  | some _ =>
    exact cliWriteFile_outcome_placed hrun hmem (by simp only [cliIo, cliWr, hA]; exact ⟨rfl, rfl⟩)
  | none =>
    cases hB : s0.fs.files (pathStr x.path) with
    | none =>
      exact cliWriteFile_outcome_placed hrun hmem
        (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)
    | some e =>
      cases e with
      | dir =>
        exact cliWriteFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, rfl⟩)
      | file _ =>
        exact cliWriteFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)

theorem cliReadStdinHook_ok_placed (stk : Nat) :
    HookOk readStdinHook (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  refine hookOk_of_on (c := ReadStdinOom) ?_ ?_
  · intro x R s0 ⟨hcap, hne, hnone⟩ _ hpre0 _
    have hpre := hpre0
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
    rw [← hx8] at hcanW
    obtain ⟨fs', -, heq⟩ := readStdinHook_eq hcanW hin
    simp only [hcap, ↓reduceIte] at heq
    rw [heq, vecOk_oom (s := s0.setFs fs') hne hnone]
    refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    change s0.mem ⊨ (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk).onPanic x s0
      (E2E.allocPanicHook (s0.setFs fs')) ∗ R
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨E2E.HooksE.HooksOkAux.allocFailedIn_allocPanicHook (s0.setFs fs'),
      E2E.HooksE.HooksOkAux.trace_prefix_allocPanicHook (s0.setFs fs')⟩,
      Satisfies.mono (sepConj_mono_left (Entails.top_right fun _ => trivial)) hpre0⟩
  · intro x R s0 hnoom hrun hpre _
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
    rw [← hx8] at hcanW
    obtain ⟨fs', hfs', heq⟩ := readStdinHook_eq hcanW hin
    by_cases hcap : x.bs.length ≤ stdinCapBytes
    · simp only [hcap, ↓reduceIte] at heq
      have hfit : x.bs ≠ [] → E2E.bumpAddr? (s0.setFs fs').mem x.bs.length 1 ≠ none :=
        fun hne hnone => hnoom ⟨hcap, hne, hnone⟩
      obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok (s := s0.setFs fs') hx8 hmem hfit
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.ok x.bs, ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
      simp only [ioVecAt] at hm ⊢
      exact hm
    · simp only [hcap, ↓reduceIte] at heq
      obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok (s := s0.setFs fs') hx8 hmem
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.error (), ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
      simp only [ioVecAt, sepConj_assoc] at hm ⊢
      exact hm

theorem cliReadFileLitHook_ok_placed (stk : Nat) :
    HookOk readFileHook (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  refine hookOk_of_on (c := ReadFileOom) ?_ ?_
  · intro x R s0 hoom hrun hpre0 hsp
    have hpre := hpre0
    simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
    have hpok' : PathOk (pathStr x.path) = true := hpok.1
    have hlenP : x.path.length ≤ 2 ^ 64 := by omega
    have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
    have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
    have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
        ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
      rw [sepConj_left_comm]; exact hmem
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
    rw [← hx0] at hrdP hcanP
    rw [← hx8] at hcanW
    have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
      readPath_eq_pathStr hx1 hrdP
    have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
      (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
    rw [hp] at heq
    obtain ⟨bs, hv, hne, hnone⟩ := hoom
    rw [hv] at heq
    dsimp only at heq
    rw [heq, vecOk_oom hne hnone]
    exact E2E.HooksE.HooksOkAux.allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp
  · intro x R s0 hnoom hrun hpre _
    simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
    have hpok' : PathOk (pathStr x.path) = true := hpok.1
    have hlenP : x.path.length ≤ 2 ^ 64 := by omega
    have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
    have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
    have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
        ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
      rw [sepConj_left_comm]; exact hmem
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
    rw [← hx0] at hrdP hcanP
    rw [← hx8] at hcanW
    have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
      readPath_eq_pathStr hx1 hrdP
    have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
      (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
    rw [hp] at heq
    have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
        cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
      intro r hr
      show cliRd s0.fs.files x.path = _
      unfold cliRd
      rw [← readView_eq_readViewF, hr]; rfl
    cases hv : readView s0.fs (pathStr x.path) with
    | none =>
      rw [hv] at heq
      dsimp only at heq
      obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.error (), ⟨rfl, (hrd none hv).symm, rfl⟩, ?_⟩
      simp only [ioVecAt, sepConj_assoc] at hm ⊢
      exact hm
    | some bs =>
      rw [hv] at heq
      dsimp only at heq
      have hfit : bs ≠ [] → E2E.bumpAddr? s0.mem bs.length 1 ≠ none :=
        fun hne hnone => hnoom ⟨bs, hv, hne, hnone⟩
      obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok hx8 hmemR hfit
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.ok bs, ⟨rfl, (hrd (some bs) hv).symm, rfl⟩, ?_⟩
      simp only [ioVecAt] at hm ⊢
      exact hm

theorem cliExternsPlaced_readFileLit_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hReadLit : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hReadLit

theorem cliExternsPlaced_writeFile_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteFileSym (writeFileSpecPlaced cliIo stk) :=
  ⟨writeFileHook, cliExternsPlaced_row mmpl W (writeFile_row_placed mmpl W),
    cliWriteFileHook_ok_placed stk⟩

theorem cliExternsPlaced_readStdin_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hStdin

theorem cliExternsPlaced_writeStdout_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteStdoutSym (writeStdoutSpecPlaced stk) :=
  ⟨writeStdoutHook, cliExternsPlaced_row mmpl W (writeStdout_row_placed mmpl W),
    cliWriteStdoutHook_ok_placed stk⟩

/-- Single-block `sha2::sha256::compress256` contract (`x2 = 1#64`). -/
def compress256SingleSpec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8)) where
  pre := fun (stA, st, blkA, blk) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ s.readReg64 .x2 = 1#64 ∧
      blk.length = 64⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ (blkA ↦ₛ blk)
  post := fun (stA, st, blkA, blk) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes (F st blk)) ∗ (blkA ↦ₛ blk)

theorem compress256Hook_single_ok (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (LibsignalHmac.compress256Hook F) (compress256SingleSpec F) := by
  intro ⟨stA, st, blkA, blk⟩ R s0 hrun hpre _
  simp only [compress256SingleSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hblk_len⟩, hmem⟩
  have hst_len : (LibsignalHmac.shaStateBytes st).length = 32 := by
    simp [LibsignalHmac.shaStateBytes]
  have hst_rd : s0.mem.readBytes stA 32 = LibsignalHmac.shaStateBytes st := by
    have hrd := ((IsBlock.pointsToBytes stA (LibsignalHmac.shaStateBytes st)).read hmem).2
    rwa [hst_len] at hrd
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ blk) ∗ ((stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ R) := by
    ac_nf at hmem ⊢
  have hblk_rd : s0.mem.readBytes blkA 64 = blk := by
    have hrd := ((IsBlock.pointsToBytes blkA blk).read hmem_blk).2
    rwa [hblk_len] at hrd
  have heq :=
    LibsignalSession.CryptoHmacSha256.compress256Hook_one_eq F hx0 hx1 hx2 rfl rfl hst_rd hblk_rd
  let outBytes := LibsignalHmac.shaStateBytes (F st blk)
  have hout_len : outBytes.length = 32 := by simp [outBytes, LibsignalHmac.shaStateBytes]
  have hmem_reg : s0.mem ⊨ memRegion stA outBytes.length ∗ ((blkA ↦ₛ blk) ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans (pointsToBytes_entails_memRegion stA _)
        (by rw [hst_len]; exact Entails.refl _)))
      hmem
  have hlen32 : outBytes.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  rw [heq]
  refine ⟨keepsFrozen_writeBytes_of_memRegion outBytes hlen32 hmem_reg,
    rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [compress256SingleSpec, State.trace_setPC, State.setMem, sepConj_assoc,
    satisfies_pure_sepConj, true_and]
  exact satisfies_writeBytes outBytes hlen32 hmem_reg

theorem cliExternsPlaced_compress256Multi_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsCompress256Sym (compress256Spec W.C.F) :=
  ⟨LibsignalHmac.compress256Hook W.C.F,
    cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W),
    compress256Hook_ok W.C.F⟩

theorem cliExternsPlaced_compress256_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsCompress256Sym (compress256SingleSpec W.C.F) :=
  ⟨LibsignalHmac.compress256Hook W.C.F,
    cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W),
    compress256Hook_single_ok W.C.F⟩

theorem cliExternsPlaced_compress256 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsCompress256Sym = some (LibsignalHmac.compress256Hook W.C.F) :=
  cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)

-- `alloc`, `core::fmt`, `std::time`, `subtle`:
theorem cliExternsPlaced_stringClone_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym (stringCloneSpec A) :=
  hStrClone

theorem cliExternsPlaced_fmtWrite_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsFmtWriteSym (fmtWriteSpec E2E.HooksE.A0) :=
  ⟨E2E.fmtWriteHook0, cliExternsPlaced_row mmpl W (fmtWrite_row_placed mmpl W),
    E2E.HooksE.fmtWriteHook0_ok⟩

theorem cliExternsPlaced_formatInner_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsFormatInnerSym (formatInnerSpec E2E.HooksE.A0) :=
  ⟨E2E.formatInnerHook0, cliExternsPlaced_row mmpl W (formatInner_row_placed mmpl W),
    E2E.HooksE.formatInnerHook0_ok⟩

theorem cliExternsPlaced_durationSinceEpoch_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDurationSinceSym durationSinceEpochSpec :=
  ⟨durationSinceExactHook, cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W),
    durationSinceExactHook_epoch_ok⟩

theorem cliExternsPlaced_durationSinceEpochAlloc_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDurationSinceSym durationSinceEpochAllocSpec :=
  ⟨durationSinceExactHook, cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W),
    durationSinceExactHook_epoch_alloc_ok⟩

theorem cliExternsPlaced_durationSinceBounded_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDurationSinceSym
      (withLsRet durationSinceBoundedSpec) :=
  hookSat_withLsRet ⟨durationSinceExactHook,
    cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W),
    durationSinceExactHook_bounded_ok⟩

theorem cliExternsPlaced_timeAdd_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsTimeAddSym (withLsRet timeAddSpec) :=
  hookSat_withLsRet ⟨E2E.timeAddHook,
    cliExternsPlaced_row mmpl W (timeAdd_row_placed mmpl W),
    E2E.HooksE.timeAddHook_ok⟩

theorem blackBoxHook_ok :
    HookOk LibsignalSession.blackBoxHook LibsignalSession.FindReceiverChainIndex.blackBoxSpec := by
  have hsat : HookSat (fun _ => some LibsignalSession.blackBoxHook)
      "subtle::black_box::<u8>" LibsignalSession.FindReceiverChainIndex.blackBoxSpec :=
    LibsignalSession.FindReceiverChainIndex.blackBoxHook_sat rfl
  rcases hsat with ⟨f, hf, hok⟩
  cases hf
  exact hok

theorem cliExternsPlaced_blackBox_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsBlackBoxSym
      LibsignalSession.FindReceiverChainIndex.blackBoxSpec :=
  ⟨LibsignalSession.blackBoxHook, cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W),
    blackBoxHook_ok⟩

-- AES-CBC & X25519:
theorem cliExternsPlaced_aesEnc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hAesEnc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesEncSym (aesEncSpec W.C.E A) :=
  hAesEnc

theorem cliExternsPlaced_aesDec_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hAesDec : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym (aesDecSpec W.C.D A) :=
  hAesDec

theorem cliExternsPlaced_pubFromSecret_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsPubFromSecretSym (pubFromSecretSpec W.C.pubKey) :=
  ⟨LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey,
    cliExternsPlaced_row mmpl W (pubFromSecret_row_placed mmpl W), pubFromSecretHook_ok W.C.pubKey⟩

theorem cliExternsPlaced_derivePublicKeyBytes_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsPubFromSecretSym (derivePublicKeyBytesSpec W.C.pubKey) :=
  ⟨LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey,
    cliExternsPlaced_row mmpl W (pubFromSecret_row_placed mmpl W), pubFromSecret_hookOk W.C.pubKey⟩

theorem cliExternsPlaced_diffieHellman_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDiffieHellmanSym (diffieHellmanSpec W.C.X) :=
  ⟨LibsignalTripleRatchet.diffieHellmanHook W.C.X,
    cliExternsPlaced_row mmpl W (diffieHellman_row_placed mmpl W), diffieHellmanHook_ok W.C.X⟩

theorem cliExternsPlaced_staticSecretDrop_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsStaticSecretDropSym zeroizeSecretSpec :=
  ⟨LibsignalTripleRatchet.zeroizeSecretHook,
    cliExternsPlaced_row mmpl W (staticSecretDrop_row_placed mmpl W), zeroizeSecretHook_ok⟩

theorem cliExternsPlaced_sharedSecretDrop_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsSharedSecretDropSym zeroizeSecretSpec :=
  ⟨LibsignalTripleRatchet.zeroizeSecretHook,
    cliExternsPlaced_row mmpl W (sharedSecretDrop_row_placed mmpl W), zeroizeSecretHook_ok⟩

-- PQXDH & SPQR (`18` left rows):
theorem cliExternsPlaced_compress512_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) {img : Obj.Image} :
    HookSat (cliExternsPlaced mmpl W) lsCompress512SymCli
      (E2E.Pqxdh.Shared.compressInPlaceStubSpec
        (E2E.Pqxdh.Shared.sha512CompressOutBytes (E2E.modelPrims X ⟨W.C, W.Q⟩)) 64 128 img) :=
  ⟨E2E.compress512Hook W.Q.F512, cliExternsPlaced_row mmpl W (compress512_row_placed mmpl W),
    compress512Hook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_toEdwards_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) {img : Obj.Image} :
    HookSat (cliExternsPlaced mmpl W) lsToEdwardsSymCli
      (E2E.Pqxdh.Shared.dalekMontToEdStubSpec (E2E.modelPrims X ⟨W.C, W.Q⟩) img) :=
  ⟨E2E.toEdwardsHook W.Q.montToEd, cliExternsPlaced_row mmpl W (toEdwards_row_placed mmpl W),
    toEdwardsHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_compress_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsCompressSymCli
      (E2E.Pqxdh.Shared.cryptoLeafStubSpec
        (fun bs => E2E.vecU8 (W.Q.compress (E2E.u8Vec 160 bs))) 160 32) :=
  ⟨E2E.compressHook W.Q.compress, cliExternsPlaced_row mmpl W (compress_row_placed mmpl W),
    cryptoLeafHook_ok_std3 (by decide) W.Q.compress⟩

theorem cliExternsPlaced_edNeg_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsEdNegSymCli
      (E2E.Pqxdh.Shared.cryptoLeafStubSpec
        (fun bs => E2E.vecU8 (W.Q.edNeg (E2E.u8Vec 160 bs))) 160 160) :=
  ⟨E2E.edNegHook W.Q.edNeg, cliExternsPlaced_row mmpl W (edNeg_row_placed mmpl W),
    cryptoLeafHook_ok_std3 (by decide) W.Q.edNeg⟩

theorem cliExternsPlaced_torsionFree_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) {img : Obj.Image} :
    HookSat (cliExternsPlaced mmpl W) lsTorsionFreeSymCli
      (E2E.Pqxdh.Shared.cryptoBoolRegStubSpec
        (E2E.modelPrims X ⟨W.C, W.Q⟩).isTorsionFree 160 img) :=
  ⟨E2E.torsionFreeHook W.Q.isTorsionFree,
    cliExternsPlaced_row mmpl W (torsionFree_row_placed mmpl W),
    torsionFreeHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_dsmb_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) {img : Obj.Image} :
    HookSat (cliExternsPlaced mmpl W) lsDsmbSymCli
      (E2E.Pqxdh.Shared.dalekDoubleMulStubSpec (E2E.modelPrims X ⟨W.C, W.Q⟩) img) :=
  ⟨E2E.dsmbHook W.Q.dsmb, cliExternsPlaced_row mmpl W (dsmb_row_placed mmpl W),
    dsmbHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_scalarMod_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsScalarModSymCli
      (E2E.Pqxdh.Shared.cryptoLeafStubSpec
        (fun bs => E2E.vecU8 (W.Q.scalarMod (E2E.u8Vec 32 bs))) 32 32) :=
  ⟨E2E.scalarModHook W.Q.scalarMod, cliExternsPlaced_row mmpl W (scalarMod_row_placed mmpl W),
    cryptoLeafHook_ok_std3 (by decide) W.Q.scalarMod⟩

theorem cliExternsPlaced_scalarWide_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsScalarWideSymCli
      (E2E.Pqxdh.Shared.cryptoLeafStubSpec
        (fun bs => E2E.vecU8 (W.Q.scalarWide (E2E.u8Vec 64 bs))) 64 32) :=
  ⟨E2E.scalarWideHook W.Q.scalarWide, cliExternsPlaced_row mmpl W (scalarWide_row_placed mmpl W),
    cryptoLeafHook_ok_std3 (by decide) W.Q.scalarWide⟩

theorem cliExternsPlaced_kemEncaps_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) :
    HookSat (cliExternsPlaced mmpl W) lsKemEncapsSymCli
      (E2E.Pqxdh.Initiator.kyberEncapsStubSpec (E2E.modelPrims X ⟨W.C, W.Q⟩)) :=
  ⟨E2E.kemEncapsHook W.Q.encaps, cliExternsPlaced_row mmpl W (kemEncaps_row_placed mmpl W),
    E2E.Pqxdh.Initiator.kemEncapsHook_ok_initiatorModelPrims X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_kemDecaps_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : E2E.UnreachedPqxdhPrimitives) :
    HookSat (cliExternsPlaced mmpl W) lsKemDecapsSymCli
      (E2E.Pqxdh.Initiator.kyberDecapsStubSpec
        (E2E.Pqxdh.ResponderCore.ofSignalPqxdhPrimitives (E2E.modelPrims X ⟨W.C, W.Q⟩))) :=
  ⟨E2E.kemDecapsHook W.Q.decaps, cliExternsPlaced_row mmpl W (kemDecaps_row_placed mmpl W),
    kemDecapsHook_ok_std3 X ⟨W.C, W.Q⟩⟩

theorem cliExternsPlaced_mlkemFromSeed_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemFromSeedSymCli (mlkemFromSeedSpec W.Q.K) :=
  ⟨E2E.mlkemFromSeedHook W.Q.K, cliExternsPlaced_row mmpl W (mlkemFromSeed_row_placed mmpl W),
    E2E.Pqxdh.mlkemFromSeedHook_ok W.Q.K⟩

theorem cliExternsPlaced_mlkemPk1_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemPk1SymCli mlkemPk1Spec :=
  ⟨E2E.mlkemPk1Hook, cliExternsPlaced_row mmpl W (mlkemPk1_row_placed mmpl W),
    E2E.Pqxdh.mlkemPk1Hook_ok⟩

theorem cliExternsPlaced_mlkemPk2_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemPk2SymCli mlkemPk2Spec :=
  ⟨E2E.mlkemPk2Hook, cliExternsPlaced_row mmpl W (mlkemPk2_row_placed mmpl W),
    E2E.Pqxdh.mlkemPk2Hook_ok⟩

theorem cliExternsPlaced_mlkemEncaps1_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemEncaps1SymCli (mlkemEncaps1Spec W.Q.K) :=
  ⟨E2E.mlkemEncaps1Hook W.Q.K, cliExternsPlaced_row mmpl W (mlkemEncaps1_row_placed mmpl W),
    E2E.Pqxdh.mlkemEncaps1Hook_ok W.Q.K⟩

theorem cliExternsPlaced_mlkemEncaps2_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemEncaps2SymCli (mlkemEncaps2Spec W.Q.K) :=
  ⟨E2E.mlkemEncaps2Hook W.Q.K, cliExternsPlaced_row mmpl W (mlkemEncaps2_row_placed mmpl W),
    E2E.Pqxdh.mlkemEncaps2Hook_ok W.Q.K⟩

theorem cliExternsPlaced_mlkemDecaps_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemDecapsSymCli (mlkemDecapsSpec W.Q.K) :=
  ⟨E2E.mlkemDecapsHook W.Q.K, cliExternsPlaced_row mmpl W (mlkemDecaps_row_placed mmpl W),
    E2E.Pqxdh.mlkemDecapsHook_ok W.Q.K⟩

theorem cliExternsPlaced_mlkemValidatePk_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsMlkemValidatePkSymCli (mlkemValidatePkSpec W.Q.K) :=
  ⟨E2E.mlkemValidatePkHook W.Q.K, cliExternsPlaced_row mmpl W (mlkemValidatePk_row_placed mmpl W),
    E2E.Pqxdh.mlkemValidatePkHook_ok W.Q.K⟩

theorem cliExternsPlaced_libcruxHmac_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hHmac : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F A) :=
  hHmac

/-! ## 5. `AllocContractsXCliPlaced` and `AllocContractsFsPlaced` at `cliGhostExterns` -/

private theorem ghost_stub_placed_rocl_ok [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (ls_hook_ok_ultra_of_mem hsat hmem)

private theorem cli_row_ghost_rocl_ok [LibsignalPlacement] {α : Type}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} {spec : Spec α}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (hh : HookOk f spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ sym)
      (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  ghost_stub_placed_rocl_ok
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W ⟨f, cliExternsPlaced_row mmpl W hrow, hh⟩
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    hmem

theorem allocContractsXCliPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    AllocContractsXCliPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, _, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, _, _, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := ghost_stub_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le⟩
      dealloc := ghost_stub_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack extHookStack_le⟩
      realloc := ghost_stub_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack extHookStack_le⟩
      shim stk _ _ := ghost_stub_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          hookOk_withStack sessionShim_hookOk stk⟩
      memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hMcLibc stk⟩
      session_memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hMcSess stk⟩
      memcpy_region stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hookOk_withStack hMcReg stk⟩
      session_memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withStack hMcSessReg stk⟩
      memmove stk _ _ := cli_row_ghost_rocl_ok mmpl g W (memmove_row_placed mmpl W) (hookMemmove_ok stk)
      session_memmove stk _ _ := cli_row_ghost_rocl_ok mmpl g W (memmove_row_placed mmpl W)
        (hookMemmove_trace_ok stk)
      memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hMsLibc stk (pos_of_extHookStack_le hle)⟩
      session_memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hMsSess stk (pos_of_extHookStack_le hle)⟩
      memset_region stk _ _ := ghost_stub_placed_rocl_ok ⟨fMs, hMsEq, hookOk_withStack hMsReg stk⟩
      session_memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hookOk_withStack hMsSessReg stk⟩ }

theorem allocContractsXCliPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsXCliPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  allocContractsXCliPlaced_of_hooks mmpl g W hG

theorem allocContractsFsPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    AllocContractsFsPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, hMsFs, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, hMcRO, hMcFs, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := ghost_stub_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          (hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le).keepsFs
            hG.alloc_fs⟩
      dealloc := ghost_stub_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          (hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.dealloc_fs⟩
      realloc := ghost_stub_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          (hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.realloc_fs⟩
      shim stk _ _ := ghost_stub_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          (hookOk_withStack sessionShim_hookOk stk).keepsFs hookNoop_fs⟩
      memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, (hMcLibc stk).keepsFs hMcFs⟩
      session_memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, (hMcSess stk).keepsFs hMcFs⟩
      memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcReg stk).keepsFs hMcFs⟩
      session_memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcSessReg stk).keepsFs hMcFs⟩
      memmove stk _ _ := cli_row_ghost_rocl_ok mmpl g W (memmove_row_placed mmpl W) <|
        (hookMemmove_ok stk).keepsFs hookMemmove_fs
      session_memmove stk _ _ := cli_row_ghost_rocl_ok mmpl g W (memmove_row_placed mmpl W) <|
        (hookMemmove_trace_ok stk).keepsFs hookMemmove_fs
      memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hMsLibc stk (pos_of_extHookStack_le hle)).keepsFs hMsFs⟩
      session_memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hMsSess stk (pos_of_extHookStack_le hle)).keepsFs hMsFs⟩
      memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack hMsReg stk).keepsFs hMsFs⟩
      session_memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack hMsSessReg stk).keepsFs hMsFs⟩
      session_memcpy_region_ro stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcRO stk).keepsFs hMcFs⟩ }

theorem allocContractsFsPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsFsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  allocContractsFsPlaced_of_hooks mmpl g W hG

/-! ## 6. Placed hook bundles at `cliGhostExterns` -/

theorem stage2ContractsMinPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced.of_hooks
    (cliExternsPlaced_alloc_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_sat mmpl g W hG)
    (cliExternsPlaced_realloc_sat mmpl g W hG)
    (cliExternsPlaced_shim_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_sat mmpl g W hG _)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cliExternsPlaced_sessionMemmove_sat mmpl W _))
    (cliGhostExterns_panic_handle_error mmpl g W)
    (cliGhostExterns_panic_handle_alloc_error mmpl g W)

theorem codecHooksPlaced_cli (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    RecordCodecsBinary.CodecHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_noAllocShim_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_sat mmpl g W hG
  memcpy := cliExternsPlaced_framelessMemcpy_sat mmpl g W hG
  panic_alloc := cliGhostExterns_panic_handle_alloc_error mmpl g W
  panic_raw := cliGhostExterns_panic_handle_error mmpl g W

theorem publicApiDecHooksPlaced_cli (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec E2E.HooksE.A0)) :
    LibsignalPublicApi.MessageDecrypt.PublicApiDecHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_sat mmpl g W hG
  stringClone := hStrClone
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

end CryptoVerification.SignalSession.Cli.Slots
