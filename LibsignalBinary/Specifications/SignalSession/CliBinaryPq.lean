/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
public import ProofLib.Placed.Multi

@[expose] public section

set_option autoImplicit false

/-!
# Whole-process correctness of the `libsignal-cli` ELF (PQXDH mode)

**Trusted: the statement.** Read it in full (see `Computational/docs/TRUSTED_BASE.md`).
`CliPqxdhBinaryCorrectPlaced bytes` states that for every pair of placements `(mpl, mmpl)` linked at
`bytes` (`libsignalSessionLib.LinkedAt bytes mpl`, `VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`),
`bytes` parses as an `ElfImage` matching both libraries (`Placed.CliElfCodeMatchesPlaced mpl mmpl elf`),
and for all hooks `W : CliHooks` and model extras `X : UnreachedPqxdhPrimitives`, the process
`Placed.cliRunPlacedSig mpl mmpl elf W` (after `Placed.cliTokenPatchPlaced`, DEV-CLI10) is total
except on `.OutOfMemory` (`CliReachesOOMPlaced`, DEV-CLI15) and satisfies `CliSpecPqxdh` (`PqDir.lean`)
and `CliSpecPqxdhNoMatch` (`PqDirNoMatch.lean`, DEV-CLI11) at `⟨W.C, W.Q⟩`.

## Scope exclusions

* `keygen` (`PqDir.lean`) and usage-error paths (`CliRejectsMalformedCommandLine`).
* Party states outside `PqxdhPartyInSpecDomain`; `init` when a session already exists (DEV-C-PREV);
  non-canonical pre-key messages (DEV-CLI3); inputs of `2^32` bytes or more (`2^32 - 2048` for a
  pre-key message's inner message).
* After an accepted pre-key `recv` over a non-matching session: the written session file bytes and
  all subsequent calls on that directory (DEV-CLI11).
* Outputs and files on runs that reach `.OutOfMemory` (DEV-CLI15).
* CPUs with AES or PMULL, and SPQR's CPU probe (`Placed.cliTokenPatchPlaced`, DEV-CLI10).

## Deviations of a run of the ELF

**DEV-M6 (machine model): fixed stack, heap, and `mmap` layout.** Each valid pair of multi-block
placements `mpl` (`libsignalSessionLib.LinkedAt bytes mpl`) and `mmpl`
(`VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`, `Placed.CliElfCodeMatchesPlaced mpl mmpl elf`)
places code and data where `elf` maps them (for the pinned non-PIE ELF `cliElfBytes`, linked with
stock `ld.lld` under `cli-elf/stock.ld` at load base `0x400000`). The process gets an 8 MiB stack
with its top at `0x7fff_ffff_0000` (DEV-CLI7), the engine's default auxiliary vector (`AT_RANDOM` =
16 zero bytes, `AT_HWCAP` = `0x3`), `mmap` slots from `0x6000_0000_0000`
(`SignalSession/Process.lean`), and `brk` starting at `elf.brkStart`. A real kernel places the
stack, `brk`, and the `mmap` area at random addresses. Effect: out of scope: no claim for another
stack/`mmap`/`brk` layout.

**DEV-M7 (machine model): this ELF and its build.** The closed headline claims are about the ELF
pinned by SHA-256 in `CliElf.lean` (`cliElfBytes`): libsignal v0.105.4's `libsignal-cli` CLI built
from source by `scripts/cli-elf-stock --stdbin --build` from
`third_party/libsignal/libsignal-session/cli-elf/stock/inputs_stock_stdbin.lock` (rustc 1.98.1 and
its `aarch64-unknown-linux-musl` `self-contained/` CRT objects and `libc.a`, stock LLVM `ld.lld`
22.1.8 `--no-relax` under `cli-elf/stock.ld`, zig 0.16.0 for `rdl_shim.S`, `std-main`, and
`libsignal-session/translation.toml` plus `cli/io/translation.toml`, with the software AES and SHA-2
backends). Effect: out of scope: production builds, other compilers and other flags are not covered.

**DEV-M11 (machine model): each call is a fresh process.** Each `init` / `send` / `recv` in
`Placed.cliRunPlacedSig mpl mmpl elf W` runs from `loadState` (after `Placed.cliTokenPatchPlaced`)
to `exit_group` or `SIGABRT`, with constant clock `UNIX_EPOCH`. Effect: out of scope for long-lived
processes.

**DEV-E1 (machine model): hooks write only their outputs.** Under AAPCS64 a callee may clobber
caller-saved registers (`x0`–`x18`, SIMD/FP, NZCV), whereas each hook in `cliHookTablePlaced`
updates only its specified output registers/memory (`cliBcmpHook` writes `x0`;
`durationSinceExactHook` writes its 24-byte result). Unhooked zero stubs halt and are forbidden by
`Placed.CliRunsToPlaced`. Effect: w.l.o.g., argued for standard compiler code generation.

**DEV-E7 (machine model): the ELF aborts where the model panics.** Protocol-model panics map to
`aborted`, and the ELF's panic symbols (`isCliPanicSymbolPlaced`) terminate the process with
`SIGABRT` (`abortOnPanic`, `CliProcess.lean`). Effect: availability only; none on confidentiality or
integrity.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E


/-! ## Relocatable `Obj.MultiPlacedLib` (`libsignalSessionLib`) CLI Hook Table & Correctness -/

/-- The multi-block placed library `libsignalSessionMultiLib` (624 code blocks, 1,248 data objects,
4 exports) extracted from the `.rlib`/`.o` archives in `GeneratedLean.LibsignalSessionPlacedObj`. -/
abbrev libsignalSessionLib : Obj.MultiPlacedLib := CryptoVerification.libsignalSessionMultiLib

abbrev lsRustNoAllocShimSymCli : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
abbrev lsRustAllocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
abbrev lsRustDeallocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
abbrev lsRustReallocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
abbrev lsRustAllocZeroedSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"

abbrev lsReadFileSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io9read_file"
abbrev lsWriteFileSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_file"
abbrev lsReadStdinSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10read_stdin"
abbrev lsWriteStdoutSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdout"

abbrev lsMemrchrSym : String := "_RNvNtNtCskxtBwYRO61I_4core5slice6memchr7memrchr"
abbrev lsFromUtf8Sym : String := "_RNvNtNtCskxtBwYRO61I_4core3str8converts9from_utf8"
abbrev lsFmtWriteSym : String := "_RNvNtCskxtBwYRO61I_4core3fmt5write"
abbrev lsFormatInnerSym : String := "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"
abbrev lsDurationSinceSym : String :=
  "_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since"
abbrev lsTimeAddSym : String :=
  "_RNvXs6_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTimeINtNtNtCskxtBwYRO61I_4core3ops5arith3AddNtNtBR_4time8DurationE3add"
abbrev lsBlackBoxSym : String :=
  "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek"
abbrev lsCompress256Sym : String := "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"
abbrev lsAesEncSym : String := "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt"
abbrev lsAesDecSym : String := "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decrypt"
abbrev lsPubFromSecretSym : String :=
  "_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from"
abbrev lsDiffieHellmanSym : String :=
  "_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman"
abbrev lsStaticSecretDropSym : String :=
  "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"
abbrev lsSharedSecretDropSym : String :=
  "_RNvXse_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12SharedSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"

/-- The `9` extern symbols de-hooked so the linked ELF bytes execute. Stock `ld.lld` cutover: `memcpy`
and `memset`, whose `.symtab` definitions in the stock link are `VerifiedLibraries.mallocngLib`
blocks `20` / `21`. Earlier F3 + IO.6b allocator/IO cutover: `7` mangled symbols,
the `5` Rust global-allocator symbols (`rdl_shim.S` → `VerifiedLibraries.mallocngLib`)
and `read_file` / `read_stdin` (`libsignal_cli_io`). (`<String as Clone>::clone` becomes an
intra-library `libsignalSessionLib` block under SC-1 route `(I)`.) -/
def cliDehookedSymsPlaced : List String :=
  [lsRustNoAllocShimSymCli,
   lsRustAllocSymCli,
   lsRustDeallocSymCli,
   lsRustReallocSymCli,
   lsRustAllocZeroedSymCli,
   lsReadFileSym,
   lsReadStdinSym,
   "memcpy",
   "memset"]

/-- Mangled-symbol PQXDH and SPQR primitive rows (`18` rows) matching `libsignalSessionMultiLib`,
with `libcrux_hmac::hmac` wired over shared `mallocng` at placement `mmpl`. -/
noncomputable def cliPqxdhHookTablePlaced (mmpl : Obj.MultiPlacement) (C : Crypto) (Q : PqxdhPrims) :
    List (String × (State → State)) :=
  [("_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512", compress512Hook Q.F512),
   ("_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
     toEdwardsHook Q.montToEd),
   ("_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
     compressHook Q.compress),
   ("_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
     edNegHook Q.edNeg),
   ("_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
     torsionFreeHook Q.isTorsionFree),
   ("_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
     dsmbHook Q.dsmb),
   ("_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
     scalarModHook Q.scalarMod),
   ("_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
     scalarWideHook Q.scalarWide),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
     kemEncapsHook Q.encaps),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
     kemDecapsHook Q.decaps),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
     mlkemFromSeedHook Q.K),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
     mlkemPk1Hook),
   ("_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
     mlkemPk2Hook),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
     mlkemEncaps1Hook Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
     mlkemEncaps2Hook Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
     mlkemDecapsHook Q.K),
   ("_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
     mlkemValidatePkHook Q.K),
   ("_RNvCs65XVORQObL2_12libcrux_hmac4hmac", libcruxHmacHookMallocng mmpl C.F)]

/-- Mangled-symbol CLI hook table (`37` rows) matching `libsignalSessionMultiLib` after the F3 + IO.6b
allocator/IO cutover (`5` `__rust_*` allocator rows, `<String as Clone>::clone`, `read_file`, and
`read_stdin` removed so the linked ELF bytes execute; `aes_256_cbc_{encrypt,decrypt}` and
`libcrux_hmac::hmac` wired over `VerifiedLibraries.mallocngLib` at placement `mmpl`) and the stock
`ld.lld` cutover (`memset` and `memcpy` removed: they run as `mallocngLib` blocks `21` / `20`). -/
noncomputable def cliHookTablePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    List (String × (State → State)) :=
  cliPqxdhHookTablePlaced mmpl W.C W.Q ++ [
  ("memmove", hookMemmove),
  ("bcmp", cliBcmpHook W.bcmp),
  ("strlen", strlenHook),
  (lsWriteFileSym, writeFileHook),
  (lsWriteStdoutSym, writeStdoutHook),
  (lsMemrchrSym, memrchrHook),
  (lsFromUtf8Sym, fromUtf8Hook W.utf8Err),
  (lsFmtWriteSym, fmtWriteHook0),
  (lsFormatInnerSym, formatInnerHook0),
  (lsDurationSinceSym, durationSinceExactHook),
  (lsTimeAddSym, timeAddHook),
  (lsBlackBoxSym, LibsignalSession.blackBoxHook),
  (lsCompress256Sym, LibsignalHmac.compress256Hook W.C.F),
  (lsAesEncSym, aesEncHookMallocng mmpl W.C.E),
  (lsAesDecSym, aesDecHookMallocng mmpl W.C.D),
  (lsPubFromSecretSym, LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey),
  (lsDiffieHellmanSym, LibsignalTripleRatchet.diffieHellmanHook W.C.X),
  (lsStaticSecretDropSym, LibsignalTripleRatchet.zeroizeSecretHook),
  (lsSharedSecretDropSym, LibsignalTripleRatchet.zeroizeSecretHook)]

/-- The `18` mangled panic extern symbols of `libsignalSessionMultiLib` mapped to `Rust.panicked`. -/
def cliPanicSymbolsPlaced : List String :=
  ["_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_",
   "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_",
   "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error",
   "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error",
   "_RNvNtCskxtBwYRO61I_4core6option13expect_failed",
   "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
   "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner",
   "_RNvNtCskxtBwYRO61I_4core9panicking5panic",
   "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt",
   "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed",
   "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"]

/-- Canonical panic-symbol predicate for `libsignalSessionLib`. -/
def isCliPanicSymbolPlaced (name : String) : Bool :=
  cliPanicSymbolsPlaced.contains name || Rust.isPanicSymbol name

/-- Mangled-symbol CLI extern map under `Obj.MultiPlacedLib` (`libsignalSessionLib` + `mallocngLib`
placement `mmpl`). -/
noncomputable def cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name =>
    if isCliPanicSymbolPlaced name then some Rust.panicked
    else (cliHookTablePlaced mmpl W).lookup name

/-- Mangled-symbol CLI extern map with `.Panicked` mapped to `SIGABRT` (`abortOnPanic`). -/
noncomputable def cliExternsPlacedSig (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name => (cliExternsPlaced mmpl W name).map abortOnPanic

namespace Placed

/-- Relocatable program of a CLI run: block `617` of `libsignalSessionLib` under `mpl` with
`cliExternsPlacedSig mmpl W` (whose extern table equals `main`'s block's by
`libsignalSessionLib_main_block`). Because `Step` fetches instructions from `s.mem` via
`Program.fetchMem` whenever `externAt? pc = none`, unhooked calls execute the `Perm.rx` ELF bytes
loaded by `elf.loadState`. -/
noncomputable def cliProgPlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl 617 (cliExternsPlacedSig mmpl W)

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Kernel-checked guard that block `617` of `libsignalSessionLib` exists and shares the exact
`externs` list of `main`'s block (with `main` at offset `0`), ensuring `cliProgPlacedSig` induces
the same `externAt?` and `Step` relation as `main`'s block without pinning `main`'s block index. -/
theorem libsignalSessionLib_main_block :
    decide (617 < libsignalSessionLib.blocks.length) = true ∧
    ((Obj.lookupBlockSym "main" libsignalSessionLib.blocks).map (·.2)) = some 0 ∧
    ((Obj.lookupBlockSym "main" libsignalSessionLib.blocks).map
        (fun p => (libsignalSessionLib.blocks.getD p.1 { code := [] }).externs)) =
      some (libsignalSessionLib.blocks.getD 617 { code := [] }).externs :=
  ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

/-- Relocatable SPQR CPU-probe patch (`STORAGE.0 := 0` at `mpl.ρ tokenStorageName`,
`TOKEN.state := 0` at `mpl.ρ tokenName + 8`; see `cliTokenPatch`, DEV-CLI10). -/
def cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) : State :=
  s.setMem ((s.mem.writeBytes (mpl.ρ LibsignalSpqrV1.tokenStorageName) [0#8]).writeBytes
    (mpl.ρ LibsignalSpqrV1.tokenName + 8#64) [0#8, 0#8, 0#8, 0#8])

/-- **Relocatable `CliRunsTo`** under multi-block placements `(mpl, mmpl)`. -/
def CliRunsToPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs)
    (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0)
      (OutcomeMatchesProcess o)

open Classical in
/-- **Relocatable `cliRunAbortOnPanic`** under multi-block placements `(mpl, mmpl)`. -/
noncomputable def cliRunPlacedSig (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    CliRun := fun i =>
  if h : ∃ o, CliRunsToPlaced mpl mmpl elf W i o then some (Classical.choose h) else none

/-- External resolution `stubVa = mpl.ρ sym` reaches the `.symtab` definition `targetVa` in `elf`:
either directly (`stubVa = targetVa`, stock `ld.lld` link) or via a 4-byte-aligned executable (`Perm.rx`)
1-word unconditional branch `B targetVa` at `stubVa` (`--branch-stubs` slot in `.img.text`). -/
def DirectOrBranchStub (elf : ElfImage) (stubVa targetVa : BitVec 64) : Prop :=
  stubVa = targetVa ∨
    (stubVa.toNat % 4 = 0 ∧
      Obj.BranchInRange stubVa targetVa ∧
      Obj.ElfMaps elf stubVa (Obj.bytesOfWordLE (Obj.branchWord 0x14000000#32 stubVa targetVa))
        (· == Perm.rx))

/-- **Relocatable `CliElfCodeMatches`** under `libsignalSessionLib` placement `mpl` and
`VerifiedLibraries.mallocngLib` placement `mmpl` (SR-28 #3 and GK2 K2/K3):
1. `libsignalSessionLib` placement, in-ELF match, and writable-data disjointness (`mpl`);
2. `VerifiedLibraries.mallocngLib` placement, in-ELF match, and writable-data disjointness (`mmpl`);
3. K3(a): cross-library code-block and writable-data disjointness plus `externAt? = none` across all
   `mallocngLib` code bytes and at every de-hooked resolution `mpl.ρ sym`;
4. K3(b): every `sym ∈ cliDehookedSymsPlaced` (the `9` external de-hooked symbols) resolves to a
   unique defined `STT_FUNC` `.symtab` entry `targetVa` in `elf`
   (`DirectOrBranchStub elf (mpl.ρ sym) targetVa`) with `externAt? targetVa = none`. -/
def CliElfCodeMatchesPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  libsignalSessionLib.Placeable mpl ∧
    libsignalSessionLib.InElf elf mpl ∧
    libsignalSessionLib.DataDisjoint mpl ∧
    VerifiedLibraries.mallocngLib.Placeable mmpl ∧
    VerifiedLibraries.mallocngLib.InElf elf mmpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl ∧
    (∀ (i : Nat) (hi : i < libsignalSessionLib.blocks.length)
       (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length) (a : BitVec 64),
      ProofLib.InRegion (mpl.base i) libsignalSessionLib.blocks[i].code.length a →
        ¬ ProofLib.InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a) ∧
    (∀ d₁ ∈ libsignalSessionLib.data, ∀ d₂ ∈ VerifiedLibraries.mallocngLib.data,
      (d₁.readOnly = true ∧ d₂.readOnly = true) ∨
        ∀ a : BitVec 64,
          ProofLib.InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a →
            ¬ ProofLib.InRegion (mmpl.ρ d₂.sym) (VerifiedLibraries.mallocngLib.patchedData mmpl d₂).length a) ∧
    (∀ (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length) (W : CliHooks) (a : BitVec 64),
      ProofLib.InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a →
        (cliProgPlacedSig mpl mmpl W).externAt? a = none) ∧
    (∀ sym ∈ cliDehookedSymsPlaced,
      (∀ W : CliHooks, (cliProgPlacedSig mpl mmpl W).externAt? (mpl.ρ sym) = none) ∧
      ∃ targetVa : BitVec 64,
        Obj.lookupUnique sym elf.symbols = some targetVa ∧
        DirectOrBranchStub elf (mpl.ρ sym) targetVa ∧
        ∀ W : CliHooks, (cliProgPlacedSig mpl mmpl W).externAt? targetVa = none)

end Placed

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec

/-! ## The PQXDH-mode input domain, and runs that reach `.OutOfMemory` -/

/-- **The inputs of the PQXDH-mode specs at model primitives `W`**: the inputs of the calls of
`CliSpecPqxdh`'s five clauses and of `CliSpecPqxdhNoMatch`, for a party state `st` in the domain
(`PqxdhPartyInSpecDomain W st`):
1. `init <peer> bundle` with no session, any typed bundle `b` and the 192 coin bytes `t`;
2. `send <peer>` of a plaintext `m` below `2^32` bytes with the 64 coin bytes `r`;
3. `recv <peer>` of `2 ‖ c` with `c` below `2^32` bytes;
4. `recv <peer>` of `3 ‖ m.bytes` for a typed pre-key message `m` whose inner message is below
   `2^32 - 2048` bytes, at any session state (no session, a matching one: `CliSpecPqxdh`; one that
   does not match: `CliSpecPqxdhNoMatch`);
5. `recv <peer>` of any input `c` below `2^32` bytes whose first byte is neither `2` nor `3`, or of
   nothing.
In 2–5 the receive coins `rc` are any 32 bytes. -/
def CliPqxdhInputs (W : PEParams) (i : Inputs) : Prop :=
  ∃ st : PqParty, PqxdhPartyInSpecDomain W st ∧
    ((st.session = none ∧
        ∃ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), i = pqInitInputs W st b t) ∨
      (∃ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64),
        m.length < 2 ^ 32 ∧ i = pqSendInputs W st m r) ∨
      (∃ (c : List (BitVec 8)) (rc : BitVec 256),
        c.length < 2 ^ 32 ∧ i = pqRecvInputs W st (wireWhisper :: c) rc) ∨
      (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 ∧ i = pqRecvInputs W st (wirePrekey :: m.bytes) rc) ∨
      (∃ (c : List (BitVec 8)) (rc : BitVec 256),
        c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
        i = pqRecvInputs W st c rc))

/-- Run on `i` under `(mpl, mmpl)` and `W` reaches `s.status = .OutOfMemory` (`brk` / `mmap` /
`mprotect` / `mremap` exhaustion) from `Placed.cliTokenPatchPlaced mpl s0` (DEV-CLI10, DEV-CLI15).
By determinism of `Step`, reaching `.OutOfMemory` forces `Placed.cliRunPlacedSig mpl mmpl elf W i = none`
and excludes `.Exception`, `.Halted`, and divergence. -/
def CliReachesOOMPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks)
    (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (Placed.cliProgPlacedSig mpl mmpl W) (Placed.cliTokenPatchPlaced mpl s0) s ∧
      s.status = .OutOfMemory

/-! ## Specs total except `.OutOfMemory` (DEV-CLI15) -/

/-- **The outcome of `run` on `i` meets `P`, or `run` has no outcome on an excused input**
(DEV-CLI15: total except `.OutOfMemory`): either `run i = some o` with `P o`, or `run i = none` and
`exc i`. With `exc := fun _ => False` it is equivalent to `∃ o, run i = some o ∧ P o`, and with
`P := (· = e)` it is equivalent to `run i = some e`. -/
def OutcomeOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (i : Inputs) (P : Outcome → Prop) : Prop :=
  (∃ o, run i = some o ∧ P o) ∨ (run i = none ∧ exc i)

/-- **`CliSpecPqxdh` total except `.OutOfMemory` (DEV-CLI15).** `CliSpecPqxdh run X W` (`PqDir.lean`)
with each clause's conclusion `run i = some e` replaced by `OutcomeOrExcusedAbort exc run i (· = e)`:
on the clause's input `i` the run is total with exactly the clause's outcome, except when `run i = none`
and `i` is excused (`exc i`). The five clauses are `CliSpecPqxdh`'s (1. `init`, 2. `send`,
3. `recv` of `2 ‖ c`, 4. `recv` of a typed pre-key message with no session or a matching one,
5. `recv` of any other first byte or of nothing), in the same order, with the same binders,
hypotheses and outcomes, including the `stdinCapBytes` / `maxPlaintextBytes` rejections (DEV-CLI21).
With `exc := fun _ => False` it is equivalent to `CliSpecPqxdh run X W`. -/
def CliSpecPqxdhOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
      OutcomeOrExcusedAbort exc run (pqInitInputs W st b t)
        (· = pqxdhExpectedOutcome W (pqInitInputs W st b t) (pqInitModel X W st b t))) ∧
    (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
      OutcomeOrExcusedAbort exc run (pqSendInputs W st m r)
        (· = if m.length > stdinCapBytes then
              .exited 2 [] (filesOf (pqSendInputs W st m r).files)
            else if m.length > maxPlaintextBytes then
              .exited 1 [] (filesOf (pqSendInputs W st m r).files)
            else
              pqxdhExpectedOutcome W (pqSendInputs W st m r) (pqSendModel W st m r.toList))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wireWhisper :: c) rc)
        (· = if (wireWhisper :: c).length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st (wireWhisper :: c) rc).files)
            else
              pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: c) rc)
                (pqRecvWhisperModel W st c rc))) ∧
    (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
        (· = if (wirePrekey :: m.bytes).length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files)
            else
              pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X W st m rc))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st c rc)
        (· = if c.length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st c rc).files)
            else
              .exited 1 [] (filesOf (pqRecvInputs W st c rc).files)))

/-- **`CliSpecPqxdhNoMatch` total except `.OutOfMemory` (DEV-CLI15).** `CliSpecPqxdhNoMatch run X W`
(`PqDirNoMatch.lean`) with its conclusion `∃ o, run i = some o ∧ OutcomeMatchesModelExceptPath …`
replaced by `OutcomeOrExcusedAbort exc run i …`, with the same binders, hypotheses and outcomes,
including the `stdinCapBytes` rejection (DEV-CLI21). With `exc := fun _ => False` it is equivalent
to `CliSpecPqxdhNoMatch run X W`. -/
def CliSpecPqxdhNoMatchOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
    ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      ¬ PqSessionMatches x g m →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
        (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
            o = .exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files)
          else
            OutcomeMatchesModelExceptPath W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X W { st with session := none } m rc) o)

/-- **Relocatable `CliPqxdhElfCorrect` under placements `(mpl, mmpl)`, total except `.OutOfMemory`
(DEV-CLI15).** `elf` matches the placed code (`Placed.CliElfCodeMatchesPlaced mpl mmpl elf`), and for
every choice of hooks `W` (no hypothesis on `W`) and every model extras `X`, the process
`Placed.cliRunPlacedSig mpl mmpl elf W` is total and meets `CliSpecPqxdh` and `CliSpecPqxdhNoMatch` at
`⟨W.C, W.Q⟩` except on inputs where the run reaches `.OutOfMemory` (`CliReachesOOMPlaced mpl mmpl elf W`). -/
def CliPqxdhElfCorrectPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  Placed.CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatchOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- **Relocatable `CliPqxdhBinaryCorrect` at specific placements `(mpl, mmpl)`**. -/
def CliPqxdhBinaryCorrectPlacedAt (mpl mmpl : Obj.MultiPlacement) (bytes : List (BitVec 8)) :
    Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectPlaced mpl mmpl elf

/-- **Relocatable `CliPqxdhBinaryCorrect`:** universally quantified over every pair of multi-block
placements `mpl` (`libsignalSessionLib.LinkedAt bytes mpl`) and `mmpl`
(`VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`). -/
def CliPqxdhBinaryCorrectPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes

end CryptoVerification.SignalSession
