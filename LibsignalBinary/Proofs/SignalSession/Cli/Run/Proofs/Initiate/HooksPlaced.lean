/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.RecordCodecs.Assembly
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import Init.Data.String.Defs
import Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

/-!
# Relocatable Hook Bundle and `TraceFsSound` for `initiate`

Proves `TraceFsSound` for block programs instantiated at `cliExternsPlaced` or `cliGhostExterns`,
provides the `sepWPp_of_sepWP_lscro` segment combinator, and defines the relocatable hook bundle
`RunHooksPlaced W A H`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## `SepWPp` / `SepWP` `LibsignalCodeRoLoaded` combinator -/

/-- Lifts a `SepWP` segment to `SepWPp` while threading `LibsignalCodeRoLoaded pl` across stores. -/
theorem sepWPp_of_sepWP_lscro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl sm.mem →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  LibsignalPublicApi.StoreKit.sepWPp_seq_lscro hcrl h

/-! ## `TraceFsSound` for `cliExternsPlaced` and `cliGhostExterns` -/

theorem cliHookTablePlaced_fsT (mmpl : MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, HookFsTraced IsFsC p.2 :=
  RunGlue.cliHookTablePlaced_fsT mmpl W

theorem fsTHooks_cliExternsPlaced (mmpl : MultiPlacement) (W : CliHooks) :
    FsTHooks (cliExternsPlaced mmpl W) :=
  RunGlue.fsTHooks_cliExternsPlaced mmpl W

theorem traceFsSound_blockProgram {pl : MultiPlacement} {i : Nat} {H : LibsignalHooks}
    (hH : FsTHooks H) :
    TraceFsSound (libsignalSessionLib.blockProgram pl i H) :=
  traceFsSound_of_fsTHooks hH fsTHooks_none rfl

theorem traceFsSound_of_isLsBlockProg [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hblk : IsLsBlockProg prog i H] (hH : FsTHooks H) :
    TraceFsSound prog := by
  rw [hblk.eq_blockProgram]
  exact traceFsSound_blockProgram hH

/-- Establishes `TraceFsSound` for any block program instantiated at `cliExternsPlaced mmpl W`. -/
theorem traceFsSound_cliPlaced [LibsignalPlacement] (mmpl : MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (cliExternsPlaced mmpl W)] :
    TraceFsSound prog :=
  traceFsSound_of_isLsBlockProg (fsTHooks_cliExternsPlaced mmpl W)

/-- Establishes `TraceFsSound` for any block program instantiated at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem traceFsSound_cliGhostPlaced [LibsignalPlacement] (mmpl : MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (hFs : CliGhostHooksFs g)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] :
    TraceFsSound prog :=
  RunGlue.traceFsSound_lsProg_cli_ghost mmpl g W hFs

theorem bcmp_row_placed (mmpl : MultiPlacement) (W : CliHooks) :
    (cliBcmpName, cliBcmpHook W.bcmp) ∈ cliHookTablePlaced mmpl W :=
  RunGlue.bcmp_row_placed mmpl W

theorem cli_hookSat_bcmp_placed (mmpl : MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) cliBcmpName cliBcmpSpec :=
  RunGlue.cli_hookSat_bcmp_placed mmpl W

/-! ## KEM encapsulate symbol and `RunHooksPlaced` bundle -/

/-- Mangled symbol name of `libcrux_ml_kem::mlkem1024::kyber::encapsulate`. -/
abbrev lsKemEncapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"

/-- Relocatable `[LibsignalPlacement]` hook bundle gathering allocator, codec, serialization,
memory, cryptographic, KEM, panic, and `TraceFsSound` contracts on `H`. -/
structure RunHooksPlaced [LibsignalPlacement] (W : CliHooks) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A H
  allocFs : AllocContractsFsPlaced A H
  codec : RecordCodecsBinary.CodecHooksPlaced A H
  ser : Proofs.libsignal.Hooks2.SerContractsXPlaced A H
  shim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec
  rawAlloc : HookSat H lsRustAllocSymCli (rustAllocSpec A)
  rawDealloc : HookSat H lsRustDeallocSymCli (rustDeallocSpec A)
  framelessMemcpy : HookSat H memcpyName framelessMemcpySpec
  sessionMemcpyRegion : HookSat H memcpyName sessionMemcpyRegionSpec
  memcpyRO : HookSat H memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec
  bcmp : HookSat H cliBcmpName cliBcmpSpec
  e2eBcmp : HookSat H E2E.bcmpName E2E.HooksE.e2eBcmpSpec
  allocZeroed : HookSat H lsRustAllocZeroedSymCli (rustAllocZeroedSpec A)
  stringClone : HookSat H lsStringCloneSym (LibsignalPublicApi.stringCloneSpec A)
  formatInner : HookSat H lsFormatInnerSym (LibsignalTripleRatchet.formatInnerSpec A)
  pubFromSecret : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec W.C.pubKey)
  dh : HookSat H lsDiffieHellmanSym (diffieHellmanSpec W.C.X)
  sharedDrop : HookSat H lsSharedSecretDropSym zeroizeSecretSpec
  staticDrop : HookSat H lsStaticSecretDropSym zeroizeSecretSpec
  blackBox : H lsBlackBoxSym = some CryptoVerification.LibsignalSession.blackBoxHook
  hkdf : HkdfPlacedHooks W.C.F H
  kemEncaps : H lsKemEncapsSym = some (E2E.kemEncapsHook W.Q.encaps)
  durationSince : H lsDurationSinceSym = some durationSinceExactHook
  panic_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked
  panic_raw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked
  panic_sym : ∀ s, s ∈ cliPanicSymbolsPlaced → H s = some Rust.panicked
  fs : ∀ {prog : Program} {i : Nat} [IsLsBlockProg prog i H], TraceFsSound prog

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
