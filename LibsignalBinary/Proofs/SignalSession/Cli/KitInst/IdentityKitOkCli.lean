/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# CLI Instantiation of `IdentityStoreKitOkIE`

Specializes `IdKit.cliIdKitOkIE` to `cliExterns W` and `cliExternsWith ext` using the CLI
`read_file` and `subtle::black_box::<u8>` hook contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

open ProofLib.ProgramReflection in
theorem cliExterns_blackBox (W : CliHooks) :
    Rust.withPanics (cliExterns W) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  Slots.cliExterns_sessionExterns_le W _ _ (by rfl_kernel)

/-- `IdentityStoreKitOkIE` for `cliIdentityStoreSpec` at `cliExterns W` and `E2E.HooksE.A0`. -/
theorem cliIdKitOkIE_cli (W : CliHooks) {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      (cliExterns W) :=
  IdKit.cliIdKitOkIE himg (RunSkeleton.RunHooks.cli W img) (RunSkeleton.cliReadFile_ok W img readStk)
    (Glue.publicKeyEq_ok_ext img.base (cliExterns_blackBox W)) hs1 hs2 hs3 hs4

theorem cliExternsWith_blackBox_hookSat {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "subtle::black_box::<u8>" CliExt.blackBoxSpec :=
  RunGlue.hookSat_cliExternsWith
    (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol])
    hOk.blackBox

theorem publicKeyEq_ok_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64) (hOk : CliExternsOk P A ext) :
    Getters.PublicKeyEqOkExt32 b (cliExternsWith ext) :=
  Glue.publicKeyEq_ok_ext32 b (cliExternsWith_blackBox_hookSat hOk)

/-- `IdentityStoreKitOkIE` for `cliIdentityStoreSpec` at `cliExternsWith ext` under
`CliExternsOk`. -/
theorem cliIdKitOkIE_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} {F0 : FsFiles} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hs1 : IdKit.trustShimNeed ≤ s1) (hs2 : IdKit.trustPollNeed readStk ≤ s2)
    (hs3 : IdKit.saveShimNeed ≤ s3) (hs4 : IdKit.savePollNeed readStk ≤ s4)
    (hread : extHookStack ≤ readStk := by decide) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec A img.base cliIo.rd F0 cliWrOk peer s1 s2 s3 s4)
      (cliExternsWith ext) :=
  IdKit.cliIdKitOkIE_ext32 himg (RunSkeleton.RunHooksExt.of_externsOk hOk img)
    (RunSkeleton.cliReadFile_ok_cliExternsWith hOk img hread)
    (publicKeyEq_ok_cliExternsWith img.base hOk) hs1 hs2 hs3 hs4

end CryptoVerification.SignalSession.Cli.KitInst.IdKit

namespace CryptoVerification.SignalSession.Cli.KitInst

export IdKit (cliExterns_blackBox cliIdKitOkIE_cli
  cliExternsWith_blackBox_hookSat publicKeyEq_ok_cliExternsWith cliIdKitOkIE_ext)

end CryptoVerification.SignalSession.Cli.KitInst
