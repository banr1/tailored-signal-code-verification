/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli

/-!
# CLI Instantiation of `SessionOnlyKitOkSE`

Specializes `SessKit.cliSessKitOkSE` to `cliExterns W` and `cliExternsWith ext` using the CLI
`read_file` and `SessionRecord::serialize` hook contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.SessKit

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst

/-- `SessionOnlyKitOkSE` for `cliSessionStoreSpec` at `cliExterns W` and `E2E.HooksE.A0`. -/
theorem cliSessKitOkSE_cli (W : CliHooks) {img : Obj.Image} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope E2E.HooksE.A0 img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord (cliExterns W) :=
  cliSessKitOkSE himg (RunSkeleton.RunHooks.cli W img) (RunSkeleton.cliReadFile_ok W img readStk)
    hDeser (Store.SerGlueX.serializeCanonX_cli W img) hs1 hs2 hs3 hs4

/-- `SessionOnlyKitOkSE` for `cliSessionStoreSpec` at `cliExternsWith ext` under `CliExternsOk`
and `sessDeserializeExtSpec`. -/
theorem cliSessKitOkSE_ext {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4)
    (hreadStk : extHookStack ≤ readStk := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord (cliExternsWith ext) :=
  cliSessKitOkSE_ext_of_hooks himg (RunSkeleton.RunHooksExt.of_externsOk hOk img)
    (RunSkeleton.cliReadFile_ok_cliExternsWith hOk img hreadStk)
    hDeser (Store.SerGlueX.serializeCanonX_ext hOk img) hs1 hs2 hs3 hs4

/-- Pool-free `sessDeserializeSpec` variant of `cliSessKitOkSE_ext`. -/
theorem cliSessKitOkSE_ext_noPool {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {img : Obj.Image} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope A img))
    (hs1 : loadShimNeed ≤ s1) (hs2 : loadPollNeed readStk ≤ s2)
    (hs3 : storeShimNeed ≤ s3) (hs4 : storePollNeedX ≤ s4)
    (hreadStk : extHookStack ≤ readStk := by decide) :
    MessageDecrypt.SessionOnlyKitOkSE
      (cliSessionStoreSpec A img.base cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4)
      Scope E2E.Record.encodeRecord (cliExternsWith ext) :=
  cliSessKitOkSE_ext hOk himg
    (Store.LoadPoll.Helpers.subroutine_ok_sessDeserializeExtSpec_of_spec hDeser)
    hs1 hs2 hs3 hs4 hreadStk

end CryptoVerification.SignalSession.Cli.KitInst.SessKit
