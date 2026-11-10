/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS0S2S5
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS1
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3PartA
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3PartB
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3PartC
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3PartD
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS4
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacX
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX

/-!
# `RatchetState::consume_message_key` on `SP2Ext` (`CmkOkX`)

Assembles segments `S0` through `S5` with `FindIndexOkX`, `HmacOkX`, and `AllocContractsX` to prove
`CmkOkX img C A ext` at `cmkStackX = 20480` bytes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open Proofs.libsignal.Stage1X

theorem cmk_ok_x {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (hfind : FindIndexOkX img A ext)
    (hhmac : HmacOkX img C.F ext) :
    CmkOkX img C A ext :=
  cmk_of_seams_x himg hA hfind hhmac (growOneChain_ok_x hA)
    (s0_past_ok_x C.F A ext img) (s0_tooFar_ok_x C.F A ext img) (s0_advance_ok_x C.F A ext img)
    (s1_ok_x C.F A ext img) (s2_ok_x C.F A ext img)
    (storeLoop_iter_of_parts_x (storeLoop_deriveSeed_ok_x C.F A ext img)
      (storeLoop_insertKey_ok_x C.F A ext img) evictOldestKey_ok_x advanceChainKey_ok_x)
    (s4_ok_x C.F A ext img)
    (s5_noChainLoop_ok_x C.F A ext img) (s5_epiloguePanic_ok_x C.F A ext img)

theorem cmk_ok_tr_ext_x {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext)
    (hHkdf : CryptoVerification.LibsignalTripleRatchet.HkdfContractsExt img C.F ext)
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    CmkOkX img C A ext :=
  cmk_ok_x himg
    (CryptoVerification.SignalSession.Cli.Store.SerGlueX.stage1XAllocContractsX_of_trAllocContractsX hA)
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.findIndex_ok_of_blackBox32 himg h_bb)
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX.hmac_sha256_ok_of_hkdfContracts himg hHkdf)

end Proofs.libsignal.Stage1X.CmkX
