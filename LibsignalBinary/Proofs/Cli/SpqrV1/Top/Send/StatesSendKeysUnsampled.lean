/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled

/-!
# Scaffolding for Inlined `States::send` `.keysUnsampled` Arm in CLI `spqr::send`

Provides `<Authenticator>::mac_hdr` and `RawVecInner::do_reserve_and_handle` callee contracts
for the inlined `.keysUnsampled` arm of `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Auth


open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes


open CryptoVerification.SpqrV1.Drop

open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#2]` meets
`(doReserve1Raw32Spec A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.DoReserve2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.doReserve2Name)
    ((doReserve1Raw32Spec A).inImage img)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.doReserve2_ok_ext_x (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    CryptoVerification.Cli.SpqrV1.Top.Send.DoReserve2OkX img A ext :=
  subroutine_ok_inImage img (CryptoVerification.Cli.SpqrV1.Alloc.do_reserve_2_raw32_ok_ext hA)

end CryptoVerification.SpqrV1.Top.Send
