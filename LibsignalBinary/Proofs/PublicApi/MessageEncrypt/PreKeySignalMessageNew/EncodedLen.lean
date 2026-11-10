/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPf

/-!
# `<wire::PreKeySignalMessage as Message>::encoded_len`

Entry-point proof that `<libsignal_protocol::proto::wire::PreKeySignalMessage as prost::message::Message>::encoded_len`
(`0x2da84`, block `119`) satisfies `preKeyMsgEncodedLenSpec A`, summing the encoded lengths of
protobuf tags 1–8 without arithmetic overflow under `PreKeyMsgWireLengthsFit`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLen

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {abs : String → Option (State → State)}

theorem encodedLen_ok_ext {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    PreKeyMsgEncodedLenOk_ext img A ext :=
  EncodedLenPf.preKeyMsgEncodedLen_ok_ext himg

theorem encodedLen_ok_trap (himg : Obj.Loads libsignalSessionImage img) :
    PreKeyMsgEncodedLenOk_trap img C A abs :=
  EncodedLenPf.preKeyMsgEncodedLen_ok_trap himg

/-- `<wire::PreKeySignalMessage as prost::message::Message>::encoded_len` (`0x2da84`) satisfies
`preKeyMsgEncodedLenSpec A`. -/
theorem encodedLen_ok (himg : Obj.Loads libsignalSessionImage img) :
    PreKeyMsgEncodedLenOk img C A ctl abs :=
  EncodedLenPf.preKeyMsgEncodedLen_ok himg

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

theorem encodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_119 H) (blkPl_119).base (preKeyMsgEncodedLenSpec A) :=
  EncodedLenPf.preKeyMsgEncodedLen_placed_ok

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLen
