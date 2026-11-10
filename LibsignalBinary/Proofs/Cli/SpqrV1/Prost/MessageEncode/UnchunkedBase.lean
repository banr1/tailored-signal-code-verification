/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# CLI Unchunked `EkSentCt1Received` and `Ct1Sent` Encoder Definitions

Generates instruction decode lemmas and defines symbol names, `fnOff` lemmas, and `subroutine_ok`
predicates for `EkSentCt1Received` and `Ct1Sent` message encoders (`[local#3]`) on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalTripleRatchet.Prost

open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Varint

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree libsignalSessionBinCli [(ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]" + 0) → (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]" + 788)]

/-- CLI symbol name for `prost::encoding::message::encode::<EkSentCt1Received, Vec<u8>> [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]"

/-- CLI symbol name for `prost::encoding::message::encode::<Ct1Sent, Vec<u8>> [local#3]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]"

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#3]")

@[simp, arm64_norm] theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name = (ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]") :=
  (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#3]")

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedEncode1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name)
    (ekSentCt1ReceivedEncodePinnedSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedEncode1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name)
    (ekSentCt1ReceivedEncodeSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedEncode1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name)
    ((ekSentCt1ReceivedEncodePinnedSpecX A).inImage img)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedEncode1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ekSentCt1ReceivedEncode1Name)
    ((ekSentCt1ReceivedEncodeSpecX A).inImage img)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Ct1SentEncode1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name)
    (ct1SentEncodePinnedSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Ct1SentEncode1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name)
    (ct1SentEncodeSpec A)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Ct1SentEncode1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name)
    ((ct1SentEncodePinnedSpecX A).inImage img)

def _root_.CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Ct1SentEncode1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1SentEncode1Name)
    ((ct1SentEncodeSpecX A).inImage img)

end CryptoVerification.SpqrV1.Prost.MessageEncode
