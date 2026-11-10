/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

open Lean Elab Tactic in
scoped elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_{"0x" ++ String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

theorem libsignalSessionCode_fnOff_serialize :
    libsignalSessionCode.fnOff serializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::serialize")

theorem libsignalSessionCode_fnOff_sessionClone :
    libsignalSessionCode.fnOff sessionCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")

theorem libsignalSessionCode_fnOff_vecVecClone :
    libsignalSessionCode.fnOff vecVecCloneName = num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") := by
  exact (ls_lemma% fnOff "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")

theorem libsignalSessionCode_fnOff_sessionLen :
    libsignalSessionCode.fnOff sessionLenName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len")

theorem libsignalSessionCode_fnOff_encodeVarint :
    libsignalSessionCode.fnOff LibsignalTripleRatchet.Prost.encodeVarintName = num% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") := by
  exact (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")

theorem libsignalSessionCode_fnOff_encodeRaw :
    libsignalSessionCode.fnOff encodeRawName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")

theorem libsignalSessionCode_fnOff_dropLocal1 :
    libsignalSessionCode.fnOff LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") := by
  exact (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")

gen_decodes libsignalSessionCode_tree serializeBin [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 192), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 268) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 444),
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 692) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 736), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 784) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 788), (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 812) → (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 840)]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SerializeBodyAux
