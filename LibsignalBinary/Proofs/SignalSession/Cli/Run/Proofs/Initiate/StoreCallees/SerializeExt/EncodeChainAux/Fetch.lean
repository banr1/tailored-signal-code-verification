/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>`: Instruction Decodes and Callee Offset Resolution
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") → (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>" + 2040)]

elab "encChain_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
      s!"libsignalSessionBin_decode_{"0x" ++ String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf

/-! ## Callee Offset Resolution from `encodeChainName` -/

set_option maxRecDepth 2000000 in
theorem encodeVarint_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeChainName, encodeVarintName, h1, h2]
  bv_omega

set_option maxRecDepth 2000000 in
theorem chainLen_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAtExt b ext).fnAddr chainLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeChainName, chainLenName, h1, h2]
  bv_omega

set_option maxRecDepth 2000000 in
theorem msgKeyLen_fnAddr_eq_encChain (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeChainName, msgKeyLenName, h1, h2]
  bv_omega

set_option maxRecDepth 2000000 in
theorem doReserve_fnAddr_eq_encChain (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAtExt b ext).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodeChainName, doReserveName, h1, h2]
  bv_omega

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
