/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction decodes and callee offsets for `encode::<Chain, Vec<u8>>` (`0x44b0`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

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
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.Serialization
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
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
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost

/-! ## Callee offset resolution on `tripleRatchetProgAt` -/

theorem encodeVarint_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, encodeChainName, encodeVarintName, h1, h2]
  rw [BitVec.add_assoc]; rfl

theorem chainLen_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, encodeChainName, chainLenName, h1, h2]
  rw [BitVec.add_assoc]; rfl

theorem msgKeyLen_fnAddr_eq_encChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAt b C ctl abs).fnAddr msgKeyLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, encodeChainName, msgKeyLenName, h1, h2]
  rw [BitVec.add_assoc]; rfl

theorem doReserve_fnAddr_eq_encChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") =
      (tripleRatchetProgAt b C ctl abs).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, encodeChainName, doReserveName, h1, h2]
  rw [BitVec.add_assoc]; rfl

theorem encChain_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) framelessMemcpySpec :=
  hook_ok_at_raw (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") (k := num% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) rfl (by decide)
    (ls_hook% "memcpy") ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

end CryptoVerification.E2E.Record.Serialization
