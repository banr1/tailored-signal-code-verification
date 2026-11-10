/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction Fetch and Callee Offsets for Seed `message::merge<Chain>`

Provides instruction-fetch automation and cross-block callee transfers (`bytes::merge`,
`int32::merge`) for `prost::encoding::message::merge::<Chain>` (`0x3974`, block `11`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") → (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" + 2532)]

elab "chainMerge_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed
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
open CryptoVerification.E2E.Record

/-! ## Callee Offset Resolution -/

theorem bytesMerge_ok_sub_seedChain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : BytesMergeOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      (bytesMergeSpec A img) := by
  have heq : (tripleRatchetProgAt img.base C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_seedChain {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Int32MergeOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      (int32MergeSpec A) := by
  have heq : (tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

/-! ## Relocatable `[LibsignalPlacement]` Callee Transfers -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem bytesMerge_placed_ok_sub_seedChain [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A))) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 7)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A)) :=
  ls_call_ro_of_block (callerProg := lsProg_11 H) h

theorem int32Merge_placed_ok_sub_seedChain [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpec A))) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (int32MergeSpec A)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
