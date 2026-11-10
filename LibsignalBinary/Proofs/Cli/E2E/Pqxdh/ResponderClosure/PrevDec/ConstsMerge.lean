/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafReserve -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafVarint -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# Handshake `bytes::merge` Symbol and Offset Constants

Symbol names, `CodeLayout` offsets, the `merge6_fetches_H` fetch helper, and wrapping 64-bit
callee-relative offset identities for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]`
and `prost::encoding::message::merge::<Chain, &mut &[u8]> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 CryptoVerification CryptoVerification.CodeLayout ProofLib.ProgramReflection

abbrev bytesMerge6Name : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]"

abbrev chainMerge5Name : String :=
  "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"

abbrev rawVecGrowOneMkName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one"

abbrev bytesMerge6Off : Nat := num% (ls_off% bytesMerge6Name)
abbrev decodeVarint5Off : Nat := num% (ls_off% decodeVarint5Name)
abbrev doReserve10Off : Nat := num% (ls_off% doReserve10Name)
abbrev chainMerge5Off : Nat := num% (ls_off% chainMerge5Name)
abbrev rawVecGrowOneMkOff : Nat := num% (ls_off% rawVecGrowOneMkName)

theorem bytesMerge6_fnOff :
    libsignalSessionCode.fnOff bytesMerge6Name = bytesMerge6Off :=
  ls_lemma% fnOff bytesMerge6Name

theorem doReserve10_fnOff :
    libsignalSessionCode.fnOff doReserve10Name = doReserve10Off :=
  ls_lemma% fnOff doReserve10Name

/-- Fetch hypotheses for `bytes::merge [local#6]` on arbitrary `H`, from fn-relative offset `k0`, `len` bytes. -/
elab "merge6_fetches_H " b:term:max H:term:max
    hfn:ident k0:num len:num : tactic => do
  let offVal := num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]")
  let offLit := Lean.Syntax.mkNumLit (toString offVal)
  Lean.Elab.Tactic.evalTactic (← `(tactic| code_fetches_range
    CryptoVerification.libsignalSessionCode
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.bytesMerge6
    $b $H $hfn $offLit $k0 $len))

/-! ## Callee Relative Offsets and Cut Offsets for `bytes::merge [local#6]` -/

abbrev bm6DecodeErrorFromRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6MemcpyRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "memcpy" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6MemcpyRelNat : Nat :=
  num% (ls_off% "memcpy" - bytesMerge6Off)

abbrev bm6ShimRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6ShimRelNat : Nat :=
  num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - bytesMerge6Off)

abbrev bm6AllocRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "__rustc::__rust_alloc" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6AllocRelNat : Nat :=
  num% (ls_off% "__rustc::__rust_alloc" - bytesMerge6Off)

abbrev bm6HandleErrorRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "alloc::raw_vec::handle_error" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6HandleErrorRelNat : Nat :=
  num% (ls_off% "alloc::raw_vec::handle_error" - bytesMerge6Off)

abbrev bm6BytesFromVecRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" - bytesMerge6Off) % 2 ^ 64)

abbrev bm6DoReserve10RelOff : BitVec 64 :=
  bv% ((2 ^ 64 + doReserve10Off - bytesMerge6Off) % 2 ^ 64)

abbrev bm6DecodeVarint5RelOff : BitVec 64 :=
  bv% ((2 ^ 64 + decodeVarint5Off - bytesMerge6Off) % 2 ^ 64)

theorem bm6_add_decodeErrorFrom_eq_fnAddr {b : BitVec 64} {H : String → Option (State → State)} :
    (libsignalSessionCode.rebase b H).fnAddr bytesMerge6Name + bm6DecodeErrorFromRelOff =
      (libsignalSessionCode.rebase b H).fnAddr
        "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" :=
  fnAddr_rel64 bytesMerge6_fnOff
    (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
    (by decide)

theorem bm6_add_bytesFromVec_eq_fnAddr {b : BitVec 64} {H : String → Option (State → State)} :
    (libsignalSessionCode.rebase b H).fnAddr bytesMerge6Name + bm6BytesFromVecRelOff =
      (libsignalSessionCode.rebase b H).fnAddr
        "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" :=
  fnAddr_rel64 bytesMerge6_fnOff
    (ls_lemma% fnOff "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from")
    (by decide)

theorem bm6_add_doReserve10_eq_fnAddr {b : BitVec 64} {H : String → Option (State → State)} :
    (libsignalSessionCode.rebase b H).fnAddr bytesMerge6Name + bm6DoReserve10RelOff =
      (libsignalSessionCode.rebase b H).fnAddr doReserve10Name :=
  fnAddr_rel64 bytesMerge6_fnOff doReserve10_fnOff (by decide)

theorem bm6_add_decodeVarint5_eq_fnAddr {b : BitVec 64} {H : String → Option (State → State)} :
    (libsignalSessionCode.rebase b H).fnAddr bytesMerge6Name + bm6DecodeVarint5RelOff =
      (libsignalSessionCode.rebase b H).fnAddr decodeVarint5Name :=
  fnAddr_rel64 bytesMerge6_fnOff decodeVarint5_fnOff (by decide)

abbrev bm6Off050 : BitVec 64 := 80#64
abbrev bm6Off074 : BitVec 64 := 116#64
abbrev bm6Off07c : BitVec 64 := 124#64
abbrev bm6Off094 : BitVec 64 := 148#64
abbrev bm6Off0e4 : BitVec 64 := 228#64
abbrev bm6Off1b8 : BitVec 64 := 440#64
abbrev bm6Off210 : BitVec 64 := 528#64
abbrev bm6Off220 : BitVec 64 := 544#64
abbrev bm6Off230 : BitVec 64 := 560#64
abbrev bm6Off254 : BitVec 64 := 596#64
abbrev bm6Off29c : BitVec 64 := 668#64
abbrev bm6Off2c0 : BitVec 64 := 704#64

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
