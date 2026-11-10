/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

@[expose] public section

set_option autoImplicit false

/-!
# Instruction Fetches and `SepWPp` Helpers for `SessionStructure::encode_raw`
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree encRawBin [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 2784)]

elab "encraw_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
      s!"encRawBin_decode_{"0x" ++ String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
