/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Instruction decode lemmas and fetch tactic for `SessionStructure::clone` (`0x240f0`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000 in
theorem libsignalSessionCode_fnOff_sym_240f0 :
    libsignalSessionCode.fnOff sessionCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")

open Lean Elab Tactic in
/-- Introduces `libsignalSessionCode_fetch_fnAddr` hypotheses for offsets `[k0, k0 + len)` of `SessionStructure::clone`. -/
elab "sessionClone_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")
  let k0 := k0.getNat
  let len := len.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (Name.mkSimple s!"sessionCloneBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

gen_decodes libsignalSessionCode_tree sessionCloneBin [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 200), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 204),
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 208) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 216), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 220), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 224) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 288), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 292), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 296) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 300), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 304),
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 308) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 436), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 440), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 444), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 448), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 452), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 456) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 468),
    raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 472), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 476) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 564), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 568), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 572) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 580), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 584), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 588) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 652),
    raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 656), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 660) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 896), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 900), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 904) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 912), raw (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 916), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 920) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" + 1208)]

end CryptoVerification.E2E.Record.Serialization
