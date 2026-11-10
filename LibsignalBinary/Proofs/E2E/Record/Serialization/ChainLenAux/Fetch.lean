/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

open Lean Elab Tactic in
elab "chainLen_fetches_range " b:term:max H:term:max hfn:term:max
    off:term:max kStart:num kEnd:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.E2E.Record.Serialization |>.str
      s!"chainLenBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

gen_decodes libsignalSessionCode_tree chainLenBin [(ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") → (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" + 412)]

end CryptoVerification.E2E.Record.Serialization
