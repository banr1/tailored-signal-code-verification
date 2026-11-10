/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.GenDecodes

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

gen_decodes libsignalSessionCode_tree responderWireBin [
  0x1adc → 0x1b30,
  0x2f74 → 0x309c,
  0x6778 → 0x693c,
  0x121b4 → 0x12294,
  0x15d14 → 0x15d78,
  0x20624 → 0x20b84,
  0x232c8 → 0x2386c,
  0x29c14 → 0x2a69c,
  0x2c614 → 0x2c718,
  0x3f614 → 0x3f688,
  0x3fc30 → 0x3fcd4,
  0x3fd6c → 0x40138]

elab "responder_wire_fetches_from " b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (.str `CryptoVerification.E2E.Pqxdh.ResponderWire
      s!"responderWireBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderWire
