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

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

gen_decodes libsignalSessionCode_tree responderBin [
  0x17490 → 0x174d0,
  0x17970 → 0x17e0c,
  0x17f84 → 0x1811c,
  0x1e8b4 → 0x1eb20,
  0x1f908 → 0x1fa70,
  0x25264 → 0x25498,
  0x26630 → 0x266c8,
  0x28f9c,
  0x29568 → 0x29638,
  0x2aa14 → 0x2ab30,
  0x2aeec,
  0x3e81c → 0x3e9c0]

elab "responder_fetches_from " b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (.str `CryptoVerification.E2E.Pqxdh.ResponderStore
      s!"responderBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderStore
