/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.GenDecodes
public meta import Lean -- shake: keep

/-!
# Instruction Decode Lemmas and Range-Fetch Tactics for `libsignal_pqxdh_e2e`

Kernel-checked (`Eq.refl`) instruction decode theorems and range-fetch tactics for
`libsignal_pqxdh_e2e::{open, pack, close}`, `RawWaker::NOOP` closures, `session_{recv,send}_wire`,
and `<SessionRecord>::remote_identity_key_bytes`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

gen_decodes libsignalSessionCode_tree libsignalPqxdhWire [
  0x17c94 → 0x17e0c]

private meta def addFetchesRangeFor (off : Nat) (hfnName : Name) (b H : Term) (kStart kEnd : Nat) :
    TacticM Unit := do
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent hfnName
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.E2E.Pqxdh.WireEntries
      s!"libsignalPqxdhWire_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

elab "remoteIdBytes_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic =>
  addFetchesRangeFor 0x17c94 `CryptoVerification.libsignalSessionCode_fnOff_0x17c94
    b H kStart.getNat kEnd.getNat

end Fetch

end CryptoVerification.E2E.Pqxdh.WireEntries
