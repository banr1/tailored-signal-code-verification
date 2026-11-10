/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Instruction decode lemmas for `SessionStructure::encoded_len` (`0x25fd0..0x2643c`)

Generates `@Eq.refl` decode lemmas `sessLen_decode_0x<off>` and the `sesslen_fetches` tactic for
the 283 instructions (`1132` bytes) of `<SessionStructure as prost::Message>::encoded_len`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Lean Meta Elab Command Tactic
open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification

set_option maxRecDepth 2000000

gen_decodes libsignalSessionCode_tree sessLen [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" + 1128)]

/-- Add `Program.fetch` hypotheses for byte offsets `[kStart, kEnd)` (exclusive) of
`SessionStructure::encoded_len` (`0x25fd0` = `155600`). -/
elab "sesslen_fetches " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len")
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.Serialization.SessionLenAux
      s!"sessLen_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end CryptoVerification.E2E.Record.Serialization.SessionLenAux
