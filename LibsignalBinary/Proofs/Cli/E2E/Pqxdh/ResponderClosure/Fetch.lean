/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.CodeLayout
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch -- shake: keep
public meta import Lean -- shake: keep

/-!
# Responder Closure Instruction Fetch Macro & Helpers

Instruction fetch macro and lookup helpers for
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}` on the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName : String :=
  "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureOff : BitVec 64 := (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

gen_decodes libsignalSessionCode_tree responderClosureBinCli [(ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0) → (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 14264)]

elab "closure_fetches_range_cli " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (num% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}").decl
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd (.str `CryptoVerification.E2E.Pqxdh.ResponderClosure
      s!"responderClosureBinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderClosure
