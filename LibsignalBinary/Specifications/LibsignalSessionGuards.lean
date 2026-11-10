/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSession
public import GeneratedLean.LibsignalSessionObj

/-!
# Image Symbol and Offset Guards for `LibsignalSession`

**Checked by Lean.** Kernel-reflection guards pinning `logFilterAddr` and symbol uniqueness in
`libsignalSessionImage` (`log::MAX_LOG_LEVEL_FILTER` and `RatchetState::consume_message_key`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Guard (kernel-checked): the linker placed the 8-byte extern datum `log::MAX_LOG_LEVEL_FILTER`
at `logFilterAddr img` in every loaded image. -/
theorem logFilterAddr_extern {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    Obj.lookup "log::MAX_LOG_LEVEL_FILTER" img.externData = some (logFilterAddr img, 8) := by
  obtain ⟨_, _, _, _, _, himg⟩ := ProofLib.ObjectLoad.load_eq_ok h
  rw [congrArg Obj.Image.externData himg]
  rfl

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): `logFilterAddr img` is what the machine's symbol table
(`s.symtab = img.symtab`, from `Spec.inImage`) gives for `log::MAX_LOG_LEVEL_FILTER`. -/
theorem logFilterAddr_symtab {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    img.symtab "" "log::MAX_LOG_LEVEL_FILTER" = some (logFilterAddr img) := by
  obtain ⟨_, _, _, _, _, himg⟩ := ProofLib.ObjectLoad.load_eq_ok h
  rw [himg]
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): `fnAddr` takes the first match in `symbols`; exactly one entry has
cmk's name, so the order of objects in the image cannot change `cmkEntry`. -/
theorem cmk_unique :
    (libsignalSessionImage.symbols.filter
      (·.1 == "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")).length =
      1 := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): exactly one extern-data entry is `log::MAX_LOG_LEVEL_FILTER`. -/
theorem log_extern_unique :
    (libsignalSessionImage.externData.filter (·.1 == "log::MAX_LOG_LEVEL_FILTER")).length = 1 := by
  rfl_kernel

end CryptoVerification.LibsignalSession
