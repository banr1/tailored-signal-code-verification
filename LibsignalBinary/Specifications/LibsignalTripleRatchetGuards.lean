/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import GeneratedLean.LibsignalSessionObj

/-!
# Symbol and Stub Guards for `LibsignalTripleRatchet`

**Checked by Lean.** Kernel-reflection guards checking on `libsignalSessionImage` that all root
entry points (`tripleRatchetEntryNames`, `msgDecryptName`) are unique symbols, all hooked/unhooked
extern names (`tripleRatchetStubNames`) exist in `stubs`, and all `inImageCalleeNames` resolve to
unique in-image code symbols rather than stubs.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

/-- The symbol names of the five entry points and of `spqr::send::<HookRng>`. -/
def tripleRatchetEntryNames : List String :=
  [tryDecryptName, otrFromName, otrEncryptName, otrApplyName, tryFromName, spqrSendName]

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: each root name has exactly one entry in the image's symbols (so `fnAddr`, which takes
the first match, is unambiguous, and the names have no typo). -/
theorem tripleRatchetEntries_unique :
    tripleRatchetEntryNames.all
      (fun n => (libsignalSessionImage.symbols.filter (·.1 == n)).length == 1) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: the host of the inlined `try_decrypt_from_record` region,
`session_message_decrypt_signal` (`msgDecryptName`), has exactly one entry in the image's symbols
(so `recordRegionEntry` / `recordRegionExit` are unambiguous). -/
theorem recordRegion_unique :
    ((libsignalSessionImage.symbols.filter (·.1 == msgDecryptName)).length == 1) = true := by
  rfl_kernel

/-- Every stub name `tripleRatchetExterns` or `TripleRatchetHooks` mentions. -/
def tripleRatchetStubNames : List String :=
  [dhName, pubFromSecretName, staticDropName, sharedDropName, rngFillName, aesEncName, aesDecName,
   formatInnerName, fmtWriteName, allocZeroedName] ++
    noHookNames

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: each of them is an extern stub of the image (no typo). -/
theorem tripleRatchetStubs_present :
    tripleRatchetStubNames.all (fun n => libsignalSessionImage.stubs.any (·.1 == n)) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard: each in-image callee (`inImageCalleeNames`) is in-image code, not a stub: exactly
one symbol entry and no stub entry. So no hook stands for it, and the proofs execute its code. -/
theorem inImageCallees_code :
    inImageCalleeNames.all (fun n =>
      (libsignalSessionImage.symbols.filter (·.1 == n)).length == 1 &&
        !libsignalSessionImage.stubs.any (·.1 == n)) = true := by
  rfl_kernel

end CryptoVerification.LibsignalTripleRatchet
