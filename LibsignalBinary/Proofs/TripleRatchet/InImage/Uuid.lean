/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse

/-!
# In-Image `<uuid::Uuid>::try_parse` Contract

Exports `uuidTryParse_ok_F`, `uuidTryParse_ok`, `uuidTryParse_ok_at`, and `uuidTryParse_root`,
showing that the compiled `<uuid::Uuid>::try_parse` computes `uuidTryParse` in
`uuidTryParseStack` bytes of stack without calling any extern hook.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr

/-- `<uuid::Uuid>::try_parse` satisfies `uuidTryParseCodeSpec uuidTryParse` for any hook table `hooks`. -/
theorem uuidTryParse_ok_F (b : BitVec 64) (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse) :=
  InImage.UuidTryParse.uuidTryParse_ok_impl b hooks

theorem uuidTryParse_ok_at_F (b : BitVec 64) (hooks : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr name + BitVec.ofNat 64 k)
      (uuidTryParseCodeSpec uuidTryParse) := by
  have h : (libsignalSessionCode.rebase b hooks).fnAddr name + BitVec.ofNat 64 k =
      (libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName := by
    simp only [Program.fnAddr_rebase, ← hk, BitVec.ofNat_add, BitVec.add_assoc]
  rw [h]
  exact uuidTryParse_ok_F b hooks

theorem uuidTryParse_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse) :=
  uuidTryParse_ok_F b (Rust.withPanics (trTrapExterns C abs))

theorem uuidTryParse_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr uuidTryParseName]
  exact subroutine_ok_kit_of_trTrap (uuidTryParse_ok_trap b C abs)

theorem uuidTryParse_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (uuidTryParseCodeSpec uuidTryParse) := by
  have h : (trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k =
      (trTrapProgAt b C abs).fnAddr uuidTryParseName := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, ← hk, BitVec.ofNat_add, BitVec.add_assoc]
  rw [h]
  exact uuidTryParse_ok_trap b C abs

theorem uuidTryParse_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (uuidTryParseCodeSpec uuidTryParse) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (uuidTryParse_ok_at_trap b C abs name k hk)

theorem uuidTryParse_root {img : Obj.Image} (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse) :=
  root_of_tripleRatchetProgAt himg (uuidTryParse_ok img.base C ctl abs)

end CryptoVerification.LibsignalTripleRatchet
