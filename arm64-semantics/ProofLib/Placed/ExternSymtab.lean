/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Interned
public import ProofLib.ObjectLoad

/-!
# Extern Symbol Agreement with ELF `.symtab`

Provides a kernel-decidable check (`externSymtabOk`) proving that a layout's interned address table
agrees with an `ElfImage` symbol table on a list of extern symbol indices (`externSymtab_of`).
-/

@[expose] public section

namespace Arm64.Obj.Interned

open Arm64.Process ProofLib.ObjectLoad ProofLib.ProgramReflection

theorem names_getD_ofList {names : List String} {nameChars : List (List Char)}
    (hnames : names = nameChars.map String.ofList) (i : Nat) :
    names.getD i "" = String.ofList (nameChars.getD i []) := by
  subst hnames
  induction nameChars generalizing i with
  | nil => rfl
  | cons c cs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Checks that `nameChars` is strictly sorted and that each index `i ∈ ids` resolves to a unique
    entry in `enc` equal to `addrs.getD i 0#64`. -/
def externSymtabOk (addrs : List (BitVec 64)) (nameChars : List (List Char)) (ids : List Nat)
    (enc : EncSymTable (BitVec 64)) : Bool :=
  namesNodup nameChars && ids.all fun i =>
    Nat.blt i nameChars.length &&
      match lookupUniqueEnc (encodeCharKey (nameChars.getD i [])) enc with
      | some a => a == addrs.getD i 0#64
      | none => false

theorem externSymtab_of {names : List String} {nameChars : List (List Char)}
    {addrs : List (BitVec 64)} {ids : List Nat} {img : ElfImage}
    {symChars : List (List Char × BitVec 64)}
    (hnames : names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : externSymtabOk addrs nameChars ids (prepareCharAssocVal symChars) = true) :
    ∀ i ∈ ids, lookupUnique (names.getD i "") img.symbols =
      some (addrs.getD (names.idxOf (names.getD i "")) 0#64) := by
  intro i hi
  simp only [externSymtabOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hnd, hall⟩ := h
  have hnd' := nodup_of_namesNodup hnames hnd
  obtain ⟨hlt, hmatch⟩ := hall i hi
  have hlt' : i < names.length := by
    rw [hnames, List.length_map]; exact blt_iff.1 hlt
  rw [idxOf_getD hnd' hlt',
    lookupUnique_eq_lookupUniqueEnc hsyms rfl (names_getD_ofList hnames i)]
  split at hmatch
  · rename_i a ha
    rw [ha]
    simpa using hmatch
  · cases hmatch

end Arm64.Obj.Interned

end
