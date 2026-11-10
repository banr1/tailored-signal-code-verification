/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionObj
public import Mathlib.Tactic.ToDual
public import ProofLib.SepLogic.Bytes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux
open ProofLib.ProgramReflection

/-! ## `.data.rel.ro` Vtable Predicates (`0x87a30..0x87d40`) -/

/-- `.data.rel.ro` future vtable (32 B): `(drop, size, align, poll)`. -/
def futVtableAtP (vtAddr dropAddr size align pollAddr : BitVec 64) : SepProp :=
  (vtAddr ↦₆₄ᵣ dropAddr) ∗
  ((vtAddr + 0x08#64) ↦₆₄ᵣ size) ∗
  ((vtAddr + 0x10#64) ↦₆₄ᵣ align) ∗
  ((vtAddr + 0x18#64) ↦₆₄ᵣ pollAddr)

set_option maxRecDepth 2000000 in
private theorem data_len_ge_field :
    num% (ls_field% dataLen) ≤ libsignalSessionImage.data.length :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

theorem rodata64_intro_atP {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {off : Nat} {val : BitVec 64}
    (h1 : libsignalSessionImage.dataOff ≤ off)
    (h2 : (off - libsignalSessionImage.dataOff) + 8 ≤ num% (ls_field% dataLen))
    (h3 : noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss)
      (off - libsignalSessionImage.dataOff) 8 = true)
    (h4 : inLiRoData libsignalSessionImage off 8 = true)
    (h5 : (libsignalSessionImage.data.drop
      (off - libsignalSessionImage.dataOff)).take 8 = unpack64 val)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ val) ∗ P := by
  have hh := loads_rodata_holdsBytes himg hF (off := off) (n := 8) (bs := unpack64 val)
    h1 (Nat.le_trans h2 data_len_ge_field) h3 h4 (unpack64_length _) h5
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

end CryptoVerification.E2E.Pqxdh.WireEntries
