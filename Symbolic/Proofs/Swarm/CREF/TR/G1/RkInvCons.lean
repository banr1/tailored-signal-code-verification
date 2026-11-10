/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# `ShapeId` for Constructed Receive-Representation Ratchet Keys

Proves `ShapeId` for honest ephemeral DH public keys (`shapeId_dhPk_randTerm32`) together with
helper lemmas on `X25519.Variant` shapes and `findRecvChain` lookup.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open

open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal.HwEvents
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain)
open CryptoProofLib.Refinement (ExternInterpretation)


unseal DY.Bytes in
private instance subVariant0RkInv (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem shape_x25519Variant_raw_tr (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k : DY.Bytes) (v : Fin 4) (t : Fin 8 := 0) :
    (gamma' i S g (({ key := k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack)).shape =
      ({ key := (gamma' i S g k).shape, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack := by
  unfold gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

/-- Every honest-send ephemeral DH public key `dhPk (randTerm t 32)` satisfies `ShapeId`. -/
theorem shapeId_dhPk_randTerm32 (t : Nat) : ShapeId (dhPk (randTerm t 32)) :=
  shapeId_dhPk (shapeId_randTerm32 t)

theorem mem_recv_of_findRecvChain_eq_some {chains : List RecvChain} {rk : DY.Bytes} {c : RecvChain}
    (h : findRecvChain chains rk = some c) :
    c ∈ chains ∧ c.ratchetKey = rk := by
  unfold findRecvChain at h
  have hbeq : (c.ratchetKey == rk) = true :=
    List.find?_some (p := fun x : RecvChain => x.ratchetKey == rk) h
  exact ⟨List.mem_of_find?_eq_some h, beq_iff_eq.mp hbeq⟩

end Symbolic.Swarm.CREF.TR.G1
