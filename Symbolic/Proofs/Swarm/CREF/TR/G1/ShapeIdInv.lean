/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Specifications.Refinement.Concretization
public import Symbolic.Specifications.Refinement.ModelTraces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Double Ratchet Term Shape-Identity Closure

Defines `TermShapeId` (terms whose `.shape` under `gamma'` is identically `u` for all `(i, S, g)`)
and proves closure over Double Ratchet term constructors (`Literal`, `randTerm 32`, `Concat`,
`dhPk`, `dh`, `normalizeX25519Key`, and `kdfExtract`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (lit)
open CryptoProofLib.Refinement (ExternInterpretation)

unseal DY.Bytes in
private instance subRandomSId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subLit0SId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat0SId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkSId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhSId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf0SId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0SId (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-- A term `u : DY.Bytes` whose `.shape` under `gamma'` is identically `u` for all `(i, S, g)`. -/
abbrev TermShapeId (u : DY.Bytes) : Prop :=
  ∀ i S g, (gamma' i S g u).shape = u

theorem termShapeId_literalToBytes (b : ByteArray) :
    TermShapeId (Literal.literalToBytes b) := by
  intro i S g
  unfold gamma'
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]
  rfl

theorem termShapeId_litOf (v : HwBytes) : TermShapeId (litOf v) :=
  termShapeId_literalToBytes _

theorem termShapeId_randTerm_of_ne_zero (t n : Nat) (hn : n ≠ 0) :
    TermShapeId (randTerm t n) := by
  intro i S g
  unfold gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  dsimp only [concretizeRandom]
  simp [hn]
  rfl

theorem termShapeId_randTerm32 (t : Nat) : TermShapeId (randTerm t 32) :=
  termShapeId_randTerm_of_ne_zero t 32 (by decide)

theorem termShapeId_dhPk {sk : DY.Bytes} (hsk : TermShapeId sk) : TermShapeId (dhPk sk) := by
  intro i S g
  have h : (gamma' i S g (dhPk sk)).shape = dhPk (gamma' i S g sk).shape := by
    unfold gamma'
    show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
    rfl
  rw [h, hsk i S g]

theorem termShapeId_dh_pack {pk sk : DY.Bytes} (hpk : TermShapeId pk) (hsk : TermShapeId sk) :
    TermShapeId (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := by
  intro i S g
  have h : (gamma' i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g pk).shape, sk := (gamma' i S g sk).shape } :
        DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
    unfold gamma'
    show ((({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]
    rfl
  rw [h, hpk i S g, hsk i S g]

theorem termShapeId_of_dhPk {sk : DY.Bytes} (h : TermShapeId (dhPk sk)) : TermShapeId sk := by
  intro i S g
  have h1 : (gamma' i S g (dhPk sk)).shape = dhPk (gamma' i S g sk).shape := by
    unfold gamma'
    show ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape = _
    rw [DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
    rfl
  have h2 := h i S g
  rw [h1] at h2
  have h3 := congrArg (fun u : DY.Bytes => u.view? DY.DiffieHellman.DhPk.SubF) h2
  change DY.Bytes.view? (({ sk := (gamma' i S g sk).shape } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
      DY.DiffieHellman.DhPk.SubF =
    DY.Bytes.view? (({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)
      DY.DiffieHellman.DhPk.SubF at h3
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at h3
  exact congrArg DY.DiffieHellman.DhPk.SubF.sk h3

theorem termShapeId_dh {pk sk : DY.Bytes} (hpk : TermShapeId pk) (hsk : TermShapeId sk) :
    TermShapeId (DY.DiffieHellman.dh pk sk) := by
  dsimp only [CanDH.dh]
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  cases hview : pk.view? DY.DiffieHellman.DhPk.SubF with
  | none => exact termShapeId_dh_pack hpk hsk
  | some y =>
    rw [hview] at hv
    dsimp only at hv
    rcases y with ⟨sk2⟩
    have hpk' : TermShapeId (BytesView.pack ({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes)) := by
      rw [hv]
      exact hpk
    have hsk2 : TermShapeId sk2 := termShapeId_of_dhPk hpk'
    by_cases hle : sk ≤ sk2 <;> simp only [hle, ↓reduceIte]
    · exact termShapeId_dh_pack (termShapeId_dhPk hsk2) hsk
    · exact termShapeId_dh_pack (termShapeId_dhPk hsk) hsk2

theorem shape_variant_pack_sid (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (x : DY.X25519.Variant.SubF DY.Bytes) :
    (gamma' i S g x.pack).shape =
      ({ key := (gamma' i S g x.key).shape, variation := x.variation, torsion := x.torsion } :
        DY.X25519.Variant.SubF DY.Bytes).pack := by
  unfold gamma'
  show (x.pack.rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

theorem termShapeId_x25519Key {pk : DY.Bytes} (hpk : TermShapeId pk) :
    TermShapeId (DY.X25519.normalizeX25519Key pk) := by
  unfold DY.X25519.normalizeX25519Key
  have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  cases hview : pk.view? DY.X25519.Variant.SubF with
  | none => exact hpk
  | some x =>
    rw [hview] at hv
    dsimp only at hv
    intro i S g
    have h1 := hpk i S g
    rw [← hv, shape_variant_pack_sid] at h1
    have h2 := congrArg (fun u : DY.Bytes => u.view? DY.X25519.Variant.SubF) h1
    change DY.Bytes.view? (({ key := (gamma' i S g x.key).shape, variation := x.variation, torsion := x.torsion } :
        DY.X25519.Variant.SubF DY.Bytes).pack) DY.X25519.Variant.SubF =
      DY.Bytes.view? (x.pack) DY.X25519.Variant.SubF at h2
    rw [DY.BytesView.view_pack, DY.BytesView.view_pack, Option.some.injEq] at h2
    exact congrArg DY.X25519.Variant.SubF.key h2

end Symbolic.Swarm.CREF.TR.G1
