/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkHole
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Known-Peer-Key Seed Spine Grammar

Defines `SpineRkK K B b v`, strengthening `SpineRk B b v` with a predicate `K` on the peer public
key at every PQXDH base DH hole (`IkmHolesK K`) and every `kdfRk` step (`DhHoleK K`), together with
the forgetful projection `SpineRkK.toSpineRk`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman (dh)
open DY.Libsignal.TripleRatchet (kdfCk kdfRk chainKeyAt)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)

/-- A DH hole `d = dh pk' (randTerm t 32)` whose peer public key `pk'` satisfies `K`. -/
def DhHoleK (K : DY.Bytes → Prop) (d : DY.Bytes) : Prop :=
  ∃ pk' t, d = dh pk' (randTerm t 32) ∧ K pk'

/-- A PQXDH input `ikm = pqxdhIkm a b e d ss` all of whose DH parts are `DhHoleK K`. -/
def IkmHolesK (K : DY.Bytes → Prop) (ikm : DY.Bytes) : Prop :=
  ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
    ikm = pqxdhIkm a b e d ss ∧ DhHoleK K a ∧ DhHoleK K b ∧ DhHoleK K e ∧
    ∀ v, d = some v → DhHoleK K v

/-- `SpineRk B` with known peer keys (`K`) at every DH hole: `IkmHolesK K` at the PQXDH base,
`DhHoleK K` at every `kdfRk` step. -/
inductive SpineRkK (K : DY.Bytes → Prop) (B : Bool → DY.Bytes → Prop) : Bool → DY.Bytes → Prop
  | hsRk {b : Bool} {ikm : DY.Bytes} : B b ikm → IkmHolesK K ikm → SpineRkK K B b (pqxdhKdf ikm).rk
  | hsCk {b : Bool} {ikm : DY.Bytes} : B b ikm → IkmHolesK K ikm → SpineRkK K B b (pqxdhKdf ikm).ck
  | rkStep1 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineRkK K B b rk → RkHole b rk dhOut → DhHoleK K dhOut → SpineRkK K B (!b) (kdfRk rk dhOut).1
  | rkStep2 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineRkK K B b rk → RkHole b rk dhOut → DhHoleK K dhOut → SpineRkK K B (!b) (kdfRk rk dhOut).2
  | ckStep1 {b : Bool} {ck : DY.Bytes} : SpineRkK K B b ck → SpineRkK K B b (kdfCk ck).1
  | ckStep2 {b : Bool} {ck : DY.Bytes} : SpineRkK K B b ck → SpineRkK K B b (kdfCk ck).2

theorem SpineRkK.mono {K K' : DY.Bytes → Prop} {B B' : Bool → DY.Bytes → Prop}
    (hK : ∀ x, K x → K' x) (hB : ∀ c m, B c m → B' c m) {b : Bool} {u : DY.Bytes}
    (hu : SpineRkK K B b u) : SpineRkK K' B' b u := by
  have hD : ∀ d, DhHoleK K d → DhHoleK K' d := fun _ ⟨pk', t, hd, hk⟩ => ⟨pk', t, hd, hK _ hk⟩
  have hI : ∀ m, IkmHolesK K m → IkmHolesK K' m := fun _ ⟨a, b, e, d, ss, hm, ha, hb, he, hdd⟩ =>
    ⟨a, b, e, d, ss, hm, hD _ ha, hD _ hb, hD _ he, fun v hv => hD _ (hdd v hv)⟩
  induction hu with
  | hsRk hi hk => exact .hsRk (hB _ _ hi) (hI _ hk)
  | hsCk hi hk => exact .hsCk (hB _ _ hi) (hI _ hk)
  | rkStep1 _ hd hk ih => exact .rkStep1 ih hd (hD _ hk)
  | rkStep2 _ hd hk ih => exact .rkStep2 ih hd (hD _ hk)
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

theorem spineRkK_chainKeyAt {K : DY.Bytes → Prop} {B : Bool → DY.Bytes → Prop} {b : Bool}
    {ck : DY.Bytes} (h : SpineRkK K B b ck) : ∀ n : Nat, SpineRkK K B b (chainKeyAt ck n)
  | 0 => h
  | n + 1 => spineRkK_chainKeyAt (.ckStep1 h) n

end Symbolic.Swarm.CREF.TR.G1.Spine
