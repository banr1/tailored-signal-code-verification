/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ModelTraces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Role- and Parity-Indexed DH-Hole Predicates

Defines `TopDhSecret`, `RkHole`, `IkmRoleHoles`, and the role- and parity-indexed seed spine
`SpineRk` over PQXDH and Double Ratchet KDF steps.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY.DiffieHellman (dh)
open DY.Libsignal.TripleRatchet (kdfCk kdfRk chainKeyAt)
open DY.Libsignal.PQXDH (pqxdhIkm pqxdhKdf)

/-- The top DH hole of a root key `rk` has public key `pk'` and secret key `randTerm t 32`:
either `rk = (kdfRk r₀ (dh pk' (randTerm t 32))).1` (from `createChain`) or
`rk = (pqxdhKdf (pqxdhIkm (dh pk' (randTerm t 32)) dh2 dh3 dh4 ss)).rk` (from `pqxdhKdf`). -/
def TopDhSecret (rk pk' : DY.Bytes) (t : Nat) : Prop :=
  (∃ r₀, rk = (kdfRk r₀ (dh pk' (randTerm t 32))).1) ∨
  (∃ dh2 dh3 dh4 ss, rk = (pqxdhKdf (pqxdhIkm (dh pk' (randTerm t 32)) dh2 dh3 dh4 ss)).rk)

/-- Role/parity-indexed root-key DH hole invariant for `kdfRk rk d`:
- At `b = false` (`aliceStart` and `dhRatchetStep` 2nd step): `d = dh pk' (randTerm t₁ 32)` where
  `rk`'s top DH hole is `dh pk' (randTerm t₀ 32)` with the SAME `pk'` and an earlier secret `t₀ ≠ t₁`.
- At `b = true` (`recvChainFor` and `dhRatchetStep` 1st step): `d = dh pk' (randTerm t₂ 32)` where
  `rk = st.rk` has top DH hole `dh pk₀' (randTerm t₂ 32)` with the SAME secret `t₂` (`st.dhs`). -/
def RkHole (b : Bool) (rk d : DY.Bytes) : Prop :=
  match b with
  | false => ∃ pk' t₀ t₁, d = dh pk' (randTerm t₁ 32) ∧ TopDhSecret rk pk' t₀ ∧ t₀ ≠ t₁
  | true => ∃ pk' pk₀' t₂, d = dh pk' (randTerm t₂ 32) ∧ TopDhSecret rk pk₀' t₂

/-- Role-indexed DH-hole provenance for a PQXDH `pqxdhIkm a b e d ss` tuple:
- Role `false` (`AliceDone`): `a` uses an `ik` secret (`P_ik`), and `b, e, d` use an `ek` secret (`P_ek`).
- Role `true` (`BobDone`): `a, e` use an `spk` secret (`P_spk`), `b` uses an `ik` secret (`P_ik`),
  and `d` uses an `opk` secret (`P_opk`). -/
def IkmRoleHoles (P_ik P_spk P_opk P_ek : Nat → Prop)
    (c : Bool) (a b e : DY.Bytes) (d : Option DY.Bytes) : Prop :=
  match c with
  | false =>
    (∃ pk' t, a = dh pk' (randTerm t 32) ∧ P_ik t) ∧
    (∃ pk' t, b = dh pk' (randTerm t 32) ∧ P_ek t) ∧
    (∃ pk' t, e = dh pk' (randTerm t 32) ∧ P_ek t) ∧
    (∀ v, d = some v → ∃ pk' t, v = dh pk' (randTerm t 32) ∧ P_ek t)
  | true =>
    (∃ pk' t, a = dh pk' (randTerm t 32) ∧ P_spk t) ∧
    (∃ pk' t, b = dh pk' (randTerm t 32) ∧ P_ik t) ∧
    (∃ pk' t, e = dh pk' (randTerm t 32) ∧ P_spk t) ∧
    (∀ v, d = some v → ∃ pk' t, v = dh pk' (randTerm t 32) ∧ P_opk t)

/-- The role/parity-indexed seed spine with `RkHole b rk dhOut` at `kdfRk` steps. -/
inductive SpineRk (B : Bool → DY.Bytes → Prop) : Bool → DY.Bytes → Prop
  | hsRk {b : Bool} {ikm : DY.Bytes} : B b ikm → SpineRk B b (pqxdhKdf ikm).rk
  | hsCk {b : Bool} {ikm : DY.Bytes} : B b ikm → SpineRk B b (pqxdhKdf ikm).ck
  | rkStep1 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineRk B b rk → RkHole b rk dhOut → SpineRk B (!b) (kdfRk rk dhOut).1
  | rkStep2 {b : Bool} {rk dhOut : DY.Bytes} :
      SpineRk B b rk → RkHole b rk dhOut → SpineRk B (!b) (kdfRk rk dhOut).2
  | ckStep1 {b : Bool} {ck : DY.Bytes} : SpineRk B b ck → SpineRk B b (kdfCk ck).1
  | ckStep2 {b : Bool} {ck : DY.Bytes} : SpineRk B b ck → SpineRk B b (kdfCk ck).2

theorem SpineRk.mono {B B' : Bool → DY.Bytes → Prop}
    (hB : ∀ c m, B c m → B' c m) {b : Bool} {u : DY.Bytes} (hu : SpineRk B b u) :
    SpineRk B' b u := by
  induction hu with
  | hsRk hi => exact .hsRk (hB _ _ hi)
  | hsCk hi => exact .hsCk (hB _ _ hi)
  | rkStep1 _ hd ih => exact .rkStep1 ih hd
  | rkStep2 _ hd ih => exact .rkStep2 ih hd
  | ckStep1 _ ih => exact .ckStep1 ih
  | ckStep2 _ ih => exact .ckStep2 ih

theorem spineRk_chainKeyAt {B : Bool → DY.Bytes → Prop} {b : Bool}
    {ck : DY.Bytes} (h : SpineRk B b ck) : ∀ n : Nat, SpineRk B b (chainKeyAt ck n)
  | 0 => h
  | n + 1 => spineRk_chainKeyAt (.ckStep1 h) n

end Symbolic.Swarm.CREF.TR.G1.Spine
