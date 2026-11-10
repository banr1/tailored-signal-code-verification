/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables
public import Computational.Proofs.SpecLemmas.Reductions.ReductionDsl.Core
import Computational.Proofs.ReductionDsl.Notation

/-!
# `pubRed` as a `ReductionDsl` program

Costed `ReductionDsl` witness program `pubRedProg` for the FS-AEAD public-part-moving reduction
`pubRed`.
-/

@[expose] public section

namespace CryptoGames.FSAEAD.Costed

open ReductionDsl
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)        => `(rdsl_pat| .inl $p)
  | `(rdsl_pat| .challenge $p:term)       => `(rdsl_pat| .inr (.inl $p))
  | `(rdsl_pat| .corruptSender $p:term)   => `(rdsl_pat| .inr (.inr (.inl $p)))
  | `(rdsl_pat| .corruptReceiver $p:term) => `(rdsl_pat| .inr (.inr (.inr (.inl $p))))
  | `(rdsl_pat| .deliver $p:term)         => `(rdsl_pat| .inr (.inr (.inr (.inr (.inl $p)))))
  | `(rdsl_pat| .inject $p:term)          => `(rdsl_pat| .inr (.inr (.inr (.inr (.inr $p)))))

variable {SS RS AD Pub M C : Type}

local notation "PT" => Ty (fsSig SS RS AD Pub M C)

local notation "PI" => fsaeadIface (SS := SS) (RS := RS) (AD := AD) (Pub := Pub) (M := M)
  (C := C) (Ty.prod (bt FSort.ad) (bt FSort.pub))

variable (pubOf : C → Option Pub) (k : ℕ)

local notation "OO" => fsOps SS RS AD Pub M C pubOf k
local notation "CC" => Comp OO PI

def withPubE {Γ : List PT} (pv : Var Γ (bt .pub)) :
    Expr OO (rrTy (bt .msg) :: Γ) (rrTy (.prod (bt .pub) (bt .msg))) :=
  rdslExpr [r] =>
    match r with
    | .inl _ => .inl ()
    | .inr (st, optM) =>
      .inr (st, match optM with
        | none => none
        | some m => some (extVar pv, m))

def pubHandle : CC [.bool, pubQ] (.prod pubR .bool) :=
  rdsl [ended, q] do
    match q with
    | .transmit (a, (p, m)) =>
      r ← query FsaeadTag.tr ((a, p), m)
      return (.inl r, ended)
    | .challenge (a, (p₀, m₀), (_p₁, m₁)) =>
      r ← query FsaeadTag.ch ((a, p₀), m₀, m₁)
      return (.inl r, ended)
    | .corruptSender _ =>
      r ← query FsaeadTag.cs ()
      return (.inr (.inl r), ended)
    | .corruptReceiver _ =>
      r ← query FsaeadTag.cr ()
      let ended' := match r with | none => ended | some _ => true
      return (.inr (.inr (.inl r)), ended')
    | .deliver (a, c) =>
      match op () c with
      | none => return (.inr (.inr (.inr none)), ended)
      | some p =>
        r ← query FsaeadTag.dl ((a, p), c)
        let r' := match r with | none => none | some _ => some (withPubE pubOf k (parentVar p))
        return (.inr (.inr (.inr r')), ended)
    | .inject (a, c) =>
      match op () c with
      | none =>
        let r' := if ended then none else some (.inl ())
        return (.inr (.inr (.inr r')), ended)
      | some p =>
        r ← query FsaeadTag.ij ((a, p), c)
        let r' := match r with | none => none | some _ => some (withPubE pubOf k (parentVar p))
        return (.inr (.inr (.inr r')), ended)

/-- Costed `ReductionDsl` program for the public-part-moving reduction `pubRed`. -/
def pubRedProg : CostedReduction OO PI (spec SS RS AD (Pub × M) C) pubCodec .unit .unit .bool .bool where
  σ := .bool
  init := rdsl [_] do return ((), false)
  handle := pubHandle pubOf k
  finish := rdsl [_, guess] do return guess

end CryptoGames.FSAEAD.Costed
