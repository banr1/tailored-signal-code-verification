/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# FS-AEAD reduction tables and game codecs

**Checked by Lean.** Shared `ReductionDsl` signature, `pubOf` operation table, target oracle
interface, and source game codecs (`pubCodec`, `ratchetCodec`) for Forward-Secure AEAD
(`FSAEAD.spec`).
-/

@[expose] public section

namespace Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables

open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState ReceiveResult spec)
open ReductionDsl (GameCodec Iface Ops Sig Ty)

inductive FSort | ss | rs | ad | pub | msg | ct

variable (SS RS AD Pub M C : Type)

/-- Signature for FS-AEAD reductions with unit-sized sorts. -/
@[reducible] def fsSig : Sig where
  Base := FSort
  den := fun | .ss => SS | .rs => RS | .ad => AD | .pub => Pub | .msg => M | .ct => C
  sz := fun _ _ => 1

def fsStateSampleSort : Bool → FSort
  | true => .ss
  | false => .rs

instance instSampleableHybKey [SampleableType SS] [SampleableType RS] :
    (b : Bool) → SampleableType ((fsSig SS RS AD Pub M C).den (fsStateSampleSort b))
  | true => inferInstanceAs (SampleableType SS)
  | false => inferInstanceAs (SampleableType RS)

/-- Operation table for FS-AEAD exposing the public-header projection `pubOf` at cost `k`. -/
@[reducible] def fsOps (pubOf : C → Option Pub) (k : ℕ) : Ops (fsSig SS RS AD Pub M C) where
  Op := Unit
  dom := fun _ => .base .ct
  cod := fun _ => .opt (.base .pub)
  eval := fun _ c => pubOf c
  cost := fun _ => k

variable {SS RS AD Pub M C}

local notation "FT" => Ty (fsSig SS RS AD Pub M C)

@[reducible] def bt (s : FSort) : FT := .base s

@[reducible] def rrTy (m : FT) : FT := .sum .unit (.prod .nat (.opt m))

def rrEnc : ReceiveResult M → (rrTy (bt .msg) : FT).denote
  | .rejected => .inl ()
  | .accepted i m => .inr (i, m)

inductive FsaeadTag | tr | ch | cs | cr | dl | ij

/-- Target oracle interface for `unifSpec + FSAEAD.spec SS RS adT.denote M C` at unit query and coin
cost. -/
def fsaeadIface (adT : FT) :
    Iface (fsSig SS RS AD Pub M C) (unifSpec + spec SS RS adT.denote M C) where
  fwdU := fun n => query (spec := unifSpec + spec SS RS adT.denote M C) (.inl n)
  uCost := 1
  Tag := FsaeadTag
  dom := fun
    | .tr => .prod adT (bt .msg)
    | .ch => .prod adT (.prod (bt .msg) (bt .msg))
    | .cs | .cr => .unit
    | .dl | .ij => .prod adT (bt .ct)
  cod := fun
    | .tr | .ch => .opt (bt .ct)
    | .cs => .opt (bt .ss)
    | .cr => .opt (.prod (bt .ss) (bt .rs))
    | .dl | .ij => .opt (rrTy (bt .msg))
  enc := fun
    | .tr, x => .inr (.inl (.inl (.inl (.inl (.inl x)))))
    | .ch, x => .inr (.inl (.inl (.inl (.inl (.inr x)))))
    | .cs, x => .inr (.inl (.inl (.inl (.inr x))))
    | .cr, x => .inr (.inl (.inl (.inr x)))
    | .dl, x => .inr (.inl (.inr x))
    | .ij, x => .inr (.inr x)
  dec := fun
    | .tr, _, u => u
    | .ch, _, u => u
    | .cs, _, u => u
    | .cr, _, u => u
    | .dl, _, u => Option.map rrEnc u
    | .ij, _, u => Option.map rrEnc u
  qCost := fun _ => 1
  smp := ReductionDsl.Samplers.empty

section PubCodec

variable {SS RS AD Pub M C : Type}

local notation "PT" => Ty (fsSig SS RS AD Pub M C)

def rrDec : (rrTy (.prod (bt .pub) (bt .msg)) : PT).denote → ReceiveResult (Pub × M)
  | .inl () => .rejected
  | .inr (i, m) => .accepted i m

@[reducible] def pubQ : PT :=
  .sum (.prod (bt .ad) (.prod (bt .pub) (bt .msg)))
  (.sum (.prod (bt .ad) (.prod (.prod (bt .pub) (bt .msg)) (.prod (bt .pub) (bt .msg))))
  (.sum .unit (.sum .unit (.sum (.prod (bt .ad) (bt .ct)) (.prod (bt .ad) (bt .ct))))))

@[reducible] def pubR : PT :=
  .sum (.opt (bt .ct)) (.sum (.opt (bt .ss)) (.sum (.opt (.prod (bt .ss) (bt .rs)))
    (.opt (rrTy (.prod (bt .pub) (bt .msg))))))

/-- Source game codec for `FSAEAD.spec` with messages `Pub × M` (`codecCost = 6`). -/
def pubCodec : GameCodec (fsSig SS RS AD Pub M C) (spec SS RS AD (Pub × M) C) where
  Q := pubQ
  R := pubR
  qenc := fun
    | .inl (.inl (.inl (.inl (.inl x)))) => .inl x
    | .inl (.inl (.inl (.inl (.inr x)))) => .inr (.inl x)
    | .inl (.inl (.inl (.inr x))) => .inr (.inr (.inl x))
    | .inl (.inl (.inr x)) => .inr (.inr (.inr (.inl x)))
    | .inl (.inr x) => .inr (.inr (.inr (.inr (.inl x))))
    | .inr x => .inr (.inr (.inr (.inr (.inr x))))
  rdec := fun
    | .inl (.inl (.inl (.inl (.inl _)))), r => match r with | .inl c => c | _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), r => match r with | .inl c => c | _ => none
    | .inl (.inl (.inl (.inr _))), r => match r with | .inr (.inl s) => s | _ => none
    | .inl (.inl (.inr _)), r => match r with | .inr (.inr (.inl s)) => s | _ => none
    | .inl (.inr _), r => match r with
      | .inr (.inr (.inr x)) => Option.map rrDec x | _ => none
    | .inr _, r => match r with
      | .inr (.inr (.inr x)) => Option.map rrDec x | _ => none
  codecCost := 6

end PubCodec

section RatchetCodec

variable {CK MK AD Pub M C : Type}

local notation "RT" => Ty (fsSig CK MK AD Pub M C)

@[reducible] def rssTy : RT := .prod (bt .ss) .nat

@[reducible] def rrsTy : RT := .prod (bt .ss) (.prod .nat (.list (.prod .nat (bt .rs))))

def rssDec : (rssTy : RT).denote → RatchetSenderState CK
  | (w, i) => ⟨w, i⟩

def rrsDec : (rrsTy : RT).denote → RatchetReceiverState CK MK
  | (w, i, d) => ⟨w, i, d⟩

def rrDecM : (rrTy (bt .msg) : RT).denote → ReceiveResult M
  | .inl () => .rejected
  | .inr (i, m) => .accepted i m

@[reducible] def ratchetQ : RT :=
  .sum (.prod (bt .ad) (bt .msg))
  (.sum (.prod (bt .ad) (.prod (bt .msg) (bt .msg)))
  (.sum .unit (.sum .unit
    (.sum (.prod (bt .ad) (.prod .nat (bt .ct)))
          (.prod (bt .ad) (.prod .nat (bt .ct)))))))

@[reducible] def ratchetR : RT :=
  .sum (.opt (.prod .nat (bt .ct)))
  (.sum (.opt rssTy)
  (.sum (.opt (.prod rssTy rrsTy))
        (.opt (rrTy (bt .msg)))))

/-- Source game codec for the ACD19 Fig. 6 ratchet FS-AEAD game over `RatchetSenderState` and
`RatchetReceiverState` (`codecCost = 6`). -/
def ratchetCodec :
    GameCodec (fsSig CK MK AD Pub M C)
      (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)) where
  Q := ratchetQ
  R := ratchetR
  qenc := fun
    | .inl (.inl (.inl (.inl (.inl x)))) => .inl x
    | .inl (.inl (.inl (.inl (.inr x)))) => .inr (.inl x)
    | .inl (.inl (.inl (.inr x))) => .inr (.inr (.inl x))
    | .inl (.inl (.inr x)) => .inr (.inr (.inr (.inl x)))
    | .inl (.inr x) => .inr (.inr (.inr (.inr (.inl x))))
    | .inr x => .inr (.inr (.inr (.inr (.inr x))))
  rdec := fun
    | .inl (.inl (.inl (.inl (.inl _)))), r => match r with | .inl c => c | _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), r => match r with | .inl c => c | _ => none
    | .inl (.inl (.inl (.inr _))), r => match r with
      | .inr (.inl s) => Option.map rssDec s | _ => none
    | .inl (.inl (.inr _)), r => match r with
      | .inr (.inr (.inl s)) => Option.map (Prod.map rssDec rrsDec) s | _ => none
    | .inl (.inr _), r => match r with
      | .inr (.inr (.inr x)) => Option.map rrDecM x | _ => none
    | .inr _, r => match r with
      | .inr (.inr (.inr x)) => Option.map rrDecM x | _ => none
  codecCost := 6

end RatchetCodec

end Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables

-- AUTO-BRIDGE BEGIN
namespace CryptoGames.FSAEAD.Costed
export Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables (
  FSort FsaeadTag bt fsOps fsSig fsStateSampleSort
  fsaeadIface instSampleableHybKey pubCodec pubQ pubR ratchetCodec
  ratchetQ ratchetR rrDec rrDecM rrEnc rrTy
  rrsDec rrsTy rssDec rssTy
)
end CryptoGames.FSAEAD.Costed
namespace CryptoGames.FSAEAD.Costed.FSort
export Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables.FSort (
  ad ct msg pub rs ss
)
end CryptoGames.FSAEAD.Costed.FSort
namespace CryptoGames.FSAEAD.Costed.FsaeadTag
export Computational.Proofs.SpecLemmas.Reductions.Primitives.FSAEAD.CostedTables.FsaeadTag (
  ch cr cs dl ij tr
)
end CryptoGames.FSAEAD.Costed.FsaeadTag
-- AUTO-BRIDGE END
