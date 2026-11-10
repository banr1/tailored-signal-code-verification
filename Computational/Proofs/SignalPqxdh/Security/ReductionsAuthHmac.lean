/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead

/-!
# First-Message MAC to `PrfHmac` Reduction for PQXDH `Auth`

**Checked by Lean.** Black-box reduction `prfHmacOfMu` transforming a multi-key `AeadMuIntCtxtAdv`
into a `PrfHmacAdv` via a first-use key-rank hybrid with deferred forgery checks, instantiated at
`aeadMuIntReductionAuth` as `prfHmacReductionAuth` (`G3.8 → G5`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh OracleComp OracleSpec
open RoKem

abbrev PrfHmacSimSpec : OracleSpec.{0, 0} ((Nat ⊕ PrimQuery) ⊕ PrfHmacQuery) :=
  PrimBaseSpec + prfHmacSpec

def prfHmacEvalQ (m : Bytes) : OracleComp PrfHmacSimSpec Bytes :=
  liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inr (.eval m)))

def prfHmacPrimQ (op : PrimQuery) : OracleComp PrfHmacSimSpec (primSpec.Range op) :=
  embedPrim (spec := prfHmacSpec) (primQ op)

def prfHmacUnif {α : Type} (mx : ProbComp α) : OracleComp PrfHmacSimSpec α :=
  embedPrim (spec := prfHmacSpec) (embedUnif mx)

def etmBody (ct : Bytes) : Bytes := ct.take (ct.length - 8)

def etmTag (ct : Bytes) : Bytes := ct.drop (ct.length - 8)

/-- Simulator state of `prfHmacOfMu` tracking first-use key ranks, challenges, and deferred
    forgeries. -/
structure PrfHmacMuState where
  keys    : List (ℕ × (ℕ × MessageKeys)) := []
  chal    : List (ℕ × (Bytes × Bytes)) := []
  pending : List (ℕ × Bytes × Bytes) := []
  bad     : Bool := false

def prfHmacMuKey (i : ℕ) (st : PrfHmacMuState) :
    OracleComp PrfHmacSimSpec ((ℕ × MessageKeys) × PrfHmacMuState) :=
  match st.keys.lookup i with
  | some e => pure (e, st)
  | none => do
    let mk ← prfHmacUnif sampleMessageKeys80
    let e := (st.keys.length, mk)
    pure (e, { st with keys := (i, e) :: st.keys })

def prfHmacTagQ (j r : ℕ) (x : Bytes) : OracleComp PrfHmacSimSpec Bytes :=
  if r < j then prfHmacUnif sampleBytes32 else prfHmacEvalQ x

def prfHmacPendingHit (pending : List (ℕ × Bytes × Bytes)) (r : ℕ) (x t : Bytes) : Bool :=
  pending.any (fun e => e.1 == r && e.2.1 == x && e.2.2 == t.take 8)

/-- Simulate one `AeadMuIntQuery` at target key rank `j`, answering every `tryForge` with
    `false`. -/
def prfHmacMuStep (j : ℕ) (q : AeadMuIntQuery) (st : PrfHmacMuState) :
    OracleComp PrfHmacSimSpec (aeadMuIntSpec.Range q × PrfHmacMuState) :=
  match q with
  | .encOnce i ad pt =>
    match st.chal.lookup i with
    | some _ => pure (none, st)
    | none => do
      let ((r, mk), st) ← prfHmacMuKey i st
      let ct ← prfHmacPrimQ (.aeadEnc mk ad pt)
      if r ≤ j then do
        let x0 := aeadMacInput ad (etmBody ct)
        let t ← prfHmacTagQ j r x0
        let ct' := etmBody ct ++ t.take 8
        pure (some ct',
          { st with
            chal := (i, (ad, ct')) :: st.chal
            pending := st.pending.filter (fun e => !(e.1 == r && e.2.1 == x0))
            bad := st.bad || prfHmacPendingHit st.pending r x0 t })
      else
        pure (some ct, { st with chal := (i, (ad, ct)) :: st.chal })
  | .tryForge i ad ct =>
    if st.chal.lookup i == some (ad, ct) then pure (false, st)
    else do
      let ((r, mk), st) ← prfHmacMuKey i st
      let x := aeadMacInput ad (etmBody ct)
      let fresh : Bool :=
        match st.chal.lookup i with
        | some (ad0, ct0) => x != aeadMacInput ad0 (etmBody ct0)
        | none => true
      if fresh ∧ 24 ≤ ct.length then
        if r ≤ j then
          pure (false, { st with pending := (r, x, etmTag ct) :: st.pending })
        else do
          let res ← prfHmacPrimQ (.aeadDec mk ad ct)
          pure (false, { st with bad := st.bad || res.isSome })
      else pure (false, st)

def prfHmacOfMuRunAt (j : ℕ) (B : AeadMuIntCtxtAdv) :
    OracleComp PrfHmacSimSpec (Unit × PrfHmacMuState) :=
  OracleComp.construct
    (C := fun _ => PrfHmacMuState → OracleComp PrfHmacSimSpec (Unit × PrfHmacMuState))
    (fun a s => pure (a, s))
    (fun q _ r s =>
      match q with
      | Sum.inl pq => do
        let u ← liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl pq))
        r u s
      | Sum.inr mq => do
        let p ← prfHmacMuStep j mq s
        r p.1 p.2)
    B.run {}

def prfHmacFinish (j : ℕ) (pending : List (ℕ × Bytes × Bytes)) :
    List (ℕ × Bytes) → OracleComp PrfHmacSimSpec Bool
  | [] => pure false
  | (r, x) :: pts => do
    let t ← prfHmacTagQ j r x
    let rest ← prfHmacFinish j pending pts
    pure (prfHmacPendingHit pending r x t || rest)

def prfHmacOfMuRun (B : AeadMuIntCtxtAdv) : OracleComp PrfHmacSimSpec Bool := do
  let j ← prfHmacUnif (sampleIndexRange (B.q_enc + B.q_dec))
  let (_, st) ← prfHmacOfMuRunAt j B
  let hit ← prfHmacFinish j st.pending (st.pending.map (fun e => (e.1, e.2.1))).dedup
  return (st.bad || hit)

/-- Black-box `PrfHmacAdv` constructed from a multi-key INT-CTXT adversary `B`. -/
def prfHmacOfMu (B : AeadMuIntCtxtAdv) : PrfHmacAdv where
  run    := prfHmacOfMuRun B
  q_prf  := B.q_dec + 1
  q_prim := B.q_prim + B.q_enc + B.q_dec

/-- Shallow `PrfHmac` reduction for `Auth` (`G3.8 → G5`). -/
def prfHmacReductionAuth (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfHmacAdv :=
  prfHmacOfMu (aeadMuIntReductionAuth S b A)

end SignalPqxdh.Security
