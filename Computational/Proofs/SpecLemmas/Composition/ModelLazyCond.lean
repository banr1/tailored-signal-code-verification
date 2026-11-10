/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore

/-!
# Exact and lazy prefix experiments for the multi-session composition driver

**Checked by Lean.** Defines the parameterized model-state E2E driver over a `KeyInd` oracle `ki`
and the exact and lazy hybrid prefix experiments `bhPrefixExactFullExpWith` and
`bhPrefixLazyFullExpWith` equated by the lazy-sampling hypothesis of multi-session composition.
Because the driver blocks adversary `testSession` queries (`bhDrvKiQueryOk`, DEV-C12) and promotes
at most one session per ephemeral key (`bhE2EGuard`), replacing the tested session key at hybrid
index `k` with a uniform `SampledSessionKey` preserves the adversary's view.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec

namespace Computational.Proofs.SpecLemmas.Composition.ModelLazyCond

open CryptoGames.SM (initState)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (SampledSessionKey BHE2EDrvState bhE2EGuard bhIdKeyOf bhBytesWord
  paramsIdsWithSpqr sessionSchemeFixedSpk BHModelInst ModelDriverInstanceMeta bhKeySOf
  allTestedSessionsFresh bhE2EDrvWon bhTargetGameSpec bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror
  bhE2EStepLocalSm bhUnpackSmResp)

/-- Samples the initial `SampledSessionKey` and SM challenge bit of a promoted instance from the
`.testSession` and `.revealSpkSk` responses. -/
abbrev ModelDriverKeyBitGen :=
  SignalPqxdh.KeyIndResponse → SignalPqxdh.KeyIndResponse → ProbComp (SampledSessionKey × Bool)

/-- Instance-indexed `ModelDriverKeyBitGen` parameterized by `σ.insts.length`. -/
abbrev BHDrvPrefixKeyBitGen :=
  ℕ → ModelDriverKeyBitGen

/-- Initializes and appends a promoted `sessionSchemeFixedSpk` instance when `bhE2EGuard` and
32-byte key lengths hold. -/
def bhFinishStartSpkGen {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (kb : SampledSessionKey × Bool) :
    Option ℕ × BHE2EDrvState S ℓ :=
  match bhE2EGuard σ sid, kr1, kr2 with
  | some (hdr, bnd, (u, j)), .drKeyResp dk, .spkSkResp spkSk =>
    if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
       dk.pqrKey.length == 32 && spkSk.length == 32 then
      let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
      let spkCoins := bhBytesWord spkSk
      let spqr := spqrV1SessionUniformCoins C.F K
      let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ spkCoins
      let gs := some (initState sch.sendPart kb.1 kb.2)
      let inst : BHModelInst S ℓ := { sid, hdr, idA, idB, spkCoins, gs }
      let im : ModelDriverInstanceMeta S :=
        { respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }
      (some σ.insts.length,
       { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })
    else (none, σ)
  | _, _, _ => (none, σ)

/-- Exact hybrid generator at step `k`: derives `bhKeySOf dk ac` with challenge bit `b_k` at `k`,
`true` below `k`, and `false` above `k`. -/
def bhMkPrefixExact (k : ℕ) (b_k : Bool) : BHDrvPrefixKeyBitGen :=
  fun len kr1 _ => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let dk := match kr1 with | .drKeyResp dk => dk | _ => default
    let b_use := if len == k then b_k else decide (len < k)
    return (bhKeySOf dk ac, b_use)

/-- Lazy hybrid generator at step `k`: substitutes a fresh uniform `SampledSessionKey` at valid
instance `k`. -/
def bhMkPrefixLazy (k : ℕ) (b_k : Bool) : BHDrvPrefixKeyBitGen :=
  fun len kr1 kr2 => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let b_use := if len == k then b_k else decide (len < k)
    match kr1, kr2 with
    | .drKeyResp dk, .spkSkResp spkSk =>
      if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
         dk.pqrKey.length == 32 && spkSk.length == 32 && len == k then
        let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
        return (k_fresh, b_k)
      else
        return (bhKeySOf dk ac, b_use)
    | .drKeyResp dk, _ =>
      return (bhKeySOf dk ac, b_use)
    | _, _ =>
      return (bhKeySOf default ac, b_use)

/-- Post-observation of a model-state E2E driver run: outputs a uniform coin if a tested session
lost freshness, otherwise prioritizes adversary win flags over the guess `b'`. -/
def bhComposedPostObs {S : SignalPqxdh.Setup} {ℓ : ℕ} (P : SignalPqxdh.Primitives) :
    Bool × BHE2EDrvState S ℓ → ProbComp Bool :=
  fun ⟨b', σ⟩ =>
    if !allTestedSessionsFresh P σ.st then do
      let coin ← $ᵗ Bool
      return coin
    else
      return (if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b')

namespace Prefix1Key

/-- Promotes `sid` under `bhE2EGuard` by querying `ki` for `.testSession` and `.revealSpkSk` and
sampling `(key, bit)` via `mkKeyBit`. -/
def bhE2ELocalStartGenWith {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (mkKeyBit : ModelDriverKeyBitGen)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp (Option ℕ × BHE2EDrvState S ℓ) := do
  match bhE2EGuard σ sid with
  | none => return (none, σ)
  | some (_, _, (u, j)) =>
    let (kr1, st1) ← (ki (.testSession sid)).run σ.st
    let (kr2, st2) ← (ki (.revealSpkSk u j)).run st1
    let kb ← mkKeyBit kr1 kr2
    return bhFinishStartSpkGen C K { σ with st := st2 } sid kr1 kr2 kb

/-- Model-state E2E driver `QueryImpl` over `ki` for a fixed `ModelDriverKeyBitGen`. -/
def bhE2EDrvImplGenWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkKeyBit : ModelDriverKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← liftM (bhE2ELocalStartGenWith ki C K mkKeyBit σ sid)
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← liftM (bhE2EStepLocalSm C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Model-state E2E driver `QueryImpl` over `ki` dispatching to `mkP σ.insts.length` at each
promotion. -/
def bhE2EDrvImplPrefixWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) ProbComp) := fun q =>
  StateT.mk fun σ =>
    (bhE2EDrvImplGenWith ki P C K qep decT encT (mkP σ.insts.length) q).run σ

/-- Exact hybrid prefix experiment at step `k` with bit `b_k`. -/
def bhPrefixExactFullExpWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixExact k b_k)) B).run {} >>=
    bhComposedPostObs P

/-- Lazy hybrid prefix experiment at step `k` with bit `b_k`. -/
def bhPrefixLazyFullExpWith (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWith ki P C K qep decT encT (bhMkPrefixLazy k b_k)) B).run {} >>=
    bhComposedPostObs P

end Prefix1Key

end Computational.Proofs.SpecLemmas.Composition.ModelLazyCond

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.E2E
export Computational.Proofs.SpecLemmas.Composition.ModelLazyCond (
  ModelDriverKeyBitGen BHDrvPrefixKeyBitGen bhFinishStartSpkGen
  bhMkPrefixExact bhMkPrefixLazy bhComposedPostObs
)
end CryptoVerification.E2E
namespace CryptoVerification.E2E.Prefix1Key
export Computational.Proofs.SpecLemmas.Composition.ModelLazyCond.Prefix1Key (
  bhE2ELocalStartGenWith bhE2EDrvImplGenWith bhE2EDrvImplPrefixWith
  bhPrefixExactFullExpWith bhPrefixLazyFullExpWith
)
end CryptoVerification.E2E.Prefix1Key
-- AUTO-BRIDGE END
