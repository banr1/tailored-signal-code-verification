/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Game

/-!
# Key indistinguishability with one-key identities and the real key derivation

**Trusted: definitions used by the statement.** The CLI statements use `pqxdhKeyIndImpl1KeyReal`,
`pqxdhKeyInd1KeyExpForHandshake`, `pqxdhKeyInd1KeyRealExp`, and `KeyInd1KeyRealAdvantage`, and
Lemma 1 (`Security/HeadlineDelta.lean`) uses `pqxdhKeyIndImpl1KeyReal` and
`pqxdhKeyInd1KeyExpForHandshake` via `KeyInd1KeyRo.lean`. Read with
`Computational/Specifications/Pqxdh/Game.lean` (`pqxdhKeyIndImpl`). See
`Computational/docs/TRUSTED_BASE.md` and `Computational/docs/DEVIATIONS.md` (DEV-CLI16).

Whereas `pqxdhKeyIndImpl1KeyRo` (`KeyInd1KeyRo.lean`, bounded by Lemma 1) idealizes `hkdfDerive96`
as a lazily sampled random oracle (`HkdfRO`, DEV-PQ14), this file defines the real one-key
handshake game `pqxdhKeyInd1KeyRealExp` using concrete `P.hkdfDerive96` and libsignal's
single-scalar X25519/XEdDSA identities (as in `bhDrvKeyInd` at `useRo = false` in
`Computational/Specifications/Game/StatementBinaryHarnessCore.lean`). The CLI statements state
clause 1 directly against `KeyInd1KeyRealAdvantage` and relate clause 2 to `KeyInd1KeyRoAdvantage`
via `KeyIndRoGap`.

Both one-key games start from `KeyIndState.empty`, disable `.revealDhSecrets` (which belongs to the
harvest-now-decrypt-later game), and evaluate classical session freshness (`isKeyIndInitStillFresh`
and `isKeyIndRespStillFresh` with flag `true`, as in `allTestedSessionsFresh` in the CLI game).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

/-- Key-indistinguishability oracle with single-scalar X25519/signing identities and real HKDF
derivation (`P.hkdfDerive96`). `.initPrin u` shares one sampled scalar across X25519 and signing,
`.roQuery` evaluates `P.hkdfDerive96`, `.revealDhSecrets` returns `.noneResp`, and all other
queries delegate to `pqxdhKeyIndImpl false S P`. -/
def pqxdhKeyIndImpl1KeyReal (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp) := fun q =>
  match q with
  | .initPrin u => do
    let st ← get
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM sampleScalar32
    let ikAPk := P.x25519Base secIKA0
    let entry : PrincipalEntry :=
      { secIKA0 := secIKA0, ikAPk := ikAPk,
        secIKAsign := secIKA0, ikSignPk := ikAPk, corrupted := false }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikAPk
  | .roQuery secrets => do
    let st ← get
    let (dk, roCache') ← liftM (evalHkdfOrRo false P st.roCache secrets)
    set { st with roCache := roCache' }
    return .drKeyResp dk
  | .revealDhSecrets => return .noneResp
  | q => pqxdhKeyIndImpl false S P q

/-- One-key key-indistinguishability experiment over handshake oracle `ki`: runs `A` from
`KeyIndState.empty S secb` and returns a uniform coin if any tested session fails classical
freshness (flag `true`), or `b' == secb` otherwise. -/
def pqxdhKeyInd1KeyExpForHandshake (S : Setup) (P : Primitives)
    (ki : QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp))
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) + ki
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested ||
        isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested ||
        isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles finalSt.sessions r)
  if !allTestedClean then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

/-- One-key key-indistinguishability experiment with real HKDF (`pqxdhKeyIndImpl1KeyReal`). -/
def pqxdhKeyInd1KeyRealExp (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  pqxdhKeyInd1KeyExpForHandshake S P (pqxdhKeyIndImpl1KeyReal S P) A

/-- Distinguishing advantage of `A` in `pqxdhKeyInd1KeyRealExp`. -/
noncomputable def KeyInd1KeyRealAdvantage (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ℝ≥0∞ :=
  𝒟[pqxdhKeyInd1KeyRealExp S P A].boolBias

end SignalPqxdh
