/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.Session.StatementSession
public import Computational.Specifications.Composition.StatementModel
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest

/-!
# Coin-Only Sampler Guards for Headline Statements

Verifies that every `ReductionDsl.Samplers` table reachable from the computational headline
statements draws uniform coins over unit domains (`sDom = .unit`) without referencing protocol or
game state, and that the shared E2E sampler and operator tables satisfy block-size honesty. Kernel
theorems check `atomicBaseSamplers` and the E2E target/adapter interfaces, while a `#eval` audit
walks all seven headline statement closures against the 4-entry sampler allowlist and negative
self-tests.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.HeadlineSamplers

open ReductionDsl (OpsSizeHonest SampSizeHonest Samplers atomicSig AtomicBaseUnif
  atomicBaseSamplers atomicAdapterOps atomicE2EOps
  atomicBaseSamplers_sizeHonest atomicAdapterOps_sizeHonest atomicE2EOps_sizeHonest)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSession (CostedOpsSizeHonest CostedSampSizeHonest)
open CryptoVerification.E2E (BHDRCtlQuery e2eBhAdapterIface)

theorem atomicBaseSamplers_sDom_unit (ℓ : ℕ) (Pt : Type) (s : (atomicBaseSamplers ℓ Pt).Samp) :
    (atomicBaseSamplers ℓ Pt).sDom s = .unit := rfl

theorem atomicBaseSamplers_eq_unifSamplers (ℓ : ℕ) (Pt : Type) :
    atomicBaseSamplers ℓ Pt =
      ReductionDsl.unifSamplers (S := atomicSig ℓ Pt) AtomicBaseUnif.sort AtomicBaseUnif.cost :=
  rfl

theorem atomicBaseSamplers_sampSizeHonest (ℓ : ℕ) (Pt : Type) :
    SampSizeHonest (atomicBaseSamplers ℓ Pt) :=
  atomicBaseSamplers_sizeHonest ℓ Pt

theorem atomicBaseSamplers_costedSampSizeHonest (ℓ : ℕ) (Pt : Type) :
    CostedSampSizeHonest (atomicBaseSamplers ℓ Pt) :=
  atomicBaseSamplers_sizeHonest ℓ Pt

theorem atomicAdapterOps_opsSizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicAdapterOps ℓ decT encT) :=
  atomicAdapterOps_sizeHonest ℓ decT encT

theorem atomicAdapterOps_costedOpsSizeHonest (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (atomicAdapterOps ℓ decT encT) :=
  atomicAdapterOps_sizeHonest ℓ decT encT

theorem atomicE2EOps_opsSizeHonest (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsSizeHonest (atomicE2EOps ℓ P C K decT encT) :=
  atomicE2EOps_sizeHonest ℓ P C K decT encT

theorem atomicE2EOps_costedOpsSizeHonest (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CostedOpsSizeHonest (atomicE2EOps ℓ P C K decT encT) :=
  atomicE2EOps_sizeHonest ℓ P C K decT encT

theorem e2eKeyIndTargetIface_smp_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (ReductionDsl.e2eKeyIndTargetIface S ℓ Pt).smp = atomicBaseSamplers ℓ Pt := rfl

theorem e2eSessionTargetIface_smp_eq (ℓ : ℕ) (Pt : Type) :
    (ReductionDsl.e2eSessionTargetIface ℓ Pt).smp = atomicBaseSamplers ℓ Pt := rfl

theorem e2eAdapterIface_smp_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) {Ctl : Type}
    (mkStart : SignalPqxdh.SessionId S → Ctl) :
    (ReductionDsl.e2eAdapterIface S ℓ Pt mkStart).smp = atomicBaseSamplers ℓ Pt := rfl

theorem e2eBhAdapterIface_smp_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (e2eBhAdapterIface S ℓ Pt).smp = atomicBaseSamplers ℓ Pt := rfl

end CryptoVerification.E2E.Guards.HeadlineSamplers

namespace CryptoVerification.E2E.Guards.HeadlineSamplersAudit

open ReductionDsl (Samplers AtomicSort atomicSig)

private def fixtureUnlistedSampler : Samplers (atomicSig 0 Empty) :=
  Samplers.empty

private def fixtureStmtWithUnlistedSampler : Prop :=
  fixtureUnlistedSampler.Samp = Empty

private def fixtureStatefulSampler (S : SignalPqxdh.Setup) : Samplers (atomicSig 0 Empty) :=
  let _ : Option (SignalPqxdh.KeyIndState S) := none
  Samplers.empty

private def fixtureStmtWithStatefulSampler : Prop :=
  ∀ S : SignalPqxdh.Setup, (fixtureStatefulSampler S).Samp = Empty

private def fixtureGhostSortSampler : Samplers (atomicSig 0 Empty) :=
  let _ := AtomicSort.ghostSt
  Samplers.empty

private def fixtureStmtWithGhostSortSampler : Prop :=
  fixtureGhostSortSampler.Samp = Empty

private def fixtureIfaceWithInlineSampler (S : SignalPqxdh.Setup) :
    ReductionDsl.Iface (atomicSig 0 Empty)
      (unifSpec + CryptoVerification.E2E.bhTargetGameSpec S 0 (BitVec 512)) where
  fwdU := (CryptoVerification.E2E.e2eBhAdapterIface S 0 Empty).fwdU
  uCost := 1
  Tag := Empty
  dom := Empty.elim
  cod := Empty.elim
  enc := fun g => g.elim
  dec := fun g => g.elim
  qCost := Empty.elim
  smp := {
    Samp := Unit
    sDom := fun _ => .unit
    sTy := fun _ => .bool
    samp := fun _ _ => do
      let _ : Option (SignalPqxdh.KeyIndState S) := none
      pure false
    sCost := fun _ => 1
  }

private def fixtureStmtWithInlineIfaceSampler : Prop :=
  ∀ S : SignalPqxdh.Setup, (fixtureIfaceWithInlineSampler S).uCost = 1

meta section

open Lean

def allowedHeadlineSamplers : Array Name := #[
  `ReductionDsl.unifSamplers,
  `ReductionDsl.atomicBaseSamplers,
  `ReductionDsl.atomicSamplers,
  `ReductionDsl.pqAtomicSamplers
]

def forbiddenSamplerStateRefs : Array Name := #[
  `SignalPqxdh.KeyIndState,
  `SignalPqxdh.AuthState,
  `CryptoGames.LibsignalSession.GhostState,
  `CryptoVerification.E2E.BHE2EDrvState,
  `CryptoVerification.E2E.ModelDriverBase,
  `CryptoVerification.E2E.ModelDriverState,
  `CryptoVerification.E2E.BHModelInst,
  `CryptoGames.SM.GameState,
  `CryptoVerification.E2E.Costed.E2ESort.ghostSt,
  `CryptoVerification.E2E.Costed.E2ESort.binSt,
  `ReductionDsl.AtomicSort.ghostSt,
  `ReductionDsl.AtomicSort.binSt
]

def forbiddenLegacyE2EDecls : Array Name := #[
  `CryptoVerification.E2E.BHE2ESamp,
  `CryptoVerification.E2E.BHE2EOp,
  `CryptoVerification.E2E.bhE2EOps,
  `CryptoVerification.E2E.compositionSamplers,
  `CryptoVerification.E2E.bhE2ESamplers,
  `CryptoVerification.E2E.bhE2ELocalStart,
  `CryptoVerification.E2E.BHE2ESort,
  `CryptoVerification.E2E.bhE2ESig,
  `CryptoVerification.E2E.bhE2ECodec,
  `CryptoVerification.E2E.BHAdapterSort,
  `CryptoVerification.E2E.BHAdapterOp,
  `CryptoVerification.E2E.bhAdapterOps,
  `CryptoVerification.E2E.bhAdapterIface,
  `CryptoVerification.E2E.bhAdapterCodec,
  `CryptoVerification.E2E.keyIndTargetIface,
  `CryptoVerification.E2E.sessionTargetIface,
  `CryptoVerification.E2E.bhKiIface,
  `CryptoVerification.E2E.bhSmTargetIface,
  `CryptoVerification.E2E.E2ECostedReds,
  `CryptoVerification.E2E.E2ECostedBounds
]

def auditedHeadlineRoots : Array Name := #[
  `SignalPqxdh.Security.PqxdhCorrectAndSecureδ,
  `CryptoVerification.E2E.SessionSecure,
  `CryptoVerification.E2E.ModelSecure,
  `CryptoVerification.SignalSession.CliPqxdhElfCorrectPlaced,
  `CryptoVerification.LibsignalCli.CliPqxdhElfSecurePlaced,
  `CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlaced,
  `CryptoVerification.E2E.CliPqxdhSecurityFor
]

partial def retHeadConst? : Expr → Option Name
  | .forallE _ _ b _ => retHeadConst? b
  | .letE _ _ _ b _  => retHeadConst? b
  | .mdata _ b       => retHeadConst? b
  | e                => e.getAppFn.constName?

partial def stripLambdas : Expr → Expr
  | .lam _ _ b _ => stripLambdas b
  | .mdata _ b   => stripLambdas b
  | e            => e

def isStructProjDef (env : Environment) (c : Name) (d : DefinitionVal) : Bool :=
  match stripLambdas d.value with
  | .proj indName _ (.bvar 0) =>
      c.getPrefix == indName &&
      match env.find? indName with
      | some (.inductInfo iv) => iv.ctors.length == 1
      | _ => false
  | _ => false

def isInternalSamplerAux (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  let user := (privateToUserName? c).getD c
  let genAux :=
    env.isProjectionFn c ||
    Lean.isAuxRecursor env c ||
    Lean.isNoConfusion env c ||
    Meta.isMatcherCore env c ||
    user.components.any fun p =>
      p.isInternalDetail || match p with | .str _ s => s.startsWith "_" | _ => false
  match ci with
  | .ctorInfo _ | .recInfo _ | .inductInfo _ | .quotInfo _ => true
  | .defnInfo d => isStructProjDef env c d || genAux
  | _ => genAux

def callsSamplersMk (env : Environment) (c : Name) : ConstantInfo → Bool
  | .defnInfo d =>
      d.value.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk ||
      (!Lean.isAuxRecursor env c && !Lean.isNoConfusion env c &&
        d.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk)
  | .opaqueInfo o => o.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk
  | .axiomInfo a => a.type.getUsedConstantsAsSet.contains `ReductionDsl.Samplers.mk
  | _ => false

def stmtNodeDeps : ConstantInfo → NameSet
  | .thmInfo _    => {}
  | .defnInfo v   => v.type.getUsedConstantsAsSet.union v.value.getUsedConstantsAsSet
  | .opaqueInfo v => v.type.getUsedConstantsAsSet
  | .axiomInfo v  => v.type.getUsedConstantsAsSet
  | .ctorInfo v   => v.type.getUsedConstantsAsSet
  | .inductInfo v => v.ctors.foldl (fun s ct => s.insert ct) v.type.getUsedConstantsAsSet
  | .recInfo v    => v.type.getUsedConstantsAsSet
  | .quotInfo v   => v.type.getUsedConstantsAsSet

def samplerStateViolations (env : Environment) (s : Name) : Array Name := Id.run do
  let samplerStops : Array Name := #[
    `CryptoVerification.E2E.Costed.E2ESort,
    `CryptoVerification.E2E.Costed.E2ESort.den,
    `CryptoVerification.E2E.Costed.E2ESort.blocks,
    `ReductionDsl.AtomicSort,
    `ReductionDsl.AtomicSort.den,
    `ReductionDsl.AtomicSort.blocks
  ]
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[s]
  let mut hits : NameSet := {}
  let mut idx := 0
  while idx < queue.size do
    let c := queue[idx]!
    idx := idx + 1
    if visited.contains c then continue
    visited := visited.insert c
    let user := (privateToUserName? c).getD c
    if c != s && (forbiddenSamplerStateRefs.contains c || forbiddenSamplerStateRefs.contains user) then
      hits := hits.insert user
    if c != s && (samplerStops.contains c || samplerStops.contains user) then continue
    let some ci := env.find? c | continue
    if c != s && retHeadConst? ci.type == some `ReductionDsl.Sig then continue
    for d in stmtNodeDeps ci do
      unless visited.contains d do
        queue := queue.push d
  return hits.toArray.qsort Name.lt

structure RootAuditResult where
  samplers : Array Name
  violations : Array String

def moduleRootOfConst (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.header.moduleNames.getD idx.toNat Name.anonymous).getRoot
  | none     => env.mainModule.getRoot

def auditStmtRoot (env : Environment) (root : Name)
    (allowed : Array Name := allowedHeadlineSamplers)
    (forbiddenDecls : Array Name := forbiddenLegacyE2EDecls) :
    CoreM RootAuditResult := do
  let some rootCi := env.find? root
    | throwError "HeadlineSamplersGuard: missing audited root `{root}`"
  let mut visited : NameSet := {}
  let mut queue : Array Name :=
    match rootCi with
    | .thmInfo ti => ti.type.getUsedConstantsAsSet.toArray.qsort Name.lt
    | _ => #[root]
  let mut foundSamplers : NameSet := {}
  let mut violations : Array String := #[]
  let mut idx := 0
  while idx < queue.size do
    let c := queue[idx]!
    idx := idx + 1
    if visited.contains c then continue
    visited := visited.insert c
    let user := (privateToUserName? c).getD c
    if forbiddenDecls.contains c || forbiddenDecls.contains user then
      violations := violations.push s!"FORBIDDEN-LEGACY-E2E({root}): {user}"
    let some ci := env.find? c | continue
    let isSamplerDecl :=
      retHeadConst? ci.type == some `ReductionDsl.Samplers &&
      !isInternalSamplerAux env c ci
    let isSamplersMkCaller := callsSamplersMk env c ci
    if isSamplerDecl || isSamplersMkCaller then
      if isSamplerDecl then
        foundSamplers := foundSamplers.insert user
      let isAllowed :=
        if isSamplerDecl then
          allowed.contains c || allowed.contains user
        else
          allowed.contains c || allowed.contains user ||
          (isInternalSamplerAux env c ci &&
            allowed.any fun a => a.isPrefixOf c || a.isPrefixOf user)
      unless isAllowed do
        violations := violations.push s!"UNLISTED-SAMPLER({root}): {user}"
      let stateHits := samplerStateViolations env c
      unless stateHits.isEmpty do
        let joined := ", ".intercalate (stateHits.toList.map toString)
        violations := violations.push s!"STATEFUL-SAMPLER({root}): {user} -> [{joined}]"
    if moduleRootOfConst env c != `Computational then
      continue
    for d in stmtNodeDeps ci do
      unless visited.contains d do
        queue := queue.push d
  return {
    samplers := foundSamplers.toArray.qsort Name.lt
    violations := violations
  }

def runHeadlineSamplersAudit : CoreM Unit := do
  let env ← getEnv
  -- Negative self-tests
  let negUnlisted ← auditStmtRoot env ``fixtureStmtWithUnlistedSampler
  unless negUnlisted.violations.any (·.startsWith "UNLISTED-SAMPLER(") do
    throwError "HeadlineSamplersGuard self-test failed: unlisted sampler was not rejected"

  let userStateful := (privateToUserName? ``fixtureStatefulSampler).getD ``fixtureStatefulSampler
  let negStateful ← auditStmtRoot env ``fixtureStmtWithStatefulSampler
    (allowed := allowedHeadlineSamplers.push userStateful)
  unless negStateful.violations.any (fun v =>
      v.startsWith "STATEFUL-SAMPLER(" && (v.splitOn "SignalPqxdh.KeyIndState").length > 1) do
    throwError "HeadlineSamplersGuard self-test failed: stateful sampler was not rejected"

  let userGhostSort := (privateToUserName? ``fixtureGhostSortSampler).getD ``fixtureGhostSortSampler
  let negGhostSort ← auditStmtRoot env ``fixtureStmtWithGhostSortSampler
    (allowed := allowedHeadlineSamplers.push userGhostSort)
  unless negGhostSort.violations.any (fun v =>
      v.startsWith "STATEFUL-SAMPLER(" && (v.splitOn "AtomicSort.ghostSt").length > 1) do
    throwError "HeadlineSamplersGuard self-test failed: ghostSt sampler sort was not rejected"

  let userUnlisted := (privateToUserName? ``fixtureUnlistedSampler).getD ``fixtureUnlistedSampler
  let negLegacy ← auditStmtRoot env ``fixtureStmtWithUnlistedSampler
    (allowed := allowedHeadlineSamplers.push userUnlisted)
    (forbiddenDecls := forbiddenLegacyE2EDecls.push userUnlisted)
  unless negLegacy.violations.any (·.startsWith "FORBIDDEN-LEGACY-E2E(") do
    throwError "HeadlineSamplersGuard self-test failed: forbidden legacy declaration was not rejected"

  let negInline ← auditStmtRoot env ``fixtureStmtWithInlineIfaceSampler
  unless negInline.violations.any (·.startsWith "UNLISTED-SAMPLER(") do
    throwError "HeadlineSamplersGuard self-test failed: inline Iface Samplers.mk was not rejected as unlisted"
  unless negInline.violations.any (fun v =>
      v.startsWith "STATEFUL-SAMPLER(" && (v.splitOn "SignalPqxdh.KeyIndState").length > 1) do
    throwError "HeadlineSamplersGuard self-test failed: inline Iface Samplers.mk was not rejected as stateful"

  -- Statement constant-closure audit
  let mut unionSamplers : NameSet := {}
  let mut allViolations : Array String := #[]
  let e2eRootsRequiringCoinSampler : Array Name := #[
    `CryptoVerification.E2E.ModelSecure,
    `CryptoVerification.LibsignalCli.CliPqxdhElfSecurePlaced,
    `CryptoVerification.LibsignalCli.CliPqxdhBinaryCorrectAndSecurePlaced,
    `CryptoVerification.E2E.CliPqxdhSecurityFor
  ]
  for root in auditedHeadlineRoots do
    let res ← auditStmtRoot env root
    for s in res.samplers do
      unionSamplers := unionSamplers.insert s
    for v in res.violations do
      allViolations := allViolations.push v
    if e2eRootsRequiringCoinSampler.contains root &&
        !res.samplers.contains `ReductionDsl.atomicBaseSamplers then
      allViolations := allViolations.push
        s!"MISSING-E2E-SAMPLER({root}): closure did not reach ReductionDsl.atomicBaseSamplers"

  for s in allowedHeadlineSamplers do
    unless unionSamplers.contains s do
      allViolations := allViolations.push
        s!"STALE-ALLOWLIST-ENTRY: {s} was not reached by any audited headline root"

  unless allViolations.isEmpty do
    let joined := "\n  ".intercalate allViolations.toList
    throwError s!"HeadlineSamplersGuard failed with {allViolations.size} violation(s):\n  {joined}"

#eval runHeadlineSamplersAudit

end

end CryptoVerification.E2E.Guards.HeadlineSamplersAudit
