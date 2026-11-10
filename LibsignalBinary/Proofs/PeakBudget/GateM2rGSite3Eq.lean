/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired

/-!
# Definitional Equality Between `cliDecPkCanonSlotEnvExact` and `GateM2rGStatesRecvTwins`

Proves by `rfl` that `RealCliDecPkGuardedDefs.cliDecPkCanonSlotEnvExact X W` equals
`GateM2rGStatesRecvTwins.m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
(fun _ K => StatesRecvProtoEnv' K) X W`, and supplies `cliDecPkCanonSlotEnvExact` specializations
of the `hRunSub` eliminators and `DecPkD2cSlotOkFrozenPlaced` lift.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Eq

open Arm64.Obj Arm64.Process
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
  (DecPkD2cSlotOkFrozenPlaced DecPkD2cSlotOkFrozenPlacedAt)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf'_of_unguarded
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_cliPqInputs_recv
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_tight
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed')
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)

/-- Definitional (`rfl`) equality between `cliDecPkCanonSlotEnvExact X W` and
`GateM2rGStatesRecvTwins.m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
(fun _ K => StatesRecvProtoEnv' K) X W`. -/
theorem m2rgs3_cliDecPkCanonSlotEnvExact_eq_m2rg [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    cliDecPkCanonSlotEnvExact X W =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
        (fun _ K => StatesRecvProtoEnv' K) X W :=
  rfl

/-- Pointwise `Iff.rfl` companion to `m2rgs3_cliDecPkCanonSlotEnvExact_eq_m2rg`. -/
theorem m2rgs3_cliDecPkCanonSlotEnvExact_iff_m2rg [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (e : List AllocEvent) :
    cliDecPkCanonSlotEnvExact X W g e ↔
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
        (fun _ K => StatesRecvProtoEnv' K) X W g e :=
  Iff.rfl

/-- `PeerSpqrStateTight640` eliminator on `cliDecPkCanonSlotEnvExact X W`. -/
theorem m2rgs3_cliDecPkCanonSlotEnvExact_of_tight [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {x : DecPkGhost} {evs : List AllocEvent}
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val)
    (hevs : cliDecPkCanonSlotEnvExact X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'
      (fun _ K => StatesRecvProtoEnv' K) X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_tight
    (fun g e => m2rgs3_cliDecPkCanonSlotEnvExact_iff_m2rg X W g e) hTight hevs

/-- `hRunSub` eliminator on `cliDecPkCanonSlotEnvExact X W` at `.recv peer` under `CliPqxdhInputs ⟨W.C, W.Q⟩ i`. -/
theorem m2rgs3_cliDecPkCanonSlotEnvExact_of_cliPqInputs_recv [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {i : Inputs} {peer : AddrV}
    {x : DecPkGhost} {evs : List AllocEvent}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hF : x.F = runFiles i) (hpeer : x.peer.val = addrValOf peer)
    (hevs : cliDecPkCanonSlotEnvExact X W x evs) :
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'
      (fun _ K => StatesRecvProtoEnv' K) X W x evs :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'_of_guarded_cliPqInputs_recv
    (fun g e => m2rgs3_cliDecPkCanonSlotEnvExact_iff_m2rg X W g e) hi hparse hF hpeer hevs

/-- `DecPkD2cSlotOkFrozenPlaced` wrapper for `cliDecPkCanonSlotEnvExact X W`. -/
theorem m2rgs3_decPkD2cSlotOkFrozenPlaced_cliDecPkCanonSlotEnvExact_of_unguarded
    [LibsignalPlacement]
    {M : AllocCostModel}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₀ : UnreachedPqxdhPrimitives → DecPkGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives)
    (hUnguarded : ∀ X',
      DecPkD2cSlotOkFrozenPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) X' W A lim
        (DecPkEnv₀ X'))
    (hBridge : ∀ X' g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      DecPkEnv₀ X' g evs →
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'
        (fun _ K => StatesRecvProtoEnv' K) X' W g evs) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim (cliDecPkCanonSlotEnvExact X W) :=
  m2rg_decPkD2cSlotOkFrozenPlaced_cmkVerNeGuardedOf'_of_unguarded X
    (fun g e => m2rgs3_cliDecPkCanonSlotEnvExact_iff_m2rg X W g e) hUnguarded hBridge

end LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Eq
