/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift

/-!
# Guarded Wide `decryptPrekey` Slot Envelope Definitions

**Checked by Lean.**

Defines `realCliDecPkBinaryWideSlotEnvGuardedFixed` and `cliDecPkCanonSlotEnvExact`, the
`PeerSpqrStateTight640`-guarded binary-kit `W4` (`decrypt_prekey`) slot envelopes.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs

open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs
  (m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed')
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (realCliDecPkBinaryWideSlotEnvFixed realCliDecPkBinaryWideSlotEnvFixed_ghost_congr)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)

/-- `PeerSpqrStateTight640`-guarded wide binary-kit `W4` (`decrypt_prekey`) slot envelope:
requires `realCliDecPkBinaryWideSlotEnvFixed X W x evs` whenever
`PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val` holds, and reduces to `⊤` (`fun _ => True`)
otherwise, where `FitsEnv M lim st (fun _ => True)` is unsatisfiable at finite `lim`. -/
abbrev realCliDecPkBinaryWideSlotEnvGuardedFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideSlotEnvFixed X W x evs

theorem realCliDecPkBinaryWideSlotEnvGuardedFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvGuardedFixed X W x =
      realCliDecPkBinaryWideSlotEnvGuardedFixed X W y := by
  funext evs
  dsimp [realCliDecPkBinaryWideSlotEnvGuardedFixed]
  rw [hf, hp,
    realCliDecPkBinaryWideSlotEnvFixed_ghost_congr X W x y hp hm hs hcp hf hc hmsg]

/-- Canonical `PeerSpqrStateTight640`-guarded `W4` (`decrypt_prekey`) slot envelope instantiated
with `CmkLoopAdvanceEvs`, `VerNeTightTopEnv`, `maxOps = 109`, and `StatesRecvProtoEnv' K`
(definitionally equal to `GateM2rGStatesRecvTwins.m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
(fun _ K => StatesRecvProtoEnv' K) X W`). When `¬ PeerSpqrStateTight640`, the predicate reduces to
`⊤`, whose `FitsEnv` precondition is unsatisfiable at finite `lim`. -/
noncomputable def cliDecPkCanonSlotEnvExact [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    DecPkGhost → List AllocEvent → Prop :=
  m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
    (fun _ K => StatesRecvProtoEnv' K) X W

end LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
