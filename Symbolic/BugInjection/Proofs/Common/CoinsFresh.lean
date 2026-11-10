/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateCli
public import Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli
public import Symbolic.BugInjection.Synthetic.Witnesses.ImplicitRejectMacCli
public import Symbolic.BugInjection.Synthetic.Witnesses.PromotedPrekeyHeadersCli
public import Symbolic.BugInjection.Synthetic.Witnesses.ZeroBaseKeyPqxdhCli
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

/-!
# `CoinsFresh` Discharge Lemmas

Reduces `CoinsFresh` under `compFits` to concrete duplicate-freedom of setup DH keys and trace
random draws, and discharges `CoinsFresh` for the composed and synthetic CLI bug-injection
witnesses under `cliCompFits` and `cliCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Common.CoinsFresh

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup secretBytes clamp)
open DY.Libsignal.Composed.Refinement.Cli (exitedZeroDraws setupDHSecrets CoinsFresh)
open DY.Libsignal.Composed.Security (SignalSessionSecure)
open Symbolic.BugInjection
  (PQXDHSpqrSetup compFits cliCompShape cliCompFits not_signalSessionSecure_of_witness)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (cliCompFitsPinned)

theorem setupDHSecrets_of_compFits {w : PQXDHSpqrSetup} {i : ExternInterpretation}
    {r : ProtocolSetup} (hf : compFits w i r) :
    setupDHSecrets r = [clamp w.aliceId, clamp w.bobId, clamp w.spk] := by
  rcases hf with ⟨_, hopk, _, _, _, _, h0, h1, h2, _⟩
  simp [setupDHSecrets, hopk, h0, h1, h2]

/-- Reduces `CoinsFresh r τ` under `compFits w i r` to duplicate-freedom on `(w, τ)`. -/
theorem coinsFresh_of_compFits {w : PQXDHSpqrSetup} {i : ExternInterpretation}
    {r : ProtocolSetup} {τ : List CliEvent} (hf : compFits w i r)
    (hnd : ([clamp w.aliceId, clamp w.bobId, clamp w.spk] ++
      τ.flatMap fun | .run ev => exitedZeroDraws ev | .env _ => []).Nodup) :
    CoinsFresh r τ := by
  unfold CoinsFresh
  rwa [setupDHSecrets_of_compFits hf]

theorem coinsFresh_unpinned_cheval26SmallSubgroupHighBitCli :
    ∀ iw r, cliCompFits Witnesses.Cheval26SmallSubgroupHighBitCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_cheval26SmallSubgroupHighBitCli :
    ∀ iw r, cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  fun iw r hf => coinsFresh_unpinned_cheval26SmallSubgroupHighBitCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

theorem coinsFresh_unpinned_cheval26SmallSubgroupTorsionCli :
    ∀ iw r, cliCompFits Witnesses.Cheval26SmallSubgroupTorsionCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26SmallSubgroupTorsionCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_cheval26SmallSubgroupTorsionCli :
    ∀ iw r, cliCompFitsPinned Witnesses.Cheval26SmallSubgroupTorsionCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26SmallSubgroupTorsionCli.trace :=
  fun iw r hf => coinsFresh_unpinned_cheval26SmallSubgroupTorsionCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

theorem coinsFresh_unpinned_cheval26WeakStateIdx1Cli :
    ∀ iw r, cliCompFits Witnesses.Cheval26WeakStateIdx1Cli.setup iw r →
      CoinsFresh r Witnesses.Cheval26WeakStateIdx1Cli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_cheval26WeakStateIdx1Cli :
    ∀ iw r, cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup iw r →
      CoinsFresh r Witnesses.Cheval26WeakStateIdx1Cli.trace :=
  fun iw r hf => coinsFresh_unpinned_cheval26WeakStateIdx1Cli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

theorem coinsFresh_unpinned_cheval26WeakStateCli :
    ∀ iw r, cliCompFits Witnesses.Cheval26WeakStateCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26WeakStateCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_cheval26WeakStateCli :
    ∀ iw r, cliCompFitsPinned Witnesses.Cheval26WeakStateCli.setup iw r →
      CoinsFresh r Witnesses.Cheval26WeakStateCli.trace :=
  fun iw r hf => coinsFresh_unpinned_cheval26WeakStateCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

/-- Image-free typecheck of `not_signalSessionSecure_of_witness` for
`Cheval26SmallSubgroupHighBitCli`. -/
theorem carrier_disproof_typecheck_cheval26SmallSubgroupHighBitCli
    (bytes : List (BitVec 8))
    (spec_half_pinned :
      cliCompShape.SpecHalf
        (cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
        Witnesses.Cheval26SmallSubgroupHighBitCli.trace)
    (impl_half_bytes :
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
        cliCompShape.ImplHalf
          (cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
          elf Witnesses.Cheval26SmallSubgroupHighBitCli.trace) :
    ¬ SignalSessionSecure bytes :=
  not_signalSessionSecure_of_witness
    spec_half_pinned
    impl_half_bytes
    coinsFresh_cheval26SmallSubgroupHighBitCli

/-- Image-free typecheck of `not_signalSessionSecure_of_witness` for
`Cheval26WeakStateIdx1Cli`. -/
theorem carrier_disproof_typecheck_cheval26WeakStateIdx1Cli
    (bytes : List (BitVec 8))
    (spec_half_pinned :
      cliCompShape.SpecHalf
        (cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup)
        Witnesses.Cheval26WeakStateIdx1Cli.trace)
    (impl_half_bytes :
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
        cliCompShape.ImplHalf
          (cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup)
          elf Witnesses.Cheval26WeakStateIdx1Cli.trace) :
    ¬ SignalSessionSecure bytes :=
  not_signalSessionSecure_of_witness
    spec_half_pinned
    impl_half_bytes
    coinsFresh_cheval26WeakStateIdx1Cli

theorem coinsFresh_unpinned_evictedChainSkippedKeyCli :
    ∀ iw r, cliCompFits Synthetic.Witnesses.EvictedChainSkippedKeyCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_unpinned_implicitRejectMacCli :
    ∀ iw r, cliCompFits Synthetic.Witnesses.ImplicitRejectMacCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.ImplicitRejectMacCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_implicitRejectMacCli :
    ∀ iw r, cliCompFitsPinned Synthetic.Witnesses.ImplicitRejectMacCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.ImplicitRejectMacCli.trace :=
  fun iw r hf => coinsFresh_unpinned_implicitRejectMacCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

theorem coinsFresh_unpinned_promotedPrekeyHeadersCli :
    ∀ iw r, cliCompFits Synthetic.Witnesses.PromotedPrekeyHeadersCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.PromotedPrekeyHeadersCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_promotedPrekeyHeadersCli :
    ∀ iw r, cliCompFitsPinned Synthetic.Witnesses.PromotedPrekeyHeadersCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.PromotedPrekeyHeadersCli.trace :=
  fun iw r hf => coinsFresh_unpinned_promotedPrekeyHeadersCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

theorem coinsFresh_unpinned_zeroBaseKeyPqxdhCli :
    ∀ iw r, cliCompFits Synthetic.Witnesses.ZeroBaseKeyPqxdhCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.ZeroBaseKeyPqxdhCli.trace :=
  fun _ _ hf => coinsFresh_of_compFits hf.1 (by decide +kernel)

theorem coinsFresh_zeroBaseKeyPqxdhCli :
    ∀ iw r, cliCompFitsPinned Synthetic.Witnesses.ZeroBaseKeyPqxdhCli.setup iw r →
      CoinsFresh r Synthetic.Witnesses.ZeroBaseKeyPqxdhCli.trace :=
  fun iw r hf => coinsFresh_unpinned_zeroBaseKeyPqxdhCli iw r ⟨hf.1.1, hf.2.1, hf.2.2⟩

end Symbolic.BugInjection.Proofs.Common.CoinsFresh
