/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.HeadlinePqCliMixEq
public import Computational.Proofs.LibsignalCli.PrefixCouplingWithCore
import Computational.Proofs.LibsignalCli.PrefixLazy1KeyReal

/-!
# Bridge from `Prefix1Key` to `CliPqPrefixBoundProp`

**Checked by Lean.** Proves `CliPqPrefixBoundProp S ℓ` from
`boolBias_bhE2EExpWithKi_1KeyReal_false_le_sum_prefix_steps`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.Ratchet CryptoGames.SM
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec

namespace CryptoVerification.E2E

theorem bhE2EExpWithKi_eq_prefix1Key {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (secb : Bool) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhE2EExpWithKi secb S P ki C K ℓ qep decT encT B =
      Prefix1Key.bhE2EExpWithKi S ki secb P C K ℓ qep decT encT B := rfl

/-- Discharges `CliPqPrefixBoundProp`. -/
theorem cliPqPrefixBoundProp_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    CliPqPrefixBoundProp (Pt := Pt) S ℓ :=
  cliPqPrefixBoundProp_of_general S ℓ fun P C K qep decT encT qStart qTot B hQStart hQTot =>
    boolBias_bhE2EExpWithKi_1KeyReal_false_le_sum_prefix_steps
      S P C K ℓ qep decT encT qStart qTot B hQStart hQTot

end CryptoVerification.E2E
