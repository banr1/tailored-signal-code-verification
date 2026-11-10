/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import Symbolic.Proofs.Tests.Refinement.Cli.SetupInitDirsGuard -- shake: keep

/-!
# Kernel-Checked Guard on Bob's Last-Resort Kyber Private Key in `initDirs`

Checks that Bob's `last-resort-kyber-pre-keys/<kpkId>` entry in `initDirs` decodes via
`SignedPreKeyRecordStructure.decode` to a record whose `privateKey` has length `3169` and leading
type byte `0x08`, and pins the axiom footprint of the supporting lemmas in
`Symbolic.Proofs.Tests.Refinement.Cli`.
-/

@[expose] public section

set_option autoImplicit false

example :
    ∀ (interp : CryptoProofLib.Refinement.ExternInterpretation)
      (r : DY.Libsignal.Composed.Refinement.ProtocolSetup),
      DY.Libsignal.Composed.Refinement.ProtocolSetupWF r →
      ∃ (bs : DY.Libsignal.HwBytes)
        (rec : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure),
        DY.Libsignal.Composed.Refinement.Cli.initDirs interp r r.bob
          (CryptoVerification.SignalSession.lastResortKyberPreKeyFile r.kpkId) = some bs ∧
        CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.decode bs = some rec ∧
        rec.privateKey.length = 3169 ∧
        rec.privateKey[0]? = some 0x08#8 :=
  Symbolic.Proofs.Tests.Refinement.Cli.initDirs_bob_lastResortKyber_privateKey

/--
info: 'Symbolic.Proofs.Tests.Refinement.Cli.initDirs_bob_lastResortKyber_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Symbolic.Proofs.Tests.Refinement.Cli.initDirs_bob_lastResortKyber_decode

/--
info: 'Symbolic.Proofs.Tests.Refinement.Cli.initDirs_bob_lastResortKyber_privateKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Symbolic.Proofs.Tests.Refinement.Cli.initDirs_bob_lastResortKyber_privateKey
