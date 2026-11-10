/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredAsmLevelSecurity
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed

/-!
# Move-Based ELF and Binary Refinement Predicates

Move-based counterparts (`*Moves`) of the CLI ELF image and binary byte-list refinement and
security predicates.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
  x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol toEdwardsSymbol
  torsionFreeSymbol)
open CryptoVerification.SignalSession (CliHooks cliRunAbortOnPanic)

/-- Move-based whole-protocol refinement over executions of the parsed ELF image `elf`. -/
def CompRefinesCliElfMoves (elf : ElfImage) : Prop :=
  CompRefinesCliMoves HooksMatchInterpretation (elfRel elf)

/-- Move-based whole-protocol refinement for a CLI binary `bytes` parsing to a valid `ElfImage`. -/
def CompRefinesCliBinaryMoves (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CompRefinesCliElfMoves elf

/-- Move-based whole-protocol security for a CLI binary `bytes` parsing to a valid `ElfImage`. -/
def CompAsmSecurityCliBinaryMoves (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CompAsmSecurityCliMoves HooksMatchInterpretation (elfRel elf)

end DY.Libsignal.Composed.Refinement.Cli
