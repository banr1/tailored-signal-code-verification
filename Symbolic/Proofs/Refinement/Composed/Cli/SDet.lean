/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.InputsInj
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.EncodeDirInj
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongr

/-!
# Determinism of the PQXDH CLI Model

Instantiates `sdetBridges` from the input-extraction and directory-injectivity modules and
proves `sdet`, establishing `PqModelPost` from `Draft.PqModelRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

theorem sdetBridges : SDetBridges where
  init_send_false := inputsEquiv_pqInitInputs_pqSendInputs_false
  init_recv_false := inputsEquiv_pqInitInputs_pqRecvInputs_false
  send_recv_false := inputsEquiv_pqSendInputs_pqRecvInputs_false
  whisper_prekey_false := inputsEquiv_pqRecvWhisper_pqRecvPrekey_false
  whisper_other_false := inputsEquiv_pqRecvWhisper_other_false
  prekey_other_false := inputsEquiv_pqRecvPrekey_other_false
  init_extract := inputsEquiv_pqInitInputs_extract
  send_extract := inputsEquiv_pqSendInputs_extract
  whisper_extract := inputsEquiv_pqRecvWhisper_extract
  prekey_extract := inputsEquiv_pqRecvPrekey_extract
  party_equiv_of_files := pqPartyEquiv_of_filesOf_encodeDir
  files_of_party_equiv := filesOf_encodeDir_eq_of_pqPartyEquiv

end DY.Libsignal.Composed.Refinement.Cli.SDet

namespace DY.Libsignal.Composed.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open SDet
open CryptoVerification.E2E (UnreachedPqxdhPrimitives PEParams)
open CryptoVerification.SignalSession (Inputs Outcome)

theorem sdet (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (interp : ExternInterpretation) (i : Inputs) (o : Outcome)
    (h : Draft.PqModelRel Xof Wof interp i o) : PqModelPost interp (Wof interp) i o :=
  SDet.sdet_of_bridges SDet.sdetBridges Xof Wof interp i o h

end DY.Libsignal.Composed.Refinement.Cli
