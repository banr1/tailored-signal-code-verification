/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.M4.DecryptPlaced
public import LibsignalBinary.Proofs.SpqrV1.M4.EncryptPlaced
public import LibsignalBinary.Proofs.SpqrV1.M4.RecordDecryptPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.IntoPbCodeSym
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.RecvPlacedCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesPolyExactPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.SendPlacedCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym

/-!
# Relocatable `Subset A4b` Proof Barrel

Umbrella module rooting `SpqrV1/Drop/ChainEpochPlaced` (blocks `143, 269, 287`),
`SpqrV1/States/IntoPb` (block `334`), `SpqrV1/Top` (blocks `124, 323..329, 351, 352`), and
`SpqrV1/M4` under `[LibsignalPlacement]`.
-/

@[expose] public section
