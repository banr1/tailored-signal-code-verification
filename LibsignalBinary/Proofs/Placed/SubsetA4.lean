/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollaries
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.EntryPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropChain2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSessionStructure3Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedB
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlaced

/-!
# Relocatable `Subset A4` Proof Barrel

Umbrella module rooting `SpqrV1/Poly/NextChunk`, `SpqrV1/Auth`,
`SpqrV1/Prost/{MessageEncode,EncodeToVec}`, and `E2E/Pqxdh` under `[LibsignalPlacement]`.
-/

@[expose] public section
