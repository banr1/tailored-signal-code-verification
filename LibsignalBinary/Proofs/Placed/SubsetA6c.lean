/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1OkTrapPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedOkTrapPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1PlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegDispatchExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.KyberMapPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudgetFd
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudgetFd
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesAuxBudgetFd
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetFd
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetFd
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudgetFd
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMapBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemPollRejectAuxPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsSelfPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.Stage4KitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySelfKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SignedPreKeyKitFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetOkFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.CliPubCalleesInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAP4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathAUntrustedPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBP4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathBPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCP4PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathCPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2V1RegErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SetUnackEpochPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptSlotWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SessDeserStoreWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2BudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1aFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1bFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2aFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2bFd
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAuxFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `Subset A6c` Proof Barrel

Umbrella module rooting `Subset A6` relocatable proof modules (part C) under `[LibsignalPlacement]`.
-/

@[expose] public section
