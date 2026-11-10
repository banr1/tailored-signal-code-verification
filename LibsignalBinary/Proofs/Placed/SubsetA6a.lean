/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsCPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsDPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsEPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3StepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.SkipField6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit.BytesMerge6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit.DecodeVarint5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit.DoReserve10Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg6PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux2
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlaced
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5APlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPathAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxB
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemRejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PqBundleInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstNoMatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWBaseKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWIdentPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyberPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWPresencePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSigMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPackPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlaced
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `Subset A6a` Proof Barrel

Umbrella module rooting `Subset A6` relocatable proof modules (part A) under `[LibsignalPlacement]`.
-/

@[expose] public section
