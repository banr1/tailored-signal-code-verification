/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.EncodeBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.ReprPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.DecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.FinalPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.BasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.DefsPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesBPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.LayoutPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced

/-!
# Relocatable `Subset A4d` Proof Barrel

Umbrella module rooting the 60 `Cli/SpqrV1` CGU-local callee `*Placed` modules (`Alloc`, `Auth`,
`Drop`, `Prost`, `ProtoRepr`, `Varint`; blocks `435..500`) into `LibsignalBinary.Cli`.
-/

@[expose] public section
