/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget

/-!
# Exact Cap-Free SPQR Entry-Point Allocation Envelopes

**Checked by Lean.**

Defines exact, cap-free allocation event envelopes for SPQR entry points:
- `DecodeStateBytesEnv`, `StatesRecvExactPairEnv`, and `CliSpqrRecvTightLinkedEnv` (`spqr::recv`,
  Block 329).
- `SpqrSendCoinsTightLinkedEnv` and `SpqrSendCoinsTightBytesEnv` (`spqr::send::<Coins>`,
  Block 427).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Message MlKem States V1State spqrAuthApi spqrDecodeState spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg)
open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget (SendPhase3EnvOfEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (MessageSerializeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-- Byte-slice-indexed form of `SpecsBudget.DecodeStateEnv`. -/
abbrev DecodeStateBytesEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DecodeStateEnv { st := ⟨0#64, 0#64, 0#64, bs⟩, outPtr := 0#64 } evs

/-- Pointer-existentialized `(States, Message)` form of `StatesRecvExactEnv K`. -/
def StatesRecvExactPairEnv {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  ∃ outA selfA msgA,
    StatesRecvExactEnv (F := F) K ⟨outA, selfA, msgA, st, msg⟩ evs

/-- Concrete `VecArg`-indexed tight linked `spqr::recv` envelope (`Block 329`). -/
def CliSpqrRecvTightLinkedEnv (W : CliHooks) (st _msg : VecArg) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    SpqrRecvTightLinkedEnv W.C.F W.Q.K
      DecodeStateBytesEnv StatesFromPbEnv StatesIntoPbExactEnv (StatesRecvExactPairEnv W.Q.K)
      st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- Cap-free state-indexed Block `427` (`spqr::send::<signal_session_ratchet::Coins>`) allocation
envelope composed from `DecodeStateEnv`, `FromPb.DefsBudget.StatesFromPbEnv`,
`StatesSendTightEnv`, `MessageSerializeEnv spqrPolyApi`, and `StatesIntoPbExactEnv`. -/
def SpqrSendCoinsTightLinkedEnv (F : ShaCompress) (K : MlKem)
    (x : SendCall) (evs : List AllocEvent) : Prop :=
  let decEnv : List AllocEvent → Prop :=
    DecodeStateEnv { st := x.st, outPtr := 0#64 }
  let fpbEnv (v1 : V1State) : List AllocEvent → Prop :=
    StatesFromPbEnv v1
  match spqrDecodeState x.st.bytes with
  | .error _ => decEnv evs
  | .ok pq =>
    match pq.inner with
    | none => SeqEnv decEnv FreeOnlyEvs evs
    | some (.v1 v1) =>
      SeqEnv decEnv
        (match States.from_pb spqrPolyApi (spqrAuthApi F) v1 with
         | .error (.panic _) => fpbEnv v1
         | .error (.err _) => SeqEnv (fpbEnv v1) FreeOnlyEvs
         | .ok st_states =>
           SeqEnv (fpbEnv v1)
             (SeqEnv (StatesSendTightEnv F K st_states x.rest)
               (match st_states.send K x.rest with
                | .ok (sOut, _) =>
                  SendPhase3EnvOfEnv (MessageSerializeEnv spqrPolyApi) StatesIntoPbExactEnv
                    0#64 pq sOut
                | .error (.err _) => FreeOnlyEvs
                | .error (.panic _) => HeaderReceived1aEnv)))
        evs

/-- Byte-slice-indexed `SpqrSendBudgetEnv` projection of `SpqrSendCoinsTightLinkedEnv F K`
(`(fun sc : SendCall => SpqrSendCoinsTightBytesEnv F K sc.st.bytes sc.rest) =
SpqrSendCoinsTightLinkedEnv F K` definitionally). -/
def SpqrSendCoinsTightBytesEnv (F : ShaCompress) (K : MlKem) : SpqrSendBudgetEnv :=
  fun stBs rest evs =>
    SpqrSendCoinsTightLinkedEnv F K
      { ret := 0#64, st := ⟨0#64, 0#64, 0#64, stBs⟩, cur := 0#64, rest := rest }
      evs

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
