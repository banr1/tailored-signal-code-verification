/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.RoFrame
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `.rodata` String Splitting and `r1b_ErrCtxPlaced.after_call`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.RoFrame`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_ErrCtxPlaced.after_call [LibsignalPlacement] {CodeOk : Memory → Prop}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    (hc : r1b_ErrCtxPlaced CodeOk g d s0 s off)
    (hx19 : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (htr0 : st_bl.trace = s.trace)
    (hfs0 : st_bl.fs.files = s.fs.files)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_ErrCtxPlaced CodeOk g d s0 sf off' :=
  hc.of_step hin (hcs.1.trans hx19) (hcs.2.1.trans hx20) (hcs.2.2.1.trans hx21)
    (htr.trans htr0) (hfs.trans hfs0)

end CryptoVerification.SignalSession.Cli.RunCompose
