/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.States
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned

/-!
# `signal_session::run`: Continuation Abbreviations and `dropSpeOwned` Slot

Continuation abbreviations (`JoinK`, `RejectK`, `PanicK`) and the shared `run_hop_dropSpeOwned`
slot used across `Compose/Arms/*` and wired into `run_ok'` in `Compose/RunOk.lean`:

| Theorem | Range (`R+k`) | Source state | Next state(s) | Module |
|---|---|---|---|---|
| `run_hop_dropSpeOwned` | `cliDropSpeName` | `AllocContractsX` | `DropSpeOwnedOk` | `Compose/Hops.lean` |
| `run_hop_pre_ok` | `R+0x0 → R+0x214` | `AtRunEntry` | `AtDispatch ∨ AtReject` | `Compose/Arms/R0.lean` |
| `run_hop_send_ok` | `R+0x214 → R+0xf8c / R+0x2c7c` | `AtDispatch` (`send`) | `AtJoin ∨ AtReject` | `Compose/Arms/R2.lean` |
| `run_hop_init1_ok` | `R+0x214 → R+0x74c / R+0x2c7c` | `AtDispatch` (`init`) | `AtInit1 ∨ AtReject` | `Compose/Arms/R1a.lean` |
| `run_hop_init2_ok` | `R+0x74c → R+0x28f0 / R+0x2c7c` | `AtInit1` | `AtInit2 ∨ AtReject` | `Compose/Arms/R1b.lean` |
| `run_hop_init3_ok` | `R+0x28f0 → R+0xf8c / R+0x2c7c` | `AtInit2` | `AtJoin ∨ AtReject` | `Compose/Arms/R1c.lean` |
| `run_hop_recvW_ok` | `R+0x214 → R+0xf8c / R+0x2c7c` | `AtDispatch` (`recv`, `2 ‖ …`) | `AtJoin ∨ AtReject` | `Compose/Arms/R3a.lean` |
| `run_hop_recvP_ok` | `R+0x214 → R+0xf8c / R+0x2c7c` | `AtDispatch` (`recv`, `3 ‖ …`) | `AtJoin ∨ AtReject` | `Compose/Arms/R3b.lean` |
| `run_hop_recvBad_ok` | `R+0x214 → R+0x2c7c` | `AtDispatch` (`recv`, empty / `∉ {2,3}`) | `AtReject` | `Compose/Arms/R3b.lean` |
| `run_hop_join_ok` | `R+0xf8c / R+0x124 / R+0x2c7c → lr` | `AtJoin ∨ AtReject` | `runPost` at `lr` | `Compose/Arms/J.lean` |
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## Continuation abbreviations -/

/-- Continuation from `AtJoin` (`R + 0xf8c`). -/
abbrev JoinK (img : Obj.Image) (ext : String → Option (State → State)) (A : RustAlloc)
    (g : RunCall) (s0 : State) (resStack : Nat) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (g' : StoresGhost) (out : Bytes),
    AtJoin img ext g g' out s0 s →
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (joinMem A g g' out s0 resStack) Q Qp (runOom s0)

/-- Continuation from `AtReject` (`R + 0x124` or `R + 0x2c7c`). -/
abbrev RejectK (img : Obj.Image) (ext : String → Option (State → State)) (A : RustAlloc)
    (g : RunCall) (s0 : State) (resStack : Nat) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s : State) (g' : StoresGhost) (rk : RejectKind),
    AtReject img ext g g' rk s0 s →
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (rejectMem A g g' rk s0 resStack) Q Qp (runOom s0)

/-- Panic continuation obligation for every hop (`g.a = none ∨ allocFailedIn s0 sf`). -/
abbrev PanicK (g : RunCall) (s0 : State) (Qp : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (Pf : SepProp), runPanicProp g s0 sf → Qp sf Pf

/-! ## `dropSpeOwnedSpec` callee slot -/

/-- `drop_glue::<SignalProtocolError>` meets `dropSpeOwnedSpec` from `himg` and `hh.alloc`.
Passed as `hdrop` to each SPE-dropping hop of `signal_session::run`. -/
theorem run_hop_dropSpeOwned {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (halloc : AllocContractsX img A ext) :
    RunDrop.DropSpeOwnedOk img A ext :=
  RunProofs.cliDropSpeOwned_ok himg halloc

end CryptoVerification.SignalSession.Cli.RunCompose
