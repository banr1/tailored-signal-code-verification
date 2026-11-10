/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `main` Hop M2 (`M+0xc0 → M+0x568 / M+0xb80`, Block `617`)

Composes `main_m2_collect_placed` (`M+0xc0 → AtM2DispatchPlaced`) with `main_m2_dispatch_placed`
(`AtM2DispatchPlaced → M+0x568 / M+0xb80`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Composes `main_m2_collect_placed` up to `AtM2DispatchPlaced` with `main_m2_dispatch_placed`
(`M+0xc0 → M+0x568 / M+0xb80`). -/
theorem main_m2_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
      Q Qp oom :=
  main_m2_collect_placed hc hstk hstk64 hok hne hps hs hpanic
    (fun _s' _vcap _vptr hd =>
      main_m2_dispatch_placed hc hstk hstk64 hok hne hps hd hpanic hexit hnext)

end CryptoVerification.SignalSession.Cli.MainHops
