/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseFailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseArgsShape
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkComposePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable M1–M6 Composition for `main` (`[LibsignalPlacement]`, Block `617`)

Plugs the placed proofs of hops M1–M6 into `main_ok_tight_compose_m1_m6_placed` to establish
`mainSpecTightPlaced` and `mainSpecPlaced` on Block `617` (`mProgPlaced H`).
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

namespace MainOkHelpers

theorem exitK_main_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {r : MainResult} {s0 : State} {stk : Nat} {R : SepProp}
    {G : Nat → State → Prop}
    (hstk : mainFrameSize ≤ stk)
    (hG : ∀ code s, G code s → ∀ sf, sf.trace = s.trace → sf.fs = s.fs →
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code →
      MainPost r s0 sf ∨ allocFailedIn s0 sf) :
    ExitKPlaced CodeOk H A s0 stk G
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) :=
  MainOkPlacedHelpers.exitK_main_placed hstk hG

theorem exitK_main_tight_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {r : MainResult} {s0 : State} {stk : Nat} {R : SepProp}
    {G : Nat → State → Prop}
    (hstk : mainFrameSize ≤ stk)
    (hG : ∀ code s, G code s → ∀ sf, sf.trace = s.trace → sf.fs = s.fs →
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code →
      MainPost r s0 sf) :
    ExitKPlaced CodeOk H A s0 stk G
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) :=
  MainOkPlacedHelpers.exitK_main_tight_placed hstk hG

end MainOkHelpers

/-- `main` satisfies `mainSpecTightPlaced` on Block `617` (`mProgPlaced H` = `lsProg_617 H`). -/
theorem main_ok_tight_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {stk hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidTryParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack) (hfacts : MainIoFacts io)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A uuidTryParse Run
        (fun p => io.pathOk p ∧ p.length < 2 ^ 32) resStack))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk A stk cliStaticsPlaced Run) :=
  main_ok_tight_compose_m1_m6_placed hc hio hfacts hparse hstk hstk64
    (fun hok hne hps hs1 hp hex hn =>
      main_m2_placed_proof hc hstk hstk64 hok hne hps hs1 hp hex hn)
    (fun hfs0 htr0 hsin hcok hcs hpc hs2 hp hex hn =>
      main_m3_placed_proof hc hio hstk hstk64 hfs0 htr0 hsin hcok hcs hpc hs2 hp hex hn)
    (fun hsp htr0 hpc hlen hs3 hp hex =>
      main_m4_sendOverCap_placed_proof hc hstk hstk64 hsp htr0 hpc hlen hs3 hp hex)
    (fun hsp htr0 hR hnover hpc hs3 hp hex hn =>
      main_m4_call_placed_proof hc hrun hstk hstk64 hsp htr0 hR hnover hpc hs3 hp hex hn)
    (fun htr0 hwr hs4 hp hn =>
      main_m5_proof_placed hc hio hstk hstk64 htr0 hwr hs4 hp hn)

/-- `main` satisfies `mainSpecPlaced` on Block `617` (`mProgPlaced H` = `lsProg_617 H`). -/
theorem main_ok_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {stk hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidTryParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack) (hfacts : MainIoFacts io)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced CodeOk A uuidTryParse Run
        (fun p => io.pathOk p ∧ p.length < 2 ^ 32) resStack))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (mainSpecPlaced CodeOk A stk cliStaticsPlaced Run) :=
  subroutine_ok_mainSpecPlaced_of_tight
    (main_ok_tight_placed_proof hc hio hfacts hrun hparse hstk hstk64)

end CryptoVerification.SignalSession.Cli.MainHops
