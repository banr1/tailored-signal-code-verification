/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2IfacePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame

/-!
# Relocatable `main` M2 Collect Half (`M+0xc0 → M+0x2f4 / M+0x1b0`, Block `617`)

Composes the first-element setup and `Vec<&str>` push loop on Block `617` under
`[LibsignalPlacement]`, establishing `AtM2DispatchPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Argument-collection half of `main_m2` (`M+0xc0 → M+0x2f4` if `i.argv.length = 2`, else
`M+0x1b0`) on Block `617`. -/
theorem main_m2_collect_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
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
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64),
      AtM2DispatchPlaced CodeOk s0 s' i.argv.length buf vcap vptr →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (argsBuf A vcap vptr ps ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ Statics)
      Q Qp oom := by
  have hn1_le : 1 ≤ i.argv.length := by
    cases h : i.argv with
    | nil => exact False.elim (hne h)
    | cons _ _ => simp
  rw [mProgPlaced_eq]
  exact M2EntryPlaced.step_collect_first_placed (M2StepsPlaced.m2EnvPlaced_init hc)
    hstk hstk64 hn1_le (argv_len_le hok) (ps_length_eq hps)
    (fun k hk => (ps_getElem_bounds hok hps k hk).1)
    ⟨by simpa only [mPcPlaced_eq] using hs.base.pc,
      hs.base.run, hs.base.sp, hs.base.fp, hs.base.inv,
      hs.base.vregs, hs.base.spAligned, fsp_spAligned hs.base.spAligned hs.base.sp⟩
    hs.x19 hs.x22 hs.x23 hs.x24 hs.x25 hs.trace hs.fs hpanic
    (fun s' vcap vptr hf' hx19' hx20' hx21' hx23' hx24' htr' hfs' hvcap_ne' => by
      rw [← mProgPlaced_eq]
      exact hnext s' vcap vptr
        ⟨⟨by simpa only [mPcPlaced_eq] using hf'.pc,
          hf'.run, hf'.sp, hf'.fp, hf'.inv, hf'.vregs, hf'.spAligned⟩,
          hf'.spAligned, hx19', hx20', hx21', hx23', hx24', hvcap_ne', htr', hfs'⟩)

end CryptoVerification.SignalSession.Cli.MainHops
