/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Spec
public import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# State-Coupled Poll and Wrapper Contracts for `decrypt_prekey`

Generalizes `DpPollK`, `dpPollSpec`, and `cliDecryptPrekeySpec` to `DpPollKState`, where `inv`
observes `(fs, trace)` at entry and `res` relates `(fs0, tr0, fs1, tr1, ws)` at exit.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.SignalSession.Cli

/-- State-coupled poll contract parameter: `inv` observes `(fs, trace)` at entry and `res`
relates the entry/exit filesystem, trace, and 6 result words `ws`. -/
structure DpPollKState where
  Ghost : Type
  args : Ghost → List (BitVec 64)
  inv : Ghost → FsState → List TraceEvent → SepProp
  res : Ghost → FsState → List TraceEvent → FsState → List TraceEvent → List (BitVec 64) → SepProp
  panics : Ghost → Prop
  need : Nat

/-- Ghost state for `dpPollSpecState`: output slot, future, `Context`, and `K`'s ghost. -/
structure DpPollGhostState (K : DpPollKState) where
  out : BitVec 64
  fut : BitVec 64
  cx : BitVec 64
  g : K.Ghost

/-- State-coupled contract for one poll of an unresumed `message_decrypt_prekey` future. -/
def dpPollSpecState (K : DpPollKState) (stk : Nat) : Spec (DpPollGhostState K) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.fut ∧ s.readReg64 .x2 = x.cx ∧
      (K.args x.g).length = 13 ∧ stk ≤ s.sp.toNat⌝ ∗
      memRegion x.out 48 ∗ dpFutStartAt x.fut (K.args x.g) ∗ dpCxAt x.cx ∗
      K.inv x.g s.fs s.trace ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.out ws ∗ K.res x.g s0.fs s0.trace sf.fs sf.trace ws) ∗
      dpFutDoneAt x.fut ∗ memRegion x.cx 32 ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨ K.panics x.g)⌝ ∗ anyHeap

/-- Ghost state for `cliDecryptPrekeySpecState`: sret slot (`x8`) and `K`'s ghost. -/
structure DecryptPrekeyGhostState (K : DpPollKState) where
  ret : BitVec 64
  g : K.Ghost

/-- State-coupled contract for `signal_session_handshake::decrypt_prekey` under `K`. -/
def cliDecryptPrekeySpecState (K : DpPollKState) (stk : Nat) : Spec (DecryptPrekeyGhostState K) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (K.args x.g).length = 13 ∧
      (K.args x.g).take 8 =
        [s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
          s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6, s.readReg64 .x7] ∧
      stk ≤ s.sp.toNat⌝ ∗
      dpWordsAt s.sp ((K.args x.g).drop 8) ∗ memRegion x.ret 48 ∗
      K.inv x.g s.fs s.trace ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.ret ws ∗ K.res x.g s0.fs s0.trace sf.fs sf.trace ws) ∗
      dpWordsAt s0.sp ((K.args x.g).drop 8) ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨ K.panics x.g)⌝ ∗ anyHeap

/-- Embeds a stateless `DpPollK` into `DpPollKState`. -/
def DpPollK.toState (K : DpPollK) : DpPollKState where
  Ghost := K.Ghost
  args := K.args
  inv := fun g _ _ => K.inv g
  res := fun g fs0 tr0 fs1 tr1 ws => ⌜K.io g fs0 tr0 fs1 tr1⌝ ∗ K.res g ws
  panics := K.panics
  need := K.need

end CryptoVerification.SignalSession.Cli.RunProofs
