/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Mathlib.Tactic.Attr.Core
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs -- shake: keep

/-!
# Wrapper and Poll Contracts for `signal_session_handshake::decrypt_prekey`

Specifies the stack-frame layout and separation-logic contracts reducing
`signal_session_handshake::decrypt_prekey` (`poll_once(message_decrypt_prekey(…, &mut Coins))`,
48-byte `Option<Result<Vec<u8>, SignalProtocolError>>` sret in `x8`) to a single poll of
`message_decrypt_prekey::<Coins>::{closure#0}`:
- Frame (`0x30 + 0x830` bytes, `x29 = entry_sp - 0x30`, future `fut = x29 - 0x830`): stores the 13
  ABI argument words (`x0..x7` plus 5 stack words) at `fut + 0x00 .. +0x68`, `&mut Coins` at
  `fut + 0x68`, state byte `0` at `fut + 0x2c0`, and a 32-byte no-op `Context` at `x29 - 0x58`.
- Polling into `out = x29 - 0x38` returns `Ready` (word 0 `≠ -3`) and sets the future state byte to
  `1`, copying the 48-byte `Result` to `[x8]` and bypassing suspended-future drop paths (`3..8`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli

/-! ## Names and frame layout -/

abbrev cliDecryptPrekeyName : String := "libsignal_cli_handshake::decrypt_prekey"

/-- Symbol name of the `async fn message_decrypt_prekey::<Coins>` poll closure. -/
abbrev cliDpPollName : String :=
  "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"

/-- Consecutive 64-bit words in memory starting at `a`. -/
def dpWordsAt : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ dpWordsAt (a + 8#64) ws

/-- Byte size of the `message_decrypt_prekey` future (`fut .. cx`). -/
abbrev dpFutSize : Nat := 0x7d8
/-- Byte offset of the future's state discriminant. -/
abbrev dpFutStateOff : Nat := 0x2c0
/-- Byte offset of the `&mut Coins` word after the 13 ABI argument words. -/
abbrev dpFutCoinsOff : Nat := 0x68
/-- Stack frame size of the `decrypt_prekey` wrapper (`0x30` saved registers + `0x830`). -/
abbrev dpWrapFrame : Nat := 0x860

/-- Abstract contract parameter for a single `message_decrypt_prekey` poll over ghost state `Ghost`:
13 ABI argument words `args`, spatial invariant `inv`, 6-word result predicate `res`, I/O relation
`io`, non-OOM panic guard `panics`, and stack requirement `need`. -/
structure DpPollK where
  Ghost : Type
  args : Ghost → List (BitVec 64)
  inv : Ghost → SepProp
  res : Ghost → List (BitVec 64) → SepProp
  io : Ghost → FsState → List TraceEvent → FsState → List TraceEvent → Prop
  panics : Ghost → Prop
  need : Nat

/-- Ghost state for a `dpPollSpec` call: output slot `out`, future `fut`, `Context` `cx`, and inner ghost `g`. -/
structure DpPollGhost (K : DpPollK) where
  out : BitVec 64
  fut : BitVec 64
  cx : BitVec 64
  g : K.Ghost

/-- Unresumed future at `fut` initialized with `args`, `&mut Coins`, and state byte `0`. -/
def dpFutStartAt (fut : BitVec 64) (args : List (BitVec 64)) : SepProp :=
  dpWordsAt fut args ∗
    (∃∗ coins : BitVec 64, (fut + BitVec.ofNat 64 dpFutCoinsOff) ↦₆₄ coins) ∗
    memRegion (fut + BitVec.ofNat 64 (dpFutCoinsOff + 8)) (dpFutStateOff - (dpFutCoinsOff + 8)) ∗
    ((fut + BitVec.ofNat 64 dpFutStateOff) ↦₈ 0#8) ∗
    memRegion (fut + BitVec.ofNat 64 (dpFutStateOff + 1)) (dpFutSize - (dpFutStateOff + 1))

/-- Completed future at `fut` with state byte `1`. -/
def dpFutDoneAt (fut : BitVec 64) : SepProp :=
  memRegion fut dpFutStateOff ∗ ((fut + BitVec.ofNat 64 dpFutStateOff) ↦₈ 1#8) ∗
    memRegion (fut + BitVec.ofNat 64 (dpFutStateOff + 1)) (dpFutSize - (dpFutStateOff + 1))

/-- No-op `core::task::Context` (`Context::from_waker(Waker::noop())`) at `cx`. -/
def dpCxAt (cx : BitVec 64) : SepProp :=
  ∃∗ wk : BitVec 64, (cx ↦₆₄ wk) ∗ ((cx + 8#64) ↦₆₄ wk) ∗ ((cx + 16#64) ↦₆₄ 0#64) ∗
    memRegion (cx + 24#64) 8

/-! ## Poll and wrapper specifications -/

/-- Contract for one poll of an unresumed `message_decrypt_prekey` future returning `Ready` (word 0 `≠ -3`) in state `1`. -/
def dpPollSpec (K : DpPollK) (stk : Nat) : Spec (DpPollGhost K) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.fut ∧ s.readReg64 .x2 = x.cx ∧
      (K.args x.g).length = 13⌝ ∗
      memRegion x.out 48 ∗ dpFutStartAt x.fut (K.args x.g) ∗ dpCxAt x.cx ∗
      K.inv x.g ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜K.io x.g s0.fs s0.trace sf.fs sf.trace⌝ ∗
      (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.out ws ∗ K.res x.g ws) ∗
      dpFutDoneAt x.fut ∗ memRegion x.cx 32 ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨ K.panics x.g)⌝ ∗ anyHeap

/-- Ghost state for `cliDecryptPrekeySpec`: sret pointer `ret` (`x8`) and inner ghost `g`. -/
structure DecryptPrekeyGhost (K : DpPollK) where
  ret : BitVec 64
  g : K.Ghost

/-- Contract for `signal_session_handshake::decrypt_prekey` parameterized by poll contract `K`. -/
def cliDecryptPrekeySpec (K : DpPollK) (stk : Nat) : Spec (DecryptPrekeyGhost K) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (K.args x.g).length = 13 ∧
      (K.args x.g).take 8 =
        [s.readReg64 .x0, s.readReg64 .x1, s.readReg64 .x2, s.readReg64 .x3,
          s.readReg64 .x4, s.readReg64 .x5, s.readReg64 .x6, s.readReg64 .x7]⌝ ∗
      dpWordsAt s.sp ((K.args x.g).drop 8) ∗ memRegion x.ret 48 ∗
      K.inv x.g ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜K.io x.g s0.fs s0.trace sf.fs sf.trace⌝ ∗
      (∃∗ ws : List (BitVec 64),
        ⌜ws.length = 6 ∧ ws.head? ≠ some 0xfffffffffffffffd#64⌝ ∗
          dpWordsAt x.ret ws ∗ K.res x.g ws) ∗
      dpWordsAt s0.sp ((K.args x.g).drop 8) ∗ stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ (allocFailedIn s0 sf ∨ K.panics x.g)⌝ ∗ anyHeap

example : libsignalSessionCode.fnOff cliDecryptPrekeyName =
    num% (ls_off% "libsignal_cli_handshake::decrypt_prekey") :=
  ls_lemma% fnOff "libsignal_cli_handshake::decrypt_prekey"

example : libsignalSessionCode.fnOff cliDpPollName =
    num% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") :=
  ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"

end CryptoVerification.SignalSession.Cli.RunProofs
