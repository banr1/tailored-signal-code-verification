/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# `PreKeySignalMessage::try_from`: Error and Allocation-Failure Cut States (`+0x978`, `+0x9f0`, `+0xa68`)

Defines the register states `KyberBoxErrState`, `IdentErrState` (`+0x978`),
`SigMsgErrState` (`+0x9f0`), and `CloneAllocFail` (`+0xa68`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire

section W6Exits

/-- Common register/machine state at the Kyber-box error-tail entries `+0x978` (`2424`) and
`+0x9f0` (`2544`): `x28 = kyberBoxPtr`, `x25 = kyberBoxLen` (Kyber `Box<[u8]>`, or `0` when absent),
`x26 = msgCap`, `x23 = ikCap`, `x19 = sret`, frame pointer `x29 = sp' + 512`. -/
def KyberBoxErrState (img : Obj.Image) (s0 : State)
    (sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
  sf.readReg64 .x25 = kyberBoxLen ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x19 = sret

/-- Error-tail entry at `+0x978` (`2424`): `IdentityKey::try_from` returned `Err`
(branch `+0x860 b.ne`). -/
abbrev IdentErrState (img : Obj.Image) (s0 : State)
    (sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (sf : State) : Prop :=
  KyberBoxErrState img s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf

/-- Error-tail entry at `+0x9f0` (`2544`): `SignalMessage::try_from` returned `Err`
(branch `+0x894 b.eq`). -/
abbrev SigMsgErrState (img : Obj.Image) (s0 : State)
    (sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (sf : State) : Prop :=
  KyberBoxErrState img s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf

/-- Frozen Allocation-failure panic entry at `+0xa68` (`2664`): reached from `+0x8bc cbz x0` when
`__rust_alloc` returns `x0 = 0#64` (`allocFailedIn s0 sf`). -/
def CloneAllocFail (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (sf : State) : Prop :=
  sf.sp = sp' ∧ sf.spAligned = true ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
  allocFailedIn s0 sf ∧ s0.trace <+: sf.trace

end W6Exits

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
