/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# `PreKeySignalMessage::try_from`: Post-Kyber `Ok` Cut States (`+0x864`, `+0x8c0`, `+0x970`)

Defines the register/pure cut predicates `IdentOkState` (`+0x864`), `SigMsgOkState`
(`+0x8c0`), and `PackOkState` (`+0x970`) along the post-loop `Ok` path.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire

section W6States

/-- Frozen cut at `+0x864` (`2148`): `IdentityKey::try_from(identity_key)` returned `Ok`
(fall-through of `+0x860 b.ne`). Extends `KyberOkState` with `x24 = sp' + 312` (result slot)
and `x27 = registration_id.unwrap_or_default()` (`+0x840 csel w27`), plus the identity-key parse
`PublicKey.deserialize ik = .ok ipk` (its 32 bytes are at `sp' + 144 .. 176`). -/
def IdentOkState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (regId : BitVec 32) (bk : List (BitVec 8)) (pk : PublicKey)
    (ik : List (BitVec 8)) (ipk : PublicKey) (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  PublicKey.deserialize ik = .ok ipk ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
  sf.readReg64 .x27 = regId.zeroExtend 64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberBoxLen ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Frozen cut at `+0x8c0` (`2240`): `SignalMessage::try_from(message)` returned `Ok`
(fall-through of `+0x894 b.eq`) and `try_clone_from_ref(ptr0, len)` returned `x0 = clonePtr ≠ 0`
(fall-through of `+0x8bc cbz x0`). `x27 = msgW0` is the first word of the `SignalMessage` result
(stored to `sret` at `+0x8d0`); `regId` is in the spill `sp' + 56` (`+0x870`). -/
def SigMsgOkState (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (msgW0 clonePtr : BitVec 64) (bk : List (BitVec 8)) (pk : PublicKey)
    (ik : List (BitVec 8)) (ipk : PublicKey) (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  PublicKey.deserialize ik = .ok ipk ∧
  clonePtr ≠ 0#64 ∧ sf.readReg64 .x0 = clonePtr ∧ sf.readReg64 .x1 = len ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
  sf.readReg64 .x27 = msgW0 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberBoxLen ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Frozen cut at `+0x970` (`2416`): the 248-byte `sret` is packed (`+0x8c0 .. +0x96c`).
Exactly the register part of `deallocChain_970_wpX`'s pre (`x19 = sret`, `x26 = msgCap`,
`x23 = ikCap`). -/
def PackOkState (img : Obj.Image) (s0 : State) (sp' sret ikCap msgCap : BitVec 64)
    (sf : State) : Prop :=
  PostEpilogueState img s0 sp' sf ∧
  sf.readReg64 .x19 = sret ∧ sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x23 = ikCap

end W6States

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
