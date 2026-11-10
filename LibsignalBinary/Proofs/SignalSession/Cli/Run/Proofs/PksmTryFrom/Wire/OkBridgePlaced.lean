/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `Ok`-Path State Cuts and Bridges

Re-exports `OkBridge` and defines the `[LibsignalPlacement]` midpoint state invariants
`BaseKeyOkStatePlaced` (`+0x684`), `DeserErrTailStatePlaced` / `DeserErrTailStateEPlaced`
(`+0x7a8`), and `KyberOkStatePlaced` (`+0x86c`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Frozen Ok exit state at `+0x684` (`1668`) under `[LibsignalPlacement]`
when `PublicKey.deserialize bk = .ok pk`: includes
`ecKeyParses bk = true`, `pkOf bk = pk`, and `(pkOf bk).bytes.toList = (bk.take 33).drop 1`. -/
def BaseKeyOkStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (bk : List (BitVec 8)) (pk : PublicKey) (sf : State) : Prop :=
  PostEpilogueStatePlaced s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Frozen exit state at `+0x7a8` (`1960`) under `[LibsignalPlacement]`
when `PublicKey.deserialize bk = .error e`. -/
def DeserErrTailStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (sf : State) : Prop :=
  PostEpilogueStatePlaced s0 sp' sf ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = 1#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

/-- Exact-`SignalProtocolError` M2 exit state at `+0x7a8` (`1960`) under `[LibsignalPlacement]`,
pinning `speWordsOf e (sf.readReg64 .x9) (sf.readReg64 .x8) (sf.readReg64 .x10)`. -/
def DeserErrTailStateEPlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (e : SignalProtocolError) (sf : State) : Prop :=
  DeserErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
  speWordsOf e (sf.readReg64 .x9) (sf.readReg64 .x8) (sf.readReg64 .x10)

/-- Frozen Ok exit state at `+0x86c` (`2156`) under `[LibsignalPlacement]`. -/
def KyberOkStatePlaced [LibsignalPlacement] (s0 : State)
    (sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64) (vb : BitVec 8)
    (bk : List (BitVec 8)) (pk : PublicKey) (sf : State) : Prop :=
  PostEpilogueStatePlaced s0 sp' sf ∧
  ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
  sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
  sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
  sf.readReg64 .x25 = kyberBoxLen ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
  sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
  sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret

theorem BaseKeyOkStatePlaced.ecKeyParses [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    ecKeyParses bk = true :=
  h.2.1

theorem BaseKeyOkStatePlaced.pkOf_eq [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    pkOf bk = pk :=
  h.2.2.1

theorem BaseKeyOkStatePlaced.pkOf_bytes [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk sf) :
    (pkOf bk).bytes.toList = (bk.take 33).drop 1 :=
  h.2.2.2.1

theorem KyberOkStatePlaced.ecKeyParses [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    ecKeyParses bk = true :=
  h.2.1

theorem KyberOkStatePlaced.pkOf_eq [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    pkOf bk = pk :=
  h.2.2.1

theorem KyberOkStatePlaced.pkOf_bytes [LibsignalPlacement] {s0 : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey} {sf : State}
    (h : KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf) :
    (pkOf bk).bytes.toList = (bk.take 33).drop 1 :=
  h.2.2.2.1

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
