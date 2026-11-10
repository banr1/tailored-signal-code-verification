/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs

/-!
# Tight-Panic Specifications for CLI `try_decrypt_with_state`

Specializes `tryDecryptSpec` and front-segment contracts (`ErrTailSpec`, `LoadRatchetSpec`,
`DhStepSpec`) to the tight panic predicate `tryDecryptOnPanicTight`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalSession

/-- `tryDecryptSpec` specialized to the tight panic predicate `tryDecryptOnPanicTight`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img with onPanic := tryDecryptOnPanicTight C S parse }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOk img C A ctl abs →
  DerivePublicKeyBytesOk img.base C ctl abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

end CryptoVerification.LibsignalTripleRatchet.Decrypt
