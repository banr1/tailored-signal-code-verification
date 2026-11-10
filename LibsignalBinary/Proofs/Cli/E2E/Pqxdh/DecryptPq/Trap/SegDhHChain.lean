/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG DH Commit Sub-Segment Contract (`S3CommitSpec_trap`)

Defines `S3CommitSpec_trap` (`+0x8ac → +0x3e4` or panic) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS10

end BS10

namespace ChainArrayBytes

end ChainArrayBytes

/-- S3 commit sub-segment contract (`+0x8ac → +0x3e4` or panic): From `S3CommitState` at `segS3CommitPC img` (`+0x8ac`) when `tr.ratchet.senderChain = some sc`,
execution updates `previous_counter` and `root_key`, serializes `x.msg.senderRatchetKey` via
`PublicKey::serialize` (`+0x8fc`), converts `receiverChainKey` via `ChainKey::to_pb` (`+0xa80`),
pushes the new `ReceiverChain` onto `tr.ratchet.receiverChains` (calling `grow_one<Chain>` at
`+0xa98` if `len = cap`), deallocates the temporary `PublicKey::serialize` box (`+0xaf0`),
evicts oldest chains via `Vec::remove(0)` (`memmove` + `drop_glue<Chain>`, `+0xb04..+0xb94`)
until `len ≤ 5`, commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩`, stages
`receiverChainKey` across `sp + 0x2b0..0x2d4`, and branches (`+0xbfc: b +996`) to `segS4PC img`
(`+0x3e4`) in `S4State`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
      (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
      (finalRootKey : RootKey) (senderChainKey : ChainKey)
      (R : SepProp) (s0 s : State),
      tr.ratchet.senderChain = some sc →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitState A ctl img x trG tr st1 receiverChainKey newSenderKey
        finalRootKey senderChainKey R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      let newChain : ReceiverChain :=
        { senderRatchetKey := x.msg.senderRatchetKey
          chainKey := some receiverChainKey
          messageKeys := [] }
      let r1 : RatchetState :=
        { tr.ratchet with
          senderChain := some ⟨newSenderKey, senderChainKey⟩
          rootKey := finalRootKey
          previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
          receiverChains :=
            RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
