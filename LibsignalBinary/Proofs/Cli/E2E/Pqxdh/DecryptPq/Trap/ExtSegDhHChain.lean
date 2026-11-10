/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed DH Commit Sub-Segment Specification (`S3CommitSpec_ext`)

Lifts `S3CommitSpec_trap` onto `tripleRatchetProgAtExt img.base ext` under
`Stage2ContractsExt img C A ext` and `AllocContractsMem4K img.base A ext`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ChainKey Crypto KeyPair RatchetState ReceiverChain RootKey
  SenderChain SessionState TripleRatchet)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.LibsignalTripleRatchet (PublicKeySerializeOkX SpqrModel TrGhost
  TryDecryptGhost tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainSpec)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (ChainKeyToPbOkX GrowOneChainOkX)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHChain

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- S3 commit sub-segment contract (`+0x8ac → +0x3e4` or panic) on `tripleRatchetProgAtExt`:
From `S3CommitState` at `segS3CommitPC img` (`+0x8ac`) when `tr.ratchet.senderChain = some sc`,
execution updates `previous_counter` and `root_key`, serializes `x.msg.senderRatchetKey` via
`PublicKey::serialize`, converts `receiverChainKey` via `ChainKey::to_pb`,
pushes the new `ReceiverChain` onto `tr.ratchet.receiverChains` (calling `grow_one<Chain>`
if `len = cap`), deallocates the temporary `PublicKey::serialize` box,
evicts oldest chains via `Vec::remove(0)` (`memmove` + `drop_glue<Chain>`)
until `len ≤ 5`, commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩`, stages
`receiverChainKey` across `sp + 0x2b0..0x2d4`, and branches to `segS4PC img`
(`+0x3e4`) in `S4State`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitSpec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  PublicKeySerializeOkX img A ext →
  ChainKeyToPbOkX img A ext →
  GrowOneChainOkX img A ext →
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName)
    (dropChainSpec A) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
      (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
      (finalRootKey : RootKey) (senderChainKey : ChainKey)
      (R : SepProp) (s0 s : State),
      tr.ratchet.senderChain = some sc →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      CryptoGames.Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitState
        A ctl img x trG tr st1 receiverChainKey newSenderKey
        finalRootKey senderChainKey R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
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
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State
            A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec
             C A ctl parse S img).onPanic x s0 s' ∗ R)))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHChain
