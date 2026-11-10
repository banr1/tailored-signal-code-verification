/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` DH Commit Checkpoint & Contract

Fetch macro `td_fetches_cli`, checkpoint state `S3CommitState` at `+0x8ac`, and sub-segment
contract `S3CommitSpec` (`+0x8ac → +0x3e4`) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `tripleRatchetProgAt`.
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

/-! ## Fetch Macro, Checkpoint State, and `S3CommitSpec` -/

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`hfn : fnOff tryDecryptName =
0x6eff8`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "td_fetches_cli " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli $b $H $hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") $k0 $len)

namespace ChainArrayBytes

end ChainArrayBytes

/-- S3 commit checkpoint PC (`+0x8ac` = `+2220`): Entry to the state-commit, `PublicKey::serialize`, `ChainKey::to_pb`, `receiver_chains` push,
oldest-chain eviction loop, and `S4State` staging block (`+0x8ac .. +0xbfc → +0x3e4`),
reached when `cbz w8, +2220` at `+0x7e0` sees `w8 = 0` (`Ok((finalRootKey, senderChainKey))`
from the sending `RootKey::create_chain` call at `+0x7d4`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x8ac#64

/-- S3 commit checkpoint state (`segS3CommitPC img = +0x8ac`): Both `RootKey::create_chain` calls (receiving at `+0x544` and sending at `+0x7d4`) and
`KeyPair::generate` (`rng_fill` + clamping + `derive_public_key_bytes` at `+0x77c..+0x7c0`)
have succeeded:
* `tr.ratchet.senderChain = some sc`, and `tr.ratchet.rootKey` in `sp + 0xb8..0xd8` has been
  zeroed (`{ tr.ratchet with rootKey := 0 }`);
* `draws = min 32 x.rest.length` bytes have been drawn from `tapeAfter`;
* `[sp + 0x190..0x1d8]` (`x25`) holds `createChainResultAt (sp + 0x190) (.ok (finalRootKey,
senderChainKey))`:
  `0#32` at `sp + 0x190`, `keyToBytes32 finalRootKey` at `sp + 0x194..0x1b4`, and
  `chainKeyBytes senderChainKey` at `sp + 0x1b4..0x1d8`;
* `[sp + 0x3d0..0x3f4]` (`x28`) holds `chainKeyBytes receiverChainKey` (`36` B), and its copies for
  `S4State` staging are already placed at `sp + 0x4d0..0x4e0` (`take 16`, `x29 - 0xb0`),
  `sp + 0x10..0x14` (`(drop 16).take 4`), and `sp + 0x2b0..0x2c0` (`drop 20`, `x25 + 0x120`);
* `[sp + 0x400..0x440]` holds `newSenderKey.publicKey` (`0x400..0x420`) and
  `newSenderKey.privateKey` (`0x420..0x440`);
* `[sp + 0x1c]` holds `msgW : BitVec 32` with `msgW.setWidth 8 = msgTypeByte x.msgType`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x3d0#64 ∧
  ∃ (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion (sp + 0x1d8#64) 0xd8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x110 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x440#64) 0x80 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x4e0#64) 0xa0 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S3 commit sub-segment contract (`+0x8ac → +0x3e4` or panic): From `S3CommitState` at `segS3CommitPC img` (`+0x8ac`) when `tr.ratchet.senderChain = some sc`,
execution updates `previous_counter` and `root_key`, serializes `x.msg.senderRatchetKey` via
`PublicKey::serialize` (`+0x8fc`), converts `receiverChainKey` via `ChainKey::to_pb` (`+0xa80`),
pushes the new `ReceiverChain` onto `tr.ratchet.receiverChains` (calling `grow_one<Chain>` at
`+0xa98` if `len = cap`), deallocates the temporary `PublicKey::serialize` box (`+0xaf0`),
evicts oldest chains via `Vec::remove(0)` (`memmove` + `drop_glue<Chain>`, `+0xb04..+0xb94`)
until `len ≤ 5`, commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩`, stages
`receiverChainKey` across `sp + 0x2b0..0x2d4`, and branches (`+0xbfc: b +996`) to `segS4PC img`
(`+0x3e4`) in `S4State`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk img.base C A ctl abs →
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
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
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
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
