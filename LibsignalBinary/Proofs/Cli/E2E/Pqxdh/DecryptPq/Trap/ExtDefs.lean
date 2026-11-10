/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Statements
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed (`Stage2ContractsExt` + `AllocContractsMem4K`) Definitions for Handshake `DecryptPq`

Defines the contract-backed (`tripleRatchetProgAtExt img.base ext`) callee bundle
`TryDecryptCallees_ext`, segment contracts `S0Spec_ext`..`S9Spec_ext`,
`S1SpecTight_ext`, `S3SpecTight_ext`, `ErrTailSpec_ext`, `ErrTailSpecTight_ext`,
and shared hook/callee-at-offset helpers for
`libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_handshake::Coins>`.
-/

set_option maxRecDepth 200000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (ChainKey Crypto MessageKeyGenerator MessageKeys Mut
  RatchetState SessionState ShaCompress SignalProtocolError TripleRatchet aesCbcDecrypt)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalSessionRepr (ratchetAt)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf decryptDraws
  serializeAddresses serviceIdParse)
open CryptoVerification.LibsignalTripleRatchet (FindReceiverChainKeyGhost GenerateKeysGhost
  PublicKeySerializeOkX RemoteIdentityKeyOkExt SpqrModel TrApplyOkX TrFromOkX TrGhost
  TryDecryptGhost createChainName entryOf_eq_tripleRatchetProgAtExt
  extHookStack extractStackExt findReceiverChainKeyName findReceiverChainKeyResultAt
  generateKeysName messageKeysAt mkgAt spqrRecvKeyAt rootStack spqrRecvName spqrRecvSpec
  tripleRatchetProgAtExt verifyMacWithAddressesName)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainSpec
  isSameAccountName isSameAccountSpecExt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (ChainKeyToPbOkX ClearUpkOkX CmkOkX
  DerivePublicKeyBytesOkX GrowOneChainOkX LocalIdentityKeyOkExt spqrRecvSpecQF
  tryDecryptOnPanicTight)
open CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq (ErrTailState
  IsSameAccountDistinctOkExt32 S1State S2State S3State S4State S5State S6State S7State S8State
  S9State dropChainName errTailPC segS1PC segS2PC segS3PC segS4PC segS5PC segS6PC segS7PC segS8PC
  segS9PC tryDecryptEntry tryDecryptName tryDecryptSpecQF)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs

/-! ## 1. Callee `Ok` Predicates and `TryDecryptCallees_ext` Bundle -/

/-- Stack budget for `find_receiver_chain_key` when `find_receiver_chain_index` uses `Stage1X.findIndexStackX` (`0x90 + 1024 + 16384 = 17552` B). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.findReceiverChainKeyStackX : Nat :=
  0x90 + (1024 + extHookStack)

/-- `findReceiverChainKeySpec A` with stack budget `findReceiverChainKeyStackX` (`0x90 + 0x50 + 16384`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.findReceiverChainKeySpecX (A : RustAlloc) :
    Spec FindReceiverChainKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
    ratchetAt A x.self x.G x.st ∗
    (x.theirA ↦ₛ x.their.bytes.toList) ∗
    memRegion x.ret 40 ∗
    stackAt s.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.findReceiverChainKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ratchetAt A x.self x.G x.st ∗
    (x.theirA ↦ₛ x.their.bytes.toList) ∗
    findReceiverChainKeyResultAt x.ret (x.st.findReceiverChainKey x.their) ∗
    stackAt s0.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.findReceiverChainKeyStackX

/-- `tripleRatchetProgAtExt` `extHookStack` variant of `FindReceiverChainKeyOk`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOkX
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.findReceiverChainKeySpecX A).inImage img)

/-- Minimum stack budget for `signal_session_coins_fill` under `CliExt.memHookStack` (`0x50 + 4096 = 4176` B). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.coinsFillStackExt : Nat :=
  0x50 + CryptoVerification.SignalSession.CliExt.memHookStack

/-- `signal_session_coins_fill` contract on `tripleRatchetProgAtExt img.base ext` for any stack `stk ≥ coinsFillStackExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  ∀ (stk : Nat), CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.coinsFillStackExt ≤ stk →
    stk ≤ 2 ^ 63 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.SignalSession.Coins.coinsFillName)
      ((CryptoVerification.SignalSession.Coins.coinsFillSpec img.base stk).inImage img)

/-- `is_same_account` (unequal keys / 32-bit `black_box`, `extHookStack`) contract. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_ext
    (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName)
    isSameAccountSpecExt

/-- `is_same_account` (`DistinctSid`, 32-bit `black_box` + `uuid_try_parse`, `extHookStack`) contract. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOk_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  IsSameAccountDistinctOkExt32 b A ext

/-- `drop_glue::<Chain> [local#4]` (`DecryptPq.dropChainName`) contract on `tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropChainName)
    (dropChainSpec A)

/-- Stack budget of `<RootKey>::create_chain` on `tripleRatchetProgAtExt`: `576 + extractStackExt = 17936` B. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.createChainStackExt : Nat :=
  576 + extractStackExt

/-- `<RootKey>::create_chain` contract at `extractStackExt` (`17936` B total stack) on `tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
    ((CryptoVerification.LibsignalTripleRatchet.Keys.createChainSpecAt C A extractStackExt).inImage img)

/-- Stack budget of `<MessageKeyGenerator>::generate_keys` calling stacked `Hkdf::extract` (`496 + extractStackExt = 17856` B). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.generateKeysStackExt : Nat :=
  496 + extractStackExt

/-- `generateKeysSpec F A` at `generateKeysStackExt` (`17856` B, matching `ExtGenKeysMac.generateKeysSpecExt`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.generateKeysSpecExt
    (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A x.genA x.g ∗ spqrRecvKeyAt A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
      A.pool ∗ stackAt s.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.generateKeysStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
      messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
      A.pool ∗ stackAt s0.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.generateKeysStackExt

/-- `<MessageKeyGenerator>::generate_keys` stacked contract (`17856` B) on `tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.generateKeysSpecExt C.F A).inImage img)

/-- `verify_mac_with_addresses` stacked contract (`computeMacStackExt32`) on `tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
    ((CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses.verifyMacWithAddressesSpecWithStack
      img C.F A parse
      CryptoVerification.LibsignalTripleRatchet.Statements.computeMacStackExt32).inImage img)

/-- `spqr::recv` `QF` contract on `tripleRatchetProgAtExt img.base ext`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_ext
    (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img)

/-- `spqr::recv` `Q` contract on `tripleRatchetProgAtExt img.base ext`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_ext
    (Q : List (BitVec 8) → Prop) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))

/-- Bundle of the 17 callee `subroutine_ok` contracts on `tripleRatchetProgAtExt img.base ext` for handshake `try_decrypt_with_state::<signal_session_handshake::Coins>`. -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOkExt img A ext
  remoteIk : RemoteIdentityKeyOkExt img A ext
  sameAcc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_ext img.base ext
  sameAccDistinct :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOk_ext img.base A ext
  clearUpk : ClearUpkOkX img A ext
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext
  chainKeyToPb : ChainKeyToPbOkX img A ext
  derivePk : DerivePublicKeyBytesOkX img C ext
  trFrom : TrFromOkX img A ext
  trApply : TrApplyOkX img A ext
  findReceiverChainKey :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOkX img A ext
  createChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_ext img C A ext
  genKeys : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_ext img C A ext
  pkSer : PublicKeySerializeOkX img A ext
  verifyMac :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_ext img C A parse ext
  cmk : CmkOkX img C A ext
  growOne : GrowOneChainOkX img A ext
  coinsFill : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext img ext

/-! ## 2. Segment Contracts `S0Spec_ext` .. `S9Spec_ext`, Tight Variants, and `TryDecryptOk*_ext` -/

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpecTight_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  LocalIdentityKeyOkExt img A ext →
  RemoteIdentityKeyOkExt img A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_ext img.base ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segS1PC img) s0
        (S1State A ctl img x R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  TrFromOkX img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      S1State A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, S2State A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1SpecTight_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  TrFromOkX img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      S1State A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, S2State A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      S2State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segS4PC img) s
          (S4State A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segS3PC img) s
          (S3State A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (errTailPC img) s
          (ErrTailState A ctl img x trG tr st1 e 0 R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext img ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_ext img C A ext →
  DerivePublicKeyBytesOkX img C ext →
  PublicKeySerializeOkX img A ext →
  ChainKeyToPbOkX img A ext →
  GrowOneChainOkX img A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      S3State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1,
              ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3SpecTight_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CoinsFillOk_ext img ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_ext img C A ext →
  DerivePublicKeyBytesOkX img C ext →
  PublicKeySerializeOkX img A ext →
  ChainKeyToPbOkX img A ext →
  GrowOneChainOkX img A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_ext img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      S3State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1,
              ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CmkOkX img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S4State A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', S5State A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_ext
    (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_ext Q Pstk F A S ext img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      S5State A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec_ext
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_ext Q A S ext img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      S5State A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_ext img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segS7PC img) s
        (S7State A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_ext img C A parse ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailState A ctl img x trG tr st1
              (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsExt img C A ext →
  AllocContractsMem4K img.base A ext →
  TrApplyOkX img A ext →
  ClearUpkOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage →
      S9State A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF_ext
    (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (tryDecryptEntry img)
    (tryDecryptSpecQF Q F C A ctl parse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_ext
    (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (tryDecryptEntry img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre
      (Q ·.st.pqRatchetState))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptOk_of_okQF_ext
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF_ext Q emp img C A ctl parse S ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_ext Q img C A ctl parse S ext := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

/-! ## 3. Shared `fnAddr` & Hook-at-Offset Helpers for `DecryptPq.tryDecryptName` -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry_eq_fnAddr_ext
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.fnAddr_tryDecrypt_add_eq_ext
    {b : BitVec 64} {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff tryDecryptName + k =
      libsignalSessionCode.fnOff name := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr name := by
  simp only [Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.fnAddr_tryDecrypt_rel64_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    {callee : String} {off' : Nat} {d : BitVec 64}
    (hfn' : libsignalSessionCode.fnOff callee = off')
    (hd : ((bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) : BitVec 64) + d =
      BitVec.ofNat 64 off') :
    (tripleRatchetProgAtExt b ext).fnAddr callee =
      (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + d := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    hfn', BitVec.add_assoc, hd]

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
