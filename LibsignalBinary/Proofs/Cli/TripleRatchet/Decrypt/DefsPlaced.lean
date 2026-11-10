/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Checkpoint States and Seams for `try_decrypt_with_state::<Coins>`

Defines relocatable `[LibsignalPlacement]` checkpoint states, whole-function spec wrappers, and
segment seams for `try_decrypt_with_state::<Coins>` (block `433`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.Cli.CoinsTape

theorem blk433_base_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

/-- Relocatable `[LibsignalPlacement]` CLI common heap invariant across Block `433` checkpoints,
using `cliTapeAfter ctl x.cur x.rest draws` and `FromRecordCallees.lsLogOff`. -/
def cliTryDecryptCommonHeapPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (draws : Nat) (s0 : State) : SepProp :=
  protocolAddressAt A x.rem x.remA ∗
  protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  cliTapeAfter ctl x.cur x.rest draws ∗
  FromRecordCallees.lsLogOff ∗
  stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
  tryDecryptSavedRegs s0.sp s0 ∗
  A.pool

def ErrTailStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = errTailPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x26 = speTag e ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x38 ∗
    memRegion (sp + 0x140#64) 0x28 ∗
    speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
    memRegion (sp + 0x190#64) 0x3f0 ∗
    cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def LoadRatchetStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segLoadRatchetPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = x.locA ∧
  (s.readReg64 .x1).setWidth 32 = 0#32 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G x.st ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x548 ∗
    cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)

def FindChainStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segFindChainPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x0 = sp + 0x38#64 ∧
  s.readReg64 .x1 = x.msgA + 0x38#64 ∧
  s.readReg64 .x8 = sp + 0x190#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x440 ∗
    cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)

def DhStepStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDhStepPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x12 = sp + 0x2c0#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x440 ∗
    cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)

def ConsumeMsgKeyStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (ck : ChainKey) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segConsumeMsgKeyPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x12 = sp + 0x2c0#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x170 ∗
    ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes ck).drop 20) ∗
    ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes ck).take 20) ∗
    memRegion (sp + 0x2d4#64) 0x2ac ∗
    cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def PqRecvStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segPqRecvPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  ∃ (seedCap seedPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0x124 ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def DeriveKeysStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDeriveKeysPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    s.readReg64 .x8 = newPqrCap ∧
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      vecU8At A (sp + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
      spqrRecvKeyAt A (sp + 0x518#64) pqrKey ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0xa4 ∗
      memRegion (sp + 0x530#64) 0x50 ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def VerifyMacStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segVerifyMacPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      messageKeysAt (sp + 0x500#64) mks ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0xc ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x3c0 ∗
      memRegion (sp + 0x554#64) 0x2c ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def AesDecryptStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segAesDecryptPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      messageKeysAt (sp + 0x500#64) mks ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0xc ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x3c0 ∗
      memRegion (sp + 0x554#64) 0x2c ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

def ApplyRatchetStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segApplyRatchetPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64),
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      vecU8 A (sp + 0x3d0#64) pt ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0x18 ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      memRegion (sp + 0x30#64) 8 ∗
      memRegion (sp + 0x140#64) 0x290 ∗
      memRegion (sp + 0x3e8#64) 0x198 ∗
      cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R)

/-- Relocatable `[LibsignalPlacement]` tight-panic `try_decrypt_with_state` spec with
`SpqrV1.GF.Mul2U16.tokenInitPlacedAt` framed and `DistinctSid`-weakened identity guard
(raw, before `withLsCodeRoLoaded lsmpl`). -/
abbrev tryDecryptRawSpecTPTightAt [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
    (·.length < 2 ^ 32) SpqrV1.GF.Mul2U16.tokenInitPlacedAt C A ctl uuidParse S

def tryDecryptSpecTPTightAt [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl (tryDecryptRawSpecTPTightAt C A ctl uuidParse S)

def cliTryDecryptSpecPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S)

def cliTryDecryptTightSpecPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl
    (CryptoVerification.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedTightSpec C A ctl uuidParse S)

def cliTryDecryptSpecPPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidParse S)

def ErrTailTightSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S parse).1 = .error e →
    (x.model C S parse).2 = st1 →
    ErrTailStatePlaced entry A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (cliTryDecryptTightSpecPlaced C A ctl parse S) x R s0 s

def S0PSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cliTryDecryptSpecPPlaced C A ctl parse S).pre x s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A ctl x R s0)

def S1TightSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome prog (cliTryDecryptTightSpecPlaced C A ctl parse S) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps prog s s' ∧
        ∃ trG, FindChainStatePlaced entry A ctl x trG tr st1 R s0 s'

def S2SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    FindChainStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
    | .ok (some ck) =>
      reaches_pc prog (segConsumeMsgKeyPC_at entry) s
        (ConsumeMsgKeyStatePlaced entry A ctl x trG tr st1 ck 0 R s0)
    | .ok none =>
      reaches_pc prog (segDhStepPC_at entry) s
        (DhStepStatePlaced entry A ctl x trG tr st1 R s0)
    | .error e =>
      reaches_pc prog (errTailPC_at entry) s
        (ErrTailStatePlaced entry A ctl x trG tr st1 e 0 R s0)

def S3TightSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    DhStepStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R))

def S4SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State),
    ConsumeMsgKeyStatePlaced entry A ctl x trG tr st1 ck draws R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', PqRecvStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps prog s s' ∧
        ((e ≠ .panic ∧ ∃ trG',
            ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

def S5WTSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (F0 : SepProp) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    x.st.pqRatchetState.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A ctl x trG tr st1 mkg draws (F0 ∗ R) s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws (F0 ∗ R) s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((ErrTailStatePlaced entry A ctl x trG tr st1 e draws (F0 ∗ R) s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S6SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State),
    mkg.seed.length = 32 →
    DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
    reaches_pc prog (segVerifyMacPC_at entry) s
      (VerifyMacStatePlaced entry A ctl x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def S7SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    VerifyMacStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps prog s s' ∧
        (AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S8SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
    | some pt =>
      ∃ s' : State, Steps prog s s' ∧
        (ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | none =>
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
            draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S9SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (R : SepProp) (s0 s : State),
    (x.model C S parse).1 = .ok pt →
    (x.model C S parse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (cliTryDecryptSpecPlaced C A ctl parse S) x R s0 s

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
