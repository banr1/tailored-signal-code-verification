/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Segment 5 Packing Helpers

Relocatable `[LibsignalPlacement]` spatial frame `packRestFramePlaced` and entailment
`packed_entails_genP3PostSpatialPlaced`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.SignalSession.Coins

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-- Untouched spatial frame threaded across `pack_eq_placed_wp` / `pack_ne_placed_wp`. -/
def packRestFramePlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
  A.pool ∗
  stackAt sp chainCloneStack ∗
  memRegion (sp + 0x3e0#64) 104 ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0x98#64) ↦₆₄ 32#64) ∗
  protocolAddressAt A rem remAddrPtr ∗
  protocolAddressAt A loc locAddrPtr ∗
  signalMessageAt A msgG whisperMsgPtr msg ∗
  memRegion (sp + 0x270#64) 48 ∗
  coinsAtPlaced cur rest ∗
  FromRecordCallees.lsLogOff ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
  vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
  vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
  vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
  optSenderChainHeap A w.sender' st.senderChain ∗
  vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
    (w.chains'.zip st.receiverChains) ∗
  OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
  OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
  vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
  vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState

set_option maxHeartbeats 400000 in
theorem packed_entails_genP3PostSpatialPlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness) (w20 : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (h_loc_deser : PublicKey.deserialize recG.localIk.bytes = .ok st.localIdentity.publicKey)
    (h_rem_deser : match st.remoteIdentity with
      | none => recG.remoteIk.bytes = []
      | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : recG.pending.isSome = st.pendingPreKey)
    (h_reg_len : recG.regIds.length = 8)
    (h_loc_len : recG.localIk.bytes.length = 33)
    (h_rem_len : st.remoteIdentity.isSome → recG.remoteIk.bytes.length = 33)
    (hreg_eq : recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1)
    (hchains_len : w.chains'.length = st.receiverChains.length)
    (hsc_inl : OptSenderChainInline w.sender' st.senderChain
      (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)) :
    ((packSrcSlotsAt sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsWrittenAt sp recG st w w20) ∗
      packRestFramePlaced A sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
        recG st w rem loc msgG msg) ⊢
      genP3PostSpatialPlaced A sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg := by
  have hst := packDstSlotsWrittenAt_entails_sessionStateAt A sp recG st w w20
    h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl
  have hspill := spillSlots_entails_genP3SpillAll sp recG st w
  have hstk : memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      stackAt sp chainCloneStack = stackAt sp rootStack :=
    (P3P4.stackAt_root_eq_chainClone sp).symm
  unfold packSrcSlotsAt packRestFramePlaced genP3PostSpatialPlaced
  refine Entails.trans
    (Q := (packDstSlotsWrittenAt sp recG st w w20 ∗
            vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
            vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
              (w.chains'.zip st.receiverChains) ∗
            vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
            vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
            optSenderChainHeap A w.sender' st.senderChain ∗
            OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
            OptKybClone A recG.kyber w.kybCap' w.kybPtr') ∗
          (((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0x10#64) ↦₆₄ w.d10) ∗
            ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0x24#64) ↦₃₂ w.w24) ∗
            ((sp + 0x28#64) ↦₃₂ w.w28) ∗ ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
            ((sp + 0x30#64) ↦₃₂ w.regW0) ∗ ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
            ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
            ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
            ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
            ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
            ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
            ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
            ((sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
            genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5) ∗
          (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
            stackAt sp chainCloneStack) ∗
          (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
            protocolAddressAt A rem remAddrPtr ∗
            protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            memRegion (sp + 0x270#64) 48 ∗
            coinsAtPlaced cur rest ∗
            FromRecordCallees.lsLogOff ∗
            A.pool ∗
            memRegion (sp + 0x3e0#64) 104 ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
            ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
            ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
            ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
            ((sp + 0x3ac#64) ↦₈ 3#8)))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hstk]
  exact Entails.trans (sepConj_mono hst (sepConj_mono_left hspill)) (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4
