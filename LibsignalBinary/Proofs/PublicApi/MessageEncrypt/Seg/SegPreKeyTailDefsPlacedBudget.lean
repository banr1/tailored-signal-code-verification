/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure

/-!
# Budget-Threaded Seam Definitions for the `segPreKey` Tail

Allocation event envelopes `PreKeyFromEncryptEnv` (`+0x8b4 → exit`) and `PreKeyFromRetEnv`
(`+0x8c8 → exit`), concrete `FitsEnv` witnesses, and budget-threaded seam states on block `198`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget (otrApplyEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (otrSignalMsgGhost otrEncryptCoreEnv_phaseCreditSpec_bounded witnessIdentityKey
   witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse witnessOtr)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (kyberPayloadLen preKeyMsgNewRawEnv_phaseCreditSpec preKeySignalMessage_new_small_length_le)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey (
  PreKeyEncryptState'Placed PreKeyEncryptRetStatePlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Remaining allocation event envelope from `+0x8c8` (after `OTR::encrypt`) to return. -/
def PreKeyFromRetEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs' : List AllocEvent) : Prop :=
  PreKeyPostEncryptEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items evs'

/-- Remaining allocation event envelope from `+0x8b4` (after `kyberMap`) to return. -/
def PreKeyFromEncryptEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext (some x.loc) x.rem x.rest)
    (PreKeyFromRetEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) evs

theorem preKeyFromRetEnv_phaseCreditSpec (taken : SessionState (List (BitVec 8))) :
    PhaseCreditSpec fineCostModel
      (PreKeyFromRetEnv witnessCrypto witnessSpqrModel witnessUuidParse
        witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        witnessWithStoresGhost witnessEncSession witnessOtr taken witnessIdentityKey
        witnessPendingPreKey)
      130000 110000 110000 512 := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  have hd32 := PhaseCreditSpec.rustDealloc fineCostModel_modelHyps.freeNonInc 32 8
  have hb32 := boxAllocEnv_phaseCreditSpec (sz := 32) (by decide)
  have hsc : PhaseCreditSpec fineCostModel (StringCloneEnv witnessWithStoresGhost.rem.name)
      9541 8196 8196 1 :=
    (PhaseCreditSpec.or_of_imp (fun _ h => h)
      ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
      ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
        (req := witnessWithStoresGhost.rem.name.bytes.length) (al := 1) (by decide)).of_imp
        fun _ h => h.2)).mono (by decide) (by decide) (by decide) (by decide)
  have hscFr := hsc.seq hfr
  have hcm (otr' : OutgoingTripleRatchet (List (BitVec 8))) :
      PhaseCreditSpec fineCostModel
        (FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        70000 60000 60000 32 := by
    have hap : PhaseCreditSpec fineCostModel
        (FromApplyEnv witnessKit witnessKitEnv () witnessWithStoresGhost witnessEncSession otr' taken)
        29000 25000 25000 32 :=
      ((otrApplyEnv_phaseCreditSpec fineCostModel_modelHyps).seq
        (hb32.seq (hp16.seq (hd32.seq hfr)))).mono (by decide) (by decide) (by decide) (by decide)
    have hsv : PhaseCreditSpec fineCostModel
        (FromSaveEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        49000 42000 42000 32 :=
      ((hb32.seq (hp16.seq hd32)).seq (hfr.or hap)).mono (by decide) (by decide) (by decide) (by decide)
    exact ((hb32.seq (hp16.seq hd32)).seq (hfr.or (hscFr.or hsv))).mono
      (by decide) (by decide) (by decide) (by decide)
  let g0 := otrSignalMsgGhost witnessCrypto witnessOtr none [2#8]
    witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc) witnessWithStoresGhost.rem
  have hg0_enc : (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 160 := by
    have h := encode_protoMsg_small_length_le witnessUuidParse g0
    have hct : g0.ciphertext.length ≤ 16 := by decide
    have hpq : g0.pqRatchet.length ≤ 1 := by decide
    omega
  let res := Mut.exec (OutgoingTripleRatchet.encrypt witnessCrypto protoSignalCodec
    witnessSpqrModel.spqr witnessWithStoresGhost.ptext
    (serializeAddresses (serviceIdParse witnessUuidParse)
      witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
    witnessWithStoresGhost.rest) witnessOtr
  have hpreBody : PhaseCreditSpec fineCostModel
      (fun evs' => match res.1 with
        | .error _ => False
        | .ok sm => SeqEnv (PreKeyMsgNewRawEnv (pendingKyberPayload witnessEncSession)
            sm.serialized.length (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length)
            (fun evs'' => FreeOnlyEvs evs'' ∨
              FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
                witnessWithStoresGhost witnessEncSession res.2 taken witnessIdentityKey evs'') evs')
      130000 110000 110000 512 := by
    cases hres : res.1 with
    | error _ =>
      exact ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => False.elim h).mono
        (by decide) (by decide) (by decide) (by decide)
    | ok sm =>
      have hsm : sm.serialized.length ≤ 160 := by
        have hresEq : res =
            (match witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
             | .error e => (.error e, witnessOtr)
             | .ok next =>
               (.ok (SignalMessage.new witnessCrypto.F protoSignalCodec witnessOtr.sessionVersion
                 ((witnessOtr.senderChainKey.messageKeys witnessCrypto.F).generateKeys witnessCrypto.F none).macKey
                 (serializeAddresses (serviceIdParse witnessUuidParse)
                   witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
                 witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
                 witnessOtr.previousCounter g0.ciphertext
                 witnessOtr.localIdentityKey witnessOtr.remoteIdentityKey [2#8]),
                { witnessOtr with senderChainKey := next, pqrState := [1#8] })) := rfl
        have hres1 := congrArg Prod.fst hresEq
        rw [hres] at hres1
        cases hnk : witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
        | error e => rw [hnk] at hres1; cases hres1
        | ok next =>
          rw [hnk] at hres1; injection hres1 with hsmEq; subst hsmEq
          dsimp only [SignalMessage.new]
          rw [List.length_append, signalMessageNew_computeMac_length]
          have hser : (serializeContent protoSignalCodec witnessOtr.sessionVersion
              witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
              witnessOtr.previousCounter g0.ciphertext [2#8]
              (serializeAddresses (serviceIdParse witnessUuidParse)
                witnessWithStoresGhost.loc witnessWithStoresGhost.rem)).length =
              1 + (encode (g0.protoMsg witnessUuidParse)).length := by
            simp [serializeContent, protoSignalCodec, SignalMessageNewGhost.protoMsg,
              SignalMessageNewGhost.addresses, otrSignalMsgGhost, g0]
            omega
          omega
      have hout : (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length ≤ 512 := by
        have h := preKeySignalMessage_new_small_length_le
          res.2.sessionVersion witnessEncSession.localRegistrationId
          witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
          (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
          res.2.localIdentityKey sm
          (by decide) (by rintro _ ⟨⟩; decide) (by decide) (by rintro _ ⟨⟩; decide)
        have hky1 : kyberPayloadLen (pendingKyberPayload witnessEncSession) = 1 := rfl
        change (PreKeySignalMessage.new res.2.sessionVersion witnessEncSession.localRegistrationId
          witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
          (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
          res.2.localIdentityKey sm).serialized.length ≤ 512
        omega
      have hmono : ∀ sL oL : Nat, sL ≤ 160 → oL ≤ 512 →
          (2 * 1 + 2 * sL + 2 * oL + 47827) + 70000 ≤ 130000 ∧
          (1 + sL + oL + 41041) + 60000 ≤ 110000 ∧
          max (1 + sL + oL + 41041) (1 + sL + oL + 41041 + 60000) ≤ 110000 ∧
          max (max (max 1 33) (max sL oL)) 32 ≤ 512 := by omega
      obtain ⟨hm1, hm2, hm3, hm4⟩ := hmono sm.serialized.length
        (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length hsm hout
      exact ((preKeyMsgNewRawEnv_phaseCreditSpec fineCostModel_modelHyps
        (pendingKyberPayload witnessEncSession) sm.serialized.length
        (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length).seq
        (hfr.or (hcm res.2))).mono hm1 hm2 hm3 hm4
  unfold PreKeyFromRetEnv PreKeyPostEncryptEnv
  exact (hfr.or hpreBody).mono (by decide) (by decide) (by decide) (by decide)

/-- Non-vacuity witness showing `PreKeyFromRetEnv` fits within concrete `BudgetLimits` under `fineCostModel`. -/
theorem preKeyFromRetEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (PreKeyFromRetEnv witnessCrypto witnessSpqrModel witnessUuidParse
        witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        witnessWithStoresGhost witnessEncSession witnessOtr
        { witnessEncSession.state with pqRatchetState := [] }
        witnessIdentityKey witnessPendingPreKey) := by
  refine fitsEnv_fineCostModel_of_phaseCredit
    (preKeyFromRetEnv_phaseCreditSpec { witnessEncSession.state with pqRatchetState := [] })
    (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

/-- Non-vacuity witness showing `PreKeyFromEncryptEnv` fits within concrete `BudgetLimits` under `fineCostModel`. -/
theorem preKeyFromEncryptEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (PreKeyFromEncryptEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        witnessWithStoresGhost witnessEncSession witnessOtr
        { witnessEncSession.state with pqRatchetState := [] }
        witnessIdentityKey witnessPendingPreKey) := by
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  let g0 := otrSignalMsgGhost witnessCrypto witnessOtr none [2#8]
    witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc) witnessWithStoresGhost.rem
  have hg0_ct : g0.ciphertext.length ≤ 16 := by decide
  have hg0_pq : g0.pqRatchet.length ≤ 1 := by decide
  have hg0_enc : (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 160 := by
    have h := encode_protoMsg_small_length_le witnessUuidParse g0
    omega
  have henc : PhaseCreditSpec fineCostModel
      (OtrEncryptCoreEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
        witnessWithStoresGhost.rem witnessWithStoresGhost.rest)
      118000 101000 101000 256 := by
    refine (otrEncryptCoreEnv_phaseCreditSpec_bounded fineCostModel_modelHyps
      witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
      witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
      witnessWithStoresGhost.rem witnessWithStoresGhost.rest 256
      hp16 (by decide) (fun st' pqrKey pqrMsg hS => ?_)).mono
      (by decide) (by decide) (by decide) (by decide)
    change some ([1#8], none, [2#8]) = some (st', pqrKey, pqrMsg) at hS
    injection hS with ht; injection ht with h1 h23; injection h23 with h2 h3
    subst h1 h2 h3
    change g0.ciphertext.length ≤ 256 ∧ g0.pqRatchet.length ≤ 256 ∧
      (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 256
    exact ⟨by omega, by omega, by omega⟩
  have hSpec : PhaseCreditSpec fineCostModel
      (PreKeyFromEncryptEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        witnessWithStoresGhost witnessEncSession witnessOtr
        { witnessEncSession.state with pqRatchetState := [] }
        witnessIdentityKey witnessPendingPreKey)
      248000 211000 211000 512 :=
    (henc.seq (preKeyFromRetEnv_phaseCreditSpec
      { witnessEncSession.state with pqRatchetState := [] })).mono
      (by decide) (by decide) (by decide) (by decide)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

/-- Budget-threaded seam state at `+0x8b4`, immediately after `kyberMap` returns. -/
def PreKeyEncryptState'Budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (PreKeyFromEncryptEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) ∧
  PreKeyEncryptState'Placed
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 ctl encRecord
    x r sess otr taken pqCap pqPtr k items R0 s0 s

/-- Budget-threaded seam state at `+0x8c8`, immediately after `OTR::encrypt` returns. -/
def PreKeyEncryptRetStateBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (PreKeyFromRetEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) ∧
  PreKeyEncryptRetStatePlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S encRecord
    x r sess otr taken pqCap pqPtr k items R0 s0 s

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
