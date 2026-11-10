/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3MatchingPathBAuxPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b2
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold

/-!
# Generalized Stage P2 for Non-Canonical `PreKeySignalMessage` Wire Encodings

Generalizes Path-A and Over-Path-C Stage P2 spatial frames and unpack/reassemble bridges
from canonical `pm = pmOfE m i` (`pm.serialized = m.bytes`) to arbitrary
`pm : PreKeySignalMessage` satisfying `pkToE? pm = some m`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

export CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  pmOfE_fields signalMessageRestVerAt signalMessageAt_eq_ver_sep
  preKeyMsgRemBaseIdKeyAt memRegion_4_eq_exists_pointsTo32
  mkPathAHdr hdrOpkIdBv?_mkPathAHdr
)
export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  opkOptTag32 hdrOpkIdBv? p2MsgFieldsAt
)

/-! ## 1. `DecPkOkD3` & Arbitrary-`serialized` `preKeyMsgAt` Unpack/Reassemble -/

/-- Whenever `Pksm.pksmParse body = some pm` and `pkToE? pm = some m`, `m.inner` (`= pm.message.serialized`)
parses under `SignalMessage.tryFrom protoSignalCodec` to `.ok pm.message`. -/
theorem tryFrom_inner_of_pksmParse_pkToE {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} (hparse : Pksm.pksmParse body = some pm) (hpk : pkToE? pm = some m) :
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok pm.message := by
  have hm_inner : m.inner = pm.message.serialized := by
    unfold pkToE? at hpk
    split at hpk
    · cases hpk
    · split at hpk
      · cases hpk
      · split at hpk
        · cases hpk
        · injection hpk with hm
          rw [← hm]
  cases body with
  | nil => simp [Pksm.pksmParse] at hparse
  | cons vb rest =>
    unfold Pksm.pksmParse at hparse
    dsimp only at hparse
    split at hparse
    · cases hparse
    · rcases hdec : Pksm.decodeProto rest with _ | mp
      · simp [hdec] at hparse
      rw [hdec] at hparse
      rcases hbk : mp.baseKey with _ | bk
      · simp [hbk] at hparse
      rcases hik : mp.identityKey with _ | ik
      · simp [hbk, hik] at hparse
      rcases hmsg : mp.message with _ | rawMsg
      · simp [hbk, hik, hmsg] at hparse
      rcases hsid : mp.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at hparse
      simp only [hbk, hik, hmsg, hsid] at hparse
      cases hkyb : Pksm.kyberOk (vb >>> 4) mp
      · simp [hkyb] at hparse
      simp only [hkyb, ↓reduceIte] at hparse
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at hparse
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at hparse
      rcases h3 : SignalMessage.tryFrom protoSignalCodec rawMsg with _ | inner
      · simp [h1, h2, h3] at hparse
      simp only [h1, h2, h3, Option.some.injEq] at hparse
      subst hparse
      have hser : inner.serialized = rawMsg := DecPkS0.tryFrom_serialized h3
      dsimp only at hm_inner ⊢
      rw [hm_inner, hser]
      exact h3

/-- Generalized `DecPkOk₀` allowing arbitrary `pm.serialized`: `pkToE? pm = some m`, `m.inner`
parses to `pm.message` with `m.inner.length + 2048 < 2 ^ 32`, and the canonical twin
`pmOfE m pm.message` satisfies `DecPkOk₀`. -/
def DecPkOkD3 (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  ∃ m : PreKeyMessageFields,
    m.inner.length + 2048 < 2 ^ 32 ∧
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok pm.message ∧
    pkToE? pm = some m ∧
    DecPkOk₀ W Scope F peer me (pmOfE m pm.message)

theorem DecPkOk₀.toDecPkOkD3 {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (h : DecPkOk₀ W Scope F peer me pm) :
    DecPkOkD3 W Scope F peer me pm := by
  obtain ⟨m, i, hm, hi, rfl⟩ := h.typed
  have hmsg : (pmOfE m i).message = i := (pmOfE_fields m i).2.2.2.2.2.2.1
  exact ⟨m, hm, hmsg ▸ hi, pkToE?_pmOfE m i hi, hmsg.symm ▸ h⟩

/-- On any `pqRecvInputs W st (wirePrekey :: body) rc`, `Pksm.pksmParse body = some pm` with
`pkToE? pm = some m`, `m.inner.length + 2048 < 2 ^ 32`, and matching-or-empty session yields
`DecPkOkD3`. -/
theorem decPkOkD3_pqRecv (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hinj : Slots.EncodeInjOn Scope) (hcov : ScopeCoversPq W Scope)
    (st : PqParty) (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m) :
    DecPkOkD3 W Scope (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  have hi := tryFrom_inner_of_pksmParse_pkToE hparse hpk
  have hfiles_eq :
      runFiles (pqRecvInputs W st (wirePrekey :: body) rc) =
      runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc) := rfl
  rw [hfiles_eq]
  exact ⟨m, hm, hi, hpk, decPkOk₀_pqRecv W Scope hinj hcov st m pm.message rc hwf hm hi hmatch⟩

theorem loadRec_false_not_some {F : FsFiles} {peer : AddrVal}
    {r : SessionRecord (List (BitVec 8))}
    (h : Slots.loadRec (fun _ => False) F peer = .ok (some r)) : False := by
  unfold Slots.loadRec at h
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
    _ | (_ | ⟨b, bs⟩)
  · simp [hget] at h
  · simp [hget] at h
  · simp only [hget] at h
    split at h
    · next hex => exact (Classical.choose_spec hex).2
    · cases h

/-- `DecPkOk₀` at `Scope := fun _ => False` holds unconditionally for any well-formed `st : PqParty`
and typed `m`, regardless of whether `st.session` matches `m`. -/
theorem decPkOk₀_pqRecv_false (W : PEParams) (st : PqParty)
    (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i) :
    DecPkOk₀ W (fun _ => False) (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) (pmOfE m i) := by
  refine ⟨⟨st.party, rfl, rfl⟩, ⟨m, i, hm, hi, rfl⟩, ?_, InitS0.distinctAcct_party st.party,
    DecPkS0.keyPairLt_pqRecv W st _ rc hwf, DecPkS0.idPairDerived_pqRecv W st _ rc,
    ⟨DecPkS0.signedWf_pqRecv W st _ rc, DecPkS0.oneTimeWf_pqRecv W st _ rc,
      DecPkS0.kyberOneTimeWf_pqRecv W st _ rc, DecPkS0.kyberLastResortWf_pqRecv W st _ rc⟩,
    DecPkS0.baseKeysLt_pqRecv W st _ rc hwf⟩
  intro r _ hload _
  exact False.elim (loadRec_false_not_some hload)

/-- `DecPkOkD3` at `Scope := fun _ => False` holds unconditionally on any
`pqRecvInputs W st (wirePrekey :: body) rc` when `Pksm.pksmParse body = some pm`,
`pkToE? pm = some m`, `m.inner.length + 2048 < 2 ^ 32`, and `PqxdhPartyInSpecDomain W st`. -/
theorem decPkOkD3_pqRecv_false (W : PEParams) (st : PqParty)
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m) (hm : m.inner.length + 2048 < 2 ^ 32) :
    DecPkOkD3 W (fun _ => False) (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  have hi := tryFrom_inner_of_pksmParse_pkToE hparse hpk
  have hfiles_eq :
      runFiles (pqRecvInputs W st (wirePrekey :: body) rc) =
      runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc) := rfl
  rw [hfiles_eq]
  exact ⟨m, hm, hi, hpk, decPkOk₀_pqRecv_false W st m pm.message rc hwf hm hi⟩

/-- Field projections of `pm` when `pkToE? pm = some m` and `pm.message = i`. -/
theorem pm_fields_of_pkToE {pm : PreKeySignalMessage} {m : PreKeyMessageFields} {i : SignalMessage}
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    pm.messageVersion = 4#8 ∧
    pm.registrationId = m.regId ∧
    pm.preKeyId = m.opkId ∧
    pm.signedPreKeyId = m.spkId ∧
    pm.baseKey = ⟨m.baseKey⟩ ∧
    pm.identityKey = ⟨⟨m.idPub⟩⟩ ∧
    pm.message = i ∧
    pm.kyberPayload = some ⟨m.kpkId, 8#8 :: m.kyberCt.toList⟩ := by
  have heq := pm_eq_pmOfE_with_serialized hpk
  rw [hmsg_i] at heq
  rw [heq]
  exact pmOfE_fields m i

/-- Remainder of `preKeyMsgRemBaseIdKeyAt` for arbitrary `pm.serialized`. -/
def pathAMsgRemInnerAtD3 (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
  E2E.HooksE.A0.live g.kyberPtr 1569 1 ∗
  memRegion (msgA + 164#64) 4 ∗
  boxU8At E2E.HooksE.A0 (msgA + 128#64) g.serPtr pm.serialized ∗
  memRegion (msgA + 241#64) 7

theorem pathAMsgRemInnerAtD3_dup_kyberPtr (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) :
    pathAMsgRemInnerAtD3 g msgA pm ⊢
      ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAtD3 g msgA pm := by
  unfold pathAMsgRemInnerAtD3
  refine Entails.pure_left fun hp => ?_
  have hne : g.kyberPtr ≠ 0#64 := hp.1
  rw [pure_sepConj_of_true hne, pure_sepConj_of_true hp]
  exact Entails.refl _

/-- Unpack `preKeyMsgAt` for any `pm` with `pkToE? pm = some m` and `pm.message = i` into
`p2MsgFieldsAt`, `signalMessageRestVerAt`, and `pathAMsgRemInnerAtD3`. -/
theorem preKeyMsgAt_unpack_pathA_d3 (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    preKeyMsgAt E2E.HooksE.A0 g msgA pm ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, m.opkId = some id → opkWord = id⌝ ∗
        p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
          opkWord m.kpkId m.regId m.spkId ∗
        signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
        pathAMsgRemInnerAtD3 g msgA pm := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pm_fields_of_pkToE hpk hmsg_i
  unfold preKeyMsgAt p2MsgFieldsAt pathAMsgRemInnerAtD3
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver,
      signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [Poll.bytesToBv8_vecU8 m.baseKey, Poll.bytesToBv8_vecU8 m.idPub,
      Poll.bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by
    simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  cases hopk_eq : m.opkId with
  | none =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_4_eq_exists_pointsTo32 (msgA + 124#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun opkWord => ?_
    refine Entails.sepExists_right opkWord (Entails.pure_right (by nofun) ?_)
    exact Entails.of_eq (by ac_rfl)
  | some id =>
    dsimp only [optU32At, opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right id (Entails.pure_right (fun _ h => Option.some.inj h) ?_)
    exact Entails.of_eq (by ac_rfl)

/-- Reassemble `p2MsgFieldsAt`, `signalMessageRestVerAt`, and `pathAMsgRemInnerAtD3` into
`signalMessageAt`, `baseKey`, `idKey`, and `preKeyMsgRemBaseIdKeyAt` for arbitrary `pm.serialized`. -/
theorem p2MsgFields_reassemble_slices_d3 (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) (opkWord : BitVec 32)
    (hopkWord : ∀ id : BitVec 32, m.opkId = some id → opkWord = id) :
    p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
      opkWord m.kpkId m.regId m.spkId ∗
    signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
    pathAMsgRemInnerAtD3 g msgA pm ⊢
      signalMessageAt E2E.HooksE.A0 g.msg msgA pm.message ∗
      ((msgA + 168#64) ↦ₛ pm.baseKey.bytes.toList) ∗
      ((msgA + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 g msgA pm := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pm_fields_of_pkToE hpk hmsg_i
  unfold p2MsgFieldsAt pathAMsgRemInnerAtD3 preKeyMsgRemBaseIdKeyAt
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver,
      signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [Poll.bytesToBv8_vecU8 m.baseKey, Poll.bytesToBv8_vecU8 m.idPub,
      Poll.bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by
    simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hoptU32 :
      ((msgA + 120#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 124#64) ↦₃₂ opkWord) ⊢
      optU32At (msgA + 120#64) m.opkId := by
    cases hopk_eq : m.opkId with
    | none =>
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
    | some id =>
      have hw := hopkWord id hopk_eq
      subst hw
      dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (((msgA + 120#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 124#64) ↦₃₂ opkWord)) ∗
    (((msgA + 112#64) ↦₈ i.messageVersion) ∗
      signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
      ((msgA + 168#64) ↦ₛ m.baseKey.toList) ∗
      ((msgA + 200#64) ↦ₛ m.idPub.toList) ∗
      boxU8At E2E.HooksE.A0 (msgA + 128#64) g.serPtr pm.serialized ∗
      (((msgA + 144#64) ↦₆₄ g.kyberPtr) ∗
        ((msgA + 152#64) ↦₆₄ 1569#64) ∗
        ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
        (E2E.HooksE.A0.live g.kyberPtr 1569 1 ∗ (g.kyberPtr ↦ₛ (8#8 :: m.kyberCt.toList))) ∗
        ((msgA + 160#64) ↦₃₂ m.kpkId) ∗
        memRegion (msgA + 164#64) 4) ∗
      ((msgA + 232#64) ↦₃₂ m.regId) ∗
      ((msgA + 236#64) ↦₃₂ m.spkId) ∗
      ((msgA + 240#64) ↦₈ 4#8) ∗
      memRegion (msgA + 241#64) 7) by simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hoptU32) ?_
  exact Entails.of_eq (by simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)

theorem pull_pure_after1_d3 {A1 Rest : SepProp} {φ : Prop} :
    A1 ∗ (⌜φ⌝ ∗ Rest) = ⌜φ⌝ ∗ (A1 ∗ Rest) := by
  ac_rfl

theorem pull_pure_msg_group_d3 {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by
  ac_rfl

theorem kpkId_shift_or_eq_append_d3 (kpkId spkId : BitVec 32) :
    ((kpkId.zeroExtend 64) <<< 32#64) ||| (spkId.zeroExtend 64) = kpkId ++ spkId := by
  bv_bits

theorem kpkId_shift_or_one_eq_append_d3 (kpkId : BitVec 32) :
    (kpkId.zeroExtend 64 <<< 32) ||| 1#64 = kpkId ++ 1#32 := by
  bv_bits

/-! ## 2. Placed Path-A Stage P2 Spatial Frame & Entry/Exit Folds (`[LibsignalPlacement]`) -/

/-- Placed spatial frame preserved untouched across `stageP2_v1_kits` on Path A for arbitrary
`y.g.msg.serialized`. -/
def pathAInnerFrameD3Placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 0x280#64) 24 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗ memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x782#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x279#64) 39 ∗
  memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗
  signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
  pathAMsgRemInnerAtD3 y.g.msgG y.g.msgA y.g.msg ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt

/-- Placed entry spatial unpack from `StageP2PathAQpanCliD3MemInvPlacedStmt` into
`stageP2PreAtPlaced ... pathAInnerFrameD3Placed`. -/
theorem stageP2_entry_unpack_pathA_d3_placed {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧
          (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        Poll.stageP2PreAtPlaced E2E.HooksE.A0
          (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFrameD3Placed y i rngPtr sp) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq]
  dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) =
      ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ E2E.HooksE.A0.pool ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_d3 y.g.msgG y.g.msgA m i hpk hmsg_i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pathAMsgRemInnerAtD3_dup_kyberPtr y.g.msgG y.g.msgA y.g.msg)))) ?_
  rw [pull_pure_msg_group_d3]
  refine Entails.pure_left fun hctBuf_nz => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := E2E.HooksE.A0) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0)
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdec0 opkWord)
    (cliSpkInv_opened hdec0 m.spkId)
    (cliKpkInvFull_opened hdec0 m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
    (Entails.pure_right ⟨hctBuf_nz, hopkWord⟩ ?_)
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, Poll.stageP2PreAtPlaced, pathAInnerFrameD3Placed]
    rw [hdrEq]
    ac_rfl)

set_option maxHeartbeats 800000 in
/-- Placed full Stage P2 error-exit spatial fold into `StageP2PathAErrPlaced`'s postcondition for
arbitrary `y.g.msg.serialized`. -/
theorem p2ErrFrame_fold_pathA_d3_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt E2E.HooksE.A0 y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores StoresGhost.opened.identity ∗
    Poll.p2ErrFrameAtPlaced E2E.HooksE.A0 s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed y i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq]
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0) 0#64
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  have hmsgFold :
      p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 y.g.msgG y.g.msgA y.g.msg ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg := by
    refine Entails.trans (p2MsgFields_reassemble_slices_d3 y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk) ?_
    rw [preKeyMsgAt_eq_base_idKey_sep]
    exact Entails.of_eq (by ac_rfl)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := p2_stack_err_fold sp fp s0 hfp
  have hany : coinsInstalledPlaced y.g.coinsP y.g.coins ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ anyHeap ⊢ anyHeap :=
    entails_anyHeap _
  dsimp only [Poll.p2ErrFrameAtPlaced, pathAInnerFrameD3Placed]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0xe0#64) 368 ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      memRegion (y.fut + 0x298#64) 20 ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗
      memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x80#64) 88 ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
      memRegion (sp + 0x3b0#64) 48 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      spMidGapsAt sp ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    decResAt E2E.HooksE.A0 y.out (.error err) ∗
    cliPollStoresKitsAt E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer
      w.opkWord m.spkId m.kpkId (pmOfE m i).baseKey (cliKitStk B) y.g.stores StoresGhost.opened ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 y.g.msgG y.g.msgA y.g.msg) ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    FromRecordCallees.lsLogOff ∗
    E2E.HooksE.A0.pool ∗
    stackAt sp (dpClosSubStack B) ∗
    (coinsInstalledPlaced y.g.coinsP y.g.coins ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ anyHeap)
    by exact Entails.of_eq (by dsimp only [cliPollStoresKitsAt]; ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right
    (sepConj_mono hstores (sepConj_mono hmsgFold
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hany)))))))))

/-- Placed coroutine sub-fold shared between `p2OkPost_fold_pathA_d3_placed` and
`p2OverOkPost_fold_pathCOver_d3_placed`. -/
theorem p2_coro_ok_with_opk_d3_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (w : PathAEntryWords) (rngPtr : BitVec 64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    ((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
    processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
    ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
    ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
    coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
    cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
    memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
    ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
    processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
    processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
    ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
    ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
    memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
    memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
    memRegion (y.fut + 0x4f3#64) 5 ∗
    p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6 ⊢
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
      (coroOpkIdAtP4 y.fut m.opkId)
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) := by
  have hopkSlot := p2_coro_opk_slot_fold y.fut m.opkId w.opkWord hopk
  have hcoro := p2_coro_ok_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
    (coroOpkIdAtP4 y.fut m.opkId)
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId))
  exact Entails.trans (sepConj_mono_left hopkSlot) (Entails.trans (by sep_frame) hcoro)

/-- Stack sub-fold shared between `p2OkPost_fold_pathA_d3_placed` and
`p2OverOkPost_fold_pathCOver_d3_placed`. -/
theorem p2_stk_ok_fold_d3_placed (sp fp fut msgA peerA : BitVec 64) (spkId : BitVec 32)
    (hfp : fp = sp + 0xc70#64) :
    (cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp) ∗
    (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
    ((sp + 0x90#64) ↦₆₄ (msgA + 0xc8#64)) ∗ ((sp + 0x98#64) ↦₆₄ (fut + 0x398#64)) ∗
    ((sp + 0xa8#64) ↦₆₄ peerA) ∗ memRegion (sp + 0xbc#64) 4 ∗
    ((sp + 0xd0#64) ↦₆₄ spkId.zeroExtend 64) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
    memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
    spMidGapsAt sp ∗
    ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗ ((sp + 0x3b8#64) ↦₆₄ msgA) ∗
    ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
    memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x538#64) 24 ⊢
    genP3SpillAll sp ∗ memRegion (sp + 0x3e0#64) 104 ∗
    memRegion (sp + 0xa90#64) 344 ∗ stageP3StackFrameAt sp (msgA + 0xc8#64) peerA := by
  have h550 :
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp =
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
    rw [← sp_550_1824_split_p2v1 sp fp hfp, sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [h550]
  exact Entails.trans (by sep_frame) (stack_match_fold sp fut msgA peerA (spkId.zeroExtend 64))

set_option maxHeartbeats 800000 in
/-- Placed full Stage P2 `+0x1778` normal-exit spatial fold into `hok`'s precondition for
arbitrary `y.g.msg.serialized`. -/
theorem p2OkPost_fold_pathA_d3_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    Poll.p2OkPostAtPlaced E2E.HooksE.A0
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed y i rngPtr sp) ⊢
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      genP3PrePlaced E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hmsgSlices := p2MsgFields_reassemble_slices_d3 y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk
  rw [hbk_eq, hmsg_i] at hmsgSlices ⊢
  unfold genP3PrePlaced
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  dsimp only [Poll.p2OkPostAtPlaced, pathAInnerFrameD3Placed]
  unfold genP3CallFramePlaced stageP3Sub5ExtraPre
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, kpkId_shift_or_one_eq_append_d3 m.kpkId]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
        stackAt sp FromRecordChainClone.chainCloneStack) := by
    rw [P3P4.stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        Poll.stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 = memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp, memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  have hc := Slots.coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0) 0#64
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  rw [hstkSub, h3e0]
  refine Entails.trans (show _ ⊢
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    (((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗ memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗ ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x538#64) 24) ∗
    ((cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 y.g.msgG y.g.msgA y.g.msg) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) recG st_bob ∗
      E2E.HooksE.A0.pool ∗ stackAt sp FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗ ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗ FromRecordCallees.lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗ ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗ ((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0xe8#64) ↦₆₄ 8#64) ∗ ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono (p2_coro_ok_with_opk_d3_placed y m w rngPtr hopk)
    (sepConj_mono (p2_stk_ok_fold_d3_placed sp fp y.fut y.g.msgA y.g.peerA m.spkId hfp)
      (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

/-- `P2SessMatchesMsg` mismatch for any `pm` with `pkToE? pm = some m` and `¬ SessMatchesPm sess pm`. -/
theorem p2Over_not_sessMatchesMsg_d3 (sess : Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hnot : ¬ DecPkS0.SessMatchesPm sess pm) :
    ¬ Over.P2SessMatchesMsg sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) := by
  have hnot' : ¬ DecPkS0.SessMatchesPm sess (pmOfE m i) := by
    intro hm'; apply hnot
    rw [pm_eq_pmOfE_with_serialized hpk, hmsg_i]
    exact (sessMatchesPm_with_serialized sess (pmOfE m i) pm.serialized).mpr hm'
  exact OverP2Inst.p2Over_not_sessMatchesMsg sess (pmOfE m i) m i rfl hnot'

end LibsignalBinary.Proofs.SignalSession.Cli.D3
