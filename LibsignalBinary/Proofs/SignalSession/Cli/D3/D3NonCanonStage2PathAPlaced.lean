/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2AuxPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Path-A Stage P2 for Non-Canonical `PreKeySignalMessage` Wire Encodings

Kit-event simplifications, PQXDH `acceptKeys` model-agreement helpers, and relocatable
Path-A Stage P2 contracts for arbitrary `pm : PreKeySignalMessage` satisfying
`pkToE? pm = some m` (`pm.serialized` unconstrained).
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
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins.Placed

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Placed Kit Event Simplifications & Shared PQXDH Agreement Helpers -/

theorem d3_cliPollSpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem d3_cliPollKpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem d3_cliPollPk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem d3_cliPollPk_opkOkEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

theorem d3_cliPollPk_opkOkUpdate_placed (A : RustAlloc) [LibsignalPlacement] (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem d3_cliPollSelf_kpEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem d3_cliPollSelf_regIdEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKitPlaced A F peer σ).regIdEvs ans = [] := rfl

def d3IkBSk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
  | .error _ => List.replicate 32 0

def d3IkBPk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
  | .error _ => List.replicate 32 0

theorem d3IkBSk_len (F : FsFiles) : (d3IkBSk F).length = 32 := by
  dsimp only [d3IkBSk]; split
  · exact Poll.vecU8_length _
  · simp

theorem d3IkBPk_len (F : FsFiles) : (d3IkBPk F).length = 32 := by
  dsimp only [d3IkBPk]; split
  · exact Poll.vecU8_length _
  · simp

theorem d3_kp_sk {F : FsFiles} (kp : IdentityKeyPair)
    (hkpEq : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    kp.privateKey.bytes.toList = bytesToBv8 (d3IkBSk F) := by
  dsimp only [d3IkBSk]; rw [hkpEq, Poll.bytesToBv8_vecU8]

theorem d3_kp_pk {F : FsFiles} (kp : IdentityKeyPair)
    (hkpEq : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (d3IkBPk F) := by
  dsimp only [d3IkBPk]; rw [hkpEq, Poll.bytesToBv8_vecU8]

theorem d3_kp_sk_placed [LibsignalPlacement] {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced E2E.HooksE.A0 F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.privateKey.bytes.toList = bytesToBv8 (d3IkBSk F) :=
  d3_kp_sk kp (cliPollSelf_kpRel_ok_placed hrel)

theorem d3_kp_pk_placed [LibsignalPlacement] {F : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced E2E.HooksE.A0 F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (d3IkBPk F) :=
  d3_kp_pk kp (cliPollSelf_kpRel_ok_placed hrel)

/-- Relocatable `[LibsignalPlacement]` Stage P2 entry unpack for Path A (`opt = none`, `DecPkOkD3`)
for arbitrary `pm.serialized`. -/
theorem preKeyMsgAt_unpack_pathA_d3_placed [LibsignalPlacement]
    (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    preKeyMsgAt E2E.HooksE.A0 g msgA pm ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, m.opkId = some id → opkWord = id⌝ ∗
        p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
          opkWord m.kpkId m.regId m.spkId ∗
        signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
        pathAMsgRemInnerAtD3 g msgA pm :=
  preKeyMsgAt_unpack_pathA_d3 g msgA m i hpk hmsg_i

/-- Relocatable `[LibsignalPlacement]` Stage P2 exit reassembly for Path A (`opt = none`,
`DecPkOkD3`) for arbitrary `pm.serialized`. -/
theorem p2MsgFields_reassemble_pathA_d3_placed [LibsignalPlacement]
    (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (opkWord : BitVec 32)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → opkWord = id) :
    p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion
      opkWord m.kpkId m.regId m.spkId ∗
    signalMessageRestVerAt E2E.HooksE.A0 g.msg msgA i ∗
    pathAMsgRemInnerAtD3 g msgA pm ⊢
      signalMessageAt E2E.HooksE.A0 g.msg msgA pm.message ∗
      ((msgA + 168#64) ↦ₛ pm.baseKey.bytes.toList) ∗
      ((msgA + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 g msgA pm :=
  p2MsgFields_reassemble_slices_d3 g msgA m i hpk hmsg_i opkWord hopk

theorem d3_acceptKeys_none_placed [LibsignalPlacement] (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost}
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields} {i : SignalMessage}
    {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)} {kp : IdentityKeyPair}
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer.val me.val (pmOfE m i))
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hspkRel : (cliPollSpkKitPlaced E2E.HooksE.A0 F m.spkId σ).getRel StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKitPlaced E2E.HooksE.A0 F m.kpkId m.spkId pm.baseKey σ).getRel
      StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKitPlaced E2E.HooksE.A0 F opkWord σ)
      StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkpRel : (cliPollSelfKitPlaced E2E.HooksE.A0 F peer σ).kpRel StoresGhost.opened.identity (.ok kp))
    (haccNone : Model.acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      (mkP2AcceptKeysInput (mkPathAHdr m) (d3IkBSk F) (d3IkBPk F) spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes) = none) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp ∧
      ∀ reg : BitVec 32,
        SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := by
  have hbk_eq : pm.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
  have hikBSk_ok : d3IkBSk F = E2E.vecU8 kp.privateKey.bytes := by dsimp only [d3IkBSk]; rw [hkpOk]
  have hikBPk_ok : d3IkBPk F = E2E.vecU8 kp.identityKey.publicKey.bytes := by dsimp only [d3IkBPk]; rw [hkpOk]
  obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
    (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
  refine ⟨k, hk, hkpOk, fun reg => ?_⟩
  have hmap :
      (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)).map
          ofSignalPqxdhDRKey = none := by
    rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]
    exact haccNone
  exact Option.map_eq_none_iff.mp hmap

theorem d3_acceptKeys_some_placed [LibsignalPlacement] (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost}
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields} {i : SignalMessage}
    {opkWord localRegId : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)} {kp : IdentityKeyPair}
    {drKey : DRKey}
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer.val me.val (pmOfE m i))
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hspkRel : (cliPollSpkKitPlaced E2E.HooksE.A0 F m.spkId σ).getRel StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKitPlaced E2E.HooksE.A0 F m.kpkId m.spkId pm.baseKey σ).getRel
      StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKitPlaced E2E.HooksE.A0 F opkWord σ)
      StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkpRel : (cliPollSelfKitPlaced E2E.HooksE.A0 F peer σ).kpRel StoresGhost.opened.identity (.ok kp))
    (haccSome : Model.acceptKeys (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      (mkP2AcceptKeysInput (mkPathAHdr m) (d3IkBSk F) (d3IkBPk F) spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey) :
    ∃ (k : ResponderPreKeySecrets) (dk0 : SignalPqxdh.DRKey),
      pkStoreKeys F m = some k ∧
      StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp ∧
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m) = some dk0 ∧
      (∀ hik hrem hspk_pub hspk_priv,
        p2BobInitSessionV1 (d3IkBPk F) (toU8 spkPubBytes)
          (mkP2AcceptKeysInput (mkPathAHdr m) (d3IkBSk F) (d3IkBPk F) spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes) drKey
          (initialStateValue W.C.F (p2BobSpqrParams drKey.pqrKey))
          hik hrem hspk_pub hspk_priv =
        pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0) := by
  have hbk_eq : pm.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
  have hikBSk_ok : d3IkBSk F = E2E.vecU8 kp.privateKey.bytes := by dsimp only [d3IkBSk]; rw [hkpOk]
  have hikBPk_ok : d3IkBPk F = E2E.vecU8 kp.identityKey.publicKey.bytes := by dsimp only [d3IkBPk]; rw [hkpOk]
  obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_placed hdec0 hspkRel hspkPubEq hspkPrivEq
    (hbk_eq ▸ hkpkRel) hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
  have hmapSome :
      (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
          ofSignalPqxdhDRKey = some drKey := by
    rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]
    exact haccSome
  obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp hmapSome
  have hikBPk_bv :
      bytesToBv8 (d3IkBPk F) = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
    rw [hikBPk_ok, hdec0.idPairDerived kp hkpOk, Poll.bytesToBv8_vecU8]
  refine ⟨k, dk0, hk, hkpOk, haccModel, fun hik hrem hspk_pub hspk_priv =>
    p2BobInitSessionV1_eq_pathAInitState (cliModelPrims_structural X W)
      W kp localRegId k m drKey dk0 (d3IkBPk F) spkPubBytes
      (mkP2AcceptKeysInput (mkPathAHdr m) (d3IkBSk F) (d3IkBPk F) spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      hik hrem hspk_pub hspk_priv
      haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3
