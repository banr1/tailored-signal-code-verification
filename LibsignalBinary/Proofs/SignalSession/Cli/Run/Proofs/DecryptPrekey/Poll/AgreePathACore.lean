/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Pure Path A `acceptKeys`, `StageP3Gen`, and `StageP4` Commit Agreement

Proves agreement between Path A `Model.acceptKeys` / `StageP3Gen` (`ver_ne`, `panic`, `err`) and
`decPkDef`, together with initial recipient `Slots.scopeIn`, `RecOk` preservation, `KyberGhost.mark`
bridges, and `decPkDef_pathA_ok` + `StoresWrOk cliWrOk`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Path A `acceptKeys` & `StageP3Gen` Decryption Branch Agreement -/

theorem pkStoreKeys_ids_eq {F : FsFiles} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    (hk : pkStoreKeys F m = some k) :
    k.spkId = m.spkId ∧ k.kpkId = m.kpkId := by
  unfold pkStoreKeys at hk
  dsimp only at hk
  split at hk
  · split at hk
    · rw [Option.map_eq_some_iff] at hk
      obtain ⟨_, _, rfl⟩ := hk
      exact ⟨rfl, rfl⟩
    · cases hk
  · cases hk

/-- Initial recipient `SessionState` constructed after `Model.acceptKeys = some dk`. -/
def pathAInitState (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) : SessionState (List (BitVec 8)) :=
  initializeRecipientSession (pqxdhSpqrSession W)
    ⟨(keyPairOf W.C me.idPriv).publicKey⟩
    ⟨⟨m.idPub⟩⟩
    (keyPairOf W.C k.spkPriv)
    (HKDF.bytesToKey32 (ofU8 dk.rootKey))
    (HKDF.bytesToKey32 (ofU8 dk.chainKey))
    (HKDF.bytesToKey32 (ofU8 dk.pqrKey))

theorem recvPrekeyState_of_accept_none (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hids : k.spkId = m.spkId ∧ k.kpkId = m.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) = none) :
    recvPrekeyState X W P me k m rc = some none := by
  unfold recvPrekeyState
  rw [hi]
  dsimp only
  have hnot : ¬ (m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId) := by
    rintro (h1 | h2)
    · exact h1 hids.1.symm
    · exact h2 hids.2.symm
  rw [ite_neg hnot, hacc]

theorem recvPrekeyState_of_accept_some (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256)
    {dk : SignalPqxdh.DRKey}
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hids : k.spkId = m.spkId ∧ k.kpkId = m.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) = some dk) :
    recvPrekeyState X W P me k m rc =
      match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P)
          i .preKey rc (pathAInitState W me k m dk) with
      | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
      | (.error .panic, _) => none
      | (.error _, _) => some none := by
  unfold recvPrekeyState pathAInitState
  rw [hi]
  dsimp only
  have hnot : ¬ (m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId) := by
    rintro (h1 | h2)
    · exact h1 hids.1.symm
    · exact h2 hids.2.symm
  rw [ite_neg hnot, hacc]
  rfl

theorem decPkDef_pathA_accept_none (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hpm : pkToE? pm = some m)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = none) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_none X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]

theorem decPkDef_pathA_ver_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
      pm.message.messageVersion.zeroExtend 32) :
    decPkDef X W Scope F peer me pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : pm.message = i := hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg] at hver
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m i
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc,
    tryDecryptFromRecord_preKey_ver_ne hver]

theorem decPkDef_pathA_panic (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hpan : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at hpan
  dsimp only at hpan
  subst hpan
  rfl

theorem decPkDef_pathA_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {e : SignalProtocolError}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (herr : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e)
    (hne : e ≠ .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at herr
  dsimp only at herr
  subst herr
  dsimp only
  have hne' : SessionState.recordError .preKey e ≠ .panic :=
    mt (recordError_eq_panic_iff .preKey e).mp hne
  cases hr : SessionState.recordError .preKey e <;> first | exact absurd hr hne' | rfl

/-! ## 2. Initial Recipient `scopeIn`, `RecOk` Preservation, & `StageP4` Commit Agreement -/

theorem spqrV1Init_pqInV1 (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    Slots.PqValid.PqInV1 (CryptoVerification.LibsignalSpqrV1.spqrV1Init F K dir k) := by
  refine ⟨CryptoVerification.SpqrV1.Top.StateSize.validState_spqrV1Init F K dir k, ?_⟩
  unfold CryptoVerification.LibsignalSpqrV1.spqrV1Init
    CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [CryptoVerification.LibsignalSpqrV1.initialState,
      CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams] at hst
    rcases hi : CryptoVerification.LibsignalSpqrV1.initInner
        (CryptoVerification.LibsignalSpqrV1.spqrDeps F K)
        CryptoVerification.LibsignalSpqrV1.Version.v1
        (CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection dir)
        (HMAC.keyToBytes32 k) with p | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst
      subst hst'
      have hin := CryptoVerification.SpqrV1.Top.StateSize.initInner_spqrDeps_raw_le hi
      have hk : (HMAC.keyToBytes32 k).length = 32 := by simp [HMAC.keyToBytes32]
      refine Nat.lt_of_le_of_lt
        (CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState _) ?_
      simp only [CryptoVerification.SpqrV1.Top.StateSize.rawPqState,
        CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_none,
        CryptoVerification.SpqrV1.Top.StateSize.rawVN, hk]
      omega
  · decide

/-- Newly initialized recipient `Session` before the inner `PreKey` decryption step. -/
def pathAInitSession (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) : Session (List (BitVec 8)) :=
  { state := pathAInitState W me k m dk
    pendingPreKey := none
    pendingKyberPreKey := none
    localRegistrationId := me.regId
    remoteRegistrationId := m.regId
    aliceBaseKey := djbKey m.baseKey }

theorem pathAInitSession_scopeIn (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) :
    let ses0 := pathAInitSession W me k m dk
    Slots.scopeIn ⟨some ses0⟩ ∧
      ses0.state.version = 4#32 ∧
      SeedsLen32 ses0.state ∧
      ses0.state.receiverChains.length < 2 ^ 32 ∧
      ses0.state.pqRatchetState.length < 2 ^ 32 := by
  let ses0 := pathAInitSession W me k m dk
  have hseeds0 : SeedsLen32 ses0.state := by
    simp [ses0, pathAInitSession, pathAInitState, initializeRecipientSession,
      SessionState.new, SessionState.setSenderChain, SeedsLen32]
  have hrc_le : ses0.state.receiverChains.length ≤ maxReceiverChains := by
    simp [ses0, pathAInitSession, pathAInitState, initializeRecipientSession,
      SessionState.new, SessionState.setSenderChain]
  have hrc_lt : ses0.state.receiverChains.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hrc_le (by decide)
  have hrep0 : CryptoVerification.E2E.Reach.SessRepr ses0.state :=
    CryptoVerification.E2E.Reach.setSenderChain_sessRepr _ _ _
      (CryptoVerification.E2E.Reach.clampScalar_idem k.spkPriv)
      (CryptoVerification.E2E.Reach.new_sessRepr _ _ _ _ _)
  have hpqIn : Slots.PqValid.PqInV1 ses0.state.pqRatchetState :=
    spqrV1Init_pqInV1 W.C.F W.Q.K .b2a (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  have hpqLt : ses0.state.pqRatchetState.length < 2 ^ 32 :=
    Nat.lt_trans hpqIn.2 (by decide)
  have hwf0 : ses0.Wf := by
    unfold Session.Wf; rfl
  have habk : ses0.aliceBaseKey.length = 33 := by
    simp [ses0, pathAInitSession, djbKey]
  have hscP : CryptoVerification.E2E.RecordX.SessionScopeP ses0 :=
    ⟨hrc_le, nofun, nofun, Or.inr habk⟩
  have hIn : Slots.scopeIn ⟨some ses0⟩ := by
    refine ⟨⟨?_, ?_, ?_⟩, ses0, rfl, hscP⟩
    · intro s hs; injection hs with hs; subst hs
      exact ⟨hseeds0, hrc_lt, nofun⟩
    · intro s hs; injection hs with hs; subst hs
      exact hpqIn
    · intro s hs; injection hs with hs; subst hs
      refine ⟨hrep0.1, hrep0.2, hwf0, ?_⟩
      change ses0.aliceBaseKey.length < _
      rw [habk]
      decide
  exact ⟨hIn, rfl, hseeds0, hrc_lt, hpqLt⟩

theorem cliKpk_markRel_error_to_mark {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {kid ksid : BitVec 32} {kbk : PublicKey}
    {s1 s2 s3 s4 : Nat} {g : KyberGhost} {e : CliKpkMarkErr}
    (hrel : (cliKpkStoreSpecFull A b cliIo.rd F cliWrOk kid ksid kbk s1 s2 s3 s4).markRel
      g kid ksid kbk (.error e)) :
    (g.mark cliIo.rd F kid ksid kbk).1 = .error () := by
  change (kpkMarkOf cliIo.rd F g kid ksid kbk).1 = e.ans at hrel
  rw [kyberMark_eq, hrel]
  dsimp only
  have hne := e.ne_ok
  cases h : e.ans <;> rw [h] at hne
  · exact absurd rfl hne
  · rfl
  · rfl
  · rfl

theorem cliKpk_markRel_ok_to_mark {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {kid ksid : BitVec 32} {kbk : PublicKey}
    {s1 s2 s3 s4 : Nat} {g : KyberGhost}
    (hrel : (cliKpkStoreSpecFull A b cliIo.rd F cliWrOk kid ksid kbk s1 s2 s3 s4).markRel
      g kid ksid kbk (.ok ())) :
    g.mark cliIo.rd F kid ksid kbk =
      (.ok (), (kpkMarkOf cliIo.rd F g kid ksid kbk).2) := by
  change (kpkMarkOf cliIo.rd F g kid ksid kbk).1 = .ok at hrel
  rw [kyberMark_eq, hrel]
  rfl

theorem decPkDef_pathA_mark_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).1 =
      .error ()) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m i
    (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  rw [hmsg, tryDecryptFromRecord_preKey_ver_eq hd hver, hok]
  dsimp only
  rcases hmk : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
    ⟨r_mk, kyber'⟩
  rw [hmk] at hmark
  dsimp only at hmark
  subst hmark
  rfl

theorem decPkDef_pathA_ok (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))} {kyber' : KyberGhost}
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpm_eq : pm = pmOfE m i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey =
      (.ok (), kyber')) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let oneTime' := match pm.preKeyId with
      | none => StoresGhost.opened.oneTime
      | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
    let g' : StoresGhost :=
      { StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := oneTime'
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (E2E.Record.encodeRecord ⟨some ses'⟩) }
    Slots.scopeKit ⟨some ses'⟩ ∧
      (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 ∧
      E2E.Record.encodeRecord ⟨some ses'⟩ =
        encodeRecordUnderExtras (fun _ => responderRecordExtras meE m) ⟨initParty peer.val, st', 1, [1]⟩ ∧
      decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) := by
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  have hpm : pkToE? pm = some m := hpm_eq ▸ pkToE?_pmOfE m i hi
  have hmsg : i = pm.message := (hpm_eq ▸ (pmOfE_fields m i).2.2.2.2.2.2.1).symm
  have htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) (pathAInitState W meE k m dk) = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq hd hver, hok]
  have hIn := (pathAInitSession_scopeIn W meE k m dk).1
  obtain ⟨hKit', hLen'⟩ := tryDecryptFromRecord_preKey_recOk_of_scopeIn hIn htry
  have hPendFalse : st'.pendingPreKey = false :=
    (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) htry).1
  have hEncEq : E2E.Record.encodeRecord
      ⟨some { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩ =
      encodeRecordUnderExtras (fun _ => responderRecordExtras meE m) ⟨initParty peer.val, st', 1, [1]⟩ :=
    DecPkS0.encodeRecord_cleared_eq_encodeRecordX (responderRecordExtras meE m)
      ⟨initParty peer.val, pathAInitState W meE k m dk, 1, [1]⟩ st' hPendFalse
  have hDec : decPkDef X W Scope F peer.val me.val pm coins =
      some (some ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (E2E.Record.encodeRecord
            ⟨some { pathAInitSession W meE k m dk with
                    state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩) }, pt)) := by
    dsimp only [decPkDef]
    rw [hload]
    dsimp only
    rw [htrust]
    dsimp only
    rw [hcur, hpm]
    dsimp only
    rw [hk, hkp, hreg]
    dsimp only
    rw [recvPrekeyState_of_accept_some X W (initParty peer.val) meE k m i
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
    rw [hmsg, htry]
    dsimp only
    rw [hmark, ← hEncEq]
    rfl
  have hky' : kyber' =
      (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).2 := by
    rw [hmark]
  have hWr : ∀ pw ∈ ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (E2E.Record.encodeRecord
            ⟨some { pathAInitSession W meE k m dk with
                    state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩) } :
        StoresGhost).writes, cliWrOk pw.1 := by
    rw [hky']
    exact storesWrOk_pathA hf
  exact ⟨hKit', hLen', hEncEq, hDec, hWr⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
