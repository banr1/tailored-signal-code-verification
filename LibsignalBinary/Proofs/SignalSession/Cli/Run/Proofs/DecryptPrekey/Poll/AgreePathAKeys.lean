/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Pure Path A Session Load, Typed Message, and Store Lookup Agreement

Proves Path A `Slots.loadRec` (`currentSession = none`) and `DecPkOk₀.typed` (`pmOfE`, `pkToE?`)
bridges, `pkStoreKeys` unfolding lemmas, and `decPkDef_pathA_lookup_err`.
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

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Path A Session Load (`currentSession = none`) & Typed `PreKeySignalMessage` -/

/-- When `cliSessionStoreSpec.loadRel` returns `.ok opt` with no `currentSession`,
`Slots.loadRec Scope F peer.val =.ok opt` and `opt.bind (·.currentSession) = none`. -/
theorem pathA_loadRec_none {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hload_rel : (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt))
    (hcur : opt.bind (·.currentSession) = none) :
    Slots.loadRec Scope F peer.val = .ok opt ∧ opt.bind (·.currentSession) = none := by
  have hloadK : (.ok opt) = Slots.loadRec Slots.scopeKit F peer.val :=
    Slots.cliSessLoadRel_eq_loadRec hinjK hload_rel
  have hloadS : Slots.loadRec Scope F peer.val = .ok opt :=
    (loadRec_scopeKit_eq hinjK hsub hf).symm.trans hloadK.symm
  exact ⟨hloadS, hcur⟩

/-- Under `DecPkOk₀`, `pm` comes from a typed `PreKeyMessageFields` `m` and parsed `SignalMessage` `i`,
and `pkToE? pm = some m`. -/
theorem pathA_pm_typed {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer me pm) :
    ∃ (m : PreKeyMessageFields) (i : SignalMessage),
      m.inner.length + 2048 < 2 ^ 32 ∧
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
      pm = pmOfE m i ∧
      pkToE? pm = some m := by
  obtain ⟨m, i, hlen, hi, rfl⟩ := hd.typed
  exact ⟨m, i, hlen, hi, rfl, pkToE?_pmOfE m i hi⟩

/-- Field projections of `pmOfE m i`. -/
theorem pmOfE_fields (m : PreKeyMessageFields) (i : SignalMessage) :
    (pmOfE m i).messageVersion = 4#8 ∧
    (pmOfE m i).registrationId = m.regId ∧
    (pmOfE m i).preKeyId = m.opkId ∧
    (pmOfE m i).signedPreKeyId = m.spkId ∧
    (pmOfE m i).baseKey = ⟨m.baseKey⟩ ∧
    (pmOfE m i).identityKey = ⟨⟨m.idPub⟩⟩ ∧
    (pmOfE m i).message = i ∧
    (pmOfE m i).kyberPayload =
      some { preKeyId := m.kpkId, ciphertext := 8#8 :: m.kyberCt.toList } := by
  rcases m with ⟨regId, opkId, spkId, kpkId, kyberCt, baseKey, idPub, inner⟩
  simp [pmOfE, E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel,
    E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.kyberBytes]

/-! ## 2. Store Lookups (`pkStoreKeys`, `keyPair`, `regId`) ↔ `decPkDef` -/

theorem pkStoreKeys_eq_none_of_spk_err {F : FsFiles} {m : PreKeyMessageFields}
    (h : getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId = .error ()) :
    pkStoreKeys F m = none := by
  unfold pkStoreKeys
  dsimp only
  rw [h]

theorem pkStoreKeys_eq_none_of_kpk_err {F : FsFiles} {m : PreKeyMessageFields}
    (h : StoresGhost.opened.kyber.get cliIo.rd F m.kpkId = .error ()) :
    pkStoreKeys F m = none := by
  unfold pkStoreKeys
  dsimp only
  rcases getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId with _ | sr
  · rfl
  · rw [h]

theorem pkStoreKeys_eq_none_of_opk_err {F : FsFiles} {m : PreKeyMessageFields} {j : BitVec 32}
    (hopk : m.opkId = some j)
    (hget : getPreKey cliIo.rd F StoresGhost.opened.oneTime j = .error ()) :
    pkStoreKeys F m = none := by
  dsimp only [pkStoreKeys]
  rcases getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId with _ | sr <;>
    rcases StoresGhost.opened.kyber.get cliIo.rd F m.kpkId with _ | kr <;> try rfl
  dsimp only
  rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;>
    rcases pkVecTag? 8 1568 kr.signedPreKey.publicKey with _ | kpub <;>
    rcases pkVecTag? 8 3168 kr.signedPreKey.privateKey with _ | ksec <;> try rfl
  dsimp only
  rw [hopk]
  dsimp only
  rw [hget]
  rfl

theorem pkStoreKeys_eq_none_of_key_decode_none {F : FsFiles} {m : PreKeyMessageFields}
    {sr : RecordCodecs.SignedPreKeyRecord} {kr : RecordCodecs.KyberPreKeyRecord}
    (hspk : getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId = .ok sr)
    (hkpk : StoresGhost.opened.kyber.get cliIo.rd F m.kpkId = .ok kr)
    (hbad : pkVec? 32 sr.signedPreKey.privateKey = none ∨
      pkVecTag? 8 1568 kr.signedPreKey.publicKey = none ∨
      pkVecTag? 8 3168 kr.signedPreKey.privateKey = none ∨
      ∃ j r, m.opkId = some j ∧
        getPreKey cliIo.rd F StoresGhost.opened.oneTime j = .ok r ∧
        pkVec? 32 r.preKey.privateKey = none) :
    pkStoreKeys F m = none := by
  dsimp only [pkStoreKeys]
  rw [hspk, hkpk]
  dsimp only
  rcases hbad with h1 | h2 | h3 | ⟨j, r, hj, hr, h4⟩
  · rw [h1]
  · rw [h2]
    rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;> rfl
  · rw [h3]
    rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;>
      rcases pkVecTag? 8 1568 kr.signedPreKey.publicKey with _ | kpub <;> rfl
  · rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;>
      rcases pkVecTag? 8 1568 kr.signedPreKey.publicKey with _ | kpub <;>
      rcases pkVecTag? 8 3168 kr.signedPreKey.privateKey with _ | ksec <;> try rfl
    dsimp only
    rw [hj]
    dsimp only
    rw [hr]
    dsimp only
    rw [h4]
    rfl

theorem pkStoreKeys_eq_some_none_opk {F : FsFiles} {m : PreKeyMessageFields}
    {sr : RecordCodecs.SignedPreKeyRecord} {kr : RecordCodecs.KyberPreKeyRecord}
    {spk : List.Vector (BitVec 8) 32}
    {kpub : List.Vector (BitVec 8) 1568} {ksec : List.Vector (BitVec 8) 3168}
    (hspk : getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId = .ok sr)
    (hkpk : StoresGhost.opened.kyber.get cliIo.rd F m.kpkId = .ok kr)
    (hspkV : pkVec? 32 sr.signedPreKey.privateKey = some spk)
    (hkpubV : pkVecTag? 8 1568 kr.signedPreKey.publicKey = some kpub)
    (hksecV : pkVecTag? 8 3168 kr.signedPreKey.privateKey = some ksec)
    (hopk : m.opkId = none) :
    pkStoreKeys F m =
      some { spkId := m.spkId, spkPriv := spk, kpkId := m.kpkId,
             kpkPub := kpub, kpkSec := ksec, opk := none } := by
  dsimp only [pkStoreKeys]
  rw [hspk, hkpk]
  dsimp only
  rw [hspkV, hkpubV, hksecV]
  dsimp only
  rw [hopk]
  rfl

theorem pkStoreKeys_eq_some_some_opk {F : FsFiles} {m : PreKeyMessageFields}
    {sr : RecordCodecs.SignedPreKeyRecord} {kr : RecordCodecs.KyberPreKeyRecord}
    {r : RecordCodecs.PreKeyRecord} {j : BitVec 32}
    {spk sk : List.Vector (BitVec 8) 32}
    {kpub : List.Vector (BitVec 8) 1568} {ksec : List.Vector (BitVec 8) 3168}
    (hspk : getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId = .ok sr)
    (hkpk : StoresGhost.opened.kyber.get cliIo.rd F m.kpkId = .ok kr)
    (hspkV : pkVec? 32 sr.signedPreKey.privateKey = some spk)
    (hkpubV : pkVecTag? 8 1568 kr.signedPreKey.publicKey = some kpub)
    (hksecV : pkVecTag? 8 3168 kr.signedPreKey.privateKey = some ksec)
    (hopk : m.opkId = some j)
    (hget : getPreKey cliIo.rd F StoresGhost.opened.oneTime j = .ok r)
    (hskV : pkVec? 32 r.preKey.privateKey = some sk) :
    pkStoreKeys F m =
      some { spkId := m.spkId, spkPriv := spk, kpkId := m.kpkId,
             kpkPub := kpub, kpkSec := ksec, opk := some (j, sk) } := by
  dsimp only [pkStoreKeys]
  rw [hspk, hkpk]
  dsimp only
  rw [hspkV, hkpubV, hksecV]
  dsimp only
  rw [hopk]
  dsimp only
  rw [hget]
  dsimp only
  rw [hskV]
  rfl

/-- Any lookup or key-decode failure on Path A causes `decPkDef` to return `some none`. -/
theorem decPkDef_pathA_lookup_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hpm : pkToE? pm = some m)
    (herr : pkStoreKeys F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd F = .error ()) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only
  rw [htrust]
  dsimp only
  rw [hcur, hpm]
  dsimp only
  rcases herr with hk | hkp | hreg
  · rw [hk]
  · rcases pkStoreKeys F m with _ | k
    · rfl
    · rw [hkp]
  · rcases pkStoreKeys F m with _ | k
    · rfl
    · rcases StoresGhost.opened.identity.keyPair cliIo.rd F with _ | kp
      · rfl
      · rw [hreg]

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
