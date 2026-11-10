/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2PathAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3ParseRejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Agree
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Pure Agreement & Store-Kit Helpers for Non-Canonical `PreKeySignalMessage`

Generalizes `SessMatchesPm` invariance, Path-B and Path-A `decPkDef` branch-agreement
lemmas, and relocatable store-kit mark/remove obligations from canonical `DecPkOk₀` to
`DecPkOkD3` (`pkToE? pm = some m` with arbitrary `pm.serialized`).
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
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Placed Poll Entry Unpacking & Path B Pure `decPkDef` Agreement under `DecPkOkD3` -/

/-- `SessMatchesPm s pm` is invariant under replacing `pm` by `pmOfE m pm.message` whenever
`pkToE? pm = some m`. -/
theorem sessMatchesPm_pmOfE_iff {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hpk : pkToE? pm = some m) (s : Session (List (BitVec 8))) :
    SessMatchesPm s (pmOfE m pm.message) ↔ SessMatchesPm s pm := by
  conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  exact (sessMatchesPm_with_serialized s (pmOfE m pm.message) pm.serialized).symm

/-- Path B scope-in and match unpacker under `DecPkOkD3`. -/
theorem pathB_scopeIn_and_match_d3 {A : RustAlloc} {b : BitVec 64}
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {s1 s2 s3 s4 : Nat} {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hload_rel : (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s) :
    Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩) ∧
      r = ⟨some s⟩ ∧
      Slots.scopeIn ⟨some s⟩ ∧
      SessMatchesPm s pm ∧
      pm.messageVersion = 4#8 ∧
      s.state.version = 4#32 ∧
      SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      s.state.pqRatchetState.length < 2 ^ 32 := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  obtain ⟨hloadS, hr_eq, hIn, hMatch0, _, hsver, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hf hdec0 hload_rel hcur
  have hMatch : SessMatchesPm s pm := (sessMatchesPm_pmOfE_iff hpk0 s).mp hMatch0
  have hver : pm.messageVersion = 4#8 := (pm_fields_of_pkToE hpk0 rfl).1
  exact ⟨hloadS, hr_eq, hIn, hMatch, hver, hsver, hSeeds, hRC, hPqLt⟩

theorem decPkDef_pathB_panic_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))}
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hpan : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = none := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hidk : (pmOfE m0 pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk0]
  have hmsg : (pmOfE m0 pm.message).message = pm.message := (pmOfE_fields m0 pm.message).2.2.2.2.2.2.1
  have hmatch0 : SessMatchesPm s (pmOfE m0 pm.message) := (sessMatchesPm_pmOfE_iff hpk0 s).mpr hmatch
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk0]
  exact decPkDef_pathB_panic X W Scope F peer me (pmOfE m0 pm.message) coins hdec0 hload
    (hidk ▸ htrust) hmatch0 (hidk ▸ hrem) (hmsg ▸ hver) (hmsg ▸ hpan)

theorem decPkDef_pathB_err_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {e : SignalProtocolError}
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (herr : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error e)
    (hne : e ≠ .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hidk : (pmOfE m0 pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk0]
  have hmsg : (pmOfE m0 pm.message).message = pm.message := (pmOfE_fields m0 pm.message).2.2.2.2.2.2.1
  have hmatch0 : SessMatchesPm s (pmOfE m0 pm.message) := (sessMatchesPm_pmOfE_iff hpk0 s).mpr hmatch
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk0]
  exact decPkDef_pathB_err X W Scope F peer me (pmOfE m0 pm.message) coins hdec0 hload
    (hidk ▸ htrust) hmatch0 (hidk ▸ hrem) (hmsg ▸ hver) (hmsg ▸ herr) hne

theorem decPkDef_pathB_ok_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {pt : List (BitVec 8)}
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hIn : Slots.scopeIn ⟨some s⟩)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hok : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .ok pt) :
    let st' := (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins s.state).2
    let ses' : Session (List (BitVec 8)) :=
      { s with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let g := StoresGhost.opened
    let g' : StoresGhost :=
      { g with
        identity := g.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        sessions := g.sessions.put (Cli.addressText peer.val) (E2E.Record.encodeRecord ⟨some ses'⟩) }
    decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) ∧
      Slots.scopeKit ⟨some ses'⟩ ∧
      (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hidk : (pmOfE m0 pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk0]
  have hmsg : (pmOfE m0 pm.message).message = pm.message := (pmOfE_fields m0 pm.message).2.2.2.2.2.2.1
  have hmatch0 : SessMatchesPm s (pmOfE m0 pm.message) := (sessMatchesPm_pmOfE_iff hpk0 s).mpr hmatch
  have hres := decPkDef_pathB_ok X W Scope F peer me (pmOfE m0 pm.message) coins hf hdec0 hIn hload
    (hidk ▸ htrust) hmatch0 (hidk ▸ hrem) (hmsg ▸ hver) (hmsg ▸ hok)
  dsimp only at hres ⊢
  rw [hmsg, hidk] at hres
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk0]
  exact hres

/-! ## 2. Pure Path A `decPkDef` & Placed Store Kit Agreement under `DecPkOkD3` -/

theorem decPkDef_pathA_eq_pmOfE_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {m : PreKeyMessageFields} {i : SignalMessage}
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    decPkDef X W Scope F peer me pm coins =
      decPkDef X W Scope F peer me (pmOfE m i) coins := by
  subst i
  exact decPkDef_eq_pmOfE_of_pkToE?_some hpk X W Scope F peer me coins

theorem cliPollKpk_markOk_d3_placed [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (m : PreKeyMessageFields) {pm : PreKeySignalMessage} (σ : DpKitStk) :
    (cliPollKpkKitPlaced A F0 m.kpkId m.spkId pm.baseKey σ).markOk m.kpkId m.spkId pm.baseKey :=
  ⟨rfl, rfl, rfl⟩

theorem cliPollPk_removeIdOk_of_pkToE_placed [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (m : PreKeyMessageFields) (i : SignalMessage) {pm : PreKeySignalMessage}
    (σ : DpKitStk) (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    ∀ opkId, m.opkId = some opkId →
      (cliPollPkKitPlaced A F0 (pmPreKeyId pm) σ).removeIdOk opkId := by
  intro opkId hopk
  have hpre : pm.preKeyId = m.opkId := (pm_fields_of_pkToE hpk hmsg_i).2.2.1
  dsimp only [cliPollPkKitPlaced, Poll.cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec, pmPreKeyId]
  rw [hpre, hopk]
  rfl

theorem pathA_recOk_of_tryDecrypt_d3 {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair}
    {reg : BitVec 32} {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    Slots.scopeKit ⟨some ses'⟩ ∧ (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  obtain ⟨m0, _, _, _hpk0, hdec0⟩ := hd3
  have hmsg : (pmOfE m0 pm.message).message = pm.message :=
    (pmOfE_fields m0 pm.message).2.2.2.2.2.2.1
  have hres := pathA_recOk_of_tryDecrypt (pm := pmOfE m0 pm.message) hdec0 (hmsg ▸ hver) (hmsg ▸ hok)
  dsimp only at hres ⊢
  rw [hmsg] at hres
  exact hres

theorem decPkDef_pathA_ver_ne_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
      pm.message.messageVersion.zeroExtend 32) :
    decPkDef X W Scope F peer me pm coins = some none := by
  subst i
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk]
  have hidk : (pmOfE m pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  exact decPkDef_pathA_ver_ne X W Scope F peer me (pmOfE m pm.message) coins hload hcur
    (hidk ▸ htrust) rfl hi hk hkp hreg hacc (hmsg ▸ hver)

theorem decPkDef_pathA_panic_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hpan : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = none := by
  subst i
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hm0 : m0 = m := Option.some.inj (hpk0.symm.trans hpk)
  subst m0
  have hidk : (pmOfE m pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk]
  exact decPkDef_pathA_panic X W Scope F peer me (pmOfE m pm.message) coins hdec0 hload hcur
    (hidk ▸ htrust) rfl hi hk hkp hreg hacc (hmsg ▸ hver) (hmsg ▸ hpan)

theorem decPkDef_pathA_err_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {e : SignalProtocolError}
    (hd3 : DecPkOkD3 W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (herr : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e)
    (hne : e ≠ .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  subst i
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hm0 : m0 = m := Option.some.inj (hpk0.symm.trans hpk)
  subst m0
  have hidk : (pmOfE m pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk]
  exact decPkDef_pathA_err X W Scope F peer me (pmOfE m pm.message) coins hdec0 hload hcur
    (hidk ▸ htrust) rfl hi hk hkp hreg hacc (hmsg ▸ hver) (hmsg ▸ herr) hne

end LibsignalBinary.Proofs.SignalSession.Cli.D3
