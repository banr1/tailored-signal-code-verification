/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2PathAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchAuxPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts

/-!
# New-Session Path A `decPkDef` Agreement for Non-Canonical `PreKeySignalMessage`

Generalizes Path-A `decPkDef` mark-error and accept branch-agreement lemmas from canonical
`DecPkOk₀` (`pm = pmOfE m i`) to `DecPkOkD3` (`pkToE? pm = some m` with arbitrary
`pm.serialized`).
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

/-! ## 1. Pure Path A `decPkDef` Mark/Accept Agreement under `DecPkOkD3` -/

theorem decPkDef_pathA_mark_err_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))}
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
    (hok : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).1 =
      .error ()) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  subst i
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hm0 : m0 = m := Option.some.inj (hpk0.symm.trans hpk)
  subst m0
  have hidk : (pmOfE m pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hspk : (pmOfE m pm.message).signedPreKeyId = pm.signedPreKeyId := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hbk : (pmOfE m pm.message).baseKey = pm.baseKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk]
  exact decPkDef_pathA_mark_err X W Scope F peer me (pmOfE m pm.message) coins hdec0 hload hcur
    (hidk ▸ htrust) rfl hi hk hkp hreg hacc (hmsg ▸ hver) (hmsg ▸ hok) (hspk ▸ hbk ▸ hmark)

theorem decPkDef_pathA_ok_d3 (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {opt : Option (SessionRecord (List (BitVec 8)))} {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))} {kyber' : KyberGhost}
    (hf : Slots.FilesOkPeer Scope F peer.val)
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
    (hok : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
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
  subst i
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  have hm0 : m0 = m := Option.some.inj (hpk0.symm.trans hpk)
  subst m0
  have hidk : (pmOfE m pm.message).identityKey = pm.identityKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hpre : (pmOfE m pm.message).preKeyId = pm.preKeyId := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hspk : (pmOfE m pm.message).signedPreKeyId = pm.signedPreKeyId := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hbk : (pmOfE m pm.message).baseKey = pm.baseKey := by
    conv => rhs; rw [pm_eq_pmOfE_with_serialized hpk]
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  have hres := decPkDef_pathA_ok X W Scope F peer me (pmOfE m pm.message) coins hf hdec0 hload hcur
    (hidk ▸ htrust) rfl hi hk hkp hreg hacc (hmsg ▸ hver) (hmsg ▸ hok) (hspk ▸ hbk ▸ hmark)
  dsimp only at hres ⊢
  rw [hpre, hidk] at hres
  rw [decPkDef_eq_pmOfE_of_pkToE?_some hpk]
  exact hres

end LibsignalBinary.Proofs.SignalSession.Cli.D3
