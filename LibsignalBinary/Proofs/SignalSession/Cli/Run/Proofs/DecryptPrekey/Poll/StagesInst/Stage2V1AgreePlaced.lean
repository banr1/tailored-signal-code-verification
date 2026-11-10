/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Store Canonicality and Agreement

Proves `[LibsignalPlacement]` `kyberPtr ≠ 0` extraction lemmas, pre-key store canonicality bridges
on `cliPoll*KitPlaced`, and `pathA_acceptInput_agree_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX initialStateValue)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

private theorem dup_pure_sepConj_right {φ : Prop} {A B : SepProp}
    (h : B ⊢ ⌜φ⌝ ∗ B) : A ∗ B ⊢ ⌜φ⌝ ∗ (A ∗ B) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left {φ : Prop} {A B : SepProp}
    (h : A ⊢ ⌜φ⌝ ∗ A) : A ∗ B ⊢ ⌜φ⌝ ∗ (A ∗ B) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFramePlaced`. -/
theorem pathAInnerFrame_dup_kyberPtr_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFramePlaced y m i rngPtr sp := by
  unfold pathAInnerFramePlaced
  repeat (first
    | exact dup_pure_sepConj_left (pathAMsgRemInnerAt_dup_kyberPtr y.g.msgG y.g.msgA m i)
    | refine dup_pure_sepConj_right ?_)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` to the front of `stageP2PreAtPlaced... (pathAInnerFramePlaced...)`. -/
theorem stageP2PreAt_dup_kyberPtr_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PreAtPlaced E2E.HooksE.A0
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
      (pathAInnerFramePlaced y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced E2E.HooksE.A0
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
      (pathAInnerFramePlaced y m i rngPtr sp) := by
  unfold stageP2PreAtPlaced
  repeat (first
    | exact pathAInnerFrame_dup_kyberPtr_placed y m i rngPtr sp
    | exact dup_pure_sepConj_left (pathAInnerFrame_dup_kyberPtr_placed y m i rngPtr sp)
    | refine dup_pure_sepConj_right ?_)

/-! ## 2. Placed Store Canonicality & Self-Kit Relations -/

theorem cliPollSelf_kpRel_ok_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {kp : IdentityKeyPair}
    (h : (cliPollSelfKitPlaced A F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp :=
  cliPollSelf_kpRel_ok (A := A) (b := 0#64) (peer := peer) (σ := σ) h

theorem cliPollSelf_kpRel_err_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKitPlaced A F peer σ).KpErr}
    (h : (cliPollSelfKitPlaced A F peer σ).kpRel StoresGhost.opened.identity (.error e)) :
    StoresGhost.opened.identity.keyPair cliIo.rd F = .error () :=
  cliPollSelf_kpRel_err (A := A) (b := 0#64) (peer := peer) (σ := σ) h

theorem cliPollSelf_regIdRel_ok_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {reg : BitVec 32}
    (h : (cliPollSelfKitPlaced A F peer σ).regIdRel StoresGhost.opened.identity (.ok reg)) :
    StoresGhost.opened.identity.regId cliIo.rd F = .ok reg :=
  cliPollSelf_regIdRel_ok (A := A) (b := 0#64) (peer := peer) (σ := σ) h

theorem cliPollSelf_regIdRel_err_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKitPlaced A F peer σ).RegIdErr}
    (h : (cliPollSelfKitPlaced A F peer σ).regIdRel StoresGhost.opened.identity (.error e)) :
    StoresGhost.opened.identity.regId cliIo.rd F = .error () :=
  cliPollSelf_regIdRel_err (A := A) (b := 0#64) (peer := peer) (σ := σ) h

/-- SPK canonicality (`hspk_wf`) on `cliPollSpkKitPlaced` under `PreKeyFilesWf`. -/
theorem cliPollSpk_wf_of_preKeysWf_placed {W : PEParams} [LibsignalPlacement] {F : FsFiles}
    {spkId : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : SignedPreKeyRecord)
    (hrel : (cliPollSpkKitPlaced E2E.HooksE.A0 F spkId σ).getRel StoresGhost.opened.signed spkId (.ok r)) :
    ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
      spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧
      r.signedPreKey.privateKey = spkPrivBytes :=
  cliPollSpk_wf_of_preKeysWf (b := 0#64) (σ := σ) hwf r hrel

/-- KPK canonicality (`hkpk_wf`) on `cliPollKpkKitPlaced` under `PreKeyFilesWf`. -/
theorem cliPollKpk_wf_of_preKeysWf_placed {W : PEParams} [LibsignalPlacement] {F : FsFiles}
    {kpkId spkId : BitVec 32} {kbk : PublicKey} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : KyberPreKeyRecord)
    (hrel : (cliPollKpkKitPlaced E2E.HooksE.A0 F kpkId spkId kbk σ).getRel
      StoresGhost.opened.kyber kpkId (.ok r)) :
    ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
      kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes :=
  cliPollKpk_wf_of_preKeysWf (b := 0#64) (spkId := spkId) (kbk := kbk) (σ := σ) hwf r hrel

/-- OPK canonicality (`hpk_wf`) on `cliPollPkKitPlaced` under `PreKeyFilesWf`. -/
theorem cliPollPk_wf_of_preKeysWf_placed {W : PEParams} [LibsignalPlacement] {F : FsFiles}
    {opkWord id : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : PreKeyRecord)
    (hrel : (cliPollPkKitPlaced E2E.HooksE.A0 F opkWord σ).getRel
      StoresGhost.opened.oneTime id (.ok r)) :
    ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
      opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
      r.preKey.publicKey = 5#8 :: opkPubBytes ∧
      r.preKey.privateKey = opkPrivBytes :=
  cliPollPk_wf_of_preKeysWf (b := 0#64) (opkWord := opkWord) (σ := σ) hwf r hrel

/-! ## 3. Placed Pure Path A Model Agreement -/

/-- Placed `pathA_acceptInput_agree` on `cliPoll*KitPlaced`. -/
theorem pathA_acceptInput_agree_placed {W : CliHooks} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    [LibsignalPlacement] {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)}
    {kp : IdentityKeyPair} {ikBSk ikBPk : SignalPqxdh.Bytes}
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hspkRel : (cliPollSpkKitPlaced E2E.HooksE.A0 F m.spkId σ).getRel
      StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKitPlaced E2E.HooksE.A0 F m.kpkId m.spkId pm.baseKey σ).getRel
      StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKitPlaced E2E.HooksE.A0 F opkWord σ)
      StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hikBSk : ikBSk = E2E.vecU8 kp.privateKey.bytes)
    (hikBPk : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList ∧
      spkPrivBytes = k.spkPriv.toList ∧
      (∀ reg : BitVec 32,
        mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes =
        ofSignalPqxdhAcceptKeysInput
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)) :=
  pathA_acceptInput_agree (b := 0#64) (opkWord := opkWord) (σ := σ) hdecOk hspkRel hspkPubEq
    hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkp hikBSk hikBPk

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
