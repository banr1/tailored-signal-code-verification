/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch -- shake: keep

/-!
# CLI Poll Stage P2 V1 Instantiation

Instantiates `StageP2PathAQpanCliStmt` (`stageP2PathA_qpan_cli_ok`) and `StageP2PathAQpanExtAtB`
(`stageP2PathA_qpan_ext_of_kits`, `stageP2PathA_qpan_ext_of_hkdf_init`) on Path A (`opt = none`,
`DecPkOk₀`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

private theorem cliPollSpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKit A b F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKit A b F sid σ).getEvs id ans = [] := rfl

private theorem cliPollKpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKit A b F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKit A b F kid sid kbk σ).getEvs id ans = [] := rfl

private theorem cliPollPk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKit A b F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKit A b F pid σ).getEvs id ans = [] := rfl

private theorem cliPollPk_opkOkEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKit A b F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

private theorem cliPollPk_opkOkUpdate (A : RustAlloc) (b : BitVec 64) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKit A b F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

private theorem cliPollSelf_kpEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKit A b F peer σ).kpEvs ans = [] := rfl

private theorem cliPollSelf_regIdEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKit A b F peer σ).regIdEvs ans = [] := rfl

private def pathAIkBSk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
  | .error _ => List.replicate 32 0

private def pathAIkBPk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
  | .error _ => List.replicate 32 0

private theorem pathAIkBSk_length (F : FsFiles) : (pathAIkBSk F).length = 32 := by
  dsimp only [pathAIkBSk]
  split
  · exact vecU8_length _
  · simp

private theorem pathAIkBPk_length (F : FsFiles) : (pathAIkBPk F).length = 32 := by
  dsimp only [pathAIkBPk]
  split
  · exact vecU8_length _
  · simp

private theorem pathAIkBSk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBSk F = E2E.vecU8 kp.privateKey.bytes := by
  dsimp only [pathAIkBSk]; rw [h]

private theorem pathAIkBPk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBPk F = E2E.vecU8 kp.identityKey.publicKey.bytes := by
  dsimp only [pathAIkBPk]; rw [h]

private theorem cliPollSelf_kpRel_sk_eq {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.privateKey.bytes.toList = bytesToBv8 (pathAIkBSk F) := by
  have hkpEq := cliPollSelf_kpRel_ok hrel
  dsimp only [pathAIkBSk]
  rw [hkpEq, bytesToBv8_vecU8]

private theorem cliPollSelf_kpRel_pk_eq {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (pathAIkBPk F) := by
  have hkpEq := cliPollSelf_kpRel_ok hrel
  dsimp only [pathAIkBPk]
  rw [hkpEq, bytesToBv8_vecU8]

set_option maxHeartbeats 1200000 in
/-- Path A Stage P2 V1 Instantiation (`StageP2PathAQpanCliStmt`). -/
theorem stageP2PathA_qpan_cli_ok : StageP2PathAQpanCliStmt := by
  intro X W img B S Scope y g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    himg hh hb hcoins hdecOk hScope hFok hloadNone htrust hg1 hfs1 hinv1 htr01
    hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 hpan herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdecOk
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathA img y m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0
      hpm rfl hdecOk hFok hScope) ?_
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_left fun hopkWord => ?_
  refine sepWPp_conseq_pre
    (stageP2PreAt_dup_kyberPtr img y m i w s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0) ?_
  refine SepWPp.pure_left fun hctBuf_nz => ?_
  let ikBSk : SignalPqxdh.Bytes := pathAIkBSk y.g.F
  let ikBPk : SignalPqxdh.Bytes := pathAIkBPk y.g.F
  have hikBSk_len : ikBSk.length = 32 := pathAIkBSk_length y.g.F
  have hikBPk_len : ikBPk.length = 32 := pathAIkBPk_length y.g.F
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk :=
    cliPollSelf_kpRel_sk_eq
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk :=
    cliPollSelf_kpRel_pk_eq
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  exact Kits.stageP2_v1_kits
    (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
    img (cliExterns W) himg
    (cliModelPrims_structural X W)
    hh.allocContracts
    (cliStageP2PureCallees_ok X W img himg hh)
    (cliInitBobErrOwned_ok X W img himg)
    (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
    (cliPollSelf_vtablesOk himg y.g.F y.g.peer (cliKitStk B))
    (cliPollSelf_kitOkI W B himg hh (cliReadFile_ok W img B.readFile) y.g.F y.g.peer)
    (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
    (cliPollSpk_vtablesOk himg y.g.F m.spkId (cliKitStk B))
    (cliPollSpk_kitOkImgE W himg y.g.F m.spkId B)
    (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (cliPollKpk_vtablesOk himg y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (cliPollKpk_kitOkImgE W himg y.g.F m.kpkId m.spkId y.g.msg.baseKey B)
    (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
    (cliPollPk_vtablesOk himg y.g.F w.opkWord (cliKitStk B))
    (cliPollPk_kitOkImgE W himg y.g.F w.opkWord B)
    (dpClosSubStack B)
    (stageP2V1CallStack_le_subStack (A := E2E.HooksE.A0) img.base y.g.F y.g.peer
      m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
    s0 s1 (pathAInnerFrame img y m i rngPtr sp)
    (fun sf Pf => Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf → Q sf Pf)
    (Qp := fun sf Pf => Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf → Qpan sf Pf)
    (fun sf Pf hp _ => by
      have hp' := poll_panicOomProp_of_matched emp hp
      rw [sepConj_emp] at hp'
      exact hpan sf Pf hp')
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId
    StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity
    y.g.me y.g.peer
    hb hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub
    hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt)
    hinv1.1 hinv1.2
    (cliPollStageP2_fsAt hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl
    (fun r hrel _ => cliPollSpk_wf_of_preKeysWf hdecOk.preKeysWf r hrel)
    rfl
    (fun r hrel _ => cliPollKpk_wf_of_preKeysWf hdecOk.preKeysWf r hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun id r _ hrel _ => cliPollPk_wf_of_preKeysWf hdecOk.preKeysWf r hrel)
    hkp_sk hkp_pk
    (Or.inr (distinctSid_of_decPkOk₀ hdecOk))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf hspkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_spk_err
          ((cliSpk_getRel_error_iff cliIo.rd y.g.F cliWrOk m.spkId _ _
            StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hspkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- KPK lookup error
    (fun spkRec e sf Pf _ _ hkpkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_kpk_err
          ((cliKpk_getRel_error_iff (A := E2E.HooksE.A0) cliIo.rd y.g.F cliWrOk m.kpkId
            StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hkpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- OPK lookup error
    (fun spkRec kpkRec opkId e sf Pf _ _ _ _ hopkHdr hpkErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_getEvs,
          List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_opk_err hmOpk
          ((cliPk_getRel_error_iff cliIo.rd y.g.F cliWrOk w.opkWord _ _ _ _
            StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Identity keypair lookup error
    (fun spkRec kpkRec wOpk e sf Pf _ _ _ _ _ hkpErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpNone := cliPollSelf_kpRel_err hkpErr
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inl hkpNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_kpErr_entails_decResAt_err E2E.HooksE.A0 img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- PQXDH acceptKeys rejection
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32,
          SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := by
        intro reg
        have hmap :
            (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
              (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)).map
                ofSignalPqxdhDRKey = none := by
          rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]
          exact haccNone
        exact Option.map_eq_none_iff.mp hmap
      have hmod := decPkDef_pathA_accept_none_anyReg X ⟨W.C, W.Q⟩ Scope y.g.F
        y.g.peer.val y.g.me.val y.g.msg y.g.coins hloadNone htrust hpkToE hi hk hkpOk haccNone0
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Local registration-ID lookup error
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e sf Pf
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hregErr
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          cliPollSelf_regIdEvs, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hregNone := cliPollSelf_regIdRel_err hregErr
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inr hregNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_regIdErr_entails_decResAt_err E2E.HooksE.A0 img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2
        hvregs2 hF2 hsym2 => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          cliPollSelf_regIdEvs, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil] at htr2
      have hopkUpd := cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hregOk := cliPollSelf_regIdRel_ok hregRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree hdecOk
        hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes
        hkpOk hikBSk_ok hikBPk_ok
      have hmapSome :
          (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
              ofSignalPqxdhDRKey = some drKey := by
        rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]
        exact haccSome
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp hmapSome
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdecOk.idPairDerived kp hkpOk, bytesToBv8_vecU8]
      have hst_eq := p2BobInitSessionV1_eq_pathAInitState (cliModelPrims_structural X W)
        W kp localRegId k m drKey dk0 ikBPk spkPubBytes
        (mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes)
        hikBPk_len (vecU8_length m.idPub)
        (by simp [toU8, hspkPub_len])
        (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len])
        haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq
      have hextra := sessionExtraRel_pathAInitSession W kp localRegId k m dk0 G_bob
        hG_pend hG_kyb hG_alice hG_regs
      have hmsg_reasm :
          signalMessageAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]
        exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      exact sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (p2OkPost_fold_pathA img y m i w s0 s2 sp (sp + 0xc70#64) rngPtr G_bob
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2)
        (hok s2 m i k kp localRegId dk0 G_bob y.g.msgA y.g.msgG.msg
          (preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
          hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
          hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 ⟨hF2, hsym2⟩)))

/-- Store-kit and pure-callee bundle at fixed `(B : RunBudgets)` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` for `stageP2PathA_qpan_ext_of_kits`. -/
structure StageP2PathACalleesExt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (B : RunBudgets) (ext : String → Option (State → State)) : Prop where
  pureCallees : ∀ (X : UnreachedPqxdhPrimitives),
    StageP2PureCallees4K (modelPrims X P) A P.C.F img (cliExternsWith ext)
  initBobErrOwned : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr initializeBobSessionSym)
      (Kits.initializeBobSessionErrOwned4KSpec (modelPrims X P) A img)
  selfKitOk : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentitySelfStoreKitOkI img
      (cliPollIdKit A img.base F0 peer (cliKitStk B))
      (cliPollSelfKit A img.base F0 peer (cliKitStk B))
      (cliExternsWith ext)
  spkKitOk : ∀ (F0 : FsFiles) (sid : BitVec 32),
    SignedPreKeyStoreKitOkImgE img
      (cliPollSpkKit A img.base F0 sid (cliKitStk B))
      (cliExternsWith ext)
  kpkKitOk : ∀ (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey),
    KyberPreKeyStoreKitOkImgE img
      (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B))
      (cliExternsWith ext)
  pkKitOk : ∀ (F0 : FsFiles) (pid : BitVec 32),
    PreKeyStoreKitOkImgE img
      (cliPollPkKit A img.base F0 pid (cliKitStk B))
      (cliExternsWith ext)

/-- Builds `StageP2PathACalleesExt` from `pureCallees` + `initBobErrOwned` + `hRead` at `B.readFile`,
discharging all four store kits via `Stage2V1Base`. -/
theorem StageP2PathACalleesExt.of_pure {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hPure : ∀ (X : UnreachedPqxdhPrimitives),
      StageP2PureCallees4K (modelPrims X P) A P.C.F img (cliExternsWith ext))
    (hInitErr : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr initializeBobSessionSym)
        (Kits.initializeBobSessionErrOwned4KSpec (modelPrims X P) A img)) :
    StageP2PathACalleesExt img P A B ext :=
  { pureCallees := hPure
    initBobErrOwned := hInitErr
    selfKitOk := cliPollSelf_kitOkI_of_hooksExt P.C B himg hh hRead
    spkKitOk := cliPollSpk_kitOkImgE_of_hooksExt himg hh B hRead
    kpkKitOk := cliPollKpk_kitOkImgE_of_hooksExt himg hh B hRead
    pkKitOk := cliPollPk_kitOkImgE_of_hooksExt P.C himg hh B hRead }

/-- Budget-indexed Path A Stage P2 (`+0x0868`) contract at fixed `(B : RunBudgets)` (avoiding
quantifying over unbudgeted `B.readFile < extHookStack`). -/
def StageP2PathAQpanExtAtB (img : Obj.Image) (P : PEParams) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64) (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img → img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 → DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') → Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok none →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened → FsAt (fun f => f = y.g.F) True (tripleRatchetProgAtExt img.base ext) s1 →
    ImgCallInv img s1 → s0.trace <+: s1.trace → s1.sp = sp → sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat → s1.pc = closureEntry img ext + 0x0868#64 →
    s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf Pf) →
    (∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (tripleRatchetProgAtExt img.base ext) s1 sf → sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      StageP2PathAErrExt X P A img B S Scope y s0 s1 sf sp Pf → Q sf Pf) →
    (∀ (s2 : State) (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost) (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X P)
        (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession P ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢ preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) →
      Steps (tripleRatchetProgAtExt img.base ext) s1 s2 → s2.trace = s1.trace →
      s2.pc = closureEntry img ext + 0x1778#64 → s2.status = .Running → s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true → s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 → s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 → ImgCallInv img s2 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        (TokenInit img ∗
         genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗ storesAt A y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗ protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗ storesAt A y.g.stores g1 ∗
       TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B))
      Q Qpan

/-- Statement of `Kits.stageP2_v1_kits_ext`, parameterized over
`StageP2ClosureHooks`, `StageP2PureCallees4K`, `initializeBobSessionErrOwned4KSpec`, and
`stageP2V1CallStack4K`. -/
def StageP2V1KitsExtStmt : Prop :=
  ∀ {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    StructuralPrims P →
    StageP2ClosureHooks A img.base ext →
    StageP2PureCallees4K P A F img ext →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (initializeBobSessionErrOwned4KSpec P A img) →
    ∀ (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit),
      IdentitySelfVtablesOk img ikit skit →
      IdentitySelfStoreKitOkI img ikit skit ext →
    ∀ (spkKit : SignedPreKeyStoreSpec A img.base),
      SignedPreKeyVtablesOk img spkKit →
      SignedPreKeyStoreKitOkImgE img spkKit ext →
    ∀ (kpkKit : KyberPreKeyStoreSpec A img.base),
      KyberPreKeyVtablesOk img kpkKit →
      KyberPreKeyStoreKitOkImgE img kpkKit ext →
    ∀ (pkKit : PreKeyStoreSpec A img.base),
      PreKeyVtablesOk img pkKit →
      PreKeyStoreKitOkImgE img pkKit ext →
    ∀ (stk : Nat), stageP2V1CallStack4K spkKit kpkKit pkKit skit ≤ stk →
    stageP2V1KitsAtProp P A F img ext skit spkKit kpkKit pkKit stk

/-- Instantiates `StageP2V1KitsExtStmt` via `Kits.stageP2_v1_kits_ext`. -/
theorem stageP2V1Kits_ext_inst : StageP2V1KitsExtStmt :=
  @Kits.stageP2_v1_kits_ext

private theorem stageP2V1CallStack4K_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack4K
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  dsimp only [stageP2V1CallStack4K]
  refine Nat.max_le.mpr
    ⟨(Nat.max_le.mp (stageP2CallStack4K_le_subStack b F0 peer spkId kpkId opkIdWord kbk B)).1, ?_⟩
  dsimp only [Initiator.pqxdhEntryStackExt, dpClosSubStack]
  omega

set_option maxHeartbeats 1200000 in
/-- Contract-Backed Path A Stage P2 V1 Instantiation (`StageP2PathAQpanExtAtB`) at fixed
`(B : RunBudgets)` from `StageP2V1KitsExtStmt`, `CliExternsOk P A ext`, and `StageP2PathACalleesExt`. -/
theorem stageP2PathA_qpan_ext_of_kits {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hKits : StageP2V1KitsExtStmt)
    (hOk : CliExternsOk P A ext)
    (hC : StageP2PathACalleesExt img P A B ext) :
    StageP2PathAQpanExtAtB img P A B (cliExternsWith ext) := by
  intro X S Scope y g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    himg hb hcoins hdecOk hScope hFok hloadNone htrust hg1 hfs1 hinv1 htr01
    hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 hpan herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdecOk
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathA_ext img y m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0
      hpm rfl hdecOk hFok hScope) ?_
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_left fun hopkWord => ?_
  refine sepWPp_conseq_pre
    (stageP2PreAt_dup_kyberPtr_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0) ?_
  refine SepWPp.pure_left fun hctBuf_nz => ?_
  let ikBSk : SignalPqxdh.Bytes := pathAIkBSk y.g.F
  let ikBPk : SignalPqxdh.Bytes := pathAIkBPk y.g.F
  have hikBSk_len : ikBSk.length = 32 := pathAIkBSk_length y.g.F
  have hikBPk_len : ikBPk.length = 32 := pathAIkBPk_length y.g.F
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit A img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk :=
    cliPollSelf_kpRel_sk_eq
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit A img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk :=
    cliPollSelf_kpRel_pk_eq
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  exact hKits
    (P := ofSignalPqxdhPrimitives (modelPrims X P)) (A := A) (F := P.C.F)
    img (cliExternsWith ext) himg
    (cliModelPrims_structural_ext X P)
    (cliStageP2ClosureHooks_ext img.base hOk)
    (hC.pureCallees X)
    (hC.initBobErrOwned X)
    (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
    (cliPollSelfKit A img.base y.g.F y.g.peer (cliKitStk B))
    (cliPollSelf_vtablesOk himg y.g.F y.g.peer (cliKitStk B))
    (hC.selfKitOk y.g.F y.g.peer)
    (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
    (cliPollSpk_vtablesOk himg y.g.F m.spkId (cliKitStk B))
    (hC.spkKitOk y.g.F m.spkId)
    (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (cliPollKpk_vtablesOk himg y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (hC.kpkKitOk y.g.F m.kpkId m.spkId y.g.msg.baseKey)
    (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
    (cliPollPk_vtablesOk himg y.g.F w.opkWord (cliKitStk B))
    (hC.pkKitOk y.g.F w.opkWord)
    (dpClosSubStack B)
    (stageP2V1CallStack4K_le_subStack (A := A) img.base y.g.F y.g.peer
      m.spkId m.kpkId w.opkWord y.g.msg.baseKey B)
    s0 s1 (pathAInnerFrameExt img y m i rngPtr sp)
    (fun sf Pf => Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s1 sf → Q sf Pf)
    (Qp := fun sf Pf => Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s1 sf → Qpan sf Pf)
    (fun sf Pf hp _ => by
      have hp' := poll_panicOomProp_of_matched emp hp
      rw [sepConj_emp] at hp'
      exact hpan sf Pf hp')
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId
    StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity
    y.g.me y.g.peer
    hb hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub
    hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt)
    hinv1.1 hinv1.2
    (cliPollStageP2_fsAt_ext hOk y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl
    (fun r hrel _ => cliPollSpk_wf_of_preKeysWf_ext hdecOk.preKeysWf r hrel)
    rfl
    (fun r hrel _ => cliPollKpk_wf_of_preKeysWf_ext hdecOk.preKeysWf r hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun id r _ hrel _ => cliPollPk_wf_of_preKeysWf_ext hdecOk.preKeysWf r hrel)
    hkp_sk hkp_pk
    (Or.inr (distinctSid_of_decPkOk₀ hdecOk))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf hspkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_spk_err
          ((cliSpk_getRel_error_iff cliIo.rd y.g.F cliWrOk m.spkId _ _
            StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hspkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap A img.base
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- KPK lookup error
    (fun spkRec e sf Pf _ _ hkpkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_kpk_err
          ((cliKpk_getRel_error_iff (A := A) cliIo.rd y.g.F cliWrOk m.kpkId
            StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hkpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap A img.base
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- OPK lookup error
    (fun spkRec kpkRec opkId e sf Pf _ _ _ _ hopkHdr hpkErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_getEvs,
          List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_opk_err hmOpk
          ((cliPk_getRel_error_iff cliIo.rd y.g.F cliWrOk w.opkWord _ _ _ _
            StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap A img.base
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Identity keypair lookup error
    (fun spkRec kpkRec wOpk e sf Pf _ _ _ _ _ hkpErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate A img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpNone := cliPollSelf_kpRel_err hkpErr
      have hmod := decPkDef_pathA_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inl hkpNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err_ext y.out err0
          (cliPollSelf_kpErr_entails_decResAt_err A img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- PQXDH acceptKeys rejection
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate A img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_ext hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32,
          SignalPqxdh.Model.acceptKeys (modelPrims X P)
            (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = none := by
        intro reg
        have hmap :
            (SignalPqxdh.Model.acceptKeys (modelPrims X P)
              (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m)).map
                ofSignalPqxdhDRKey = none := by
          rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]
          exact haccNone
        exact Option.map_eq_none_iff.mp hmap
      have hmod := decPkDef_pathA_accept_none_anyReg X P Scope y.g.F
        y.g.peer.val y.g.me.val y.g.msg y.g.coins hloadNone htrust hpkToE hi hk hkpOk haccNone0
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap_ext A y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Local registration-ID lookup error
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e sf Pf
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hregErr
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          cliPollSelf_regIdEvs, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate A img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hregNone := cliPollSelf_regIdRel_err hregErr
      have hmod := decPkDef_pathA_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inr hregNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err_ext y.out err0
          (cliPollSelf_regIdErr_entails_decResAt_err A img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_ext img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2
        hvregs2 hF2 hsym2 => by
      rw [cliPollSpk_getEvs, cliPollKpk_getEvs, cliPollPk_opkOkEvs, cliPollSelf_kpEvs,
          cliPollSelf_regIdEvs, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil] at htr2
      have hopkUpd := cliPollPk_opkOkUpdate A img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hregOk := cliPollSelf_regIdRel_ok hregRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_ext hdecOk
        hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes
        hkpOk hikBSk_ok hikBPk_ok
      have hmapSome :
          (SignalPqxdh.Model.acceptKeys (modelPrims X P)
            (acceptInput P ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
              ofSignalPqxdhDRKey = some drKey := by
        rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]
        exact haccSome
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp hmapSome
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf P.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdecOk.idPairDerived kp hkpOk, bytesToBv8_vecU8]
      have hst_eq := p2BobInitSessionV1_eq_pathAInitState_ext (cliModelPrims_structural_ext X P)
        P kp localRegId k m drKey dk0 ikBPk spkPubBytes
        (mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes)
        hikBPk_len (vecU8_length m.idPub)
        (by simp [toU8, hspkPub_len])
        (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len])
        haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq
      have hextra := sessionExtraRel_pathAInitSession_ext P kp localRegId k m dk0 G_bob
        hG_pend hG_kyb hG_alice hG_regs
      have hmsg_reasm :
          signalMessageAt A y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]
        exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      exact sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (p2OkPost_fold_pathA_ext img y m i w s0 s2 sp (sp + 0xc70#64) rngPtr G_bob
          (pathAInitState P ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2)
        (hok s2 m i k kp localRegId dk0 G_bob y.g.msgA y.g.msgG.msg
          (preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg)
          hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
          hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 ⟨hF2, hsym2⟩)))

/-- Direct `StageP2PathAQpanExtAtB` instantiation from `CliExternsOk P A ext`, `RunHooksExt`,
`hRead`, and the leaf HKDF/initial-state contracts (`hext`, `hexp`, `hinit`), discharging
`stageP2V1Kits_ext_inst`, all four store kits, and `cliInitBobErrOwned4K_ok_ext`. -/
theorem stageP2PathA_qpan_ext_of_hkdf_init {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (CryptoVerification.SignalSession.Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (hext : ∀ X, Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hexp : ∀ X, Initiator.PqxdhHkdfExpandMultiInfoOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hinit : CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext)) :
    StageP2PathAQpanExtAtB img P A B (cliExternsWith ext) :=
  stageP2PathA_qpan_ext_of_kits stageP2V1Kits_ext_inst hOk
    (StageP2PathACalleesExt.of_pure himg hh hRead
      (fun X => cliStageP2PureCallees4K_of_hkdf_init X himg hOk (hext X) (hexp X) hinit)
      (fun X => cliInitBobErrOwned4K_ok_ext X himg hOk))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
