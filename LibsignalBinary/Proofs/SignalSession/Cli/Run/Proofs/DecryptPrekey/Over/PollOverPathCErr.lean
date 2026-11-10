/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInst
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P2 Statement and Stage P3 Error Exit

Opens the six CLI store kits under `DecPkOkD2c` and `FilesOkPeer`, defines and instantiates the
Path C CPS Stage P2 contract `StageP2OverQpanCliStmt` (`+0x0868 → +0x1778`, plus `Ext` variants),
and folds Stage P3 `Err` / `verNe` rejection exits back into `dpPollSpecState.post`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
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
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. D2(c) Opened-Stores Kit Entailment -/

theorem storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext {A : RustAlloc} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    (b : BitVec 64) (σ : DpKitStk) (storesPtr : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hfPeer : Slots.FilesOkPeer Scope F peer.val)
    (hdecOk : DecPkOkD2c W Scope F peer.val me pm)
    (pid sid kid : BitVec 32) (kbk : PublicKey) :
    storesAt A storesPtr StoresGhost.opened ⊢
      cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ
        storesPtr StoresGhost.opened := by
  have hd0 := hdecOk.toDecPkOk₀_emptyScope
  exact storesAt_entails_cliPollStoresKitsAt (A := A) b σ
    storesPtr StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hd0)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hd0 pid)
    (cliSpkInv_opened hd0 sid)
    (cliKpkInvFull_opened hd0 kid sid kbk)

theorem storesAt_opened_entails_cliPollStoresKitsAt_d2c {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    (b : BitVec 64) (σ : DpKitStk) (storesPtr : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hfPeer : Slots.FilesOkPeer Scope F peer.val)
    (hdecOk : DecPkOkD2c W Scope F peer.val me pm)
    (pid sid kid : BitVec 32) (kbk : PublicKey) :
    storesAt E2E.HooksE.A0 storesPtr StoresGhost.opened ⊢
      cliPollStoresKitsAt E2E.HooksE.A0 b F Slots.scopeKit peer pid sid kid kbk σ
        storesPtr StoresGhost.opened :=
  storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext (A := E2E.HooksE.A0) b σ storesPtr
    hsub hfPeer hdecOk pid sid kid kbk

/-! ## 2. General-`Qpan` CPS Stage P2 Statement for Overwrite Path C (`StageP2OverQpanCliStmt`) -/

/-- Outcome of the 6 Stage P2 error exits on Path C (`+0x0868 → s0.readReg64 .x30`):
all 6 CLI store/key/crypto error paths preserve `sf.trace = s1.trace`, keep the stores intact at
`StoresGhost.opened`, satisfy `decPkDefD2c = some none`, and emit a `SpeOwned` error
(`err ≠ .panic`, `err ≠ .store ()`). -/
inductive StageP2OverErr (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop where
  | reject (err : ApiError AddrVal Unit)
      (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
      (htr : sf.trace = s1.trace)
      (hmodel : decPkDefD2c X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
        some none)
      (hpost : Pf ⊢
        dpFutDoneAt y.fut ∗
        memRegion sp 3280 ∗
        decResAt E2E.HooksE.A0 y.out (.error err) ∗
        storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        logOff img ∗
        E2E.HooksE.A0.pool ∗
        stackAt sp (dpClosSubStack B) ∗
        anyHeap)

/-- General-`Qpan` CPS Stage P2 contract for Overwrite Path C (`opt = some r`,
`r.currentSession = some s_old`, `¬ SessMatchesPm s_old y.g.msg`, `DecPkOkD2c`) at `+0x0868`:
runs `promote_matching_session` (miss) + PQXDH responder handshake + `promote_state` (archiving
`Over.clearPending s_old` into `previous_sessions` at `[encSession (clearPending s_old)]`), lifting
Stage P2 OOM panics (`PanicOomProp s0`) into `Qpan` via `hpan`. -/
def StageP2OverQpanCliStmt : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True
      (tripleRatchetProgAtExt img.base (cliExterns W)) s1 →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = closureEntry img (cliExterns W) + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf Pf) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      StageP2OverErr X W img B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) →
      Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = closureEntry img (cliExterns W) + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      ImgCallInv img s2 →
      SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2
        (TokenInit img ∗
         genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt E2E.HooksE.A0 y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores g1 ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

private theorem cliPromoteMatchingMiss_ok (W : CliHooks) (img : Obj.Image) :
    Over.PromoteMatchingMissGenProp E2E.HooksE.A0 img (cliExterns W) :=
  OverP2Inst.subroutine_ok_of_spec_map
    (fun x : Over.P2PromoteMissGhost =>
      (⟨x.recPtr, x.msgVer, x.serPtr, x.serBytes, x.outPtr, x.g, x.r, x.s⟩ :
        Over.PromoteMissGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (Over.promote_matching_session_miss_ok
      (by simpa [Rust.withPanics, Rust.isPanicSymbol] using Poll.cliExterns_blackBox W))

private theorem cliPromoteOver_ok (W : CliHooks) (img : Obj.Image) :
    Over.PromoteOverGenProp E2E.HooksE.A0 img (cliExterns W) :=
  OverP2Inst.subroutine_ok_inImage_of_spec_map
    (fun x : Over.P2PromoteOverGenGhost =>
      (⟨x.recPtr, x.src, x.prevCap, x.prevPtr, x.G, x.sess, x.newBs⟩ :
        Over.PromoteOverGenGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (Over.promote_state_over_gen_ok
      (Store.SerGlueXCli.serContractsX_cli W img))

set_option maxHeartbeats 800000 in
/-- Instantiation of `StageP2OverQpanCliStmt` on `cliExterns W` via
`stageP2PathCOver_qpan_cli_ok`, `promote_matching_session_miss_ok`, and
`promote_state_over_gen_ok`. -/
theorem stageP2Over_qpan_cli_ok : StageP2OverQpanCliStmt := by
  intro X W img B S Scope y r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    himg hh hbase hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hinv1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 hpan herr hok
  have hr_scope : Slots.scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact stageP2PathCOver_qpan_cli_ok
    X W img B S Scope y g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    (cliPromoteMatchingMiss_ok W img)
    (cliPromoteOver_ok W img)
    himg hh hbase hcoins
    hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hinv1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    hpan
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

/-! ## 2b. Contract-Backed `Ext` Stage P2 Definitions & Callee Bridges -/

/-- `(P : PEParams) (A : RustAlloc)` analogue of `StageP2OverErr` for arbitrary `ext`. -/
inductive StageP2OverErrExt (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustAlloc) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop where
  | reject (err : ApiError AddrVal Unit)
      (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
      (htr : sf.trace = s1.trace)
      (hmodel : decPkDefD2c X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
        some none)
      (hpost : Pf ⊢
        dpFutDoneAt y.fut ∗
        memRegion sp 3280 ∗
        decResAt A y.out (.error err) ∗
        storesAt A y.g.stores StoresGhost.opened ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        logOff img ∗
        A.pool ∗
        stackAt sp (dpClosSubStack B) ∗
        anyHeap)

/-- Budget-indexed Stage P2 contract for Overwrite Path C at fixed `(B : RunBudgets)`. -/
def StageP2OverQpanExtAtB (img : Obj.Image) (P : PEParams) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True
      (tripleRatchetProgAtExt img.base ext) s1 →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = closureEntry img ext + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf Pf) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (tripleRatchetProgAtExt img.base ext) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      StageP2OverErrExt X P A img B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X P)
        (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession P ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) →
      Steps (tripleRatchetProgAtExt img.base ext) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = closureEntry img ext + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      ImgCallInv img s2 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        (TokenInit img ∗
         genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores g1 ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

/-- Stage-decoupled `(P : PEParams) (A : RustAlloc) (ext : ...)` CPS Stage P2 contract for
Overwrite Path C (`opt = some r`, `r.currentSession = some s_old`, `¬ SessMatchesPm s_old y.g.msg`,
`DecPkOkD2c`) at `+0x0868` on `tripleRatchetProgAtExt img.base ext`. -/
def StageP2OverQpanExtAt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True
      (tripleRatchetProgAtExt img.base ext) s1 →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = closureEntry img ext + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qpan sf Pf) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (tripleRatchetProgAtExt img.base ext) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      StageP2OverErrExt X P A img B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X P)
        (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession P ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) →
      Steps (tripleRatchetProgAtExt img.base ext) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = closureEntry img ext + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      ImgCallInv img s2 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        (TokenInit img ∗
         genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut (some r) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores g1 ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

/-- Contract-backed `promote_matching_session` miss proof (`p2PromoteMissStackExt = 17632` B) on
`cliExternsWith ext` from `hOk.blackBox`. -/
theorem cliPromoteMatchingMissExt_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderStore.promoteMatchingSessionName)
      (Over.promoteMatchingSessionMissSpecExt A) :=
  Over.promote_matching_session_miss_ok_ext32 (Slots.cliExternsWith_blackBox hOk)

/-- Contract-backed `SessionRecord::promote_state` archive proof (`Over.PromoteOverGenProp`) on
`cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliPromoteOver_ok_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Over.PromoteOverGenProp A img (cliExternsWith ext) :=
  OverP2Inst.subroutine_ok_inImage_of_spec_map
    (fun x : Over.P2PromoteOverGenGhost =>
      (⟨x.recPtr, x.src, x.prevCap, x.prevPtr, x.G, x.sess, x.newBs⟩ :
        Over.PromoteOverGenGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (Over.promote_state_over_gen_ok
      (Store.SerGlueXCli.serContractsX_ext hOk img))

set_option maxHeartbeats 800000 in
/-- Lifts `StageP2PathCOverQpanExtAt img P A ext` (`Stage2OverInst.lean`) to `StageP2OverQpanExtAt`,
packaging all 6 Stage P2 rejection branches into `decPkDefD2c = some none`. -/
theorem stageP2Over_qpan_ext_of_pathCOver {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hP2 : StageP2PathCOverQpanExtAt img P A ext) :
    StageP2OverQpanExtAt img P A ext := by
  intro X B S Scope y r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    himg hread hbase hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hinv1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 hpan herr hok
  have hr_scope : Slots.scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact hP2 X B S Scope y g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    himg hread hbase hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hinv1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    hpan
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err X P Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none X P Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

/-- Non-vacuity specialization of `StageP2OverQpanExtAt` to `(W : CliHooks)` / `E2E.HooksE.A0`. -/
theorem stageP2OverQpanExtAt_of_cli (W : CliHooks) (img : Obj.Image)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    StageP2OverQpanExtAt img ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliExterns W) :=
  stageP2Over_qpan_ext_of_pathCOver
    (stageP2PathCOverQpanExtAt_of_cli W img
      (cliPromoteMatchingMiss_ok W img) (cliPromoteOver_ok W img) hh)

/-! ## 3. Spatial Fold & Exit Packaging for Stage P3 `Err` / `verNe` on Path C -/

set_option maxHeartbeats 800000 in
theorem stageP3ErrPathC_entails_exit_ext {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer kpkId spkId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (g1 : StoresGhost)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty A img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch sp ∗
      anyHeap) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
        ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    storesAt A y.g.stores g1 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    decResAt A y.out (.error err) ∗
      storesAt A y.g.stores g1 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      A.pool ∗
      (TokenInit img ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  rw [overScratch_eq_sp538_spHighGaps sp]
  unfold stageP3ErrPostPrevEmpty genP3S5PostFrame stageP3CoroFrameAt stageP3OverStackFrameAt
  rw [hs2_sp]
  have hlog :
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) =
      logOff img := rfl
  rw [hlog]
  have hstk1 :
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack =
      stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        stackAt sp rootStack =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      stackAt sp (dpClosSubStack B) := by
    rw [hstk1, hstk2]
  have hdec := recordResultAt_err_entails_decResAt A y.out
    (SessionState.recordError .preKey e) err
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
  have hstack := stageP3Err_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      recordResultAt A y.out (.error (SessionState.recordError .preKey e)) ∗
      storesAt A y.g.stores g1 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      logOff img ∗
      A.pool ∗
      (TokenInit img ∗ coinsPost ∗ anyHeap) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
        ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗
      ((sp ↦₆₄ 0#64) ∗
        genP3S5SpillRem sp ∗
        memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
        ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
        ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
        ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗
        memRegion (sp + 0x250#64) 20 ∗
        memRegion (sp + 0x264#64) 12 ∗
        memRegion (sp + 0x270#64) 48 ∗
        memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 192 ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
        memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x3ad#64) 27 ∗
        (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((sp + 0x3d8#64) ↦₆₄ errsLen)) ∗
        memRegion (sp + 0x3e0#64) 344 ∗
        memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗
        spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)) ?_
  rw [← coro_2ac_20_eq_8_12 y.fut, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  refine sepConj_mono hdec (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono ?_ (sepConj_mono_right ?_)))))))))
  · refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  · exact Entails.trans (sepConj_mono_left hsp0) hstack

theorem stageP3ErrPathC_entails_exit (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s2 : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer kpkId spkId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (g1 : StoresGhost)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty E2E.HooksE.A0 img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame E2E.HooksE.A0 img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch sp ∗
      anyHeap) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
        ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    storesAt E2E.HooksE.A0 y.g.stores g1 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores g1 ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      (TokenInit img ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 :=
  stageP3ErrPathC_entails_exit_ext (A := E2E.HooksE.A0) img B y s0 s2
    rngPtr whisperMsgPtr whisperG preKeyMsgRem coinsPost opkId? msgVer kpkId spkId e err g1
    hs2_sp hsp_sub hmsg_fold

set_option maxHeartbeats 800000 in
theorem stageP3_exit_pathC_to_pollPost_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkId? : Option (BitVec 32))
    (kpkId spkId : BitVec 32)
    (e : SignalProtocolError)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDefD2c X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty A img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost ∗
      Over.overScratch s2.sp ∗
      anyHeap)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut opkId?)
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .decryptionFailed)
  have hsf_sp0 : sf.sp = s0.sp := by rw [hsf_sp, hs2_sp, sp_frame_sub_add]
  have hcs_full : CalleeSavedPreserved s0 sf :=
    closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
  refine ⟨?_, hsf_sp0, hcs_full⟩
  intro hsteps0f hm_f
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm_f
  rw [hs2_sp] at hm1
  have hexit := stageP3ErrPathC_entails_exit_ext img B y s0 s2 rngPtr whisperMsgPtr whisperG
    preKeyMsgRem coinsPost opkId? (y.g.msg.message.messageVersion.zeroExtend 32) kpkId spkId e err
    StoresGhost.opened hs2_sp hsp_sub hmsg_fold
  dsimp only at hexit
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm1
  have hm3 : sf.mem ⊨
      (decResAt A y.out (.error err) ∗
        storesAt A y.g.stores StoresGhost.opened ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        logOff img ∗
        A.pool ∗
        ((TokenInit img ∗ coinsPost ∗ anyHeap) ∗ stageP1VtablesAt img kit ikit) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by dsimp only [sp]; sep_frame) hm2
  have hout : slotOutTr
      (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      StoresGhost.opened (.error err) s0.trace sf.trace :=
    slotOutTr_d2c_of_reject StoresGhost.opened hS (err := err) nofun nofun hdec
  have hpost_goal := pathA_exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf StoresGhost.opened
    (.error err) ((TokenInit img ∗ coinsPost ∗ anyHeap) ∗ stageP1VtablesAt img kit ikit)
    hFs hsteps0f htr_f hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm3

theorem stageP3_exit_pathC_to_pollPost
    {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkId? : Option (BitVec 32))
    (kpkId spkId : BitVec 32)
    (e : SignalProtocolError)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDefD2c X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty E2E.HooksE.A0 img.base s0 s2 y.fut y.out e ∗
      genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost ∗
      Over.overScratch s2.sp ∗
      anyHeap)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut opkId?)
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf :=
  stageP3_exit_pathC_to_pollPost_ext (P := ⟨W.C, W.Q⟩) B S hh.fs hS stk' hneed hstk63 y
    s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem coinsPost P_f R opkId? kpkId spkId e
    hs2_sp hsp_sub hmsg_fold hdec hent hsf_sp htr_f hcs_f hvregs_f

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
