/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# CLI Poll Stage P2 Over-Path (`Path C`) Instantiation

Defines `StageP2PathCOverModelRej`, `StageP2PathCOverErr`, and `StageP2PathCOverQpanCliStmt` (plus
`Ext` generalizations) and proves `stageP2PathCOver_qpan_cli_ok` by instantiating
`Over.stageP2_over_v1_kits` at the CLI Poll store kits when `¬ DecPkS0.SessMatchesPm sess y.g.msg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

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
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
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
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Stage P2 Over-Path (`Path C`) Error & CPS Statement -/

/-- Pure model-rejection witness discharged on all 6 Stage P2 error arms on Path C (`Over`):
either a store-key / identity lookup fails (`pkStoreKeys = none ∨ keyPair = .error () ∨ regId = .error ()`)
or PQXDH `acceptKeys` rejects for every local registration ID. -/
def StageP2PathCOverModelRej (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {B : RunBudgets} {S : RunSem} {img : Obj.Image}
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S)) : Prop :=
  ∃ (m : PreKeyMessageFields) (i : SignalMessage),
    pkToE? y.g.msg = some m ∧
    SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i ∧
    y.g.msg = pmOfE m i ∧
    ((pkStoreKeys y.g.F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
     (∃ (k : ResponderPreKeySecrets) (kp : RecordCodecs.IdentityKeyPair),
       pkStoreKeys y.g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
       ∀ reg : BitVec 32,
         SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
           (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))

/-- Exit postcondition of all 6 Stage P2 store-error and PQXDH-rejection arms on Path C (`Over`). -/
def StageP2PathCOverErr (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ err : ApiError AddrVal Unit,
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRej X W y ∧
    (Pf ⊢
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

/-- General-`Qpan` CPS Stage P2 contract for Path C (`opt = some r`, `r.currentSession = some sess`,
`¬ DecPkS0.SessMatchesPm sess y.g.msg`) at `+0x0868`, parameterized cleanly over the two
`SessionRecord` promotion callees (`Over.PromoteMatchingMissGenProp` and `Over.PromoteOverGenProp`). -/
def StageP2PathCOverQpanCliStmt : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Over.PromoteMatchingMissGenProp E2E.HooksE.A0 img (cliExterns W) →
    Over.PromoteOverGenProp E2E.HooksE.A0 img (cliExterns W) →
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    Slots.scopeIn r →
    ¬ DecPkS0.SessMatchesPm sess y.g.msg →
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
      StageP2PathCOverErr X W img B S y s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
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
           G_bob (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         p2StageP3Sub5ExtraPrePrev1 E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
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

/-! ## 2. Kit Event Simplifications & Proof of `stageP2PathCOver_qpan_cli_ok` -/

private theorem p2Over_cliPollSpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKit A b F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKit A b F sid σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollKpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKit A b F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKit A b F kid sid kbk σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollPk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKit A b F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKit A b F pid σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollPk_opkOkEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKit A b F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

private theorem p2Over_cliPollPk_opkOkUpdate (A : RustAlloc) (b : BitVec 64) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKit A b F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

private theorem p2Over_cliPollSelf_kpEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKit A b F peer σ).kpEvs ans = [] := rfl

private theorem p2Over_cliPollSelf_regIdEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKit A b F peer σ).regIdEvs ans = [] := rfl

set_option maxHeartbeats 1200000 in
/-- Instantiates `StageP2PathCOverQpanCliStmt` at `cliExterns W` via `Over.stageP2_over_v1_kits`. -/
theorem stageP2PathCOver_qpan_cli_ok : StageP2PathCOverQpanCliStmt := by
  intro X W img B S Scope y g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss hPromOver himg hh hb hcoins hdec0 hScope hFok hcur hIn hnotMatch _htrust hg1
    hfs1 hinv1 htr01 hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 hpan herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdec0
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (OverP2Inst.stageP2_entry_unpack_pathCOver img y r sess m i s0 sp (sp + 0xc70#64)
      rngPtr v_a8 v_b8 v_d0 hcur hpm rfl hdec0 hFok hScope) ?_
  refine SepWPp.exists_elim fun g => ?_
  refine SepWPp.exists_elim fun recG => ?_
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_left fun ⟨_hkit, _hgcur, hcanon, hctBuf_nz, hopkWord⟩ => ?_
  have hPromMissAt : Over.PromoteMatchingMissAtProp E2E.HooksE.A0 img (cliExterns W)
      y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) :=
    Over.promoteMatchingMissAt_of_gen hPromMiss y.fut g recG sess 4#8
      (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk)
      (OverP2Inst.p2Over_not_sessMatchesMsg sess y.g.msg m i hpm hnotMatch)
      (OverP2Inst.p2Over_serBytes_len m)
  have hPromOverAt : Over.PromoteOverAtProp E2E.HooksE.A0 img (cliExterns W)
      y.fut g recG sess :=
    Over.promoteOverAt_of_gen hPromOver y.fut g recG sess
      (OverP2Inst.encSessionMem_clearPending_lt_32 hIn hcur hcanon)
  let ikBSk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
    | .error _ => List.replicate 32 0
  let ikBPk : SignalPqxdh.Bytes :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
    | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by
    dsimp only [ikBSk]
    split
    · exact vecU8_length _
    · simp
  have hikBPk_len : ikBPk.length = 32 := by
    dsimp only [ikBPk]
    split
    · exact vecU8_length _
    · simp
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp hrel
    have hkpEq := cliPollSelf_kpRel_ok hrel
    dsimp only [ikBSk]
    rw [hkpEq, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp hrel
    have hkpEq := cliPollSelf_kpRel_ok hrel
    dsimp only [ikBPk]
    rw [hkpEq, bytesToBv8_vecU8]
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  exact Over.stageP2_over_v1_kits
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
    (OverP2Inst.stageP2OverV1CallStack_le_subStack (A := E2E.HooksE.A0) img.base y.g.F y.g.peer
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
    y.g.me y.g.peer g recG sess
    hPromMissAt hPromOverAt
    hb hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub
    hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt)
    hinv1.1 hinv1.2
    (cliPollStageP2_fsAt hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl
    (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf hdec0.preKeysWf r' hrel)
    rfl
    (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf hdec0.preKeysWf r' hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf hdec0.preKeysWf r' hrel)
    hkp_sk hkp_pk
    (Or.inr (distinctSid_of_decPkOk₀ hdec0))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf hspkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_spk_err
          ((cliSpk_getRel_error_iff cliIo.rd y.g.F cliWrOk m.spkId _ _
            StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hspkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- KPK lookup error
    (fun _spkRec e sf Pf _ _ hkpkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_kpk_err
          ((cliKpk_getRel_error_iff (A := E2E.HooksE.A0) cliIo.rd y.g.F cliWrOk m.kpkId
            StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hkpkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- OPK lookup error
    (fun _spkRec _kpkRec opkId e sf Pf _ _ _ _ hopkHdr hpkErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, p2Over_cliPollPk_getEvs,
          List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_opk_err hmOpk
          ((cliPk_getRel_error_iff cliIo.rd y.g.F cliWrOk w.opkWord _ _ _ _
            StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inl hpkNone)⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 img.base
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Identity keypair lookup error
    (fun _spkRec _kpkRec wOpk e sf Pf _ _ _ _ _ hkpErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, p2Over_cliPollPk_opkOkEvs,
          p2Over_cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpNone := cliPollSelf_kpRel_err hkpErr
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inl hkpNone))⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_kpErr_entails_decResAt_err E2E.HooksE.A0 img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- PQXDH acceptKeys rejection
    (fun spkRec _spkPubBytes spkPrivBytes kpkRec _kyberPubBytes _kyberPrivBytes
        wOpk _opkPkBytes _opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, p2Over_cliPollPk_opkOkEvs,
          p2Over_cliPollSelf_kpEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := by
        dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := by
        dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree hdec0 hspkRel hspkPubEq hspkPrivEq
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
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inr ⟨k, kp, hk, hkpOk, haccNone0⟩⟩
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Local registration-ID lookup error
    (fun _spkRec _spkPubBytes _spkPrivBytes _kpkRec _kyberPubBytes _kyberPrivBytes
        wOpk _opkPkBytes _opkSkBytes _kp _drKey e sf Pf
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hregErr
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, p2Over_cliPollPk_opkOkEvs,
          p2Over_cliPollSelf_kpEvs, p2Over_cliPollSelf_regIdEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hregNone := cliPollSelf_regIdRel_err hregErr
      have hrej : StageP2PathCOverModelRej X W y :=
        ⟨m, i, hpkToE, hi, hpm, Or.inl (Or.inr (Or.inr hregNone))⟩
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_regIdErr_entails_decResAt_err E2E.HooksE.A0 img.base
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA img y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hrej, hpost⟩)
    -- Fresh Bob V1 session at `+0x1778` with archived `sess` in `previous_sessions`
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2
        hvregs2 hF2 hsym2 => by
      rw [p2Over_cliPollSpk_getEvs, p2Over_cliPollKpk_getEvs, p2Over_cliPollPk_opkOkEvs,
          p2Over_cliPollSelf_kpEvs, p2Over_cliPollSelf_regIdEvs,
          List.append_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htr2
      have hopkUpd := p2Over_cliPollPk_opkOkUpdate E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok hkpRel
      have hregOk := cliPollSelf_regIdRel_ok hregRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := by
        dsimp only [ikBSk]; rw [hkpOk]
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := by
        dsimp only [ikBPk]; rw [hkpOk]
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree hdec0
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
        rw [hikBPk_ok, hdec0.idPairDerived kp hkpOk, bytesToBv8_vecU8]
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
      refine sepWPp_drop_steps hSteps12 ?_
      refine sepWPp_conseq_pre
        (OverP2Inst.p2OverOkPost_fold_pathCOver img y m i w s0 s2 sp (sp + 0xc70#64) rngPtr
          recG G_bob sess (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hcanon hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2) ?_
      refine SepWPp.exists_elim fun prevCap' => ?_
      refine SepWPp.exists_elim fun prevPtr' => ?_
      refine SepWPp.pure_left fun hcap_ne => ?_
      exact hok s2 m i k kp localRegId dk0 G_bob prevCap' prevPtr' y.g.msgA y.g.msgG.msg
        (preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
        hcap_ne hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
        hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2 ⟨hF2, hsym2⟩)

/-! ## 3. `(P : PEParams) (A : RustAlloc)` Stage-Decoupled `Ext` Contract (`StageP2PathCOverQpanExtAt`) -/

/-- `(P : PEParams) (A : RustAlloc)` generalization of `StageP2PathCOverModelRej`. -/
def StageP2PathCOverModelRejExt (X : UnreachedPqxdhPrimitives) (P : PEParams)
    {A : RustAlloc} {B : RunBudgets} {S : RunSem} {img : Obj.Image}
    (y : DpPollGhostState (dpSlotPollKState A img B S)) : Prop :=
  ∃ (m : PreKeyMessageFields) (i : SignalMessage),
    pkToE? y.g.msg = some m ∧
    SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i ∧
    y.g.msg = pmOfE m i ∧
    ((pkStoreKeys y.g.F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error ()) ∨
     (∃ (k : ResponderPreKeySecrets) (kp : RecordCodecs.IdentityKeyPair),
       pkStoreKeys y.g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp ∧
       ∀ reg : BitVec 32,
         SignalPqxdh.Model.acceptKeys (modelPrims X P)
           (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = none))

/-- `(P : PEParams) (A : RustAlloc)` generalization of `StageP2PathCOverErr`. -/
def StageP2PathCOverErrExt (X : UnreachedPqxdhPrimitives) (P : PEParams) (A : RustAlloc) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ err : ApiError AddrVal Unit,
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRejExt X P y ∧
    (Pf ⊢
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

/-- Stage-decoupled `(P : PEParams) (A : RustAlloc) (ext : ...)` CPS Stage P2 contract for Path C
(`opt = some r`, `r.currentSession = some sess`, `¬ DecPkS0.SessMatchesPm sess y.g.msg`) at `+0x0868`
on `tripleRatchetProgAtExt img.base ext` (mirroring `StageP2PathAQpanExtAt`). -/
def StageP2PathCOverQpanExtAt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (g1 : StoresGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    img.base &&& 0xfff#64 = 0#64 →
    y.g.coins.length < 2 ^ 63 →
    DecPkOk₀ P (fun _ => False) y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    r.currentSession = some sess →
    Slots.scopeIn r →
    ¬ DecPkS0.SessMatchesPm sess y.g.msg →
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
      StageP2PathCOverErrExt X P A img B S y s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (G_bob : SessionGhost)
      (prevCap' prevPtr' : BitVec 64)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      prevCap' ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X P)
        (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel G_bob
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
           G_bob (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         p2StageP3Sub5ExtraPrePrev1 A s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
           (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
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

/-- Non-vacuity specialization of `StageP2PathCOverQpanExtAt` to `(W : CliHooks)` / `E2E.HooksE.A0`. -/
theorem stageP2PathCOverQpanExtAt_of_cli (W : CliHooks) (img : Obj.Image)
    (hPromMiss : Over.PromoteMatchingMissGenProp E2E.HooksE.A0 img (cliExterns W))
    (hPromOver : Over.PromoteOverGenProp E2E.HooksE.A0 img (cliExterns W))
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    StageP2PathCOverQpanExtAt img ⟨W.C, W.Q⟩ E2E.HooksE.A0 (cliExterns W) :=
  fun X B S Scope y g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan himg _hread =>
    stageP2PathCOver_qpan_cli_ok X W img B S Scope y g1 r sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
      hPromMiss hPromOver himg hh

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
