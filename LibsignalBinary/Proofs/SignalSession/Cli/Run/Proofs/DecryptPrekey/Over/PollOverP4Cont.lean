/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Spatial
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P4 Continuation

Proves `slotOutTr_d2c_of_reject`, `slotOutTr_d2c_of_accept`, and `closure_pathC_p4_cont`, executing
`Over.StageP4Prev1VRegsStmt` (`+0x34dc → x30`) on overwrite Path C (`¬ SessMatchesPm`) and packaging
both `.ok pt` and `.markErr` into `dpPollSpecState.post`.
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

/-! ## 1. `slotOutTr` D2(c) Helpers -/

theorem slotOutTr_d2c_of_reject {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    (g' : StoresGhost) {err : ApiError AddrVal Unit} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
    (hdec : decPkDefD2c X W Scope F peer me pm coins = some none) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.error err) tr0 trf := by
  refine ⟨fun h => hne_p (Except.error.inj h), fun h => hne_s (Except.error.inj h), ?_⟩
  rw [hS, hdec]

theorem slotOutTr_d2c_of_accept {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hdec : decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.ok pt) tr0 trf := by
  refine ⟨nofun, nofun, ?_⟩
  rw [hS, hdec]
  exact ⟨rfl, hwr⟩

/-! ## 2. Stage P4 Continuation on Path C (`closure_pathC_p4_cont_ext`, `closure_pathC_p4_cont`) -/

/-- Stage-decoupled 4-kit Stage P4 (`+0x34dc → s0.readReg64 .x30`) contract on overwrite Path C
at `(img, A, B, ext)`, mirroring `StageP4PathAV1ExtAt` with `cliPollSessPrev1Kit` /
`cliPollStorePrev1Ops`. -/
def StageP4Prev1PathCExtAt (img : Obj.Image) (A : RustAlloc) (B : RunBudgets)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost) (pid kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (remoteIk : IdentityKey)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (G : SessionGhost) (ss : Session (List (BitVec 8))),
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1Kit A img.base F0 peer σ
    let ops : Over.StorePrev1Ops prev1Kit := cliPollStorePrev1Ops
    let ikit := cliPollIdKit A img.base F0 peer σ
    let pkKit := cliPollPkKit A img.base F0 pid σ
    let kpkKit := cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ
    dpClosSubStack B ≤ 2 ^ 64 →
    SessionExtraRel G ss →
    ops.RecPrev1Ok G ss enc →
    kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
    (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
    pt.length ≤ ptCap.toNat →
    ptCap.toNat < 2 ^ 63 →
    ptPtr ≠ 0#64 →
    s.fs.files = F0 →
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s0.trace <+: s.trace →
    s.readReg64 .x19 = coroPtr →
    s.readReg64 .x24 = s.sp + 0x370#64 →
    s.readReg64 .x25 = s.sp + 0x210#64 →
    s.readReg64 .x26 = outPtr →
    s.readReg64 .x27 = ctxPtr →
    s.readReg64 .x28 = 0xfffffffffffffffe#64 →
    calleeSavedVRegs s = calleeSavedVRegs s0 →
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (Over.stageP4Prev1Pre img prev1Kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
        peer remoteIk baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        Over.StageP4Prev1Branch img prev1Kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
          baseKey StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss sf Pf)
      (PanicOomProp s0)

/-- Non-vacuity bridge instantiating `StageP4Prev1PathCExtAt` at `(E2E.HooksE.A0, cliExterns W)`
from `Over.StageP4Prev1VRegsStmt` and `RunHooks`. -/
theorem stageP4Prev1PathCExtAt_of_cli
    (hP4 : Over.StageP4Prev1VRegsStmt)
    {img : Obj.Image} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    StageP4Prev1PathCExtAt img E2E.HooksE.A0 B (cliExterns W) := by
  intro F0 peer pid kyberPreKeyId signedPreKeyId baseKey remoteIk
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? b_2c0 pt enc G ss
  dsimp only
  intro hsub64 hExtra hrec_ok hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hfiles hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  let σ := cliKitStk B
  have hp4_64 : stageP4CallStack
      (cliPollSessPrev1Kit E2E.HooksE.A0 img.base F0 peer σ)
      (cliPollIdKit E2E.HooksE.A0 img.base F0 peer σ)
      (cliPollPkKit E2E.HooksE.A0 img.base F0 pid σ)
      (cliPollKpkKit E2E.HooksE.A0 img.base F0 kyberPreKeyId signedPreKeyId baseKey σ) ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4CallStack_le_subStack (A := E2E.HooksE.A0) img.base F0 Slots.scopeKit peer pid
        signedPreKeyId kyberPreKeyId baseKey B)
      hsub64
  exact hP4.toA0 img (cliExterns W)
    (cliPollSessPrev1Kit E2E.HooksE.A0 img.base F0 peer σ)
    cliPollStorePrev1Ops
    (cliPollIdKit E2E.HooksE.A0 img.base F0 peer σ)
    (cliPollPkKit E2E.HooksE.A0 img.base F0 pid σ)
    (cliPollKpkKit E2E.HooksE.A0 img.base F0 kyberPreKeyId signedPreKeyId baseKey σ)
    hh.allocContracts
    (cliDropSessionStructure3_ok hh)
    (cliPollSess_prev1KitOkSE W himg F0 peer B)
    (cliPollSess_prev1VtablesOk himg F0 peer σ)
    (cliPollId_kitOkIE W himg F0 peer B)
    (cliPollId_vtablesOk himg F0 peer σ)
    (cliPollPk_kitOkImgE W himg F0 pid B)
    (cliPollPk_vtablesOk himg F0 pid σ)
    (cliPollKpk_kitOkImgE W himg F0 kyberPreKeyId signedPreKeyId baseKey B)
    (cliPollKpk_vtablesOk himg F0 kyberPreKeyId signedPreKeyId baseKey σ)
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss
    (cliBase_aligned himg) hExtra hrec_ok rfl rfl
    hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hp4_64
    (cliPollStageP4_fsAt hh F0 Slots.scopeKit peer pid signedPreKeyId kyberPreKeyId baseKey B hfiles)
    hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

set_option maxHeartbeats 800000 in
private theorem p4_finish_dpPollPost_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (B : RunBudgets) (S : RunSem)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s' sf : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (Pf outAt preKeyMsgRem coinsPost R : SepProp)
    (opkId? : Option (BitVec 32)) (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (ans : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (sess1 oneTime1 : DirGhost) (id1 : IdGhost) (kyber1 : KyberGhost)
    (g' : StoresGhost)
    (hs'_sp0 : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout_ent : outAt ⊢ decResAt A y.out ans ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sess1)
    (hsigned : g'.signed = StoresGhost.opened.signed)
    (honeTime : g'.oneTime = oneTime1)
    (hid : g'.identity = id1)
    (hkyber : g'.kyber = kyber1)
    (hpub : g'.pub = StoresGhost.opened.pub)
    (hpost_f : Pf ⊢ Over.stageP4Prev1ExitAt img
      (cliPollSessPrev1Kit A img.base y.g.F y.g.peer (cliKitStk B))
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKit A img.base y.g.F pid (cliKitStk B))
      (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B))
      s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut opkId?) outAt kpkId spkId pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey sess1 id1 oneTime1 kyber1)
    (hsteps0f : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr_sf : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' ans s0.trace sf.trace)
    (hm_f : sf.mem ⊨
      (Pf ∗ pathAP4RemAt img B y (s0.sp - 0xcd0#64) rngPtr whisperMsgPtr whisperG
        msgVer pid kpkId spkId preKeyMsgRem coinsPost) ∗
      ((memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
        memRegion y.cx 32 ∗
        stageP1VtablesAt img
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))) ∗ R)) :
    sf.mem ⊨
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post
        y s0 sf ∗ R := by
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  have hexit := stageP4PathCExit_entails_exit_ext img B y s0 s' rngPtr 8#64 whisperMsgPtr ptCap ptPtr
    whisperG outAt preKeyMsgRem coinsPost opkId? msgVer pid kpkId spkId pt ans
    sess1 oneTime1 id1 kyber1 g' hs'_sp0 hsp_sub hout_ent hmsg_fold
    hsess hid honeTime hsigned hkyber hpub
  dsimp only at hexit
  have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
  have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
  have hm_f3 : sf.mem ⊨
      (decResAt A y.out ans ∗
        storesAt A y.g.stores g' ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        logOff img ∗
        A.pool ∗
        (TokenInit img ∗ coinsPost ∗ anyHeap ∗ stageP1VtablesAt img kit ikit) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by sep_frame) hm_f2
  have hpost_goal := pathA_exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf g' ans
    (TokenInit img ∗ coinsPost ∗ anyHeap ∗ stageP1VtablesAt img kit ikit)
    hFs hsteps0f htr_sf hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3

private theorem p4_finish_dpPollPost
    {img : Obj.Image} {W : CliHooks}
    (B : RunBudgets) (S : RunSem)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s' sf : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (Pf outAt preKeyMsgRem coinsPost R : SepProp)
    (opkId? : Option (BitVec 32)) (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (ans : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (sess1 oneTime1 : DirGhost) (id1 : IdGhost) (kyber1 : KyberGhost)
    (g' : StoresGhost)
    (hs'_sp0 : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout_ent : outAt ⊢ decResAt E2E.HooksE.A0 y.out ans ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sess1)
    (hsigned : g'.signed = StoresGhost.opened.signed)
    (honeTime : g'.oneTime = oneTime1)
    (hid : g'.identity = id1)
    (hkyber : g'.kyber = kyber1)
    (hpub : g'.pub = StoresGhost.opened.pub)
    (hpost_f : Pf ⊢ Over.stageP4Prev1ExitAt img
      (cliPollSessPrev1Kit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
      (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid (cliKitStk B))
      (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B))
      s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut opkId?) outAt kpkId spkId pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey sess1 id1 oneTime1 kyber1)
    (hsteps0f : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf)
    (htr_sf : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' ans s0.trace sf.trace)
    (hm_f : sf.mem ⊨
      (Pf ∗ pathAP4RemAt img B y (s0.sp - 0xcd0#64) rngPtr whisperMsgPtr whisperG
        msgVer pid kpkId spkId preKeyMsgRem coinsPost) ∗
      ((memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
        memRegion y.cx 32 ∗
        stageP1VtablesAt img
          (cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))) ∗ R)) :
    sf.mem ⊨
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post
        y s0 sf ∗ R :=
  p4_finish_dpPollPost_ext B S hh.fs stk' hneed hstk63 y s0 s' sf
    rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf outAt preKeyMsgRem coinsPost R
    opkId? msgVer pid kpkId spkId pt ans sess1 oneTime1 id1 kyber1 g'
    hs'_sp0 hsp_sub hout_ent hmsg_fold hsess hsigned honeTime hid hkyber hpub
    hpost_f hsteps0f htr_sf hout hm_f

set_option maxHeartbeats 1200000 in
theorem closure_pathC_p4_cont_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP4 : StageP4Prev1PathCExtAt img A B ext)
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hdecOk : DecPkOkD2c P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X P)
      (acceptInput P ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession P ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (tripleRatchetProgAtExt img.base ext) s2 s')
    (hpc' : s'.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hfz' : img.FrozenLoaded s')
    (hsym' : s'.symtab = img.symtab)
    (hent_s' : P_s' ⊢
      Over.stageP3DispatchOkMidPrev1 A img.base s0 s2 y.fut y.out 8#64
        prevCap prevPtr ptCap ptPtr (E2E.Record.encSession (Over.clearPending s_old))
        pt 0#8 G'
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame A img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C (pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      Over.overScratch s2.sp) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F m.spkId σ
    let kpkKit := cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState P ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp P.C P.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let prev1Kit := cliPollSessPrev1Kit A img.base y.g.F y.g.peer σ
  let ops : Over.StorePrev1Ops prev1Kit := cliPollStorePrev1Ops
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F m.spkId σ
  let kpkKit := cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let enc := E2E.Record.encSession (Over.clearPending s_old)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState P meE k m dk
  generalize hst'_eq :
    (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 = st' at hent_s'
  generalize hcoins_eq :
    Coins.coinsAfter img.base y.g.coinsP y.g.coins
      (decryptDraws P.C st0 y.g.msg.message.senderRatchetKey y.g.coins) = coinsPost at hent_s'
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession P meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hok_pair : genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := Prod.ext hok hst'_eq
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (pathA_files_eq_of_trace_eq hFs hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathC_entails_p4_ext img B y s0 s2 s' rngPtr 8#64 prevCap prevPtr
    whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId enc pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm1' : s'.mem ⊨
      (Over.stageP3DispatchOkMidPrev1 A img.base s0 s2 y.fut y.out 8#64
          prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
        genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
          coinsPost ∗
        Over.overScratch s2.sp) ∗
      (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' := by
    simpa only [hs2_sp, sepConj_assoc] using hm1
  have hm2 : s'.mem ⊨
      Over.stageP4Prev1Pre img prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    rw [← sepConj_assoc] at hm1' ⊢
    exact Arm64.Satisfies.mono (sepConj_mono_left hmid) hm1'
  have hm_sess : s'.mem ⊨ sessionStateAt A (y.fut + 0xf8#64) G' st' ∗ anyHeap := by
    refine Arm64.Satisfies.mono ?_ hm2
    unfold Over.stageP4Prev1Pre Over.stageP4Prev1RawPre
    have hcomm : ∀ A1 A2 S A3 A4 : SepProp,
        (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 ⊢ S ∗ anyHeap := fun A1 A2 S A3 A4 =>
      Entails.trans (Entails.of_eq (by ac_rfl : (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 = S ∗ (A1 ∗ A2 ∗ A3 ∗ A4)))
        (sepConj_mono_right (entails_anyHeap _))
    exact hcomm _ _ _ _ _
  have hex0 : SessionExtraRel G'
      { pathAInitSession P meE k m dk with
        state := (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
    rw [hst'_eq]; exact hex'
  have hm_sess0 : s'.mem ⊨ sessionStateAt A (y.fut + 0xf8#64) G'
      (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗ anyHeap := by
    rw [hst'_eq]; exact hm_sess
  have hrecOk : ops.RecPrev1Ok G' ses' enc := by
    have hr := pathC_recPrev1Ok_of_tryDecrypt (A := A) (b := img.base) (σ := σ)
      hs_old hdecOk hver hok hex0 hm_sess0
    dsimp only at hr
    rw [hst'_eq] at hr
    exact hr
  have hwp4 := hP4 y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey y.g.msg.identityKey
    s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    prevCap prevPtr ptCap ptPtr 8#64
    m.opkId 0#8 pt enc G' ses'
    (Nat.le_of_lt (Nat.lt_of_le_of_lt hsp_sub (s0.sp - 0xcd0#64).isLt))
    hex' hrecOk
    (cliPollKpk_markOk_of_pmOfE (A := A) img.base y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE (A := A) img.base y.g.F m i σ hpm_eq)
    hpt_le hpt_lt hpt_ne
    hf' hfz' hsym' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hfz_f, _hsym_f, hBr⟩⟩ |
    ⟨hpanf, Pf, hmf, hoom⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, _hsave, hmark, _hrem, _hstore, htr_f, hpost_f⟩ |
      ⟨hsave, _, _⟩ |
      ⟨c, e, _hsave, hmark, htr_f, hpost_f⟩ |
      ⟨opkId, _c, _e, hopk, _hsave, _hmark, hrem, _, _⟩ |
      ⟨_c, _hsave, _hmark, _hrem, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hpost_f' : Pf ⊢ Over.stageP4Prev1ExitAt img prev1Kit ikit pkKit kpkKit s0 s'
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (vecResultAt A y.out (.ok pt)) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        revert _hrem htr_f hpost_f
        cases m.opkId <;> intro _ _ hp <;> exact hp
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.ok ()) = [] := rfl
        have h4 : ops.storeEvsPrev1 y.g.peer.val G' ses' enc (.ok ()) = [] := rfl
        revert _hrem htr_f hpost_f
        cases m.opkId with
        | none =>
          intro _ htr_f _
          dsimp only at htr_f
          rw [h1, h2, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
        | some opkId =>
          intro _ htr_f _
          have h3 : pkKit.removeEvs opkId (.ok ()) = [] := rfl
          dsimp only at htr_f
          rw [h1, h2, h3, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let kyber' := (kpkMarkOf cliIo.rd y.g.F StoresGhost.opened.kyber
        m.kpkId m.spkId y.g.msg.baseKey).2
      have hmark_eq : StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
          y.g.msg.signedPreKeyId y.g.msg.baseKey = (.ok (), kyber') := by
        rw [hspk_id]
        exact cliKpk_markRel_ok_to_mark hmark
      obtain ⟨hDec, hWr⟩ :=
        decPkDefD2c_pathC_ok X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
          hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (Cli.removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (Over.encodeRecordPrev1 ses' enc) }
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKit, cliPreKeyStoreSpec]
        rw [hpre_id]
      exact p4_finish_dpPollPost_ext B S hFs stk' hneed hstk63 y s0 s' sf rngPtr whisperMsgPtr
        ptCap ptPtr whisperG Pf (vecResultAt A y.out (.ok pt)) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.ok pt)
        (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_accept hS hDec hWr) hm_f
    · exact False.elim (cliId_saveRel_not_err hsave)
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.error e) = [] := rfl
        rw [h1, h2, List.append_nil, List.append_nil, htr'] at htr_f
        exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      have hmark_err :
          (StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
            y.g.msg.signedPreKeyId y.g.msg.baseKey).1 = .error () := by
        rw [hspk_id]
        exact cliKpk_markRel_error_to_mark hmark
      have hDec := decPkDefD2c_pathC_mark_err X P Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
        hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      exact p4_finish_dpPollPost_ext B S hFs stk' hneed hstk63 y s0 s' sf rngPtr whisperMsgPtr
        ptCap ptPtr whisperG Pf (speErrAt kpkKit.markErr y.out e) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.error err)
        StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hs'_sp0 hsp_sub
        (cliPollKpk_markErr_entails_decResAt_anyHeap A img.base y.g.F m.kpkId m.spkId
          y.g.msg.baseKey σ y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl hpost_f hsteps0f htr_sf
        (slotOutTr_d2c_of_reject g' hS nofun nofun hDec) hm_f
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys hk hopk hrem)
    · exact False.elim (by cases hstore)
  · rw [← sepConj_assoc] at hmf
    refine Or.inr (Or.inl ⟨hpanf, Pf ∗ pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG
      (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
      hmf, Or.inl ?_⟩)
    intro R'' hm_pan
    rw [sepConj_assoc] at hm_pan
    have h1 := hoom _ hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at h1
    obtain ⟨hp, hrest⟩ := h1
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hp, ?_⟩
    rw [← sepConj_assoc] at hrest
    exact Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hrest
  · exact (not_satisfies_false_sepConj hoom).elim

theorem closure_pathC_p4_cont
    (hP4 : Over.StageP4Prev1VRegsStmt)
    {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s2 s')
    (hpc' : s'.pc =
      (tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hfz' : img.FrozenLoaded s')
    (hsym' : s'.symtab = img.symtab)
    (hent_s' : P_s' ⊢
      Over.stageP3DispatchOkMidPrev1 E2E.HooksE.A0 img.base s0 s2 y.fut y.out 8#64
        prevCap prevPtr ptCap ptPtr (E2E.Record.encSession (Over.clearPending s_old))
        pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame E2E.HooksE.A0 img s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      Over.overScratch s2.sp) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
    let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId σ
    let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      stageP1VtablesAt img kit ikit
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5PanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) :=
  closure_pathC_p4_cont_ext (P := ⟨W.C, W.Q⟩) B S hh.fs
    (stageP4Prev1PathCExtAt_of_cli hP4 W B himg hh) hS stk' hneed hstk63 y
    hfPeer hs_old hdecOk hloadS hcur htrusted hnot_match
    m i k kp reg dk recG G₁ G' rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr
    whisperG preKeyMsgRem P_s' R pt s0 s2 s'
    hpm_eq hi hk hkp hreg hacc hex hmsg_fold hfiles2 htr2 hs2_sp hsp_align2 hsp_sub
    hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
    hx19' hx24' hx25' hx26' hx27' hx28' hfz' hsym' hent_s'

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
